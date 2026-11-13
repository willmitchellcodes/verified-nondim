"""Framing 2: user constraints on a nondimensionalization, decided with certificates.

You can ask for any combination of

    eliminate_at_least = k     remove at least k parameters
    at_most_params     = m     ...or equivalently: at most m parameters remain
    keep   = [p, ...]          never normalize these parameters to 1
    want   = {"R0": "beta*N/gamma", ...}
                               these named groups must appear as parameters of the reduced model

and `solve` answers SAT (with a concrete reduced model) or UNSAT (with the reason).
Every verdict is backed by integer-matrix facts that `lean_export.py` turns into
Lean theorems, so a "no" is as checkable as a "yes".

THE RANK CRITERION (see docs/DECISIONS.md, D7). Let A be the maximal scaling
matrix. With positive parameters, a set S of parameters can be normalized to 1
simultaneously iff the columns of A indexed by S are linearly independent. So

    "eliminate >= k while keeping P"  is satisfiable
        iff  rank(A restricted to parameter columns not in P) >= k.

Independent column sets form a matroid, so the greedy choice is optimal and no
SAT/ILP search is needed.

THE NAMED-GROUP CRITERION (after Tanburn et al. 2025, Thm 3.8). Wanted groups
w_1..w_k can all appear as reduced parameters iff each is (i) a monomial in the
parameters, (ii) invariant under every scaling (A w = 0, i.e. dimensionless),
and (iii) together they are multiplicatively independent (their exponent
vectors have rank k). If moreover the exponent matrix extends to a unimodular
integer matrix, the regrouping needs no fractional powers.
"""

from __future__ import annotations

from dataclasses import dataclass, field

import sympy as sp

from .intlinalg import independent_columns, int_row_echelon, rank
from .model import Model, OutOfScopeError, monomial_exponents
from .scaling import Nondimensionalization, ScalingAnalysis, analyze, nondimensionalize


@dataclass
class Regrouping:
    """The reduced parameters rewritten in terms of the user's named groups."""

    groups: list[tuple[sp.Symbol, sp.Expr, sp.Expr]]  # (symbol, in original variables, in hat parameters)
    reduced_rhs: list[sp.Expr]  # reduced system written with the group symbols
    reduced_extra_invariants: list[sp.Expr]  # unit links / initial-condition ratios, likewise
    M: sp.Matrix  # q x q: row j = exponents of group j over the hat parameters
    integer: bool  # True iff M is unimodular (no fractional powers needed)
    n_wanted: int

    @property
    def Minv(self) -> sp.Matrix:
        return self.M.inv()


@dataclass
class ConstraintResult:
    satisfiable: bool
    eliminate_at_least: int
    keep: list[sp.Symbol]
    candidates: list[sp.Symbol]  # parameters allowed to be normalized
    available_rank: int  # rank of A on the candidate columns = max number removable
    reason: str  # "ok" | "rank" | "not_monomial" | "not_parameter_only" | "not_invariant" | "dependent"
    explanation: str
    witness: Nondimensionalization | None = None
    want: dict[str, sp.Expr] = field(default_factory=dict)
    want_vectors: sp.Matrix | None = None  # n x k integer exponent vectors of the wanted groups (columns)
    regrouping: Regrouping | None = None

    def __str__(self) -> str:
        return ("SAT: " if self.satisfiable else "UNSAT: ") + self.explanation


def _regroup(nd: Nondimensionalization, want: dict[str, sp.Expr], W_full: sp.Matrix) -> Regrouping:
    """Rewrite the reduced model so each wanted group is one of its parameters.

    An invariant monomial has the same value before and after scaling, so in the
    reduced model it is the same monomial in the hat parameters. That gives a
    k x q integer matrix W; we complete it to an invertible q x q matrix M and
    change parameters kappa -> g with g_j = prod_i kappa_i^{M[j, i]}.
    """
    m = nd.model
    free = [p for p in m.params if p not in nd.normalized]
    q, k = len(free), W_full.shape[1]
    W = sp.Matrix([[W_full[m.index(p), j] for p in free] for j in range(k)]) if k else sp.zeros(0, q)

    # Completion 1: keep as many original hat parameters as possible (most readable).
    unit_rows = independent_columns(W.T.row_join(sp.eye(q)), list(range(k + q)))[k:]
    units = sp.Matrix(len(unit_rows), q, lambda a, i: 1 if i == unit_rows[a] - k else 0)
    M = W.col_join(units) if q else sp.zeros(0, 0)
    if q and abs(M.det()) != 1 and k:
        # Completion 2: a unimodular completion exists iff W is primitive; try it.
        U, H, _ = int_row_echelon(W.T)
        B = U.inv().T
        M2 = W.col_join(B[k:, :])
        if abs(M2.det()) == 1:
            M = M2
    integer = (q == 0) or abs(M.det()) == 1

    names = list(want)
    kappa = [nd.new_symbol[p] for p in free]
    syms, groups = [], []
    for j in range(q):
        in_hat = sp.Mul(*[kappa[i] ** M[j, i] for i in range(q)])
        if j < k:
            g = sp.Symbol(names[j], positive=True)
        elif in_hat in kappa:
            g = in_hat  # an untouched hat parameter keeps its name
        else:
            g = sp.Symbol(f"pi_{j - k + 1}", positive=True)
        in_orig = sp.powsimp(in_hat.xreplace({nd.new_symbol[p]: nd.new_expr[p] for p in free}), force=True)
        syms.append(g)
        groups.append((g, sp.simplify(in_orig), in_hat))
    Minv = M.inv() if q else M
    back = {kappa[i]: sp.Mul(*[syms[j] ** Minv[i, j] for j in range(q)]) for i in range(q)}
    rhs = [sp.simplify(g.xreplace(back)) for g in nd.reduced_rhs]
    inv = [sp.simplify(g.xreplace(back)) for g in nd.reduced_extra_invariants]
    return Regrouping(groups, rhs, inv, M, integer, k)


def solve(
    model: Model,
    eliminate_at_least: int = 0,
    at_most_params: int | None = None,
    keep=(),
    want: dict | None = None,
    analysis: ScalingAnalysis | None = None,
) -> ConstraintResult:
    """Decide a constraint. Names may be given as strings: keep=["beta"], want={"R0": "beta*N/gamma"}."""
    an = analysis or analyze(model)
    keep = [model.symbol(p) if isinstance(p, str) else p for p in keep]
    want = {name: model.parse(e) for name, e in (want or {}).items()}
    k = eliminate_at_least
    if at_most_params is not None:
        k = max(k, len(model.params) - at_most_params)
    cands = [p for p in model.params if p not in keep]
    cols = [model.index(p) for p in cands]
    r = an.A.shape[0]
    rho_c = rank(an.A[:, cols]) if cols and r else 0
    base = dict(eliminate_at_least=k, keep=keep, candidates=cands, available_rank=rho_c, want=want)

    def fail(reason, text, **kw):
        return ConstraintResult(False, reason=reason, explanation=text, **base, **kw)

    if rho_c < k:
        return fail(
            "rank",
            f"only {rho_c} independent scaling direction(s) act on {[str(c) for c in cands]}, "
            f"so at most {rho_c} of them can be removed (asked for {k}).",
        )

    # Wanted groups: monomial, parameter-only, invariant, independent.
    vecs = []
    for name, expr in want.items():
        num, den = sp.fraction(sp.cancel(sp.together(expr)))
        if len(sp.Add.make_args(sp.expand(num))) != 1 or len(sp.Add.make_args(sp.expand(den))) != 1:
            return fail("not_monomial", f"{name} = {expr} is not a product of powers, so it cannot be a "
                        "scaling invariant chosen by this method (cf. Segel-Slemrod's e0/(s0 + Km)).")
        try:
            v = monomial_exponents(expr, model.variables)
        except OutOfScopeError as e:
            return fail("not_monomial", f"{name} = {expr}: {e}")
        if any(not x.is_Integer for x in v):
            return fail("not_monomial", f"{name} = {expr} has fractional exponents; use an integer power of it.")
        if any(v[model.index(x)] != 0 for x in [model.t, *model.states]):
            return fail("not_parameter_only", f"{name} = {expr} involves time or a state variable; "
                        "a reduced *parameter* must be built from parameters only.")
        vecs.append(v)
    W_full = sp.Matrix(vecs).T if vecs else sp.zeros(len(model.variables), 0)
    if vecs:
        moved = an.A * W_full
        for j, name in enumerate(want):
            bad = [i for i in range(r) if moved[i, j] != 0]
            if bad:
                return fail("not_invariant", f"{name} = {want[name]} is not dimensionless: scaling "
                            f"#{bad[0] + 1} multiplies it by lambda^{moved[bad[0], j]}.", want_vectors=W_full)
        max_groups = len(model.params) - an.param_rank
        if rank(W_full) < len(vecs) or len(vecs) > max_groups:
            return fail("dependent", f"the wanted groups are not independent (rank {rank(W_full)} < {len(vecs)}); "
                        f"at most {max_groups} independent parameter groups exist.", want_vectors=W_full)

    nd = nondimensionalize(model, keep=keep, analysis=an)
    text = f"normalize {[str(s) for s in nd.normalized]} (removes {len(nd.normalized)} >= {k})"
    regroup = None
    if want:
        regroup = _regroup(nd, want, W_full)
        text += "; groups " + ", ".join(f"{g} = {e}" for g, e, _ in regroup.groups)
        if not regroup.integer:
            text += " (needs fractional powers: the wanted groups do not extend to a unimodular basis)"
    return ConstraintResult(True, reason="ok", explanation=text + ".", witness=nd,
                            want_vectors=W_full if vecs else None, regrouping=regroup, **base)


def check_constraint(model, eliminate_at_least, keep=(), want=(), analysis=None) -> ConstraintResult:
    """Backward-compatible wrapper around `solve` (want may be a list of expressions)."""
    if not isinstance(want, dict):
        want = {f"g{i + 1}": w for i, w in enumerate(want)}
    return solve(model, eliminate_at_least, keep=keep, want=want, analysis=analysis)


def max_removable(model: Model, keep=(), analysis: ScalingAnalysis | None = None) -> int:
    """The largest k for which "eliminate >= k while keeping `keep`" is satisfiable."""
    return solve(model, 0, keep=keep, analysis=analysis).available_rank

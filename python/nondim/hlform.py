"""A solver-independent description of a scaling reduction ("Hubert-Labahn form").

Any tool that reduces a model by scaling symmetries (desr, or the small solver in
this package) can be described by the same few integer matrices:

    A      r x n   scalings of the n variables (states and parameters)
    tau    r       how each scaling acts on time
    V = [Vi | Vn]  n x n, unimodular, with inverse  W = [Wu ; Wd]
           Vi: auxiliary monomials the reduction sets to 1
           Vn: the invariants = the new, dimensionless variables
    G, d   with  G * (A * Vi) = d * I   (the auxiliary monomials can be scaled freely)

plus the reduced right-hand sides written in the invariants. `HLReduction` holds
exactly that. `check()` re-derives every relation with exact arithmetic, and
`lean_export2.certificate` turns the same relations into Lean theorems, so the
solver that produced the matrices never has to be trusted.

Time is kept separate from the other variables because the Lean theory treats
autonomous systems dx/dt = f(x): a scaling acts on the point x and on time.
"""

from __future__ import annotations

from dataclasses import dataclass, field
from functools import reduce

import sympy as sp

from .intlinalg import rank
from .model import Model, OutOfScopeError, exponent_matrix, monomial_exponents
from .scaling import Nondimensionalization


class NotSupported(ValueError):
    """The reduction is valid but outside what the general Lean theory covers yet."""


@dataclass
class HLReduction:
    model: Model
    source: str  # e.g. "desr 3.0.0" or "nondim"
    variables: list[sp.Symbol]  # the n non-time variables, in Lean index order
    A: sp.Matrix  # r x n
    tau: list[int]  # r
    Vi: sp.Matrix  # n x k
    Vn: sp.Matrix  # n x m
    Wu: sp.Matrix  # k x n
    Wd: sp.Matrix  # m x n
    G: sp.Matrix  # k x r
    d: int
    invariant_symbols: list[sp.Symbol]  # names of the m invariants (columns of Vn)
    reduced_rhs: dict[sp.Symbol, sp.Expr]  # state -> its reduced equation, in the invariant symbols
    time_exponents: list[int] = field(default_factory=list)  # w: new time = (prod variables^w) * t
    state_col: dict[sp.Symbol, int] = field(default_factory=dict)  # state -> its column of Vn
    time_invariant: sp.Expr | None = None  # the new time, e.g. gamma*t (for reports)
    # the same data with time included, for the Buckingham Pi statement
    full_order: list[sp.Symbol] = field(default_factory=list)
    Dfull: sp.Matrix | None = None  # r x (n+1)
    Pfull: sp.Matrix | None = None  # (n+1) x (n+1-r): all invariants, including the new time
    V1full: sp.Matrix | None = None
    W1full: sp.Matrix | None = None
    W2full: sp.Matrix | None = None

    # ------------------------------------------------------------ derived

    @property
    def n(self) -> int:
        return len(self.variables)

    @property
    def r(self) -> int:
        return self.A.shape[0]

    @property
    def states(self) -> list[sp.Symbol]:
        return list(self.model.states)

    @property
    def parameters(self) -> list[sp.Symbol]:
        return [v for v in self.variables if v not in self.model.states]

    def invariant_monomials(self) -> list[sp.Expr]:
        return [sp.Mul(*[v ** self.Vn[i, j] for i, v in enumerate(self.variables)]) for j in range(self.Vn.shape[1])]

    def auxiliary_monomials(self) -> list[sp.Expr]:
        return [sp.Mul(*[v ** self.Vi[i, j] for i, v in enumerate(self.variables)]) for j in range(self.Vi.shape[1])]

    def reduced_parameters(self) -> list[sp.Symbol]:
        """Invariants built from parameters only: the constants of the reduced model."""
        state_rows = [self.variables.index(z) for z in self.model.states]
        return [s for j, s in enumerate(self.invariant_symbols)
                if all(self.Vn[i, j] == 0 for i in state_rows)]

    def terms(self) -> list[list[tuple[sp.Rational, list[int]]]]:
        """Each variable's equation as a list of (coefficient, exponent vector) terms."""
        return system_terms(self.model, self.variables)

    def time_factor(self) -> sp.Expr:
        """T, the monomial in the parameters with new time = T * t."""
        return sp.Mul(*[v ** e for v, e in zip(self.variables, self.time_exponents)])

    def state_factor_exponents(self, z: sp.Symbol) -> list[int]:
        """u with  new variable for z  =  z * prod variables^u  (u involves parameters only)."""
        j, row = self.state_col[z], self.variables.index(z)
        return [int(self.Vn[i, j]) - (1 if i == row else 0) for i in range(self.n)]

    def reconstruct(self) -> dict[sp.Symbol, sp.Expr]:
        """Each variable written in the invariants, on the cross-section (auxiliaries = 1)."""
        return {v: sp.Mul(*[self.invariant_symbols[j] ** self.Wd[j, p] for j in range(self.Wd.shape[0])])
                for p, v in enumerate(self.variables)}

    # ------------------------------------------------------------ checks

    def check(self) -> None:
        """Re-derive every relation the Lean certificate will state. Raises ValueError on failure."""
        n, r, k, m = self.n, self.r, self.Vi.shape[1], self.Vn.shape[1]

        def need(cond, what):
            if not cond:
                raise ValueError(f"{self.source} reduction of {self.model.name}: {what}")

        need(self.A.shape == (r, n) and len(self.tau) == r, "A / tau have the wrong shape")
        need(self.Vi.shape == (n, k) and self.Vn.shape == (n, m) and k + m == n, "V has the wrong shape")
        need(self.Wu.shape == (k, n) and self.Wd.shape == (m, n), "W has the wrong shape")
        # 1. symmetry, term by term, straight from the equations
        for i, terms in enumerate(self.terms()):
            for _, exps in terms:
                w = self.A * sp.Matrix(exps)
                need(all(w[j] + self.tau[j] == self.A[j, i] for j in range(r)),
                     f"scaling is not a symmetry of the equation for {self.variables[i]}")
        # 2. unimodular pair, invariants, free auxiliaries
        need(self.Vi * self.Wu + self.Vn * self.Wd == sp.eye(n), "Vi*Wu + Vn*Wd != 1")
        need(self.A * self.Vn == sp.zeros(r, m), "a column of Vn is not invariant")
        need(self.d != 0 and self.G * (self.A * self.Vi) == self.d * sp.eye(k), "G*(A*Vi) != d*1")
        # 3. auxiliaries involve parameters only
        params = set(self.parameters)
        need(all(self.Vi[i, j] == 0 or v in params for i, v in enumerate(self.variables) for j in range(k)),
             "an auxiliary monomial involves a state variable")
        # 4. the reduced equations, as a statement about the original variables:
        #    new variable nu_z = z * c_z(parameters), new time = T(parameters) * t, and
        #    c_z * f_z  ==  T * g_z(invariants)   identically.
        need(len(self.time_exponents) == n, "time exponents have the wrong length")
        need(all(e == 0 or v in params for v, e in zip(self.variables, self.time_exponents)),
             "the new time involves a state variable")
        need(set(self.state_col) == set(self.model.states), "some state has no new variable")
        to_original = dict(zip(self.invariant_symbols, self.invariant_monomials()))
        T = self.time_factor()
        for z, f in zip(self.model.states, self.model.rhs):
            u = self.state_factor_exponents(z)
            need(all(e == 0 or v in params for v, e in zip(self.variables, u)),
                 f"the new variable for {z} is not {z} times a monomial in the parameters")
            c = sp.Mul(*[v ** e for v, e in zip(self.variables, u)])
            diff = sp.simplify(c * f - T * self.reduced_rhs[z].xreplace(to_original))
            need(diff == 0, f"reduced equation for {z} does not match (difference {diff})")
        # 5. the full matrices (with time) for the Pi theorem
        if self.Dfull is not None:
            N = n + 1
            need(self.V1full * self.W1full + self.Pfull * self.W2full == sp.eye(N), "full V*W != 1")
            need(self.Dfull * self.Pfull == sp.zeros(r, N - r), "full invariants are not invariant")
            need(self.G * (self.Dfull * self.V1full) == self.d * sp.eye(k), "full G*(D*V1) != d*1")
            tpos = self.full_order.index(self.model.t)
            tcol = [1 if i == tpos else self.time_exponents[self.variables.index(v)]
                    for i, v in enumerate(self.full_order)]
            need(any(list(self.Pfull[:, j]) == tcol for j in range(self.Pfull.shape[1])),
                 "the new time is not one of the listed invariants")

    def independent_K(self) -> sp.Matrix:
        """The exponent matrix derived from the equations by *this* package (rows: time, then variables).

        Used to cross-check a foreign solver: its scalings must kill these columns, and there
        must be as many scalings as rank-nullity allows.
        """
        K = exponent_matrix(self.model)  # rows in model.variables order: t, states, params
        order = [self.model.t, *self.variables]
        return sp.Matrix([[K[self.model.index(v), j] for j in range(K.shape[1])] for v in order])

    def full_scaling_matrix(self) -> sp.Matrix:
        """[tau | A]: rows are scalings, columns are time then the variables."""
        return sp.Matrix(self.tau).row_join(self.A) if self.r else sp.zeros(0, self.n + 1)

    def is_maximal(self) -> bool:
        K = self.independent_K()
        F = self.full_scaling_matrix()
        return F * K == sp.zeros(self.r, K.shape[1]) and rank(F) == self.r == self.n + 1 - rank(K)

    def summary(self) -> str:
        lines = [f"{self.model.name} reduced by {self.source}",
                 f"  scalings: {self.r};  variables: {', '.join(map(str, self.variables))}"]
        if self.time_invariant is not None:
            lines.append(f"  new time: {self.time_invariant}")
        for s, mono in zip(self.invariant_symbols, self.invariant_monomials()):
            lines.append(f"    {s} = {mono}")
        lines.append("  reduced system:")
        for z in self.model.states:
            lines.append(f"    d{self.invariant_symbols[self.state_col[z]]}/d(new time) = {self.reduced_rhs[z]}")
        lines.append(f"  parameters: {len(self.parameters)} -> {len(self.reduced_parameters())}")
        return "\n".join(lines)


def system_terms(model: Model, variables: list[sp.Symbol]) -> list[list[tuple[sp.Rational, list[int]]]]:
    """Expand each right-hand side into terms coefficient * prod x^e (integer e, possibly negative)."""
    if model.t in set().union(*[f.free_symbols for f in model.rhs]):
        raise NotSupported("the general theory covers autonomous systems (time must not appear in the equations)")
    out = []
    for v in variables:
        if v not in model.states:
            out.append([])
            continue
        f = sp.expand(model.rhs[model.states.index(v)])
        terms = []
        for term in sp.Add.make_args(f):
            if term == 0:
                continue
            coeff, _ = term.as_coeff_Mul()
            try:
                exps = monomial_exponents(term, variables)
            except OutOfScopeError as e:
                raise NotSupported(f"equation for {v}: {term} is not a monomial ({e}); "
                                   "the general theory covers polynomial right-hand sides") from e
            if any(not sp.Rational(x).is_Integer for x in exps):
                raise NotSupported(f"equation for {v}: fractional exponent in {term}")
            terms.append((sp.Rational(coeff), [int(x) for x in exps]))
        out.append(terms)
    return out


def left_inverse_certificate(B: sp.Matrix) -> tuple[sp.Matrix, int]:
    """Integer G and d != 0 with G * B = d * I, for B with independent columns."""
    k = B.shape[1]
    if k == 0:
        return sp.zeros(0, B.shape[0]), 1
    if B.rank() < k:
        raise ValueError("columns are linearly dependent: no left inverse exists")
    L = (B.T * B).inv() * B.T  # rational left inverse
    d = reduce(sp.ilcm, [sp.Rational(x).q for x in L], 1)
    G = (L * d).applyfunc(sp.Integer)
    assert G * B == d * sp.eye(k)
    return G, int(d)


def from_nondim(nd: Nondimensionalization) -> HLReduction:
    """Describe a reduction computed by this package's own solver in Hubert-Labahn form."""
    m, an = nd.model, nd.analysis
    if m.extra_invariants:
        raise NotSupported("models with unit links (same_units) are not yet expressed in the general Lean theory")
    if m.t in set().union(*[f.free_symbols for f in m.rhs]):
        raise NotSupported("the general theory covers autonomous systems (time must not appear in the equations)")
    if an.A.shape[0] == 0:
        raise NotSupported(f"{m.name} has no scaling symmetry: there is nothing to reduce")
    system_terms(m, [*m.states, *m.params])  # polynomial right-hand sides only
    if not nd.integer_exponents():
        raise NotSupported("the reduction uses fractional powers (the Hubert-Labahn form needs integer ones)")
    if len(nd.normalized) != an.A.shape[0] or not nd.fully_invariant():
        raise NotSupported("the reduction does not use every scaling symmetry (some act on states or time only)")
    variables = [*m.states, *m.params]
    full = [m.t, *variables]
    col = lambda v: m.index(v)  # noqa: E731
    A = sp.Matrix([[an.A[j, col(v)] for v in variables] for j in range(an.A.shape[0])])
    tau = [int(an.A[j, col(m.t)]) for j in range(an.A.shape[0])]
    kept = [v for v in variables if v not in nd.normalized]

    def unit(v, order):
        return [1 if u == v else 0 for u in order]

    def expvec(v, order):
        e = nd.exponent_vector(v)
        return [int(e[col(u)]) for u in order]

    Vi = sp.Matrix([unit(s, variables) for s in nd.normalized]).T
    Vn = sp.Matrix([expvec(v, variables) for v in kept]).T
    W = Vi.row_join(Vn).inv()
    k = len(nd.normalized)
    G, d = left_inverse_certificate(A * Vi)
    # with time
    V1f = sp.Matrix([unit(s, full) for s in nd.normalized]).T
    Pf = sp.Matrix([expvec(v, full) for v in [m.t, *kept]]).T
    Wf = V1f.row_join(Pf).inv()
    Df = sp.Matrix(tau).row_join(A)
    red = HLReduction(
        model=m, source="nondim", variables=variables, A=A, tau=tau,
        Vi=Vi, Vn=Vn, Wu=W[:k, :], Wd=W[k:, :], G=G, d=d,
        invariant_symbols=[nd.new_symbol[v] for v in kept],
        reduced_rhs={z: g for z, g in zip(m.states, nd.reduced_rhs)},
        time_exponents=expvec(m.t, variables), state_col={z: kept.index(z) for z in m.states},
        time_invariant=nd.new_expr[m.t],
        full_order=full, Dfull=Df, Pfull=Pf, V1full=V1f, W1full=Wf[:k, :], W2full=Wf[k:, :],
    )
    red.check()
    return red

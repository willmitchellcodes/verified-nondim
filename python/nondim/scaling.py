"""Maximal scaling symmetries and the nondimensionalization they produce.

Pipeline (after Hubert & Labahn 2013 and Tanburn et al. 2025):

1. Build the exponent matrix K (see model.py).
2. The integer left kernel of K is the lattice of all scaling symmetries.
   A basis of it, written as rows, is the maximal scaling matrix A (r x n).
3. Let rho = rank of A restricted to the parameter columns. At most rho
   parameters can be removed by scaling, so the reduced model has
   (#params - rho) parameters, and no scaling can do better.
4. Pick a set S of rho parameters whose columns of A are independent and
   "normalize" them to 1. Every other variable x becomes the invariant
       x_hat = x * prod_{s in S} s^{e_s},  with A1[:, S] e = -A1[:, x].
5. Because the vector field is invariant, the reduced right-hand side is just
   f with s := 1 for s in S and every other variable replaced by its hat.

This module is the *untrusted solver*. Its outputs are later re-checked in
Lean (see lean_export.py), so a bug here shows up as a failed proof, not as a
silently wrong model.
"""

from __future__ import annotations

from dataclasses import dataclass, field

import sympy as sp

from .intlinalg import (
    all_column_bases,
    independent_columns,
    int_row_echelon,
    left_kernel_basis,
    rank,
)
from .model import Model, exponent_matrix


@dataclass
class ScalingAnalysis:
    model: Model
    K: sp.Matrix  # n x m exponent matrix
    A: sp.Matrix  # r x n maximal scaling matrix (rows = independent scalings)
    rank_K: int
    param_rank: int  # rho: max number of parameters removable by scaling

    @property
    def n_scalings(self) -> int:
        return self.A.shape[0]

    @property
    def param_cols(self) -> list[int]:
        m = self.model
        return [m.index(p) for p in m.params]

    @property
    def min_params(self) -> int:
        return len(self.model.params) - self.param_rank

    def describe_scalings(self) -> list[str]:
        V = self.model.variables
        out = []
        for i in range(self.A.shape[0]):
            parts = [f"{v}^{self.A[i, j]}" for j, v in enumerate(V) if self.A[i, j] != 0]
            out.append("lambda acts as  " + ", ".join(parts))
        return out

    def summary(self) -> str:
        p = len(self.model.params)
        lines = [
            str(self.model),
            f"  exponent matrix K: {self.K.shape[0]} x {self.K.shape[1]}, rank {self.rank_K}",
            f"  independent scaling symmetries r = n - rank K = "
            f"{len(self.model.variables)} - {self.rank_K} = {self.n_scalings}",
            *("    " + s for s in self.describe_scalings()),
            f"  rank of A on parameter columns rho = {self.param_rank}",
            f"  => parameters: {p} -> {self.min_params} (best possible by scaling)",
        ]
        return "\n".join(lines)


def analyze(model: Model) -> ScalingAnalysis:
    K = exponent_matrix(model)
    n = len(model.variables)
    A = left_kernel_basis(K) if K.shape[1] else sp.eye(n)
    rK = rank(K) if K.shape[1] else 0
    # Tidy A: echelon on parameter columns first, so the first rho rows act on
    # parameters and any remaining rows act only on t and the states.
    pc = [model.index(p) for p in model.params]
    other = [j for j in range(n) if j not in pc]
    perm = pc + other
    if A.shape[0]:
        _, Hp, _ = int_row_echelon(A[:, perm])
        inv = [perm.index(j) for j in range(n)]
        A = Hp[:, inv]
    rho = rank(A[:, pc]) if A.shape[0] and pc else 0
    return ScalingAnalysis(model, K, A, rK, rho)


@dataclass
class Nondimensionalization:
    analysis: ScalingAnalysis
    normalized: list[sp.Symbol]  # S: parameters set to 1
    A1: sp.Matrix  # k x n subgroup of scalings used (A1[:, S] invertible)
    exponents: dict[sp.Symbol, dict[sp.Symbol, sp.Rational]]  # x_hat = x * prod s^e
    new_symbol: dict[sp.Symbol, sp.Symbol]
    new_expr: dict[sp.Symbol, sp.Expr]  # x_hat written in original variables
    reduced_rhs: list[sp.Expr]  # in hat variables
    reduced_extra_invariants: list[sp.Expr] = field(default_factory=list)

    @property
    def model(self) -> Model:
        return self.analysis.model

    @property
    def reduced_params(self) -> list[sp.Symbol]:
        return [self.new_symbol[p] for p in self.model.params if p not in self.normalized]

    def exponent_vector(self, x: sp.Symbol) -> list[sp.Rational]:
        """Exponent vector (over the original variables) of the invariant x_hat."""
        V = self.model.variables
        v = [sp.Integer(0)] * len(V)
        v[V.index(x)] = sp.Integer(1)
        for s, e in self.exponents[x].items():
            v[V.index(s)] += e
        return v

    def fully_invariant(self) -> bool:
        """True if every new variable is invariant under *all* scalings in A."""
        A = self.analysis.A
        for x in self.new_expr:
            if any(x != 0 for x in A * sp.Matrix(self.exponent_vector(x))):
                return False
        return True

    def integer_exponents(self) -> bool:
        return all(e.is_Integer for d in self.exponents.values() for e in d.values())

    def summary(self) -> str:
        m = self.model
        lines = [f"Nondimensionalization of {m.name}: normalize {', '.join(map(str, self.normalized)) or '(nothing)'} to 1"]
        for x in m.variables:
            if x in self.normalized:
                continue
            lines.append(f"    {self.new_symbol[x]} = {self.new_expr[x]}")
        tau = self.new_symbol[m.t]
        lines.append("  reduced system:")
        for z, g in zip(m.states, self.reduced_rhs):
            lines.append(f"    d{self.new_symbol[z]}/d{tau} = {g}")
        if self.reduced_extra_invariants:
            lines.append("  extra invariants become: " + ", ".join(map(str, self.reduced_extra_invariants)))
        lines.append(
            f"  parameters {len(m.params)} -> {len(self.reduced_params)}: "
            + (", ".join(map(str, self.reduced_params)) or "(none)")
        )
        return "\n".join(lines)


def _hat(x: sp.Symbol) -> sp.Symbol:
    return sp.Symbol(f"{x.name}_hat", positive=True)


def nondimensionalize(
    model: Model,
    normalize: list[sp.Symbol] | None = None,
    keep: tuple[sp.Symbol, ...] | list[sp.Symbol] = (),
    analysis: ScalingAnalysis | None = None,
    names: dict[sp.Symbol, str] | None = None,
) -> Nondimensionalization:
    """Reduce `model` by normalizing the parameters in `normalize` to 1.

    Parameters may be given as symbols or by name: nondimensionalize(sir, ["gamma", "N"]).
    If `normalize` is None, greedily pick as many parameters as possible,
    skipping those in `keep`. `names` optionally renames the new variables, e.g.
    {"t": "tau", "S": "X", "beta": "R0"}.
    """
    an = analysis or analyze(model)
    V = model.variables
    A = an.A
    as_symbol = lambda x: model.symbol(x) if isinstance(x, str) else x  # noqa: E731
    keep = [as_symbol(k) for k in keep]
    if normalize is not None:
        normalize = [as_symbol(s) for s in normalize]
    if normalize is None:
        order = [model.index(p) for p in model.params if p not in keep]
        S_idx = independent_columns(A, order) if A.shape[0] else []
        normalize = [V[j] for j in S_idx]
    if any(s not in model.params for s in normalize):
        raise ValueError("can only normalize parameters")
    S_idx = [model.index(s) for s in normalize]
    k = len(S_idx)
    if k and rank(A[:, S_idx]) < k:
        raise ValueError(
            f"cannot normalize {normalize} simultaneously: their columns of the "
            "scaling matrix are dependent (no family of scalings moves them independently)"
        )
    if k:
        U, _, _ = int_row_echelon(A[:, S_idx])
        A1 = (U * A)[:k, :]
        B = A1[:, S_idx]
        Binv = B.inv()
    else:
        A1 = sp.zeros(0, len(V))
        Binv = sp.zeros(0, 0)

    names = {as_symbol(k): v for k, v in (names or {}).items()}
    exponents: dict[sp.Symbol, dict[sp.Symbol, sp.Rational]] = {}
    new_symbol: dict[sp.Symbol, sp.Symbol] = {}
    new_expr: dict[sp.Symbol, sp.Expr] = {}
    for j, x in enumerate(V):
        if j in S_idx:
            continue
        e = -Binv * A1[:, j] if k else sp.zeros(0, 1)
        exponents[x] = {V[S_idx[i]]: e[i] for i in range(k) if e[i] != 0}
        new_symbol[x] = sp.Symbol(names[x], positive=True) if x in names else _hat(x)
        new_expr[x] = x * sp.Mul(*[s**p for s, p in exponents[x].items()])

    subs = {s: sp.Integer(1) for s in normalize}
    subs.update(new_symbol)
    reduced = [sp.simplify(f.xreplace(subs)) for f in model.rhs]
    red_inv = [sp.simplify(g.xreplace(subs)) for g in model.extra_invariants]
    return Nondimensionalization(an, list(normalize), A1, exponents, new_symbol, new_expr, reduced, red_inv)


def verify_symbolically(nd: Nondimensionalization) -> list[sp.Expr]:
    """Untrusted (SymPy) check of the chain rule identity for each equation.

    If x_hat = x * M_x then d z_hat / d tau = (M_z / M_t) * dz/dt, so we need
        (M_z / M_t) * f(t, z, c)  ==  g(t_hat, z_hat, c_hat)  (written in old variables).
    Returns the list of residuals (all zero when correct).
    """
    m = nd.model
    back = {nd.new_symbol[x]: nd.new_expr[x] for x in nd.new_expr}
    M_t = nd.new_expr[m.t] / m.t
    residuals = []
    for z, f, g in zip(m.states, m.rhs, nd.reduced_rhs):
        M_z = nd.new_expr[z] / z
        r = sp.simplify(sp.powsimp(M_z / M_t * f - g.xreplace(back), force=True))
        residuals.append(r)
    return residuals


def all_nondimensionalizations(model: Model, keep=(), analysis: ScalingAnalysis | None = None, names=None):
    """Every maximal choice of normalized parameters (one per column basis of A)."""
    an = analysis or analyze(model)
    cands = [model.index(p) for p in model.params if p not in keep]
    size = rank(an.A[:, cands]) if cands and an.A.shape[0] else 0
    V = model.variables
    return [
        nondimensionalize(model, [V[j] for j in S], analysis=an, names=names)
        for S in all_column_bases(an.A, cands, size)
    ]

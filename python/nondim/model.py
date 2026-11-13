"""ODE models and their exponent matrices.

A model is dz_i/dt = f_i(t, z, c) with time t, states z and positive
parameters c. A diagonal scaling multiplies every variable by a power of a
scale factor lambda:

    t -> lambda^{a_t} t,   z_i -> lambda^{a_i} z_i,   c_j -> lambda^{b_j} c_j.

The system is unchanged by the scaling exactly when every quantity
t * f_i / z_i is unchanged (Tanburn et al. 2025, Lemma 3.1). For a sum of
monomials this means every monomial is invariant, i.e. its exponent vector k
satisfies a . k = 0. Stacking those exponent vectors as columns gives the
exponent matrix K, and the scalings are the integer vectors a with a K = 0.
"""

from __future__ import annotations

from dataclasses import dataclass, field
from functools import reduce

import sympy as sp


class OutOfScopeError(ValueError):
    """Raised when an expression is not a ratio of monomial sums in the model's variables.

    Examples: exp(-E/(R*T)), log(x), sin(theta). These are a documented failure
    mode of scaling-based nondimensionalization, not a bug.
    """


@dataclass
class Model:
    name: str
    t: sp.Symbol
    states: list[sp.Symbol]
    params: list[sp.Symbol]
    rhs: list[sp.Expr]
    # Monomials that must stay invariant under any scaling we use. Use these for
    # initial conditions (S/S0), conservation laws (S/N), or unit constraints
    # the equations alone do not enforce (b/c when b and c share units).
    extra_invariants: list[sp.Expr] = field(default_factory=list)
    # What is measured, e.g. {"y": rho*I}. Only used by identifiability.py.
    outputs: dict[str, sp.Expr] = field(default_factory=dict)
    notes: str = ""

    def __post_init__(self):
        if len(self.states) != len(self.rhs):
            raise ValueError("need exactly one right-hand side per state")

    @property
    def variables(self) -> list[sp.Symbol]:
        """Column order used everywhere: [t, states..., params...]."""
        return [self.t, *self.states, *self.params]

    @classmethod
    def from_strings(
        cls,
        name: str,
        equations: dict[str, str],
        params: str,
        same_units: list[tuple[str, str]] = (),
        outputs: dict[str, str] | None = None,
        time: str = "t",
        notes: str = "",
    ) -> "Model":
        """Build a model from plain text. This is the easiest way to add your own.

            Model.from_strings(
                "SIR",
                equations={"S": "-beta*S*I", "I": "beta*S*I - gamma*I"},
                params="beta gamma N",
                same_units=[("S", "N"), ("I", "N")],   # S and I are measured like N
            )

        `same_units` pairs become invariants a/b: the algorithm may only use
        scalings that treat both members of a pair alike. `outputs` names what
        is measured (used only by the identifiability analysis).
        """
        names = [time, *equations, *params.split()]
        sym = {n: sp.Symbol(n, positive=True) for n in names}
        parse = lambda e: sp.sympify(e, locals=sym)  # noqa: E731
        for expr in [*equations.values(), *(outputs or {}).values()]:
            extra = parse(expr).free_symbols - set(sym.values())
            if extra:
                raise ValueError(f"unknown symbol(s) {sorted(map(str, extra))} in {expr!r}; add them to params")
        return cls(
            name, sym[time], [sym[z] for z in equations], [sym[p] for p in params.split()],
            [parse(e) for e in equations.values()],
            extra_invariants=[sym[a] / sym[b] for a, b in same_units],
            outputs={k: parse(v) for k, v in (outputs or {}).items()},
            notes=notes,
        )

    def symbol(self, name: str) -> sp.Symbol:
        """Look a variable up by name, e.g. model.symbol("beta")."""
        for v in self.variables:
            if v.name == name:
                return v
        raise KeyError(f"{name!r} is not a variable of {self.name}; have {[v.name for v in self.variables]}")

    def parse(self, text) -> sp.Expr:
        """Parse an expression written in the model's variable names."""
        if isinstance(text, sp.Basic):
            return text
        return sp.sympify(text, locals={v.name: v for v in self.variables})

    def index(self, v: sp.Symbol) -> int:
        return self.variables.index(v)

    def __str__(self) -> str:
        lines = [f"Model {self.name}"]
        for z, f in zip(self.states, self.rhs):
            lines.append(f"  d{z}/d{self.t} = {f}")
        lines.append(f"  parameters: {', '.join(map(str, self.params))}")
        if self.extra_invariants:
            lines.append(f"  extra invariants: {', '.join(map(str, self.extra_invariants))}")
        return "\n".join(lines)


def monomial_exponents(term: sp.Expr, variables: list[sp.Symbol]) -> list[sp.Rational]:
    """Exponent vector of a single monomial term (numeric coefficient ignored)."""
    vec = [sp.Integer(0)] * len(variables)
    for factor in sp.Mul.make_args(term):
        if factor.is_number:
            continue
        base, exp = factor.as_base_exp()
        if base not in variables:
            raise OutOfScopeError(
                f"factor {factor} is not a power of a model variable; "
                "scaling analysis only handles ratios of sums of monomials"
            )
        if not exp.is_Rational:
            raise OutOfScopeError(f"symbolic exponent in {factor}")
        vec[variables.index(base)] += exp
    return vec


def _monomials(poly_expr: sp.Expr) -> list[sp.Expr]:
    return [m for m in sp.Add.make_args(sp.expand(poly_expr)) if m != 0]


def invariance_columns(expr: sp.Expr, variables: list[sp.Symbol]) -> list[list[sp.Rational]]:
    """Exponent columns that must be killed by a scaling for `expr` to be invariant.

    Write expr = P/Q in lowest terms. Under a diagonal scaling, P/Q is invariant
    iff every monomial of P and of Q gets the same weight, i.e. each monomial
    divided by a reference monomial of Q is invariant. For a polynomial
    (Q = 1) the columns are just the monomials' exponent vectors.
    """
    P, Q = sp.fraction(sp.cancel(sp.together(expr)))
    p_terms, q_terms = _monomials(P), _monomials(Q)
    if not p_terms:
        return []
    ref = monomial_exponents(q_terms[0], variables)
    cols = []
    for m in p_terms + q_terms[1:]:
        e = monomial_exponents(m, variables)
        cols.append([a - b for a, b in zip(e, ref)])
    return cols


def exponent_matrix(model: Model) -> sp.Matrix:
    """Integer matrix K (n_vars x n_cols). Scalings are integer rows a with a*K = 0."""
    V = model.variables
    cols: list[list[sp.Rational]] = []
    for z, f in zip(model.states, model.rhs):
        if f == 0:
            continue
        cols += invariance_columns(model.t * f / z, V)
    for inv in model.extra_invariants:
        cols += invariance_columns(inv, V)
    clean: list[list[sp.Integer]] = []
    for c in cols:
        den = reduce(sp.ilcm, [sp.Rational(x).q for x in c], 1)
        c = [sp.Integer(x * den) for x in c]
        if any(c) and c not in clean:
            clean.append(c)
    if not clean:
        return sp.zeros(len(V), 0)
    return sp.Matrix(clean).T

"""Classical Buckingham Pi from a table of physical dimensions.

Given each quantity's dimension vector (e.g. beta has P^-1 T^-1), the
dimensionless monomials are the integer kernel of the dimension matrix D

(base dimensions x quantities). By rank-nullity there are
n - rank(D) independent Pi groups.

Compare with scaling.analyze: the scaling-symmetry approach reads the
equations themselves and can find *more* symmetries than physical units
alone (Lotka-Volterra is the standard example).
"""

from __future__ import annotations

import sympy as sp

from .intlinalg import rank, right_kernel_basis


def dimension_matrix(
    dims: dict[sp.Symbol, dict[str, int]],
) -> tuple[sp.Matrix, list[str], list[sp.Symbol]]:
    qs = list(dims)
    bases = sorted({b for d in dims.values() for b in d})
    D = (
        sp.Matrix([[dims[q].get(b, 0) for q in qs] for b in bases])
        if bases
        else sp.zeros(0, len(qs))
    )
    return D, bases, qs


def pi_groups(dims: dict[sp.Symbol, dict[str, int]]) -> list[sp.Expr]:
    D, _, qs = dimension_matrix(dims)
    if D.shape[0] == 0:
        return list(qs)
    N = right_kernel_basis(D)
    return [
        sp.Mul(*[q ** N[i, j] for i, q in enumerate(qs)]) for j in range(N.shape[1])
    ]


def pi_count(dims: dict[sp.Symbol, dict[str, int]]) -> int:
    D, _, qs = dimension_matrix(dims)
    return len(qs) - (rank(D) if D.shape[0] else 0)

"""Exact integer linear algebra used by the nondimensionalizer.

Everything here works over the integers (or rationals) with SymPy matrices, so
results are exact. Floating point never touches the certificates we later
hand to Lean.

The workhorse is `int_row_echelon`: it finds a *unimodular* integer matrix U
(det U = +-1) with U * M = H, where H is in row echelon form. Because U is
unimodular, the rows of U that map to zero rows of H form a Z-basis of the
integer left kernel {y in Z^m : y M = 0}. That is exactly the lattice of
scaling symmetries we want (Hubert & Labahn 2013, Sec. 5).
"""

from __future__ import annotations

from itertools import combinations
from typing import Sequence

import sympy as sp


def _as_int_matrix(M) -> sp.Matrix:
    M = sp.Matrix(M)
    for x in M:
        if not (x.is_Integer):
            raise ValueError(f"expected an integer matrix, found entry {x!r}")
    return M


def int_row_echelon(M) -> tuple[sp.Matrix, sp.Matrix, list[int]]:
    """Return (U, H, pivots) with U unimodular and U*M == H in row echelon form.

    Pivot entries are positive, entries above each pivot are reduced, and
    rows of H below len(pivots) are zero. This is a Hermite-normal-form style
    reduction done with the extended Euclidean algorithm on rows.
    """
    H = _as_int_matrix(M).copy()
    m, n = H.shape
    U = sp.eye(m)
    row = 0
    pivots: list[int] = []
    for col in range(n):
        if row >= m:
            break
        # Euclid: repeatedly reduce the column below `row` until one nonzero remains.
        while True:
            nonzero = [i for i in range(row, m) if H[i, col] != 0]
            if not nonzero:
                break
            piv = min(nonzero, key=lambda i: abs(H[i, col]))
            if piv != row:
                H.row_swap(piv, row)
                U.row_swap(piv, row)
            finished = True
            for i in range(row + 1, m):
                if H[i, col] != 0:
                    q = H[i, col] // H[row, col]
                    H[i, :] = H[i, :] - q * H[row, :]
                    U[i, :] = U[i, :] - q * U[row, :]
                    if H[i, col] != 0:
                        finished = False
            if finished:
                break
        if H[row, col] == 0:
            continue
        if H[row, col] < 0:
            H[row, :] = -H[row, :]
            U[row, :] = -U[row, :]
        for i in range(row):  # reduce entries above the pivot
            q = H[i, col] // H[row, col]
            if q != 0:
                H[i, :] = H[i, :] - q * H[row, :]
                U[i, :] = U[i, :] - q * U[row, :]
        pivots.append(col)
        row += 1
    assert U * _as_int_matrix(M) == H
    assert abs(U.det()) == 1
    return U, H, pivots


def rank(M) -> int:
    """Rank over Q (same as the number of echelon pivots over Z)."""
    return sp.Matrix(M).rank()


def left_kernel_basis(M) -> sp.Matrix:
    """Z-basis (as rows) of {y in Z^m : y M = 0}. Shape: (m - rank) x m."""
    U, _, pivots = int_row_echelon(M)
    return U[len(pivots):, :]


def right_kernel_basis(M) -> sp.Matrix:
    """Z-basis (as columns) of {x in Z^n : M x = 0}. Shape: n x (n - rank)."""
    return left_kernel_basis(sp.Matrix(M).T).T


def independent_columns(M, order: Sequence[int] | None = None) -> list[int]:
    """Greedy matroid basis: scan columns in `order`, keep those that raise the rank.

    Greedy is optimal for "pick as many independent columns as possible", which
    is why constraint questions like "eliminate >= k parameters while keeping P"
    reduce to rank computations instead of a hard search.
    """
    M = sp.Matrix(M)
    order = list(range(M.shape[1])) if order is None else list(order)
    chosen: list[int] = []
    for j in order:
        if rank(M[:, chosen + [j]]) > len(chosen):
            chosen.append(j)
    return chosen


def all_column_bases(M, candidates: Sequence[int], size: int) -> list[tuple[int, ...]]:
    """Every set of `size` columns (from candidates) that is linearly independent."""
    M = sp.Matrix(M)
    out = []
    for S in combinations(candidates, size):
        if size == 0 or rank(M[:, list(S)]) == size:
            out.append(S)
    return out


def left_inverse_on_columns(M, cols: Sequence[int]) -> sp.Matrix:
    """Rational L with L * M[:, cols] == identity (a rank >= len(cols) certificate)."""
    Ms = sp.Matrix(M)[:, list(cols)]
    L = (Ms.T * Ms).inv() * Ms.T
    assert L * Ms == sp.eye(len(cols))
    return L


def right_inverse(M) -> sp.Matrix:
    """Rational R with M * R == identity (certifies M has full row rank)."""
    M = sp.Matrix(M)
    R = M.T * (M * M.T).inv()
    assert M * R == sp.eye(M.shape[0])
    return R

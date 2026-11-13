"""Framing 3: scaling symmetries and what data can (not) tell you.

If a scaling changes some parameters but leaves time and every *measured*
output unchanged, then two different parameter sets produce identical data.
Those parameters are structurally non-identifiable: no amount of perfect data
can pin them down. Only scaling-invariant combinations can be estimated.

    output-preserving scalings  B  =  { a : a K = 0,  a_t = 0,  a . (output monomials) = 0 }

CAVEAT (Villaverde & Massonis 2021): this is a one-way test. A parameter moved
by B is certainly non-identifiable; a parameter *not* moved may still be
non-identifiable through a symmetry that is not a scaling. Use a full tool
(StructuralIdentifiability.jl, SIAN, DAISY) for a complete answer.

The second half of this module checks the prediction numerically: the
sensitivity matrix of the outputs with respect to log-parameters must have the
predicted scaling directions in its null space.
"""

from __future__ import annotations

from dataclasses import dataclass

import numpy as np
import sympy as sp
from scipy.integrate import solve_ivp

from .intlinalg import left_kernel_basis, right_kernel_basis
from .model import Model, exponent_matrix, invariance_columns


@dataclass
class IdentifiabilityResult:
    model: Model
    outputs: dict[str, sp.Expr]
    B: sp.Matrix  # rows = output-preserving scalings (over model.variables)
    nonidentifiable: list[sp.Symbol]  # parameters moved by some row of B
    not_flagged: list[sp.Symbol]  # parameters no output-preserving scaling moves
    hidden_scale_states: list[sp.Symbol]  # states whose overall scale the data cannot see
    identifiable_groups: list[sp.Expr]  # parameter monomials invariant under B

    def summary(self) -> str:
        V = self.model.variables
        lines = [f"Identifiability of {self.model.name} from outputs "
                 + ", ".join(f"{k} = {v}" for k, v in self.outputs.items())]
        if self.B.shape[0] == 0:
            lines.append("  no output-preserving scaling: scaling symmetries reveal no non-identifiability")
        for i in range(self.B.shape[0]):
            parts = [f"{v} -> lambda^{self.B[i, j]} {v}" for j, v in enumerate(V) if self.B[i, j] != 0]
            lines.append("  data unchanged by:  " + ",  ".join(parts))
        lines.append(f"  NOT identifiable (moved by a scaling): {[str(p) for p in self.nonidentifiable] or 'none found'}")
        lines.append(f"  not flagged by this test:              {[str(p) for p in self.not_flagged]}")
        if self.hidden_scale_states:
            lines.append(f"  states with unobservable scale:        {[str(z) for z in self.hidden_scale_states]}")
        lines.append(f"  parameter groups the data can see:     {[str(g) for g in self.identifiable_groups]}")
        lines.append("  (one-way test: 'not flagged' does not prove identifiable)")
        return "\n".join(lines)


def analyze_identifiability(model: Model, outputs: dict | None = None, known=()) -> IdentifiabilityResult:
    """Find scalings that leave the measured outputs (and `known` parameters) unchanged."""
    outputs = {k: model.parse(v) for k, v in (outputs or model.outputs).items()}
    if not outputs:
        raise ValueError("no outputs given: pass outputs={'y': 'rho*I'} or set model.outputs")
    V = model.variables
    n = len(V)
    cols = [[1 if v == model.t else 0 for v in V]]  # time is measured: a_t = 0
    for h in outputs.values():
        cols += [[int(x) for x in c] for c in invariance_columns(h, V)]
    for p in known:
        p = model.symbol(p) if isinstance(p, str) else p
        cols.append([1 if v == p else 0 for v in V])
    K = exponent_matrix(model)
    Kext = K.row_join(sp.Matrix(cols).T) if K.shape[1] else sp.Matrix(cols).T
    B = left_kernel_basis(Kext)
    moved = lambda v: any(B[i, model.index(v)] != 0 for i in range(B.shape[0]))  # noqa: E731
    pc = [model.index(p) for p in model.params]
    if B.shape[0]:
        N = right_kernel_basis(B[:, pc])
        groups = [sp.Mul(*[p ** N[i, j] for i, p in enumerate(model.params)]) for j in range(N.shape[1])]
    else:
        groups = list(model.params)
    return IdentifiabilityResult(
        model, outputs, B,
        [p for p in model.params if moved(p)], [p for p in model.params if not moved(p)],
        [z for z in model.states if moved(z)], groups,
    )


# --------------------------------------------------------------- numerics

def simulate_outputs(model: Model, outputs: dict[str, sp.Expr], params: dict, z0: dict, ts) -> np.ndarray:
    """Integrate the model and return the outputs at times `ts` (shape: n_outputs x len(ts))."""
    pv = {p: float(params[p]) for p in model.params}
    f = sp.lambdify((model.t, model.states), [fi.subs(pv) for fi in model.rhs], "numpy")
    h = sp.lambdify((model.t, model.states), [hi.subs(pv) for hi in outputs.values()], "numpy")
    sol = solve_ivp(lambda t, y: f(t, y), (0.0, float(ts[-1])), [float(z0[z]) for z in model.states],
                    t_eval=ts, rtol=1e-10, atol=1e-12, method="LSODA")
    return np.array([np.broadcast_to(np.asarray(row, dtype=float), sol.t.shape) for row in h(sol.t, sol.y)])


def log_sensitivity_matrix(model, outputs, params, z0, ts, rel_step: float = 1e-4):
    """d(outputs)/d(log theta) by central differences; theta = (parameters, initial conditions).

    Returns (J, names). A direction v with J v = 0 changes parameters without
    changing the data (to first order): a non-identifiable direction.
    """
    outputs = {k: model.parse(v) for k, v in outputs.items()}
    theta = [("param", p) for p in model.params] + [("ic", z) for z in model.states]

    def run(shift):
        pv, zv = dict(params), dict(z0)
        for (kind, s), d in zip(theta, shift):
            if kind == "param":
                pv[s] = params[s] * np.exp(d)
            else:
                zv[s] = z0[s] * np.exp(d)
        return simulate_outputs(model, outputs, pv, zv, ts).ravel()

    J = np.zeros((len(outputs) * len(ts), len(theta)))
    for j in range(len(theta)):
        e = np.zeros(len(theta))
        e[j] = rel_step
        J[:, j] = (run(e) - run(-e)) / (2 * rel_step)
    return J, [f"{s}" if kind == "param" else f"{s}(0)" for kind, s in theta]


def predicted_null_directions(res: IdentifiabilityResult) -> np.ndarray:
    """Rows of B as directions in log-(parameters, initial conditions) space."""
    m = res.model
    idx = [m.index(p) for p in m.params] + [m.index(z) for z in m.states]
    return np.array([[float(res.B[i, j]) for j in idx] for i in range(res.B.shape[0])]).reshape(-1, len(idx))


def numerical_nullity(J: np.ndarray, tol: float = 1e-5) -> tuple[int, np.ndarray]:
    """Number of singular values below tol * largest, and all singular values."""
    s = np.linalg.svd(J, compute_uv=False)
    return int(np.sum(s < tol * s[0])), s

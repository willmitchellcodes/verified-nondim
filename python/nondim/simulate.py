"""Floating-point sanity check: do original and reduced trajectories agree?

This is deliberately *outside* the proof. Lean proves facts about the exact
real-number model. Here we integrate both systems numerically and compare,
which catches transcription mistakes and shows the size of solver error.
"""

from __future__ import annotations

import numpy as np
import sympy as sp
from scipy.integrate import solve_ivp

from .scaling import Nondimensionalization


def compare_trajectories(
    nd: Nondimensionalization,
    params: dict[sp.Symbol, float] | None = None,
    z0: dict[sp.Symbol, float] | None = None,
    t_end: float = 10.0,
    n_points: int = 50,
    seed: int = 0,
) -> float:
    """Max relative error between the mapped original solution and the reduced solution."""
    m = nd.model
    rng = np.random.default_rng(seed)
    params = params or {p: float(rng.uniform(0.5, 2.0)) for p in m.params}
    z0 = z0 or {z: float(rng.uniform(0.2, 1.0)) for z in m.states}

    f = sp.lambdify((m.t, m.states), [fi.subs(params) for fi in m.rhs], "numpy")
    ts = np.linspace(0.0, t_end, n_points)
    sol = solve_ivp(lambda t, y: f(t, y), (0, t_end), [z0[z] for z in m.states],
                    t_eval=ts, rtol=1e-11, atol=1e-13, method="LSODA")

    # Scale factors M_x (pure parameter monomials) evaluated numerically.
    M = {x: float((nd.new_expr[x] / x).subs(params)) for x in [m.t, *m.states]}
    kappa = {nd.new_symbol[p]: float(nd.new_expr[p].subs(params)) for p in m.params if p not in nd.normalized}
    tau_sym = nd.new_symbol[m.t]
    zh = [nd.new_symbol[z] for z in m.states]
    g = sp.lambdify((tau_sym, zh), [gi.subs(kappa) for gi in nd.reduced_rhs], "numpy")
    taus = M[m.t] * ts
    sol_r = solve_ivp(lambda tau, y: g(tau, y), (taus[0], taus[-1]),
                      [M[z] * z0[z] for z in m.states], t_eval=taus, rtol=1e-11, atol=1e-13, method="LSODA")

    mapped = np.array([M[z] * sol.y[i] for i, z in enumerate(m.states)])
    scale = np.maximum(np.abs(mapped), 1e-12)
    return float(np.max(np.abs(mapped - sol_r.y) / scale))

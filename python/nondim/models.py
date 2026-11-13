"""Test models from the course (Ellner & Guckenheimer) and the literature.

Each function returns a fresh Model. Start with logistic -> SIR -> Lotka-Volterra;
Michaelis-Menten is the showcase for non-uniqueness; `spurious_*` reproduces the
failure mode of Tanburn et al. (2025) Example 3.12.
"""

import sympy as sp

from .model import Model

_pos = dict(positive=True)


def logistic() -> Model:
    t, N, r, K = sp.symbols("t N r K", **_pos)
    return Model(
        "logistic", t, [N], [r, K], [r * N * (1 - N / K)],
        notes="dN/dt = rN(1 - N/K). Expect 2 -> 0 parameters: u = N/K, tau = r t.",
    )


def sir() -> Model:
    """Kermack-McKendrick SIR as in Ellner & Guckenheimer Ch. 6.

    N enters only through the conservation law S + I + R = N, so we tell the
    algorithm that S, I, R are measured in the same units as N.
    """
    t, S, I, R, beta, gamma, N = sp.symbols("t S I R beta gamma N", **_pos)
    return Model(
        "SIR", t, [S, I, R], [beta, gamma, N],
        [-beta * S * I, beta * S * I - gamma * I, gamma * I],
        extra_invariants=[S / N, I / N, R / N],
        notes="Expect 3 -> 1 parameter. Normalizing gamma and N gives R0 = beta N / gamma.",
    )


def sir_no_population() -> Model:
    """SIR with N dropped entirely: shows the ODE alone is parameter-free."""
    t, S, I, beta, gamma = sp.symbols("t S I beta gamma", **_pos)
    return Model(
        "SIR_noN", t, [S, I], [beta, gamma], [-beta * S * I, beta * S * I - gamma * I],
        notes="2 -> 0 parameters; R0 then hides in the initial condition.",
    )


def sir_reported() -> Model:
    """SIR where we only see reported prevalence y = rho * I (rho = unknown reporting fraction)."""
    t, S, I, beta, gamma, rho = sp.symbols("t S I beta gamma rho", **_pos)
    return Model(
        "SIR_reported", t, [S, I], [beta, gamma, rho], [-beta * S * I, beta * S * I - gamma * I],
        outputs={"y": rho * I},
        notes="Identifiability example: beta and rho cannot be told apart from y alone.",
    )


def lotka_volterra() -> Model:
    t, x, y, a, b, c, d = sp.symbols("t x y a b c d", **_pos)
    return Model(
        "LotkaVolterra", t, [x, y], [a, b, c, d],
        [a * x - b * x * y, -c * y + d * x * y],
        outputs={"prey_count": x},
        notes="Expect 4 -> 1 (three scalings: time, prey units, predator units).",
    )


def michaelis_menten() -> Model:
    """Full enzyme kinetics (no QSSA), s = substrate, c = complex, e = e0 - c."""
    t, s, c, k1, km1, k2, e0 = sp.symbols("t s c k1 km1 k2 e0", **_pos)
    return Model(
        "MichaelisMenten", t, [s, c], [k1, km1, k2, e0],
        [-k1 * (e0 - c) * s + km1 * c, k1 * (e0 - c) * s - (km1 + k2) * c],
        notes="Expect 4 -> 2 (time and concentration scalings).",
    )


def michaelis_menten_ic() -> Model:
    """Michaelis-Menten with the initial substrate s0 as a parameter (s(0) = s0)."""
    t, s, c, k1, km1, k2, e0, s0 = sp.symbols("t s c k1 km1 k2 e0 s0", **_pos)
    return Model(
        "MichaelisMentenIC", t, [s, c], [k1, km1, k2, e0, s0],
        [-k1 * (e0 - c) * s + km1 * c, k1 * (e0 - c) * s - (km1 + k2) * c],
        extra_invariants=[s / s0],
        notes="Expect 5 -> 3, e.g. the textbook (K, lambda, epsilon = e0/s0) after choosing invariants.",
    )


def rosenzweig_macarthur() -> Model:
    """Predator-prey with logistic prey and a Holling type II functional response (rational RHS)."""
    t, N, P, r, K, a, h, e, m = sp.symbols("t N P r K a h e m", **_pos)
    f = a * N / (1 + a * h * N)
    return Model(
        "RosenzweigMacArthur", t, [N, P], [r, K, a, h, e, m],
        [r * N * (1 - N / K) - f * P, e * f * P - m * P],
        notes="Rational right-hand side. Expect 6 -> 3.",
    )


def spurious_original() -> Model:
    """dx/dt = a x + b x + b  (Tanburn et al. Example 3.12)."""
    t, x, a, b = sp.symbols("t x a b", **_pos)
    return Model("Spurious_original", t, [x], [a, b], [a * x + b * x + b])


def spurious_substituted() -> Model:
    """Same model after c = a + b, with the unit link between b and c forgotten.

    The algorithm now finds an extra (spurious) scaling and claims one more
    parameter can be removed. That is wrong for the original physics.
    """
    t, x, b, c = sp.symbols("t x b c", **_pos)
    return Model("Spurious_substituted", t, [x], [b, c], [c * x + b])


def spurious_fixed() -> Model:
    """Substituted model with the unit constraint restored: b/c must be invariant."""
    t, x, b, c = sp.symbols("t x b c", **_pos)
    return Model("Spurious_fixed", t, [x], [b, c], [c * x + b], extra_invariants=[b / c])


def arrhenius_out_of_scope() -> Model:
    """Temperature-dependent growth with exp(-E/(R T)): outside the monomial framework."""
    t, x, k, E, Rg, T = sp.symbols("t x k E R_g T", **_pos)
    return Model("Arrhenius", t, [x], [k, E, Rg, T], [k * sp.exp(-E / (Rg * T)) * x])


ALL = {
    "logistic": logistic,
    "sir": sir,
    "sir_noN": sir_no_population,
    "sir_reported": sir_reported,
    "lotka_volterra": lotka_volterra,
    "michaelis_menten": michaelis_menten,
    "michaelis_menten_ic": michaelis_menten_ic,
    "rosenzweig_macarthur": rosenzweig_macarthur,
    "spurious_original": spurious_original,
    "spurious_substituted": spurious_substituted,
    "spurious_fixed": spurious_fixed,
}

"""What to run for each built-in model: default choices, constraints, units.

This is the one place to edit when you add a model (after defining it in
models.py). Everything is plain data.

    normalize    which parameters to set to 1 (None = let the solver choose)
    constraints  list of requests for constraints.solve (Framing 2)
    dims         physical dimensions, only for the Buckingham Pi comparison
    certify      write a matrix-level Lean certificate for this model (lean/NondimVerify/Cert/)

Certificates in the general form (lean/NondimVerify/Certified/) are written for every model
the general theory covers; see `GENERAL` below.
"""

CATALOG = {
    "logistic": dict(
        normalize=None, certify=True,
        constraints=[dict(eliminate_at_least=2), dict(eliminate_at_least=3)],
    ),
    "sir": dict(
        normalize=["gamma", "N"],  # textbook choice: the surviving parameter is R0 = beta*N/gamma
        certify=True,
        constraints=[
            dict(eliminate_at_least=2, keep=["beta"]),            # SAT
            dict(eliminate_at_least=3),                           # UNSAT: only 2 scalings exist
            dict(eliminate_at_least=2, keep=["gamma", "N"]),      # UNSAT: beta alone gives 1
            dict(at_most_params=1, want={"R0": "beta*N/gamma"}),  # SAT: R0 as a named group
            dict(want={"force": "beta*N"}),                       # UNSAT: beta*N has units 1/time
        ],
        dims={"t": {"T": 1}, "S": {"P": 1}, "I": {"P": 1}, "R": {"P": 1},
              "beta": {"P": -1, "T": -1}, "gamma": {"T": -1}, "N": {"P": 1}},
    ),
    "sir_noN": dict(normalize=None),
    "sir_reported": dict(normalize=None),
    "lotka_volterra": dict(
        normalize=None, certify=True,
        constraints=[dict(eliminate_at_least=3, keep=["c"]), dict(eliminate_at_least=4),
                     dict(want={"alpha": "c/a"})],
        dims={"t": {"T": 1}, "x": {"P": 1}, "y": {"P": 1}, "a": {"T": -1},
              "b": {"P": -1, "T": -1}, "c": {"T": -1}, "d": {"P": -1, "T": -1}},
    ),
    "michaelis_menten": dict(normalize=None),
    "michaelis_menten_ic": dict(
        normalize=["k1", "s0"], certify=True,
        constraints=[
            dict(eliminate_at_least=2, keep=["k1"]),
            dict(eliminate_at_least=2, want={"eps": "e0/s0", "sigma": "k1*s0/(km1 + k2)"}),  # UNSAT: not a monomial
            dict(eliminate_at_least=2, want={"eps": "e0/s0", "lam": "k2/km1"}),
            dict(want={"a": "e0/s0", "b": "s0/e0"}),  # UNSAT: dependent
        ],
    ),
    "rosenzweig_macarthur": dict(
        normalize=None, certify=True,
        constraints=[dict(eliminate_at_least=3, keep=["r", "m"]),
                     dict(at_most_params=3, want={"H": "a*h*K", "ratio": "e*a*K/m"})],
    ),
    "spurious_original": dict(normalize=None),
    "spurious_substituted": dict(normalize=None),
    "spurious_fixed": dict(normalize=None, certify=True, constraints=[dict(eliminate_at_least=2)]),
}

# Models exported in the general form (right-hand sides that are polynomials or quotients of
# polynomials; unit links allowed).
# "Own" certificates come from this package's solver; "Desr" ones from desr, when it is installed.
GENERAL = ["logistic", "sir", "sir_noN", "sir_reported", "lotka_volterra", "michaelis_menten",
           "michaelis_menten_ic", "rosenzweig_macarthur", "spurious_original", "spurious_substituted",
           "spurious_fixed"]

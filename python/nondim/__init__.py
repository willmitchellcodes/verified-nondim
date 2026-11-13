"""Automatic nondimensionalization of ODE models, with certificates that Lean 4 can check.

    from nondim import Model, analyze, nondimensionalize, solve

    sir = Model.from_strings(
        "SIR",
        equations={"S": "-beta*S*I", "I": "beta*S*I - gamma*I"},
        params="beta gamma N",
        same_units=[("S", "N"), ("I", "N")],
    )
    print(nondimensionalize(sir, ["gamma", "N"]).summary())
"""

__version__ = "0.1.0"

from .constraints import solve
from .identifiability import analyze_identifiability
from .lean_export import certificate, write_certificate
from .leanproject import init_lean
from .model import Model, OutOfScopeError
from .scaling import all_nondimensionalizations, analyze, nondimensionalize, verify_symbolically

__all__ = [
    "Model", "OutOfScopeError", "analyze", "nondimensionalize", "all_nondimensionalizations",
    "verify_symbolically", "solve", "analyze_identifiability", "certificate", "write_certificate",
    "init_lean", "__version__",
]

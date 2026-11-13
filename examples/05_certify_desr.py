"""Example 5: let Lean check what desr computes.

desr (https://github.com/ofloveandhate/desr) is the reference implementation of the
Hubert-Labahn nondimensionalization algorithm. It is not on PyPI:

    pip install git+https://github.com/ofloveandhate/desr

Run:  python examples/05_certify_desr.py
"""
import _path  # noqa: F401  (lets the example run from a source checkout)

from nondim import models
from nondim.desr_bridge import INSTALL_HINT, compare, desr_available, from_desr
from nondim.hlform import NotSupported
from nondim.lean_export2 import certificate

if not desr_available():
    raise SystemExit(INSTALL_HINT)

# 1. Run desr on Lotka-Volterra and read its answer in a solver-independent form.
model = models.lotka_volterra()
reduction = from_desr(model)          # every matrix relation is re-checked here, exactly
print(reduction.summary())

# 2. Compare with this package's own solver: two independent implementations.
result = compare(model)
print("\nsame scaling symmetries:", result["same_scalings"])
print("parameters left: desr", result["desr_after"], "/ ours", result["ours_after"])

# 3. Turn desr's answer into a Lean file. Lean then proves, without trusting desr or us:
#      symmetry            desr's scalings are symmetries of the equations
#      reduction_correct   along every positive solution, desr's new variables satisfy
#                          desr's reduced equations in desr's new time
#      invariants_complete anything unit-independent is a function of desr's invariants
text = certificate(reduction, "Desr.LotkaVolterra")
start = text.index("theorem reduction_correct")
print("\n--- from the Lean certificate ---")
print(text[start:text.index("/-- **The same solution", start)].rstrip())

# 4. Models outside the supported scope are refused with a reason, never mis-certified.
for key in ("sir", "rosenzweig_macarthur"):
    try:
        from_desr(models.ALL[key]())
    except NotSupported as why:
        print(f"\n{key}: not certified yet. {why}")

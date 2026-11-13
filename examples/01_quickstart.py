"""The whole idea in 20 lines: SIR has three parameters, but only one matters.

    python examples/01_quickstart.py
"""
import _path  # noqa: F401
from nondim.model import Model
from nondim.scaling import analyze, nondimensionalize

# 1. Write the model. `same_units` says S and I are counted in the same units as N.
sir = Model.from_strings(
    "SIR",
    equations={"S": "-beta*S*I", "I": "beta*S*I - gamma*I"},
    params="beta gamma N",
    same_units=[("S", "N"), ("I", "N")],
)

# 2. Find every change of units the equations allow, and how many parameters that removes.
analysis = analyze(sir)
print(analysis.summary())

# 3. Use those unit changes to set gamma = 1 and N = 1. What is left is R0.
reduced = nondimensionalize(sir, [sir.symbol("gamma"), sir.symbol("N")], analysis=analysis)
print()
print(reduced.summary())

"""Framing 2: ask for a nondimensionalization with conditions, get SAT or a reasoned UNSAT.

    python examples/02_constraints.py
"""
import _path  # noqa: F401
from nondim import models
from nondim.constraints import solve

sir = models.sir()
print("SIR")
print("  remove >= 2, keep beta      :", solve(sir, 2, keep=["beta"]))
print("  remove >= 3                 :", solve(sir, 3))
print("  at most 1 parameter, named R0:", solve(sir, at_most_params=1, want={"R0": "beta*N/gamma"}))
print("  want beta*N                 :", solve(sir, want={"force": "beta*N"}))

mm = models.michaelis_menten_ic()
print("\nMichaelis-Menten with initial substrate s0")
print("  want eps = e0/s0 and lam = k2/km1:")
res = solve(mm, 2, want={"eps": "e0/s0", "lam": "k2/km1"})
print("   ", res)
print("  want Segel-Slemrod's eps = e0/(s0 + Km), which is not a product of powers:")
print("   ", solve(mm, want={"eps": "e0/(s0 + (km1 + k2)/k1)"}))

lv = models.lotka_volterra()
res = solve(lv, 3, want={"alpha": "c/a"})
print("\nLotka-Volterra with alpha = c/a")
for z, rhs in zip(lv.states, res.regrouping.reduced_rhs):
    print(f"  d{res.witness.new_symbol[z]}/d{res.witness.new_symbol[lv.t]} = {rhs}")

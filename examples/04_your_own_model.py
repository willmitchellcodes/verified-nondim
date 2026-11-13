"""Template: analyze your own model, then write a Lean certificate for it.

    python examples/04_your_own_model.py

Edit the model below. Rules of thumb:
  * every symbol in the equations must be a state or listed in `params`;
  * use `same_units` whenever two quantities are measured in the same units but the
    equations alone do not force it (initial values, totals, sums written as one symbol);
  * only products, quotients and sums of powers are in scope (no exp/log).
"""
import _path  # noqa: F401
from pathlib import Path

from nondim.constraints import solve
from nondim.lean_export import write_certificate
from nondim.model import Model
from nondim.scaling import analyze, nondimensionalize, verify_symbolically
from nondim.simulate import compare_trajectories

# A chemostat: nutrient n feeds biomass x with Monod uptake; D is the dilution rate.
model = Model.from_strings(
    "Chemostat",
    equations={
        "n": "D*(n_in - n) - mu*n/(k + n)*x/Y",
        "x": "mu*n/(k + n)*x - D*x",
    },
    params="D n_in mu k Y",
)

analysis = analyze(model)
print(analysis.summary(), "\n")

reduced = nondimensionalize(model, analysis=analysis)  # or choose: [model.symbol("D"), ...]
print(reduced.summary())
print("  chain rule:", "pass" if all(r == 0 for r in verify_symbolically(reduced)) else "FAIL")
print(f"  numerics:   {compare_trajectories(reduced):.1e}")

request = solve(model, eliminate_at_least=3, keep=["D"])
print("\nremove >= 3 but keep D:", request)

out = Path(__file__).resolve().parents[1] / "lean" / "Scratch" / "Chemostat.lean"
write_certificate(reduced, out, [request], module="Chemostat")
print(f"\nLean certificate written to {out}")
print("check it with:  cd lean && lake env lean Scratch/Chemostat.lean")

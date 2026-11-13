"""Framing 3: which parameters can data determine?

    python examples/03_identifiability.py

Part 1 is symbolic and instant. Part 2 fits synthetic epidemic data (a few seconds)
and writes reports/identifiability_sir.md and .png.
"""
import _path  # noqa: F401
from pathlib import Path

from nondim import models
from nondim.experiment_sir import run
from nondim.identifiability import analyze_identifiability

print(analyze_identifiability(models.sir_reported()).summary())
print()
print(analyze_identifiability(models.lotka_volterra(), {"prey_count": "x"}).summary())

res = run(Path(__file__).resolve().parents[1] / "reports")
print("\nFitting the 5 raw parameters from 12 random starts:")
for name, spread in res["raw_spread"].items():
    print(f"  {name:6s} estimates differ by a factor of {spread:8.3g} between equally good fits")
print("...but the invariant groups agree:")
for name, spread in res["group_spread"].items():
    print(f"  {name:20s} factor {spread:.4f}")

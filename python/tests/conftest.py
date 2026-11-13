"""Shared fixtures. Test files mirror the pipeline:

    test_intlinalg      exact integer linear algebra
    test_model          equations -> exponent matrix
    test_scaling        Framing 1 (solver side): symmetries, reductions, checks
    test_constraints    Framing 2: SAT/UNSAT verdicts, cross-checked by brute force
    test_identifiability  Framing 3: predictions vs. numerical sensitivities, data experiment
    test_lean_export    the Python -> Lean bridge, checked without Lean
    test_lean_build     the bridge checked WITH Lean, including corrupted certificates
    test_cli            every command runs
"""
import shutil
import subprocess
from pathlib import Path

import pytest
import sympy as sp

from nondim import models

ROOT = Path(__file__).resolve().parents[2]
LEAN = ROOT / "lean"
ALL_KEYS = list(models.ALL)


def P(name):
    return sp.Symbol(name, positive=True)


@pytest.fixture(scope="session")
def lake():
    exe = shutil.which("lake") or shutil.which("lake", path=str(Path.home() / ".elan" / "bin"))
    if exe is None:
        pytest.skip("Lean toolchain (lake) not installed: run ./setup.sh")
    probe = subprocess.run([exe, "env", "lean", "--version"], cwd=LEAN, capture_output=True, text=True)
    if probe.returncode != 0:
        pytest.skip("Lean project not set up: run ./setup.sh")
    return exe

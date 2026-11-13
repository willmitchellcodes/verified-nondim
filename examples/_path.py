"""Lets the examples run from anywhere: `python examples/01_quickstart.py`."""
import sys
from pathlib import Path

sys.path.insert(0, str(Path(__file__).resolve().parents[1] / "python"))

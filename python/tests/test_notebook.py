"""The teaching notebook runs from top to bottom and shows what its text says it shows.

The notebook is executed here without Jupyter: its code cells are run in order in one namespace.
"""
import contextlib
import io
import json

import pytest

from conftest import ROOT

NOTEBOOK = ROOT / "examples" / "walkthrough.ipynb"


@pytest.fixture(scope="module")
def run():
    nb = json.loads(NOTEBOOK.read_text())
    outputs, namespace = [], {}
    for cell in nb["cells"]:
        if cell["cell_type"] != "code":
            continue
        buf = io.StringIO()
        with contextlib.redirect_stdout(buf):
            exec("".join(cell["source"]), namespace)
        outputs.append(buf.getvalue())
    return nb, outputs


def test_notebook_is_valid_and_stored_without_outputs():
    nb = json.loads(NOTEBOOK.read_text())
    assert nb["nbformat"] == 4
    assert all(c.get("outputs", []) == [] for c in nb["cells"] if c["cell_type"] == "code")
    assert sum(c["cell_type"] == "markdown" for c in nb["cells"]) >= 8


def test_every_code_cell_runs(run):
    nb, outputs = run
    assert len(outputs) == sum(c["cell_type"] == "code" for c in nb["cells"]) >= 8


def test_it_shows_what_the_text_promises(run):
    _, outputs = run
    everything = "\n".join(outputs)
    assert "parameters 2 -> 0" in everything                 # logistic loses both parameters
    assert "N*beta/gamma" in everything                      # R0 survives in SIR
    requests = outputs[4].strip().splitlines()                # the four requests of section 2
    assert [line.split(":")[0] for line in requests] == ["SAT", "UNSAT", "SAT", "UNSAT"]
    assert "NOT identifiable" in everything and "beta" in everything and "rho" in everything
    assert "parameters: 6 -> 3" in everything                # Rosenzweig-MacArthur
    assert "theorem reduction_correct" in everything         # the Lean statement is shown
    assert "theorem goal2_impossible" in everything and "theorem cannot_remove_more" in everything


def test_the_explanations_match_the_models(run):
    nb, _ = run
    prose = "\n".join("".join(c["source"]) for c in nb["cells"] if c["cell_type"] == "markdown")
    for phrase in ["scaling symmetries", "unit link", "one way", "R_0", "does not tell you"]:
        assert phrase in prose, phrase

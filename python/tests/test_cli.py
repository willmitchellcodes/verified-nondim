"""Every command runs and says the important thing."""
import pytest

from conftest import ALL_KEYS
from nondim import cli
from nondim.report import model_report, summary_table


def run(capsys, *argv):
    cli.main(list(argv))
    return capsys.readouterr().out


def test_no_command_prints_help(capsys):
    assert "tour" in run(capsys)


def test_tour(capsys):
    out = run(capsys, "tour")
    assert "Step 7" in out and "N*beta/gamma" in out and "UNSAT" in out and "NOT identifiable" in out


def test_list(capsys):
    out = run(capsys, "list")
    assert all(k in out for k in ALL_KEYS)


@pytest.mark.parametrize("key", ALL_KEYS)
def test_show_every_model(capsys, key):
    out = run(capsys, "show", key)
    assert "## 1. Scaling symmetries" in out and "chain-rule check (SymPy): pass" in out


def test_reduce(capsys):
    out = run(capsys, "reduce", "sir", "-n", "gamma", "N")
    assert "beta_hat = N*beta/gamma" in out and "chain-rule check: pass" in out
    out = run(capsys, "reduce", "lotka_volterra", "--keep", "a")
    assert "parameters 4 -> 1" in out


def test_reduce_reports_impossible_choices(capsys):
    with pytest.raises(SystemExit, match="cannot do that"):
        cli.main(["reduce", "michaelis_menten_ic", "-n", "e0", "s0"])


def test_constrain(capsys):
    assert run(capsys, "constrain", "sir", "-k", "2", "--keep", "beta").startswith("SAT")
    assert run(capsys, "constrain", "sir", "-k", "3").startswith("UNSAT")
    assert run(capsys, "constrain", "sir", "--at-most", "0").startswith("UNSAT")
    out = run(capsys, "constrain", "lotka_volterra", "--want", "alpha=c/a")
    assert "alpha = c/a" in out and "-alpha" in out


def test_identify(capsys):
    assert "['beta', 'rho']" in run(capsys, "identify", "sir_reported")
    assert "none found" in run(capsys, "identify", "sir", "-o", "y=I")
    with pytest.raises(SystemExit):
        cli.main(["identify", "logistic"])


def test_unknown_model_is_a_clear_error():
    with pytest.raises(SystemExit, match="unknown model"):
        cli.main(["show", "nope"])


def test_reports_are_complete():
    text = model_report("sir")
    for heading in ["## The model", "## 1.", "## 2.", "## 3.", "## 4. Constraints"]:
        assert heading in text
    assert "**UNSAT**" in text and "**SAT**" in text and "Buckingham" in text
    assert "## 5. Identifiability" in model_report("sir_reported")
    assert summary_table().count("\n") == len(ALL_KEYS) + 1


@pytest.mark.parametrize("script, expect", [
    ("01_quickstart.py", "parameters 3 -> 1"),
    ("02_constraints.py", "UNSAT"),
    ("04_your_own_model.py", "parameters 5 -> 2"),
])
def test_examples_run(script, expect, tmp_path):
    import subprocess
    import sys

    from conftest import ROOT
    p = subprocess.run([sys.executable, str(ROOT / "examples" / script)], capture_output=True, text=True, cwd=tmp_path)
    assert p.returncode == 0, p.stderr
    assert expect in p.stdout


@pytest.mark.slow
def test_identifiability_example_runs(tmp_path):
    import subprocess
    import sys

    from conftest import ROOT
    p = subprocess.run([sys.executable, str(ROOT / "examples" / "03_identifiability.py")], capture_output=True, text=True)
    assert p.returncode == 0, p.stderr
    assert "NOT identifiable" in p.stdout and "invariant groups agree" in p.stdout

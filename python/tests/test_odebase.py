"""The ODEbase pilot: reading model files safely, and what the audit reports.

The fixtures below are made-up models written in the file format of OscarODEbase.jl; no model
data from ODEbase is stored in this repository. A test at the end runs on the real files when a
local clone exists (`nondim audit --fetch`) and is skipped otherwise.
"""
from pathlib import Path

import pytest
import sympy as sp

from nondim import odebase
from nondim.cli import default_odebase_dir, main
from nondim.odebase import ParseError, parse_entry, parse_polynomial
from nondim.scaling import analyze

# A reversible binding reaction in a compartment k4, with a conservation law and an unused parameter.
BINDING = '''# made-up test model in the OscarODEbase file format
using Oscar;
paramsRing,(k1,k2,k3,k4,k5)=rational_function_field(QQ,["k1","k2","k3","k4","k5"])
polRing,(x1,x2,x3)=polynomial_ring(paramsRing,["x1","x2","x3"])
chemSystem=[((-1)*k4*k1*x1*x2 + 1*k4*k2*x3)/k4, ((-1)*k4*k1*x1*x2 + 1*k4*k2*x3)/k4,
  (1*k4*k1*x1*x2 + (-1)*k4*k2*x3)/k4 ]
constraints=[ 1*k4*x1 + 1*k4*x3 - k4*k5 ]
ID="TEST0000000001"
pol=true
desc="Made-up binding model"
paramNames=[ "kon","koff","unused","compartment","total" ]
speciesNames=[ "A","B","AB" ]
'''

DECAY = '''paramsRing,(k1,k2)=rational_function_field(QQ,["k1","k2"])
polRing,(x1,x2)=polynomial_ring(paramsRing,["x1","x2"])
chemSystem=[ (-1)*k1*x1^2, 1*k1*x1^2 - k2*x2 ]
constraints=[ ]
ID="TEST0000000002"
desc="Made-up dimerisation"
'''

ALGEBRAIC = '''paramsRing,(k1)=rational_function_field(QQ,["k1"])
polRing,(x1,x2)=polynomial_ring(paramsRing,["x1","x2"])
chemSystem=[ (-1)*k1*x1 ]
constraints=[ x2 - x1 ]
ID="TEST0000000003"
desc="One species defined by a constraint"
'''


# ----------------------------------------------------------------- the parser never executes anything

SYM = {name: sp.Symbol(name, positive=True) for name in ("k1", "k2", "x1", "x2")}


@pytest.mark.parametrize("src, expected", [
    ("1*k1*x1", "k1*x1"), ("(-1)*k1*x1 + k2", "k2 - k1*x1"), ("k1*x1^2/k2", "k1*x1**2/k2"),
    ("-(k1 - k2)*x1", "(k2 - k1)*x1"), ("3//2*x1", "3*x1/2"), ("(k1 + k2)*(x1 - x2)", "(k1 + k2)*(x1 - x2)"),
    ("  k1  ", "k1"), ("2^3*x1", "8*x1"),
])
def test_arithmetic_is_parsed(src, expected):
    assert sp.expand(parse_polynomial(src, SYM) - sp.sympify(expected, locals=SYM)) == 0


@pytest.mark.parametrize("src", [
    "__import__('os').system('echo hi')", "k1; k2", "exec(k1)", "k9*x1", "x1**2", "k1 +", "(k1", "k1 x1",
    "x1^k1", "open('/etc/passwd')", "k1.real", "[k1]", "1e5*k1",
])
def test_anything_else_is_refused(src):
    with pytest.raises(ParseError):
        parse_polynomial(src, SYM)


def test_entry_is_read_including_a_list_that_spans_lines():
    e = parse_entry(BINDING)
    assert e.id == "TEST0000000001" and e.description == "Made-up binding model"
    assert e.species == ["x1", "x2", "x3"] and len(e.parameters) == 5
    assert len(e.equations) == 3 and len(e.constraints) == 1
    k1, k2, x1, x2, x3 = (e.symbols[n] for n in ("k1", "k2", "x1", "x2", "x3"))
    assert sp.simplify(e.equations[0] - (-k1 * x1 * x2 + k2 * x3)) == 0


def test_species_defined_by_a_constraint_is_reported_not_guessed():
    with pytest.raises(ParseError, match="defined by a constraint"):
        parse_entry(ALGEBRAIC)


@pytest.mark.parametrize("broken", ["", "polRing,(x1)=polynomial_ring(R,[\"x1\"])\nchemSystem=[ k1*x1 ]\n",
                                    "polRing,(x1)=polynomial_ring(R,[\"x1\"])\nchemSystem=[ x1\n"])
def test_malformed_files_raise_parse_errors(broken):
    with pytest.raises(ParseError):
        parse_entry(broken)


# ----------------------------------------------------------------- from an entry to a model

def test_conservation_law_becomes_links_between_its_terms():
    e = parse_entry(BINDING)
    links = odebase.constraint_links(e.constraints[0])
    x1, x3, k5 = (e.symbols[n] for n in ("x1", "x3", "k5"))
    assert {sp.simplify(r) for r in links} <= {x3 / x1, k5 / x1, x1 / x3, k5 / x3, x1 / k5, x3 / k5}
    assert len(links) == 2  # three terms -> two independent ratios


def test_relation_with_one_term_gives_no_link():
    assert odebase.constraint_links(sp.Symbol("x1", positive=True)) == []


def test_unused_parameters_are_dropped_and_the_total_joins_through_the_law():
    e = parse_entry(BINDING)
    free, linked = odebase.to_model(e, use_constraints=False), odebase.to_model(e)
    assert [str(p) for p in free.params] == ["k1", "k2"]            # k3 unused; k4 cancels; k5 only in the law
    assert [str(p) for p in linked.params] == ["k1", "k2", "k5"]
    assert len(linked.extra_invariants) == 2


def test_equations_are_stored_term_by_term():
    """(a*x - b)/c is kept as a*x/c - b/c: the form Lean's data records (they differ at c = 0)."""
    m = odebase.to_model(parse_entry(BINDING))
    assert all(sp.fraction(f)[1] == 1 for f in m.rhs)


# ----------------------------------------------------------------- the audit

def test_audit_row_for_the_binding_model():
    row = odebase.audit_entry(parse_entry(BINDING))
    assert (row.species, row.parameters, row.unused_parameters, row.conservation_laws) == (3, 3, 2, 1)
    assert row.scalings == analyze(odebase.to_model(parse_entry(BINDING))).n_scalings == 2
    assert row.removable == 2 and row.remaining == 1 and row.spurious == 0
    assert row.in_lean_scope


def test_audit_of_a_directory_reports_every_file_once(tmp_path):
    (tmp_path / "BIOMD0000000001.jl").write_text(BINDING)
    (tmp_path / "BIOMD0000000002.jl").write_text(DECAY)
    (tmp_path / "BIOMD0000000003.jl").write_text(ALGEBRAIC)
    (tmp_path / "BIOMD0000000004.jl").write_text(DECAY + "#" * 5000)
    (tmp_path / "README.md").write_text("not a model")
    rows, skipped = odebase.audit(tmp_path, max_bytes=3000)
    assert [r.id for r in rows] == ["TEST0000000001", "TEST0000000002"]
    reasons = dict(skipped)
    assert "defined by a constraint" in reasons["BIOMD0000000003"]
    assert "larger than" in reasons["BIOMD0000000004"]
    assert len(rows) + len(skipped) == 4


def test_report_totals_are_consistent(tmp_path):
    (tmp_path / "BIOMD0000000001.jl").write_text(BINDING)
    (tmp_path / "BIOMD0000000002.jl").write_text(DECAY)
    rows, skipped = odebase.audit(tmp_path)
    text = odebase.report(rows, skipped)
    assert "| models read | 2 |" in text
    assert f"| parameters in total / removable by scaling | {sum(r.parameters for r in rows)} / " \
           f"{sum(r.removable for r in rows)} " in text
    assert text.count("\n| TEST") == 2
    assert "This is a pilot" in text and "only a handful of results are checked in Lean" in text


def test_empty_directory_gives_a_report_not_a_crash(tmp_path):
    rows, skipped = odebase.audit(tmp_path)
    assert rows == [] and "No model could be read" in odebase.report(rows, skipped)


def test_smallest_models_are_chosen_for_lean_in_a_fixed_order(tmp_path):
    (tmp_path / "BIOMD0000000001.jl").write_text(BINDING)
    (tmp_path / "BIOMD0000000002.jl").write_text(DECAY)
    rows, _ = odebase.audit(tmp_path)
    assert odebase.certifiable(rows, 5) == ["TEST0000000002", "TEST0000000001"]  # 4 variables before 6
    assert odebase.certifiable(rows, 1) == ["TEST0000000002"]
    assert odebase.certifiable(rows, 5, max_size=3) == []


def test_certificates_are_written_with_credit_to_the_source(tmp_path):
    data = tmp_path / "data"
    data.mkdir()
    (data / "TEST0000000001.jl").write_text(BINDING)
    paths = odebase.write_certificates(data, ["TEST0000000001"], tmp_path / "NondimVerify")
    text = paths[0].read_text()
    assert "namespace NondimVerify.Certified.ODEbase.TEST0000000001" in text
    assert "Made-up binding model (BioModels TEST0000000001, as preprocessed by ODEbase)" in text
    assert "theorem links_respected" in text and "theorem reduction_correct" in text


def test_cli_audit_writes_the_report(tmp_path, capsys):
    data = tmp_path / "data"
    data.mkdir()
    (data / "BIOMD0000000001.jl").write_text(BINDING)
    main(["audit", "--data", str(data), "--out", str(tmp_path / "reports"), "--no-desr"])
    assert "| models read | 1 |" in (tmp_path / "reports" / "odebase_pilot.md").read_text()
    assert "report:" in capsys.readouterr().out


def test_cli_audit_without_data_says_how_to_get_it(tmp_path):
    with pytest.raises(SystemExit) as e:
        main(["audit", "--data", str(tmp_path / "nowhere"), "--out", str(tmp_path)])
    assert "--fetch" in str(e.value) and "git clone" in str(e.value)


def test_committed_report_is_a_pilot_report():
    report = Path(__file__).resolve().parents[2] / "reports" / "odebase_pilot.md"
    if not report.exists():
        pytest.skip("no ODEbase report in this checkout")
    text = report.read_text()
    assert text.startswith("# ODEbase pilot") and "| models read |" in text
    read = int(text.split("| models read | ")[1].split(" |")[0])
    assert text.count("\n| BIOMD") >= read  # every model read has a row (skipped ones are listed too)


def test_real_models_when_a_local_clone_exists():
    data = default_odebase_dir()
    if not data.exists():
        pytest.skip("no local clone of the model files (run `nondim audit --fetch`)")
    rows, skipped = odebase.audit(data, limit=25)
    assert len(rows) >= 15
    assert all(r.scalings <= r.scalings_equations + r.conservation_laws + 5 for r in rows)
    assert all(0 <= r.removable <= r.parameters for r in rows)

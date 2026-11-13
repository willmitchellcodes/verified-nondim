"""The Python -> Lean bridge, checked WITHOUT Lean.

Every generated theorem is re-read from the certificate text by an independent
parser (lean_reader.py) and re-evaluated. If the exporter printed a wrong
matrix, a wrong rank or a wrong equation, these tests fail before Lean runs.
"""
import pytest
import sympy as sp

from conftest import LEAN, P
from lean_reader import check_matrix_claim, check_real_identity, lean_to_python, matrices, theorems
from nondim import models
from nondim.catalog import CATALOG
from nondim.cli import certify
from nondim.constraints import solve
from nondim.lean_export import LeanExportError, certificate, lean_fin_vec, lean_matrix, lean_name, to_lean
from nondim.report import build
from nondim.scaling import all_nondimensionalizations, nondimensionalize

CERTIFIED = [k for k, c in CATALOG.items() if c.get("certify")]
a, b, c = P("a"), P("b"), P("c")


# ------------------------------------------------------------ the printer

@pytest.mark.parametrize("expr", [
    a, a * b, a / b, a / b**2, -a, a - b, a + b * c, (a + b) / (a * c + 1), a**3, 1 / a, sp.Rational(2, 3) * a,
    -sp.Rational(1, 2) * a / b, a * (b - c) / (1 + a * b), sp.Integer(7), sp.Integer(-2), a / (b * c), (a + 1) ** 2,
])
def test_to_lean_round_trips_numerically(expr):
    env = {"a": 1.7, "b": 0.6, "c": 2.3}
    got = eval(lean_to_python(to_lean(expr)), {"__builtins__": {}}, env)
    assert got == pytest.approx(float(expr.subs({a: 1.7, b: 0.6, c: 2.3})))


@pytest.mark.parametrize("bad", [sp.sqrt(a), a**b, sp.exp(a), sp.log(a)])
def test_to_lean_refuses_what_it_cannot_print(bad):
    with pytest.raises(LeanExportError):
        to_lean(bad)


def test_lean_matrix_and_vector_literals():
    assert lean_matrix(sp.Matrix([[1, -2], [0, 3]])) == "!![1, -2;\n    0, 3]"
    assert lean_fin_vec([4, 5]) == "![4, 5]"
    with pytest.raises(LeanExportError):
        lean_matrix(sp.zeros(0, 3))


def test_reserved_words_are_renamed():
    assert lean_name(sp.Symbol("at")) == "at_" and lean_name(sp.Symbol("beta")) == "beta"
    assert to_lean(sp.Symbol("fun", positive=True) * a) in ("(a * fun_)", "(fun_ * a)")


# ------------------------------------------------------------ whole certificates

def _all_certificates():
    """Catalog certificates plus one for every alternative choice of every model."""
    out = {}
    for key in CERTIFIED:
        _, _, nd, results = build(key)
        out[key] = certificate(nd, results)
    for key in models.ALL:
        for i, nd in enumerate(all_nondimensionalizations(models.ALL[key]())):
            if nd.analysis.A.shape[0] and nd.normalized:
                out[f"{key}/choice{i}"] = certificate(nd)
    return out


CERTS = _all_certificates()


def test_we_cover_many_certificates():
    assert len(CERTS) > 40


@pytest.mark.parametrize("name", list(CERTS))
def test_every_theorem_is_understood_and_true(name):
    text = CERTS[name]
    M, T = matrices(text), theorems(text)
    assert {"symmetries", "rank_K", "rank_A", "rank_Apar", "new_vars_invariant",
            "change_of_variables_invertible"} <= set(T)
    for thm, stmt in T.items():
        verdict = check_matrix_claim(stmt, M)
        if verdict is None:
            verdict = check_real_identity(stmt)
        assert verdict is not None, f"{thm}: statement shape not recognized: {stmt}"
        assert verdict, f"{thm} is FALSE: {stmt}"


@pytest.mark.parametrize("name", list(CERTS))
def test_certificate_matches_the_solver(name):
    key = name.split("/")[0]
    text = CERTS[name]
    M = matrices(text)
    m = models.ALL[key]()
    n = len(m.variables)
    assert M["Amat"].shape[1] == n == M["Kmat"].shape[0] == M["Vmat"].shape[0] == M["Tmat"].shape[0]
    assert M["Amat"].shape[0] == n - M["Kmat"].rank(), "maximality: r = n - rank K"
    assert M["Apar"].shape[1] == len(m.params)
    assert M["Tmat"].shape == (n, n)
    assert f"namespace NondimVerify.Cert." in text and text.rstrip().endswith(text.split("namespace ")[1].split()[0])
    assert text.startswith("import NondimVerify.Basic")
    assert "sorry" not in text
    assert sum(1 for line in text.splitlines() if line.startswith("theorem rhs_")) == len(m.states)


def test_constraint_sections_carry_the_right_theorems():
    m = models.michaelis_menten_ic()
    cs = [solve(m, 2, keep=["k1"]), solve(m, 6), solve(m, want={"eps": "e0/s0", "lam": "k2/km1"}),
          solve(m, want={"x": "e0*k1"}), solve(m, want={"p": "e0/s0", "q": "s0/e0"}), solve(m, want={"x": "k2 + km1"})]
    T = theorems(certificate(cs[0].witness, cs))
    assert "constraint1_enough" in T and "constraint2_unsat" in T
    assert {"constraint3_want_invariant", "constraint3_want_independent", "constraint3_regroup_invertible",
            "constraint3_regroup_unimodular", "constraint3_regroup_s", "constraint3_regroup_c"} <= set(T)
    assert "constraint4_want_not_invariant" in T and "constraint4_want_invariant" not in T
    assert "constraint5_want_dependent" in T
    assert not any(t.startswith("constraint6_want") for t in T)


def test_fractional_regrouping_is_not_exported_as_equations():
    res = solve(models.lotka_volterra(), want={"sq": "(c/a)**2"})
    text = certificate(res.witness, [res])
    assert "constraint1_regroup_invertible" in text and "constraint1_regroup_unimodular" not in text
    assert "fractional powers" in text


# ------------------------------------------------------------ files on disk

def test_certificates_on_disk_are_up_to_date(tmp_path):
    """`lean/NondimVerify/Cert/*.lean` must be exactly what the solver produces today."""
    mods = certify(lean_dir=tmp_path, quiet=True)
    assert len(mods) == len(CERTIFIED)
    for mod in mods:
        fresh = (tmp_path / "Cert" / f"{mod}.lean").read_text()
        on_disk = (LEAN / "NondimVerify" / "Cert" / f"{mod}.lean").read_text()
        assert fresh == on_disk, f"{mod}.lean is stale: run `python -m nondim certify`"
    assert (tmp_path / "Cert.lean").read_text() == (LEAN / "NondimVerify" / "Cert.lean").read_text()
    on_disk_files = {p.stem for p in (LEAN / "NondimVerify" / "Cert").glob("*.lean")}
    assert on_disk_files == set(mods), "stray or missing certificate files"


def test_exporting_is_deterministic():
    _, _, nd, results = build("sir")
    assert certificate(nd, results) == certificate(*build("sir")[2:])


def test_sir_certificate_states_the_textbook_reduction():
    text = certificate(nondimensionalize(models.sir(), [P("gamma"), P("N")]))
    assert "beta_hat = N*beta/gamma" in text and "Parameters: 3 -> 1" in text

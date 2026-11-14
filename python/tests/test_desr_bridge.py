"""Certifying desr: the adapter, and desr against this package's own solver.

Skipped when desr is not installed (pip install git+https://github.com/ofloveandhate/desr).

desr is treated as untrusted: nothing below assumes its answer is right. The tests check that
  * what the adapter extracts satisfies every relation the Lean certificate will state;
  * desr and our solver, two independent implementations, agree on the facts that do not
    depend on arbitrary choices (the space of scalings, the number of parameters left);
  * a wrong answer from desr would be caught (simulated by corrupting its output);
  * everything outside the supported scope is refused with a reason.
"""
import copy
import itertools
import random

import pytest
import sympy as sp

from nondim.desr_bridge import compare, desr_available, from_desr, to_desr

if not desr_available():
    pytest.skip("desr is not installed (pip install git+https://github.com/ofloveandhate/desr)",
                allow_module_level=True)

from conftest import LEAN  # noqa: E402
from nondim import lean_export2, models  # noqa: E402
from nondim.catalog import GENERAL  # noqa: E402
from nondim.cli import _camel, comparison_table, main  # noqa: E402
from nondim.hlform import NotSupported, from_nondim  # noqa: E402
from nondim.model import Model  # noqa: E402
from nondim.scaling import analyze, nondimensionalize  # noqa: E402

SUPPORTED = ["logistic", "sir_noN", "lotka_volterra", "michaelis_menten", "rosenzweig_macarthur",
             "spurious_original", "spurious_substituted"]


def test_desr_is_available_and_reports_a_version():
    assert desr_available()


@pytest.mark.parametrize("key", SUPPORTED)
def test_desr_output_passes_every_check(key):
    red = from_desr(models.ALL[key]())
    red.check()
    assert red.source.startswith("desr")
    assert red.is_maximal(), "desr missed a scaling symmetry (by our independently derived exponent matrix)"


@pytest.mark.parametrize("key", SUPPORTED)
def test_desr_and_our_solver_agree(key):
    res = compare(models.ALL[key]())
    assert res["same_scalings"], "the two tools found different scaling symmetries"
    assert res["desr_after"] == res["ours_after"], "the two tools disagree on how many parameters remain"
    assert res["agree"]


@pytest.mark.parametrize("key, expected", [
    ("logistic", {"r*t", "N/K"}),
    ("sir_noN", {"gamma*t", "I*beta/gamma", "S*beta/gamma"}),
    ("lotka_volterra", {"a*t", "c/a", "d*x/a", "b*y/a"}),
])
def test_desr_invariants_are_the_textbook_ones(key, expected):
    red = from_desr(models.ALL[key]())
    got = {red.time_invariant, *red.invariant_monomials()}
    want = {sp.sympify(e, locals={str(v): v for v in red.model.variables}) for e in expected}
    assert {sp.simplify(g) for g in got} == {sp.simplify(w) for w in want}


@pytest.mark.parametrize("key, text", [
    ("sir_noN", {"S": "-nu0*nu1", "I": "nu0*nu1 - nu0"}),
    ("logistic", {"N": "nu0 - nu0**2"}),
])
def test_desr_reduced_systems_are_the_textbook_ones(key, text):
    red = from_desr(models.ALL[key]())
    names = {str(s): s for s in red.invariant_symbols}
    for z in red.model.states:
        assert sp.expand(red.reduced_rhs[z] - sp.sympify(text[str(z)], locals=names)) == 0


@pytest.mark.parametrize("key", SUPPORTED)
def test_desr_and_own_reduced_systems_are_related_by_renaming_invariants(key):
    """The two tools may pick different invariants. Both reduced systems must still be the
    original system on their own cross-section, which `check()` verified; here we also confirm
    they have the same number of state equations and reduced parameters."""
    theirs, ours = from_desr(models.ALL[key]()), from_nondim(nondimensionalize(models.ALL[key]()))
    assert len(theirs.reduced_rhs) == len(ours.reduced_rhs)
    assert len(theirs.reduced_parameters()) == len(ours.reduced_parameters())
    assert theirs.r == ours.r


def test_variable_order_is_desrs_and_time_is_separated():
    red = from_desr(models.lotka_volterra())
    assert [str(v) for v in red.variables] == ["a", "b", "c", "d", "x", "y"]
    assert [str(v) for v in red.full_order] == ["a", "b", "c", "d", "t", "x", "y"]
    assert red.A.shape == (3, 6) and len(red.tau) == 3
    assert red.Dfull.shape == (3, 7)


def test_to_desr_builds_the_same_equations():
    m = models.lotka_volterra()
    system = to_desr(m)
    ours = {str(z): f for z, f in zip(m.states, m.rhs)}
    plain = {sp.Symbol(v.name): v for v in m.variables}
    seen = 0
    for var, rhs in system.derivative_dict.items():
        if str(var) in ours:  # desr also lists dt/dt = 1 and dparam/dt = 0
            assert sp.expand(sp.sympify(rhs).xreplace(plain) - ours[str(var)]) == 0
            seen += 1
    assert seen == len(m.states)


# ----------------------------------------------------------------- a wrong desr would be caught

def _bump(M):
    M = M.copy()
    M[0, 0] += 1
    return M


@pytest.mark.parametrize("field", ["A", "Vn", "Vi", "Wu", "Wd", "Pfull", "V1full"])
def test_a_wrong_matrix_from_desr_is_caught_before_export(field):
    red = copy.deepcopy(from_desr(models.sir_no_population()))
    setattr(red, field, _bump(getattr(red, field)))
    with pytest.raises(ValueError):
        red.check()


def test_a_wrong_reduced_system_from_desr_is_caught_before_export():
    red = copy.deepcopy(from_desr(models.sir_no_population()))
    z = red.model.states[0]
    red.reduced_rhs[z] = red.reduced_rhs[z] * 2
    with pytest.raises(ValueError, match="reduced equation"):
        red.check()


def test_a_missed_symmetry_would_be_detected():
    """Drop one of desr's scalings: every identity still holds for the smaller matrix, but
    the cross-check against our exponent matrix says a symmetry is missing."""
    red = from_desr(models.lotka_volterra())
    assert red.is_maximal()
    smaller = copy.deepcopy(red)
    smaller.A, smaller.tau = red.A[:2, :], red.tau[:2]
    assert not smaller.is_maximal()


# ----------------------------------------------------------------- scope

@pytest.mark.parametrize("key, reason", [
    ("sir", "unit links"), ("michaelis_menten_ic", "unit links"), ("spurious_fixed", "unit links"),
    ("sir_reported", "do not appear"),
])
def test_unsupported_models_are_refused_with_a_reason(key, reason):
    with pytest.raises(NotSupported, match=reason):
        from_desr(models.ALL[key]())


@pytest.mark.parametrize("equations, params, reason", [
    ({"x": "1 - x"}, "", "no scaling symmetry"),
    ({"x": "a*x*t"}, "a", "autonomous"),
    ({"x": "a*y/x - b*x", "y": "c*y"}, "a b c", "scheme"),
])
def test_edge_models_are_refused_with_a_reason(equations, params, reason):
    with pytest.raises(NotSupported, match=reason):
        from_desr(Model.from_strings("Edge", equations, params))


def test_desr_reports_a_zero_scaling_for_a_model_without_symmetry():
    """An edge case in desr itself, found while testing: for dx/dt = 1 - x it returns one
    "scaling" whose weights are all zero. The adapter must not count that as a symmetry."""
    from desr import ODETranslator
    m = Model.from_strings("Edge", {"x": "1 - x"}, "")
    tr = ODETranslator.from_ode_system(to_desr(m))
    assert sp.Matrix(tr.scaling_matrix).rank() == 0
    assert analyze(m).n_scalings == 0


def test_compare_never_raises_on_any_builtin_model():
    for key in models.ALL:
        res = compare(models.ALL[key]())
        assert res["desr"] is not None or res["note"]


def test_laurent_model_with_a_negative_exponent_is_supported_by_both():
    m = Model.from_strings("Laurent", {"x": "a - b*x/y", "y": "c - d*y"}, "a b c d")
    res = compare(m)
    assert res["agree"] and res["desr_after"] == 1


# ----------------------------------------------------------------- property test on random models

def _random_model(rng: random.Random, idx: int) -> Model:
    """A random polynomial system in which every parameter appears (one parameter per term)."""
    n_states, n_params = rng.choice([1, 2]), rng.choice([2, 3, 4])
    states = ["x", "y"][:n_states]
    params = rng.sample(["a", "b", "c", "d"][:n_params], n_params)
    owners = [states[i % n_states] for i in range(n_params)]
    rng.shuffle(owners)
    eqs = {s: [] for s in states}
    for p, s in zip(params, owners):
        mono = p
        for z in states:
            e = rng.choice([0, 1, 1, 2])
            if e:
                mono += f"*{z}**{e}"
        eqs[s].append(rng.choice(["", "-"]) + mono)
    text = {s: (" + ".join(ts).replace("+ -", "- ") if ts else "0") for s, ts in eqs.items()}
    return Model.from_strings(f"Random{idx}", text, " ".join(sorted(params)))


def test_random_models_desr_and_our_solver_agree():
    """Two independent implementations on models nobody hand-picked. Whenever desr's answer is in
    scope it must pass every check, be maximal, and agree with ours."""
    rng, compared, skipped = random.Random(2026), 0, 0
    for idx in range(120):
        m = _random_model(rng, idx)
        try:
            theirs = from_desr(m)
        except NotSupported:
            skipped += 1
            continue
        an = analyze(m)
        assert theirs.r == an.n_scalings, (m.rhs, theirs.r, an.n_scalings)
        assert theirs.is_maximal(), m.rhs
        assert len(theirs.reduced_parameters()) == an.min_params, m.rhs
        res = compare(m)
        assert res["same_scalings"], m.rhs
        compared += 1
    assert compared >= 25, f"only {compared} random models were in scope ({skipped} skipped)"


SKEW = dict(equations={"x": "-a*y - c*x*y**2", "y": "b*x*y - c*x**2"}, params="a b c")


def test_regression_invariants_that_are_not_cross_section_coordinates():
    """Found by the random test above. desr's answer for this model is correct, but its new
    variable for x is NOT the value of x on the cross-section (there x = nu0 / kappa0^3).
    A certificate format that states the reduced equations on the cross-section cannot certify
    it; the current format (new variables along the original solution) can."""
    red = from_desr(Model.from_strings("Skew", **SKEW))
    red.check()
    x = red.model.states[0]
    nu_x = red.invariant_symbols[red.state_col[x]]
    on_section = red.reconstruct()[x]
    assert sp.simplify(on_section - nu_x) != 0          # the phenomenon is real
    assert sp.simplify(on_section * red.invariant_symbols[0] ** 3 - nu_x) == 0
    # desr's reduced system, checked by hand in exact arithmetic at a point
    vals = dict(zip(red.variables, [sp.Rational(k) for k in (2, 3, 5, 7, 11)]))
    pis = {s: m.xreplace(vals) for s, m in zip(red.invariant_symbols, red.invariant_monomials())}
    for z, f in zip(red.model.states, red.model.rhs):
        c = sp.Mul(*[v ** e for v, e in zip(red.variables, red.state_factor_exponents(z))]).xreplace(vals)
        assert c * f.xreplace(vals) == red.time_factor().xreplace(vals) * red.reduced_rhs[z].xreplace(pis)


# ----------------------------------------------------------------- files, CLI, report

@pytest.mark.parametrize("key", SUPPORTED)
def test_desr_certificates_on_disk_are_up_to_date(key):
    red = from_desr(models.ALL[key]())
    name = _camel(red.model.name)
    on_disk = (LEAN / "NondimVerify" / "Certified" / "Desr" / f"{name}.lean").read_text()
    assert on_disk == lean_export2.certificate(red, f"Desr.{name}")


def test_every_general_model_has_a_desr_certificate_or_a_reason():
    for key in GENERAL:
        m = models.ALL[key]()
        try:
            from_desr(m)
        except NotSupported as e:
            assert str(e)
            continue
        assert (LEAN / "NondimVerify" / "Certified" / "Desr" / f"{_camel(m.name)}.lean").exists()


def test_certificate_names_desr_as_the_source():
    text = lean_export2.certificate(from_desr(models.sir_no_population()), "Desr.SIRNoN")
    assert "reduced by desr" in text and "namespace NondimVerify.Certified.Desr.SIRNoN" in text
    assert "nu0" in text  # desr's own names for the invariants


def test_cli_desr_command(capsys):
    main(["desr", "lotka_volterra"])
    out = capsys.readouterr().out
    assert "reduced by desr" in out and "same scalings: True" in out and "kappa0 = c/a" in out


def test_cli_desr_command_explains_unsupported_models():
    with pytest.raises(SystemExit) as e:
        main(["desr", "sir"])
    assert "unit links" in str(e.value)


def test_cli_compare_writes_the_report(tmp_path, capsys):
    main(["compare", "--out", str(tmp_path)])
    text = (tmp_path / "desr_comparison.md").read_text()
    assert "| lotka_volterra | 4 | 3 / 3 | 1 / 1 | yes |" in text
    assert "**NO**" not in text
    assert text.count("\n| ") >= len(models.ALL)


def test_comparison_table_has_one_row_per_model():
    table = comparison_table()
    for key in models.ALL:
        assert f"| {key} |" in table

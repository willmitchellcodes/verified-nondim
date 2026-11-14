"""The solver-independent form of a reduction (`hlform`) and the general-form Lean export.

No Lean and no desr needed here. Three questions:
  * does `HLReduction.check()` accept what our solver produces, on every model in scope?
  * does it REJECT a reduction corrupted in any one relation? (the Python-side teeth)
  * are the limits of the form reported as limits (NotSupported with a reason), never as
    wrong answers or crashes?
"""
import copy
import re

import pytest
import sympy as sp

from conftest import LEAN
from lean_reader import matrices
from nondim import lean_export2, models
from nondim.catalog import CATALOG, GENERAL
from nondim.cli import _camel, certify_general, own_reduction
from nondim.hlform import HLReduction, NotSupported, from_nondim, left_inverse_certificate, system_terms
from nondim.model import Model
from nondim.scaling import all_nondimensionalizations, analyze, nondimensionalize


def own(key) -> HLReduction:
    """This package's reduction with the catalog's choice of normalized parameters."""
    return own_reduction(key)


def own_text(key, module="Own.X") -> str:
    return lean_export2.certificate(own(key), module, CATALOG[key].get("constraints"))


POLYNOMIAL = [k for k in GENERAL if k != "rosenzweig_macarthur"]


# ----------------------------------------------------------------- terms: the model as data

def test_terms_of_sir_are_the_textbook_monomials():
    red = own("sir_noN")
    names = [str(v) for v in red.variables]
    S, I, beta, gamma = (names.index(x) for x in ("S", "I", "beta", "gamma"))
    terms = red.terms()
    assert terms[beta] == [] and terms[gamma] == []  # parameters have no equation
    assert len(terms[S]) == 1 and len(terms[I]) == 2
    (c, e), = terms[S]
    assert c == -1 and e[S] == e[I] == e[beta] == 1 and e[gamma] == 0


@pytest.mark.parametrize("key", POLYNOMIAL)
def test_terms_rebuild_the_equations_exactly(key):
    red = own(key)
    for v, terms in zip(red.variables, red.terms()):
        rebuilt = sum(c * sp.Mul(*[x ** e for x, e in zip(red.variables, exps)]) for c, exps in terms)
        expected = red.model.rhs[red.model.states.index(v)] if v in red.model.states else 0
        assert sp.expand(rebuilt - expected) == 0


def test_terms_never_contain_a_zero_coefficient():
    """Lean's symmetry check reads the terms as written (see NondimVerifyTest/Limits.lean §2):
    a term `0 * x^5` would make it say no. The exporter must never emit one."""
    m = Model.from_strings("Cancel", {"x": "a*x - a*x + b*x**2 - 0*x**5"}, "a b")
    terms = system_terms(m, [*m.states, *m.params])
    assert all(c != 0 for ts in terms for c, _ in ts)
    assert len(terms[0]) == 1  # a*x - a*x cancelled, only b*x^2 is left


def test_terms_keep_fractional_coefficients_and_negative_exponents():
    m = Model.from_strings("L", {"x": "a - b*x/y", "y": "c/2 - d*y"}, "a b c d")
    terms = system_terms(m, [*m.states, *m.params])
    assert any(c == sp.Rational(1, 2) for c, _ in terms[1])
    assert any(-1 in e for _, e in terms[0])


@pytest.mark.parametrize("equations, params, reason", [
    ({"x": "a*x*t"}, "a", "autonomous"),
    ({"x": "a*x/(1 + b*x)"}, "a b", "polynomial"),
    ({"x": "a*sqrt(x)"}, "a", "fractional exponent"),
])
def test_out_of_scope_equations_are_refused_with_a_reason(equations, params, reason):
    m = Model.from_strings("Bad", equations, params)
    with pytest.raises(NotSupported, match=reason):
        system_terms(m, [*m.states, *m.params])


# ----------------------------------------------------------------- left-inverse certificates

@pytest.mark.parametrize("B", [
    sp.Matrix([[1, 0], [0, 1]]), sp.Matrix([[2]]), sp.Matrix([[1, 1], [0, 2], [3, 0]]),
    sp.Matrix([[-1, -1], [-1, 0]]), sp.zeros(3, 0),
])
def test_left_inverse_certificate_is_a_certificate(B):
    G, d = left_inverse_certificate(B)
    assert d != 0 and G * B == d * sp.eye(B.shape[1])
    assert all(sp.Integer(x) == x for x in G)


def test_left_inverse_needs_a_factor_when_the_scaling_is_not_primitive():
    """x -> lam^2 x can be normalized only with a square root: the certificate has d = 2."""
    G, d = left_inverse_certificate(sp.Matrix([[2]]))
    assert abs(d) == 2


def test_left_inverse_does_not_exist_for_dependent_columns():
    with pytest.raises(ValueError, match="dependent"):
        left_inverse_certificate(sp.Matrix([[1, 1], [2, 2]]))


# ----------------------------------------------------------------- our own reductions in HL form

@pytest.mark.parametrize("key", GENERAL)
def test_own_reduction_passes_every_check(key):
    red = own(key)
    red.check()
    assert red.is_maximal()
    an = analyze(red.model)
    assert red.r == an.n_scalings
    assert len(red.reduced_parameters()) == an.min_params


@pytest.mark.parametrize("key", GENERAL)
def test_every_choice_of_normalized_parameters_gives_a_valid_form(key):
    count = 0
    for nd in all_nondimensionalizations(models.ALL[key]()):
        try:
            red = from_nondim(nd)
        except NotSupported:
            continue
        red.check()
        count += 1
    assert count >= 1


@pytest.mark.parametrize("key", GENERAL)
def test_invariants_are_invariant_and_reconstruction_inverts_them(key):
    red = own(key)
    point = red.reconstruct()
    # substituting the cross-section point into each invariant returns that invariant's symbol
    for sym, mono in zip(red.invariant_symbols, red.invariant_monomials()):
        assert sp.simplify(sp.powsimp(mono.xreplace(point), force=True) - sym) == 0
    # and every auxiliary monomial equals 1 there
    for aux in red.auxiliary_monomials():
        assert sp.simplify(aux.xreplace(point)) == 1


@pytest.mark.parametrize("key", GENERAL)
def test_reduced_equations_agree_numerically_with_the_original(key):
    """Independent of sympy.simplify: at random positive points of the ORIGINAL variables,
    (factor of the new variable) * f  ==  (time factor) * g(invariants), in exact arithmetic."""
    import random
    red, rng = own(key), random.Random(1)
    for _ in range(5):
        point = {v: sp.Rational(rng.randint(1, 9), rng.randint(1, 9)) for v in red.variables}
        pis = {s: mono.xreplace(point) for s, mono in zip(red.invariant_symbols, red.invariant_monomials())}
        T = red.time_factor().xreplace(point)
        for z, f in zip(red.model.states, red.model.rhs):
            c = sp.Mul(*[v ** e for v, e in zip(red.variables, red.state_factor_exponents(z))]).xreplace(point)
            assert c * f.xreplace(point) == T * red.reduced_rhs[z].xreplace(pis)


@pytest.mark.parametrize("key", GENERAL)
def test_new_variables_are_state_times_parameters_and_time_is_parameters(key):
    red = own(key)
    params = set(red.parameters)
    assert all(e == 0 or v in params for v, e in zip(red.variables, red.time_exponents))
    assert red.time_invariant == red.time_factor() * red.model.t
    for z in red.model.states:
        u = red.state_factor_exponents(z)
        assert all(e == 0 or v in params for v, e in zip(red.variables, u))
        mono = red.invariant_monomials()[red.state_col[z]]
        assert sp.simplify(mono / z - sp.Mul(*[v ** e for v, e in zip(red.variables, u)])) == 0


# ----------------------------------------------------------------- the checker has teeth

def _bump(M, i=0, j=0):
    M = M.copy()
    M[i, j] += 1
    return M


CORRUPTIONS = {
    "scaling_is_not_a_symmetry": lambda r: setattr(r, "A", _bump(r.A)),
    "wrong_time_weight": lambda r: setattr(r, "tau", [r.tau[0] + 1, *r.tau[1:]]),
    "invariant_with_units": lambda r: setattr(r, "Vn", _bump(r.Vn)),
    "inverse_is_not_the_inverse": lambda r: setattr(r, "Wd", _bump(r.Wd)),
    "auxiliaries_not_free": lambda r: setattr(r, "G", _bump(r.G)),
    "zero_factor": lambda r: setattr(r, "d", 0),
    "wrong_reduced_equation": lambda r: r.reduced_rhs.update(
        {r.model.states[0]: r.reduced_rhs[r.model.states[0]] + 1}),
    "sign_error_in_reduced_equation": lambda r: r.reduced_rhs.update(
        {r.model.states[0]: -r.reduced_rhs[r.model.states[0]]}),
    "pi_groups_with_units": lambda r: setattr(r, "Pfull", _bump(r.Pfull)),
    "wrong_time_factor": lambda r: setattr(r, "time_exponents", [e + 1 for e in r.time_exponents]),
    "new_time_involves_a_state": lambda r: setattr(
        r, "time_exponents", [e + (1 if v in r.model.states else 0) for v, e in zip(r.variables, r.time_exponents)]),
    "state_assigned_the_wrong_new_variable": lambda r: r.state_col.update(
        {r.model.states[0]: (r.state_col[r.model.states[0]] + 1) % r.Vn.shape[1]}),
}


@pytest.mark.parametrize("name", list(CORRUPTIONS))
@pytest.mark.parametrize("key", ["sir_noN", "lotka_volterra"])
def test_corrupted_reduction_is_rejected(key, name):
    red = copy.deepcopy(own(key))
    CORRUPTIONS[name](red)
    with pytest.raises(ValueError):
        red.check()


def test_auxiliary_monomial_involving_a_state_is_rejected():
    """The reduction theorem needs the auxiliary monomials to be constant along solutions."""
    red = copy.deepcopy(own("sir_noN"))
    state_row = red.variables.index(red.model.states[0])
    red.Vi = _bump(red.Vi, state_row, 0)
    with pytest.raises(ValueError):
        red.check()


def test_certificate_refuses_to_print_a_corrupted_reduction():
    red = copy.deepcopy(own("logistic"))
    red.A = _bump(red.A)
    with pytest.raises(ValueError):
        lean_export2.certificate(red)


# ----------------------------------------------------------------- limits are reported as limits

def _model(name):
    return {
        "not_rational": lambda: Model.from_strings("Exp", {"x": "a*exp(-x) - b*x"}, "a b"),
        "root": lambda: Model.from_strings("Root", {"x": "a*sqrt(x) - b*x"}, "a b"),
        "time_dependent": lambda: Model.from_strings("TimeDep", {"x": "a*x*t"}, "a"),
        "no_scaling": lambda: Model.from_strings("NoScaling", {"x": "1 - x"}, ""),
        "no_parameters": lambda: Model.from_strings("NoParams", {"x": "-x"}, ""),
        "needs_roots": lambda: Model.from_strings("Roots", {"x": "a/y - b*x", "y": "c*x - d*y"}, "a b c d"),
    }[name]()


@pytest.mark.parametrize("name, reason", [
    ("not_rational", "not a power of a model variable"), ("root", "fractional"),
    ("time_dependent", "autonomous"),
    ("no_scaling", "no scaling symmetry"), ("no_parameters", "does not use every scaling"),
    ("needs_roots", "fractional powers"),
])
def test_out_of_scope_models_raise_not_supported_with_the_reason(name, reason):
    from nondim.model import OutOfScopeError
    # the solver itself (OutOfScopeError) or the general form (NotSupported) refuses, with a reason
    with pytest.raises((NotSupported, OutOfScopeError), match=reason):
        from_nondim(nondimensionalize(_model(name)))


def test_model_with_negative_exponents_is_in_scope():
    m = Model.from_strings("Laurent", {"x": "a - b*x/y", "y": "c - d*y"}, "a b c d")
    red = from_nondim(nondimensionalize(m))
    red.check()
    assert len(red.parameters) == 4 and len(red.reduced_parameters()) == 1


# ----------------------------------------------------------------- the Lean text

@pytest.mark.parametrize("key", GENERAL)
def test_certificate_states_every_guarantee(key):
    red = own(key)
    text = lean_export2.certificate(red, "Own.X")
    for name in ["theorem symmetry", "theorem unimodular", "theorem invariant", "theorem auxiliaries_free",
                 "theorem auxiliaries_are_parameters", "theorem time_factor_is_parameters",
                 "theorem reduction_correct", "theorem cross_section", "theorem invariants_complete",
                 "theorem kills_K", "theorem rank_K", "theorem rank_A"]:
        assert name in text, name
    for prefix in ("eq_", "reduced_identity_", "new_", "factor_"):
        assert len(re.findall(rf"theorem {prefix}\w+", text)) == len(red.model.states), prefix
    assert "sorry" not in text and "axiom" not in text
    assert text.count("theorem eq_") == len(red.model.states)


@pytest.mark.parametrize("key", GENERAL)
def test_matrices_in_the_lean_text_satisfy_the_relations(key):
    """Re-read the generated file with the independent reader and re-check the relations from
    the text alone, so a printing bug cannot hide behind a correct in-memory reduction."""
    red = own(key)
    M = matrices(lean_export2.certificate(red, "Own.X"))
    n, k = red.n, red.Vi.shape[1]
    assert M["Vi"] * M["Wu"] + M["Vn"] * M["Wd"] == sp.eye(n)
    assert M["A"] * M["Vn"] == sp.zeros(red.r, n - k)
    assert M["G"] * (M["A"] * M["Vi"]) == red.d * sp.eye(k)
    assert M["Dfull"] * M["Pfull"] == sp.zeros(red.r, n + 1 - red.r)
    assert M["V1full"] * M["W1full"] + M["Pfull"] * M["W2full"] == sp.eye(n + 1)
    assert M["Afull"] * M["Kmat"] == sp.zeros(red.r, M["Kmat"].shape[1])


TERM = re.compile(r"⟨\(?(-?\d+)(?: / (\d+))?\)?, !\[([-\d, ]+)\]⟩")


@pytest.mark.parametrize("key", POLYNOMIAL)
def test_symmetry_can_be_rechecked_from_the_lean_text(key):
    """Parse `sys`, `A`, `tau` back out of the Lean file and redo Lean's symmetry check by hand."""
    red = own(key)
    text = lean_export2.certificate(red, "Own.X")
    block = text[text.index("terms := !["):text.index("theorem eq_")]
    rows = [ln for ln in block.splitlines() if ln.strip().startswith(("terms", "["))]
    assert len(rows) == red.n
    A = matrices(text)["A"]
    tau = [int(x) for x in re.search(r"def tau .*?!\[([-\d, ]+)\]", text).group(1).split(",")]
    seen = 0
    for i, row in enumerate(rows):
        for num, den, exps in TERM.findall(row):
            e = sp.Matrix([int(x) for x in exps.split(",")])
            assert [(A * e)[j] + tau[j] for j in range(red.r)] == [A[j, i] for j in range(red.r)]
            seen += 1
    assert seen == sum(len(ts) for ts in red.terms())


def test_exporting_is_deterministic():
    assert lean_export2.certificate(own("lotka_volterra"), "Own.X") == lean_export2.certificate(own("lotka_volterra"), "Own.X")


@pytest.mark.parametrize("key", GENERAL)
def test_own_certificates_on_disk_are_up_to_date(key):
    red = own(key)
    name = _camel(red.model.name)
    on_disk = (LEAN / "NondimVerify" / "Certified" / "Own" / f"{name}.lean").read_text()
    assert on_disk == own_text(key, f"Own.{name}")


def test_certify_general_writes_files_and_an_index(tmp_path):
    done = certify_general(tmp_path / "NondimVerify", quiet=True, use_desr=False)
    assert len(done["Own"]) == len(GENERAL) and done["Desr"] == []
    index = (tmp_path / "NondimVerify" / "Certified.lean").read_text()
    for name in done["Own"]:
        assert (tmp_path / "NondimVerify" / "Certified" / "Own" / f"{name}.lean").exists()
        assert f"import NondimVerify.Certified.Own.{name}" in index


def test_the_library_index_imports_the_general_theory():
    top = (LEAN / "NondimVerify.lean").read_text()
    for mod in ["System", "Criterion", "BuckinghamPi", "Reduction", "Rational", "Identifiability", "Certified"]:
        assert f"import NondimVerify.{mod}" in top
    tests = (LEAN / "NondimVerifyTest.lean").read_text()
    for mod in ["System", "Criterion", "BuckinghamPi", "Reduction", "Rational", "Identifiability", "Limits"]:
        assert f"import NondimVerifyTest.{mod}" in tests

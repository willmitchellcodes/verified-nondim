"""The Python -> Lean bridge, checked WITH Lean (skipped when `lake` is missing).

Two directions:
  * soundness of the pipeline: everything the solver exports is accepted by Lean;
  * the checker has teeth: a certificate corrupted in any one place is REJECTED.
A checker that accepts everything would pass the first test, so the second matters more.
"""
import re
import subprocess

import pytest

from conftest import LEAN
from nondim.report import build
from nondim.lean_export import certificate

pytestmark = [pytest.mark.lean, pytest.mark.slow]


def lean_accepts(lake, text: str, tmp_name: str) -> tuple[bool, str]:
    path = LEAN / f"_tmp_{tmp_name}.lean"
    path.write_text(text)
    try:
        p = subprocess.run([lake, "env", "lean", path.name], cwd=LEAN, capture_output=True, text=True, timeout=900)
        return p.returncode == 0 and "error" not in p.stdout, p.stdout + p.stderr
    finally:
        path.unlink(missing_ok=True)


def test_lake_build_passes(lake):
    p = subprocess.run([lake, "build"], cwd=LEAN, capture_output=True, text=True, timeout=3600)
    assert p.returncode == 0, p.stdout[-3000:] + p.stderr[-3000:]


def test_no_sorry_outside_the_exercises(lake):
    for f in (LEAN / "NondimVerify").rglob("*.lean"):
        if f.name != "Exercises.lean":
            assert "sorry" not in f.read_text(), f


def _sir():
    _, _, nd, results = build("sir")
    return certificate(nd, results, module="Mutant")


def _replace_once(text, pattern, repl):
    new, n = re.subn(pattern, repl, text, count=1, flags=re.S)
    assert n == 1, f"mutation pattern not found: {pattern}"
    return new


MUTATIONS = {
    # name: (regex, replacement) applied to the SIR certificate
    "scaling_that_is_not_a_symmetry": (r"(def Amat .*?!!\[)0, -1", r"\g<1>0, 1"),
    "wrong_exponent_matrix_entry": (r"(def Kmat .*?!!\[)1, 1, 1", r"\g<1>1, 1, 2"),
    "overclaimed_rank_of_K": (r"Kmat\.rank = 5", "Kmat.rank = 6"),
    "underclaimed_rank_of_K": (r"Kmat\.rank = 5", "Kmat.rank = 4"),
    "claims_three_removable": (r"Apar\.rank = 2", "Apar.rank = 3"),
    "new_variable_with_units": (r"(def Vmat .*?!!\[)1, 0, 0, 0, 0", r"\g<1>1, 1, 0, 0, 0"),
    "wrong_parameter_columns": (r"Amat\.submatrix id !\[4, 5, 6\]", "Amat.submatrix id ![3, 5, 6]"),
    "wrong_sign_in_reduced_equation": (r"(theorem rhs_S.*?=\n    \()\(-1\) \* ", r"\g<1>"),
    "dropped_factor_in_reduced_equation": (r"(theorem rhs_I.*?=\n.*?)S \* beta", r"\g<1>S"),
    "unsat_constraint_claimed_sat": (r"theorem constraint2_unsat : 3 > ", "theorem constraint2_unsat : 3 ≤ "),
    "group_with_units_claimed_invariant": (r"theorem constraint5_want_not_invariant : Amat \* Wmat5 ≠ 0",
                                           "theorem constraint5_want_not_invariant : Amat * Wmat5 = 0"),
    "non_invertible_change_of_variables": (r"(def Tmat .*?)0, -1, -1, -1, 1, 0, 1\]", r"\g<1>0, 0, 0, 0, 0, 0, 0]"),
}


def test_unmutated_certificate_is_accepted(lake):
    ok, log = lean_accepts(lake, _sir(), "control")
    assert ok, log[-3000:]


@pytest.mark.parametrize("name", list(MUTATIONS))
def test_corrupted_certificate_is_rejected(lake, name):
    pattern, repl = MUTATIONS[name]
    ok, log = lean_accepts(lake, _replace_once(_sir(), pattern, repl), name)
    assert not ok, f"Lean ACCEPTED a certificate with the defect '{name}'"
    assert "error" in log


def test_mutations_really_change_the_certificate():
    base = _sir()
    for name, (pattern, repl) in MUTATIONS.items():
        assert _replace_once(base, pattern, repl) != base, name


def test_lean_test_library_builds(lake):
    p = subprocess.run([lake, "build", "NondimVerifyTest"], cwd=LEAN, capture_output=True, text=True, timeout=3600)
    assert p.returncode == 0, p.stdout[-3000:] + p.stderr[-3000:]


# ----------------------------------------------------------------- certificates in the general form

def _general_sir():
    from nondim import lean_export2, models
    from nondim.hlform import from_nondim
    from nondim.scaling import nondimensionalize
    return lean_export2.certificate(from_nondim(nondimensionalize(models.sir_no_population())), "Mutant2")


GENERAL_MUTATIONS = {
    # name: (regex, replacement) applied to the general-form certificate of SIR (variables S, I, beta, gamma)
    "data_is_not_the_equation_exponent": (r"(terms := !\[\[⟨\(-1\), !\[1, 1, 1), 0\]", r"\g<1>, 1]"),
    "data_is_not_the_equation_coefficient": (r"⟨1, !\[1, 1, 1, 0\]⟩", "⟨2, ![1, 1, 1, 0]⟩"),
    "data_drops_a_term": (r"\[⟨\(-1\), !\[0, 1, 0, 1\]⟩, ", "["),
    "scaling_that_is_not_a_symmetry": (r"(def A .*?!!\[)-1, -1, 1, 0", r"\g<1>-1, -1, 2, 0"),
    "wrong_time_weight": (r"def tau : Fin 2 → ℤ := !\[0, -1\]", "def tau : Fin 2 → ℤ := ![0, 1]"),
    "new_variable_with_units": (r"(def Vn .*?!!\[)1, 0;", r"\g<1>1, 1;"),
    "inverse_is_not_the_inverse": (r"(def Wd .*?!!\[)1, 0, 0, 0", r"\g<1>1, 0, 1, 0"),
    "auxiliaries_not_free": (r"(def G .*?!!\[)1, 0;", r"\g<1>0, 0;"),
    "auxiliary_monomial_uses_a_state": (r"(def Vi .*?!!\[)0, 0;", r"\g<1>1, 0;"),
    "wrong_time_factor": (r"def w : Fin 4 → ℤ := !\[0, 0, 0, 1\]", "def w : Fin 4 → ℤ := ![0, 0, 1, 0]"),
    "time_factor_uses_a_state": (r"def w : Fin 4 → ℤ := !\[0, 0, 0, 1\]", "def w : Fin 4 → ℤ := ![1, 0, 0, 1]"),
    "factor_of_new_variable_uses_a_state": (r"def u_S : Fin 4 → ℤ := !\[0, 0, 1, -1\]",
                                            "def u_S : Fin 4 → ℤ := ![0, 1, 1, -1]"),
    "wrong_sign_in_reduced_equation": (r"(def red_S .*?:= \()\(-1\) \* ", r"\g<1>"),
    "dropped_term_in_reduced_equation": (r"(def red_I .*?:= \(\(π 1\) \* )\(\(-1\) \+ \(π 0\)\)", r"\g<1>(π 0)"),
    "wrong_new_variable_for_a_state": (r"\(fun i => Vn i 0\) = u_S", "(fun i => Vn i 1) = u_S"),
    "pi_groups_incomplete_certificate": (r"(def Pfull .*?!!\[)1, 0, 0;", r"\g<1>1, 0, 1;"),
    "overclaimed_rank_of_K": (r"Kmat\.rank = 3", "Kmat.rank = 4"),
    "overclaimed_number_of_scalings": (r"Afull\.rank = 2", "Afull.rank = 3"),
}


def test_unmutated_general_certificate_is_accepted(lake):
    ok, log = lean_accepts(lake, _general_sir(), "control2")
    assert ok, log[-3000:]


@pytest.mark.parametrize("name", list(GENERAL_MUTATIONS))
def test_corrupted_general_certificate_is_rejected(lake, name):
    pattern, repl = GENERAL_MUTATIONS[name]
    ok, log = lean_accepts(lake, _replace_once(_general_sir(), pattern, repl), "g_" + name)
    assert not ok, f"Lean ACCEPTED a general-form certificate with the defect '{name}'"
    assert "error" in log


def test_general_mutations_really_change_the_certificate():
    base = _general_sir()
    for name, (pattern, repl) in GENERAL_MUTATIONS.items():
        assert _replace_once(base, pattern, repl) != base, name


EDGE_MODELS = {
    "negative_exponent": ({"x": "a - b*x/y", "y": "c - d*y"}, "a b c d"),
    "fractional_coefficients": ({"x": "a*x/2 - b*x**2/3"}, "a b"),
    "one_scaling_only": ({"x": "a - x"}, "a"),
    "higher_powers": ({"x": "a*x**2*y - b*x", "y": "c*y - d*x**2*y**2"}, "a b c d"),
    "cubic_one_state": ({"x": "a*x**2 - b*x**3"}, "a b"),
}


def test_edge_models_are_accepted_in_the_general_form(lake):
    """Boundary inputs of the exporter: Laurent terms, rational coefficients, a single scaling,
    higher powers. Each must produce a certificate Lean accepts."""
    from nondim import lean_export2
    from nondim.hlform import from_nondim
    from nondim.model import Model
    from nondim.scaling import nondimensionalize

    parts = ["import NondimVerify.Reduction\nimport NondimVerify.Theory"]
    for name, (eqs, params) in EDGE_MODELS.items():
        red = from_nondim(nondimensionalize(Model.from_strings(name, eqs, params)))
        text = lean_export2.certificate(red, f"Edge.{name}")
        parts.append(text.replace("import NondimVerify.Reduction\nimport NondimVerify.Theory\n", "", 1))
    ok, log = lean_accepts(lake, "\n".join(parts), "edge")
    assert ok, log[-4000:]


def test_desr_on_models_nobody_hand_picked_is_accepted(lake):
    """desr's answers for random models (and for the model whose invariants are not the
    cross-section coordinates) become certificates Lean accepts."""
    from nondim.desr_bridge import desr_available
    if not desr_available():
        pytest.skip("desr is not installed")
    import random

    from nondim import lean_export2
    from nondim.desr_bridge import from_desr
    from nondim.hlform import NotSupported
    from nondim.model import Model
    from test_desr_bridge import SKEW, _random_model

    reds = [from_desr(Model.from_strings("Skew", **SKEW))]
    rng = random.Random(7)
    for idx in range(200):
        if len(reds) >= 9:
            break
        try:
            reds.append(from_desr(_random_model(rng, idx)))
        except NotSupported:
            pass
    assert len(reds) >= 9
    parts = ["import NondimVerify.Reduction\nimport NondimVerify.Theory"]
    for i, red in enumerate(reds):
        text = lean_export2.certificate(red, f"Rand.M{i}")
        parts.append(text.replace("import NondimVerify.Reduction\nimport NondimVerify.Theory\n", "", 1))
    ok, log = lean_accepts(lake, "\n".join(parts), "random_desr")
    assert ok, log[-4000:]


def test_a_wrong_answer_attributed_to_desr_is_rejected(lake):
    """Simulate a bug in desr: take its real certificate and change one reduced equation."""
    from nondim.desr_bridge import desr_available
    if not desr_available():
        pytest.skip("desr is not installed")
    from nondim import lean_export2, models
    from nondim.desr_bridge import from_desr

    good = lean_export2.certificate(from_desr(models.lotka_volterra()), "DesrMutant")
    ok, log = lean_accepts(lake, good, "desr_control")
    assert ok, log[-3000:]
    bad = _replace_once(good, r"(def red_y .*?):= (.*?)\n", r"\g<1>:= (\g<2> + 1)\n")
    ok, log = lean_accepts(lake, bad, "desr_mutant")
    assert not ok, "Lean ACCEPTED a wrong reduced equation"
    assert "unsolved goals" in log  # the algebraic identity for y no longer holds


KEY_THEOREMS = [
    # the general theory
    "NondimVerify.LaurentSystem.IsSymmetry.map_solution", "NondimVerify.LaurentSystem.IsSymmetry.solution_iff",
    "NondimVerify.LaurentSystem.IsSolution.param_const", "NondimVerify.exists_normalizing_scaling",
    "NondimVerify.not_normalizable_of_kernel_vector", "NondimVerify.left_inverse_or_kernel",
    "NondimVerify.normalizable_iff", "NondimVerify.normalizable_iff_rank",
    "NondimVerify.LaurentSystem.IsSymmetry.nondimensionalize",
    "NondimVerify.buckingham_pi", "NondimVerify.buckingham_pi_factorization",
    "NondimVerify.spans_kernel_of_certificate", "NondimVerify.finrank_dimensionless",
    "NondimVerify.eq_reconstruct_of_section", "NondimVerify.LaurentSystem.IsSymmetry.reduction",
    "NondimVerify.LaurentSystem.IsSymmetry.reduction_of_parameters",
    "NondimVerify.LaurentSystem.IsSolution.hasDerivAt_newVariable",
    # certificates in the general form
    "NondimVerify.Certified.Own.SIRNoN.reduction_correct", "NondimVerify.Certified.Own.LotkaVolterra.cross_section",
    "NondimVerify.Certified.Desr.SIRNoN.reduction_correct", "NondimVerify.Certified.Desr.LotkaVolterra.reduction_correct",
    "NondimVerify.Certified.Desr.MichaelisMenten.invariants_complete",
    "NondimVerifyTest.BuckinghamPi.mass_is_irrelevant", "NondimVerifyTest.Limits.doubled_not_solution",
    # the first release
    "NondimVerify.monomial_scale", "NondimVerify.finrank_scalingSpace", "NondimVerify.maximal_of_rank",
    "NondimVerify.SIR.trajectory_forward", "NondimVerify.SIR.trajectory_backward",
    "NondimVerify.SIR.equilibrium_iff", "NondimVerify.SIR.threshold",
    "NondimVerify.Cert.SIR.symmetries", "NondimVerify.Cert.SIR.rank_K", "NondimVerify.Cert.SIR.rhs_I",
    "NondimVerify.Cert.SIR.constraint2_unsat", "NondimVerify.Cert.RosenzweigMacArthur.rhs_N",
]


def test_key_theorems_do_not_depend_on_sorry(lake):
    """`#print axioms` lists what each proof ultimately rests on; `sorryAx` must not appear."""
    src = "import NondimVerify\nimport NondimVerifyTest\n" + "\n".join(f"#print axioms {t}" for t in KEY_THEOREMS) + "\n"
    ok, log = lean_accepts(lake, src, "axioms")
    assert ok, log[-3000:]
    assert "sorryAx" not in log
    # nothing beyond Lean's three standard axioms
    used = set(re.findall(r"\[([^\]]*)\]", log.replace("\n", " ")))
    names = {a.strip() for group in used for a in group.split(",") if a.strip()}
    assert names <= {"propext", "Classical.choice", "Quot.sound"}, names
    assert log.count("depends on axioms") + log.count("does not depend on any axioms") == len(KEY_THEOREMS)


def test_every_choice_of_every_model_is_accepted(lake):
    """Robustness of the bridge: not only the catalog's choices but every maximal
    nondimensionalization of every built-in model yields a certificate Lean accepts."""
    from nondim import models
    from nondim.scaling import all_nondimensionalizations

    parts, count = ["import NondimVerify.Basic"], 0
    for key, make in models.ALL.items():
        for i, nd in enumerate(all_nondimensionalizations(make())):
            if nd.analysis.A.shape[0] and nd.normalized:
                text = certificate(nd, module=f"All.M{count}")
                parts.append(text.replace("import NondimVerify.Basic\n", "", 1))
                count += 1
    assert count >= 30
    ok, log = lean_accepts(lake, "\n".join(parts), "all_choices")
    assert ok, log[-4000:]

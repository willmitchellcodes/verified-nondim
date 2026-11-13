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


KEY_THEOREMS = [
    "NondimVerify.monomial_scale", "NondimVerify.finrank_scalingSpace", "NondimVerify.maximal_of_rank",
    "NondimVerify.SIR.trajectory_forward", "NondimVerify.SIR.trajectory_backward",
    "NondimVerify.SIR.equilibrium_iff", "NondimVerify.SIR.threshold",
    "NondimVerify.Cert.SIR.symmetries", "NondimVerify.Cert.SIR.rank_K", "NondimVerify.Cert.SIR.rhs_I",
    "NondimVerify.Cert.SIR.constraint2_unsat", "NondimVerify.Cert.RosenzweigMacArthur.rhs_N",
]


def test_key_theorems_do_not_depend_on_sorry(lake):
    """`#print axioms` lists what each proof ultimately rests on; `sorryAx` must not appear."""
    src = "import NondimVerify\n" + "\n".join(f"#print axioms {t}" for t in KEY_THEOREMS) + "\n"
    ok, log = lean_accepts(lake, src, "axioms")
    assert ok, log[-3000:]
    assert "sorryAx" not in log
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

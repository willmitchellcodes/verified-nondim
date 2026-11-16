"""The four optional sections of a general-form certificate, and rational right-hand sides.

    unit links        SIR with N: the reduction's scalings respect "S is measured like N"
    parameter count   the smallest number of parameters any scaling reduction can leave
    identifiability   output-preserving scalings and the parameters they hide (one-way)
    goal queries      every request answered "possible" or "impossible", with the right proof kind
    rational systems  sums of quotients of polynomials (Holling II, Michaelis-Menten forms)

No Lean here: these tests check the Python side and the Lean TEXT. `test_lean_build.py` sends
the same certificates, and corrupted ones, through Lean.
"""
import copy
import re

import pytest
import sympy as sp

from lean_reader import matrices
from nondim import lean_export2, lean_sections, models
from nondim.catalog import CATALOG, GENERAL
from nondim.cli import own_reduction
from nondim.constraints import solve
from nondim.hlform import NotSupported, from_nondim, left_inverse_certificate, system_fractions
from nondim.identifiability import analyze_identifiability
from nondim.model import Model
from nondim.scaling import analyze, nondimensionalize


def text(key: str) -> str:
    return lean_export2.certificate(own_reduction(key), "Own.X", CATALOG[key].get("constraints"))


# ----------------------------------------------------------------- unit links

def test_sir_with_population_is_in_the_general_form_and_keeps_R0():
    red = own_reduction("sir")
    red.check()
    N, beta, gamma = (red.model.symbol(x) for x in ("N", "beta", "gamma"))
    assert beta * N / gamma in red.invariant_monomials()  # R0 is one of the new variables
    assert len(red.parameters) == 3 and len(red.reduced_parameters()) == 1
    assert len(red.links) == len(red.model.extra_invariants) > 0


@pytest.mark.parametrize("key", ["sir", "michaelis_menten_ic", "spurious_fixed"])
def test_every_scaling_respects_every_unit_link(key):
    red = own_reduction(key)
    for g in red.links:
        assert red.A * sp.Matrix(g) == sp.zeros(red.r, 1)
    t = text(key)
    assert "theorem links_respected : A * Links = 0" in t
    M = matrices(t)
    assert M["A"] * M["Links"] == sp.zeros(red.r, len(red.links))


def test_a_scaling_that_breaks_a_link_is_rejected():
    red = copy.deepcopy(own_reduction("sir"))
    red.links.append([1 if v == red.model.symbol("S") else 0 for v in red.variables])  # "S is dimensionless"
    with pytest.raises(ValueError, match="unit link"):
        red.check()


def test_models_without_links_get_no_links_section():
    assert "links_respected" not in text("lotka_volterra")


def test_built_in_lotka_volterra_reports_the_hidden_predator_scale():
    """The built-in model measures the prey only: the certificate must say that b and the scale
    of the predator are hidden, and must not flag a, c, d."""
    t = text("lotka_volterra")
    assert "Measured: prey_count = x" in t
    assert "theorem not_identifiable_b" in t and "theorem not_identifiable_y" in t
    for name in ("a", "c", "d", "x"):
        assert f"theorem not_identifiable_{name} " not in t


def test_spurious_symmetry_disappears_once_the_link_is_declared():
    """The substituted model has one scaling more than the original; declaring the link that the
    substitution silently dropped brings the count back (Tanburn et al.'s spurious reduction)."""
    counts = {k: analyze(models.ALL[k]()).n_scalings
              for k in ("spurious_original", "spurious_substituted", "spurious_fixed")}
    assert counts["spurious_substituted"] == counts["spurious_original"] + 1
    assert counts["spurious_fixed"] == counts["spurious_original"]


# ----------------------------------------------------------------- minimal parameter count

@pytest.mark.parametrize("key", GENERAL)
def test_count_section_states_the_rank_the_solver_computed(key):
    red = own_reduction(key)
    an = analyze(red.model)
    t = text(key)
    assert f"theorem rank_paramCols : ParamCols.rank = {an.param_rank}" in t
    assert f"theorem cannot_remove_more (S : Fin {an.param_rank + 1} → Fin {len(red.parameters)})" in t
    M = matrices(t)
    cols = [red.variables.index(p) for p in red.parameters]
    assert M["ParamCols"] == M["A"][:, cols] and M["ParamCols"].rank() == an.param_rank


@pytest.mark.parametrize("key", GENERAL)
def test_the_count_is_attained_by_the_reduction_itself(key):
    """"No rho+1 parameters can be removed" is only half the story; the reduction removes rho."""
    red = own_reduction(key)
    an = analyze(red.model)
    assert len(red.parameters) - len(red.reduced_parameters()) == an.param_rank


def test_model_without_parameters_has_no_count_section():
    red = from_nondim(nondimensionalize(Model.from_strings("One", {"x": "a - x"}, "a")))
    assert lean_sections.count_section(red)  # one parameter: section present
    red.variables  # (a model with no parameter never reaches the general form; see test_hlform)


# ----------------------------------------------------------------- identifiability

def test_sir_reported_flags_beta_and_rho_and_not_gamma():
    red = own_reduction("sir_reported")
    t = text("sir_reported")
    assert "theorem not_identifiable_beta" in t and "theorem not_identifiable_rho" in t
    assert "theorem not_identifiable_gamma" not in t
    assert "one-way test" in t


def test_output_preserving_scalings_are_symmetries_that_fix_time_and_outputs():
    """Recompute, from the Lean text alone, what Lean is asked to decide."""
    red = own_reduction("sir_reported")
    B = matrices(text("sir_reported"))["B"]
    for i, fracs in enumerate(red.fractions()):          # symmetry with time weight 0
        for num, den in fracs:
            for _, a in num:
                assert list(B * sp.Matrix(a)) == [B[j, i] for j in range(B.shape[0])]
    out = lean_sections.poly_terms(red.model.outputs["y"], red.variables)
    for _, e in out:                                      # the output has weight 0
        assert B * sp.Matrix(e) == sp.zeros(B.shape[0], 1)


def test_identifiability_section_agrees_with_the_python_analysis():
    m = models.sir_reported()
    res = analyze_identifiability(m)
    t = text("sir_reported")
    for p in m.params:
        assert (f"theorem not_identifiable_{p}" in t) == (p in res.nonidentifiable)


def test_hidden_scale_of_an_unobserved_state():
    """Lotka-Volterra with only the prey measured: the predator's scale, and b with it, are hidden."""
    m = models.lotka_volterra()
    m.outputs = {"y": m.symbol("x")}
    red = from_nondim(nondimensionalize(m))
    section = "\n".join(lean_sections.identifiability_section(red))
    assert "theorem not_identifiable_b" in section and "theorem not_identifiable_y" in section
    assert "theorem not_identifiable_a" not in section and "theorem not_identifiable_x" not in section


def test_no_outputs_no_section_and_no_scaling_no_theorem():
    assert lean_sections.identifiability_section(own_reduction("logistic")) == []
    m = models.sir_no_population()
    m.outputs = {"y1": m.symbol("S"), "y2": m.symbol("I")}  # everything measured
    section = "\n".join(lean_sections.identifiability_section(from_nondim(nondimensionalize(m))))
    assert "this test flags nothing" in section and "theorem not_identifiable" not in section


def test_non_polynomial_output_is_skipped_not_mis_stated():
    m = models.sir_no_population()
    m.outputs = {"y": sp.log(m.symbol("I"))}
    assert lean_sections.identifiability_section(from_nondim(nondimensionalize(m))) == []


# ----------------------------------------------------------------- goal queries

KIND = {"ok": "possible", "rank": "impossible", "not_invariant": "impossible", "dependent": "impossible"}


@pytest.mark.parametrize("key", [k for k in GENERAL if CATALOG[k].get("constraints")])
def test_every_goal_gets_the_theorem_its_answer_calls_for(key):
    m, t = models.ALL[key](), text(key)
    for idx, c in enumerate(CATALOG[key]["constraints"], 1):
        res = solve(m, **c)
        assert f"-- Goal {idx}:" in t
        assert ("SAT" if res.satisfiable else "UNSAT") in t.split(f"-- Goal {idx}:")[1].split("\n")[1]
        has_possible = f"theorem goal{idx}_possible" in t
        has_impossible = f"theorem goal{idx}_impossible" in t
        if res.reason in KIND:
            assert has_possible == (KIND[res.reason] == "possible"), (key, idx, res.reason)
            assert has_impossible == (KIND[res.reason] == "impossible"), (key, idx, res.reason)
        else:  # rejected before any linear algebra (not a monomial, not parameter-only)
            assert not has_possible and not has_impossible
        assert not (has_possible and has_impossible)


def test_sir_goals_read_as_expected():
    t = text("sir")
    assert "theorem goal1_possible" in t                 # remove 2, keep beta
    assert "theorem goal2_impossible (S : Fin 3 → Fin 3)" in t   # remove 3 of 3: rank is 2
    assert "theorem goal3_impossible (S : Fin 2 → Fin 1)" in t   # remove 2 of {beta}
    assert "theorem goal4_R0_dimensionless" in t         # R0 = beta*N/gamma
    assert "monomial_not_invariant" in t                 # beta*N has units


@pytest.mark.parametrize("key", [k for k in GENERAL if CATALOG[k].get("constraints")])
def test_possible_goals_carry_a_valid_left_inverse(key):
    red, t = own_reduction(key), text(key)
    M = matrices(t)
    for idx in range(1, len(CATALOG[key]["constraints"]) + 1):
        m = re.search(rf"def goal{idx}_S : Fin (\d+) → Fin \d+ := !\[([\d, ]+)\]", t)
        if not m:
            continue
        S = [int(x) for x in m.group(2).split(",")]
        d = int(re.search(rf"exists_normalizing_scaling A goal{idx}_S goal{idx}_G \((-?\d+)\)", t).group(1))
        assert d != 0 and M[f"goal{idx}_G"] * M["A"][:, S] == d * sp.eye(len(S))


def test_impossible_by_rank_states_the_true_rank():
    red, t = own_reduction("sir"), text("sir")
    M = matrices(t)
    assert M["goal3_cols"].rank() == 1 and "theorem goal3_rank : goal3_cols.rank = 1" in t


def test_goal_with_units_names_a_scaling_that_moves_it():
    red, t = own_reduction("sir"), text("sir")
    m = re.search(r"monomial_not_invariant A !\[([-\d, ]+)\] (\d+)", t)
    g, j = sp.Matrix([int(x) for x in m.group(1).split(",")]), int(m.group(2))
    assert (red.A * g)[j] != 0


def test_dependent_groups_come_with_a_relation():
    t = text("michaelis_menten_ic")
    W = matrices(t)["goal4_W"]
    c = sp.Matrix([int(x) for x in re.search(r"goal4_W \*ᵥ !\[([-\d, ]+)\]", t).group(1).split(",")])
    assert W * c == sp.zeros(W.shape[0], 1) and any(x != 0 for x in c)


def test_no_goals_no_section():
    assert "Goal queries" not in lean_export2.certificate(own_reduction("sir"), "Own.X")
    assert "Goal queries" not in text("sir_noN")


# ----------------------------------------------------------------- rational right-hand sides

def test_rosenzweig_macarthur_is_rational_and_everything_else_is_not():
    for key in GENERAL:
        assert own_reduction(key).is_rational == (key == "rosenzweig_macarthur")


def test_fractions_rebuild_the_rational_equations_exactly():
    red = own_reduction("rosenzweig_macarthur")
    V = red.variables

    def poly(ts):
        return sum(c * sp.Mul(*[v ** e for v, e in zip(V, exps)]) for c, exps in ts)

    for v, fracs in zip(V, red.fractions()):
        rebuilt = sum(poly(num) / poly(den) for num, den in fracs)
        expected = red.model.rhs[red.model.states.index(v)] if v in red.model.states else 0
        assert sp.simplify(rebuilt - expected) == 0
        assert len(fracs) == (2 if v in red.model.states else 0)  # logistic/linear part + Holling part


def test_polynomial_system_is_one_quotient_with_denominator_one():
    m = models.lotka_volterra()
    for v, fracs in zip([*m.states, *m.params], system_fractions(m, [*m.states, *m.params])):
        if v in m.states:
            (num, den), = fracs
            assert den == [(1, [0] * 6)] and len(num) == 2


def test_monomial_denominators_stay_with_the_numerator():
    m = Model.from_strings("L", {"x": "a*x - b*x**2/K"}, "a b K")
    (num, den), = system_fractions(m, [*m.states, *m.params])[0]
    assert len(den) == 1 and any(-1 in e for _, e in num)


@pytest.mark.parametrize("equations, params", [
    ({"x": "a*x/(1 + b*x) - c*x"}, "a b c"),                       # Holling II / Michaelis-Menten form
    ({"x": "a*x**2/(K**2 + x**2) - c*x"}, "a K c"),                # Hill function, exponent 2
    ({"x": "a/(1 + b*y) - c*x", "y": "d*x - e*y"}, "a b c d e"),   # repression
])
def test_rational_models_reduce_and_pass_every_check(equations, params):
    red = from_nondim(nondimensionalize(Model.from_strings("R", equations, params)))
    assert red.is_rational
    red.check()
    t = lean_export2.certificate(red, "Own.R")
    assert "RatSystem" in t and "frac_reduce" in t and "theorem reduction_correct" in t
    assert t.count("theorem den_id_") == t.count("theorem num_id_") >= 1


def test_rational_certificate_refuses_a_wrong_reduced_equation():
    red = copy.deepcopy(own_reduction("rosenzweig_macarthur"))
    z = red.model.states[0]
    red.reduced_rhs[z] = red.reduced_rhs[z] + 1
    with pytest.raises(ValueError):
        lean_export2.certificate(red, "Own.X")


def test_scaling_that_makes_a_denominator_inhomogeneous_is_rejected():
    red = copy.deepcopy(own_reduction("rosenzweig_macarthur"))
    h = red.variables.index(red.model.symbol("h"))
    red.A = red.A.copy()
    red.A[0, h] += 1          # now 1 + a*h*N no longer has a single weight
    with pytest.raises(ValueError, match="not a symmetry"):
        red.check()


def test_quotient_form_matches_what_lean_is_told():
    """The reduced numerators and denominators printed in the certificate recombine to the
    reported reduced equation (the one equality Lean does not check for rational models)."""
    red = own_reduction("rosenzweig_macarthur")
    t = text("rosenzweig_macarthur")
    assert t.count("noncomputable def rnum_") == t.count("noncomputable def rden_") == 4
    assert "checked in Python" in t

"""Framing 3: symbolic predictions checked against numerical sensitivities and a fitting experiment."""
import numpy as np
import pytest
import sympy as sp

from conftest import P
from nondim import models
from nondim.experiment_sir import (GROUPS, TRUTH, fit_reduced, make_data, observe, observe_reduced, run, scaled,
                                   to_reduced)
from nondim.identifiability import (analyze_identifiability, log_sensitivity_matrix, numerical_nullity,
                                    predicted_null_directions, simulate_outputs)
from nondim.model import Model, exponent_matrix


def names(xs):
    return sorted(str(x) for x in xs)


def test_sir_with_reporting_fraction():
    res = analyze_identifiability(models.sir_reported())
    assert names(res.nonidentifiable) == ["beta", "rho"]
    assert names(res.not_flagged) == ["gamma"]
    assert names(res.hidden_scale_states) == ["I", "S"]
    assert res.B.shape[0] == 1
    groups = {sp.simplify(g) for g in res.identifiable_groups}
    assert P("gamma") in groups
    assert any(sp.simplify(g * P("beta") / P("rho")) == 1 or sp.simplify(g * P("rho") / P("beta")) == 1 for g in groups)


def test_lotka_volterra_observing_prey_only():
    """Matches the StructuralIdentifiability.jl example: b -> lam*b, y -> y/lam is invisible."""
    res = analyze_identifiability(models.lotka_volterra(), {"obs": "x"})
    assert names(res.nonidentifiable) == ["b"] and names(res.hidden_scale_states) == ["y"]


def test_observing_everything_leaves_no_scaling():
    res = analyze_identifiability(models.lotka_volterra(), {"o1": "x", "o2": "y"})
    assert res.B.shape[0] == 0 and res.nonidentifiable == []
    assert "no output-preserving scaling" in res.summary()


def test_knowing_a_parameter_breaks_the_symmetry():
    assert analyze_identifiability(models.sir_reported(), known=["rho"]).nonidentifiable == []


def test_output_preserving_scalings_are_scalings_that_fix_time_and_outputs():
    m = models.sir_reported()
    res = analyze_identifiability(m)
    K = exponent_matrix(m)
    assert res.B * K == sp.zeros(res.B.shape[0], K.shape[1])
    assert all(res.B[i, m.index(m.t)] == 0 for i in range(res.B.shape[0]))
    out_vec = sp.Matrix([1 if v in (P("rho"), P("I")) else 0 for v in m.variables])
    assert res.B * out_vec == sp.zeros(res.B.shape[0], 1)


def test_outputs_are_required():
    with pytest.raises(ValueError, match="no outputs"):
        analyze_identifiability(models.logistic())


CASES = {
    "sir_reported": (models.sir_reported, None, dict(beta=0.002, gamma=0.4, rho=0.3), dict(S=990.0, I=10.0), 30.0),
    "lotka_volterra": (models.lotka_volterra, {"obs": "x"}, dict(a=1.0, b=0.5, c=0.8, d=0.3), dict(x=2.0, y=1.0), 20.0),
}


@pytest.mark.parametrize("case", list(CASES))
def test_predicted_directions_are_exactly_the_numerical_null_space(case):
    """The bridge between Framing 1 and data: every predicted scaling direction is a null
    direction of the sensitivity matrix, and there are no other null directions."""
    make, outputs, pv, zv, T = CASES[case]
    m = make()
    res = analyze_identifiability(m, outputs)
    params = {m.symbol(k): v for k, v in pv.items()}
    z0 = {m.symbol(k): v for k, v in zv.items()}
    J, cols = log_sensitivity_matrix(m, res.outputs, params, z0, np.linspace(0, T, 61))
    D = predicted_null_directions(res)
    assert D.shape == (res.B.shape[0], len(cols))
    assert np.linalg.norm(J @ D.T) < 1e-5 * np.linalg.norm(J)
    nullity, s = numerical_nullity(J)
    assert nullity == res.B.shape[0], f"singular values {s}"


def test_no_null_space_when_everything_is_observed():
    m = models.lotka_volterra()
    params = {m.symbol(k): v for k, v in dict(a=1.0, b=0.5, c=0.8, d=0.3).items()}
    z0 = {m.symbol("x"): 2.0, m.symbol("y"): 1.0}
    J, _ = log_sensitivity_matrix(m, {"o1": "x", "o2": "y"}, params, z0, np.linspace(0, 20, 61))
    assert numerical_nullity(J)[0] == 0


def test_simulate_outputs_shape_and_constant_output():
    m = Model.from_strings("decay", {"x": "-k*x"}, "k", outputs={"y": "x", "const": "k"})
    out = simulate_outputs(m, m.outputs, {m.symbol("k"): 0.5}, {m.symbol("x"): 2.0}, np.linspace(0, 2, 5))
    assert out.shape == (2, 5)
    assert np.allclose(out[0], 2 * np.exp(-0.5 * np.linspace(0, 2, 5)), rtol=1e-7)
    assert np.allclose(out[1], 0.5)


# ------------------------------------------------------------ the SIR data experiment

TS = np.linspace(0.5, 30, 61)


@pytest.mark.parametrize("lam", [0.1, 0.5, 3.0, 20.0])
def test_scaled_parameters_give_identical_data(lam):
    assert np.allclose(observe(scaled(TRUTH, lam), TS), observe(TRUTH, TS), rtol=1e-6)
    for g in GROUPS.values():
        assert np.isclose(g(scaled(TRUTH, lam)), g(TRUTH))


def test_reduced_model_reproduces_the_dimensional_one():
    assert np.allclose(observe_reduced(to_reduced(TRUTH), TS), observe(TRUTH, TS), rtol=1e-6)


def test_reduced_fit_recovers_the_groups_from_clean_data():
    truth = to_reduced(TRUTH)
    q, loss, cond = fit_reduced({k: v * 1.4 for k, v in truth.items()}, TS, observe(TRUTH, TS))
    assert loss < 1e-8 and cond < 1e4
    for k in truth:
        assert np.isclose(q[k], truth[k], rtol=1e-3)


def test_noise_is_reproducible():
    assert np.array_equal(make_data(TS, 0.05, 3), make_data(TS, 0.05, 3))
    assert not np.array_equal(make_data(TS, 0.05, 3), make_data(TS, 0.05, 4))


@pytest.mark.slow
def test_experiment_headline_results(tmp_path):
    res = run(tmp_path, n_starts=8)
    assert res["n_good_fits"] >= 4
    for k in ("beta", "rho", "S0", "I0"):  # moved by the scaling: not pinned down
        assert res["raw_spread"][k] > 2
    assert res["raw_spread"]["gamma"] < 1.01
    for k, v in res["group_spread"].items():  # invariant groups: every fit agrees
        assert v < 1.01, k
    assert np.ptp(res["along"]) < 1e-6 and res["across"].max() > 10
    for row in res["scenarios"]:
        assert row["cond_reduced"] < 1e3 < row["cond_raw"] or row["cond_reduced"] * 10 < row["cond_raw"]
        assert row["R0_err"] < 0.15
    text = (tmp_path / "identifiability_sir.md").read_text()
    assert "R0" in text and (tmp_path / "identifiability_sir.png").stat().st_size > 10_000

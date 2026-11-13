"""Framing 2: constraint verdicts, cross-checked against brute force."""
import itertools
import random

import pytest
import sympy as sp

from conftest import ALL_KEYS, P
from nondim import models
from nondim.catalog import CATALOG
from nondim.constraints import check_constraint, max_removable, solve
from nondim.scaling import analyze, nondimensionalize, verify_symbolically


def brute_force_max(model, an, keep):
    """Largest set of non-kept parameters that can actually be normalized together."""
    cands = [p for p in model.params if p not in keep]
    for k in range(len(cands), 0, -1):
        for S in itertools.combinations(cands, k):
            try:
                nondimensionalize(model, list(S), analysis=an)
                return k
            except ValueError:
                pass
    return 0


@pytest.mark.parametrize("key", ALL_KEYS)
def test_rank_criterion_agrees_with_brute_force_for_every_keep_set(key):
    """For EVERY subset `keep` and EVERY k: solve says SAT  <=>  some k non-kept parameters normalize."""
    m = models.ALL[key]()
    an = analyze(m)
    for r in range(len(m.params) + 1):
        for keep in itertools.combinations(m.params, r):
            best = brute_force_max(m, an, keep)
            assert max_removable(m, keep, an) == best
            for k in range(len(m.params) + 2):
                res = solve(m, k, keep=keep, analysis=an)
                assert res.satisfiable == (k <= best)
                if res.satisfiable:
                    assert len(res.witness.normalized) >= k
                    assert not set(res.witness.normalized) & set(keep)
                    assert all(x == 0 for x in verify_symbolically(res.witness))
                else:
                    assert res.reason == "rank" and res.witness is None


def test_sir_examples_from_the_docs():
    m = models.sir()
    beta, gamma, N = P("beta"), P("gamma"), P("N")
    sat = solve(m, 2, keep=["beta"])
    assert sat.satisfiable and set(sat.witness.normalized) == {gamma, N}
    assert not solve(m, 3).satisfiable
    assert not solve(m, 2, keep=[gamma, N]).satisfiable
    assert solve(m, 2, keep=[]).available_rank == 2


def test_at_most_params_is_the_same_as_eliminate_at_least():
    m = models.rosenzweig_macarthur()
    assert solve(m, at_most_params=3).satisfiable and not solve(m, at_most_params=2).satisfiable
    assert solve(m, at_most_params=3).eliminate_at_least == 3


def test_strings_and_symbols_are_interchangeable():
    m = models.sir()
    assert solve(m, 2, keep=["beta"]).explanation == solve(m, 2, keep=[P("beta")]).explanation


@pytest.mark.parametrize("want, reason", [
    ({"R0": "beta*N/gamma"}, "ok"),
    ({"inv": "gamma/(beta*N)"}, "ok"),
    ({"x": "beta*N"}, "not_invariant"),
    ({"x": "gamma"}, "not_invariant"),
    ({"x": "beta + gamma"}, "not_monomial"),
    ({"x": "exp(beta*N/gamma)"}, "not_monomial"),
    ({"x": "sqrt(beta*N/gamma)"}, "not_monomial"),
    ({"x": "S/N"}, "not_parameter_only"),
    ({"x": "gamma*t"}, "not_parameter_only"),
    ({"a": "beta*N/gamma", "b": "gamma/(beta*N)"}, "dependent"),
    ({"a": "beta*N/gamma", "b": "(beta*N/gamma)**2"}, "dependent"),
])
def test_wanted_group_verdicts_on_sir(want, reason):
    res = solve(models.sir(), want=want)
    assert res.reason == reason and res.satisfiable == (reason == "ok")
    assert str(res).startswith("SAT" if res.satisfiable else "UNSAT")


def test_rank_failure_is_reported_before_group_failures():
    assert solve(models.sir(), 3, want={"x": "beta*N"}).reason == "rank"


def _check_regrouping(res, seed=0):
    """Numerically: the regrouped equations equal the reduced ones when groups are evaluated."""
    nd, g = res.witness, res.regrouping
    rng = random.Random(seed)
    syms = set().union(*[e.free_symbols for e in nd.reduced_rhs], *[h.free_symbols for _, _, h in g.groups])
    point = {s: sp.Rational(rng.randint(2, 9), rng.randint(1, 4)) for s in syms}
    group_values = {sym: in_hat.subs(point) for sym, _, in_hat in g.groups}
    for old, new in zip(nd.reduced_rhs, g.reduced_rhs):
        assert abs(sp.N(old.subs(point) - new.subs({**point, **group_values}))) < 1e-9
    # groups written in original variables are invariant under every scaling
    A, V = nd.analysis.A, nd.model.variables
    for _, in_orig, _ in g.groups:
        vec = sp.Matrix([in_orig.as_powers_dict().get(v, 0) for v in V])
        assert A * vec == sp.zeros(A.shape[0], 1)
    assert g.M.rank() == g.M.shape[0]
    assert g.integer == (abs(g.M.det()) == 1)


@pytest.mark.parametrize("key, kw", [
    ("sir", dict(want={"R0": "beta*N/gamma"})),
    ("lotka_volterra", dict(eliminate_at_least=3, want={"alpha": "c/a"})),
    ("lotka_volterra", dict(want={"alpha_inv": "a/c"})),
    ("michaelis_menten_ic", dict(want={"eps": "e0/s0", "lam": "k2/km1"})),
    ("michaelis_menten_ic", dict(want={"eps": "e0/s0", "lam": "k2/km1", "K": "km1/(k1*s0)"})),
    ("rosenzweig_macarthur", dict(want={"H": "a*h*K", "ratio": "e*a*K/m"})),
    ("rosenzweig_macarthur", dict(keep=["m"], want={"mix": "a*h*K*m/r"})),
])
def test_regrouping_is_correct(key, kw):
    res = solve(models.ALL[key](), **kw)
    assert res.satisfiable and res.regrouping.integer
    names = [str(g) for g, _, _ in res.regrouping.groups]
    assert names[: len(kw["want"])] == list(kw["want"])
    _check_regrouping(res)


def test_wanted_group_actually_appears_in_the_equations():
    res = solve(models.lotka_volterra(), want={"alpha": "c/a"})
    assert any(sp.Symbol("alpha", positive=True) in e.free_symbols for e in res.regrouping.reduced_rhs)


def test_non_primitive_group_needs_fractional_powers():
    res = solve(models.lotka_volterra(), want={"sq": "(c/a)**2"})
    assert res.satisfiable and not res.regrouping.integer
    assert "fractional" in res.explanation
    _check_regrouping(res)


def test_too_many_groups_is_dependent():
    res = solve(models.lotka_volterra(), want={"a1": "c/a", "a2": "a/c"})
    assert res.reason == "dependent"


def test_check_constraint_wrapper_accepts_a_list():
    m = models.sir()
    assert check_constraint(m, 1, want=[m.parse("beta*N/gamma")]).satisfiable


@pytest.mark.parametrize("key", [k for k, c in CATALOG.items() if c.get("constraints")])
def test_catalog_constraints_all_run_and_include_both_verdicts(key):
    m = models.ALL[key]()
    results = [solve(m, **c) for c in CATALOG[key]["constraints"]]
    assert all(r.explanation for r in results)
    if key in ("sir", "michaelis_menten_ic", "lotka_volterra"):
        assert {r.satisfiable for r in results} == {True, False}

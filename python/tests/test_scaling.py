"""Framing 1, solver side: scaling symmetries and the reductions built from them."""
import itertools
import random

import pytest
import sympy as sp

from conftest import ALL_KEYS, P
from nondim import models
from nondim.buckingham import dimension_matrix, pi_count, pi_groups
from nondim.catalog import CATALOG
from nondim.model import OutOfScopeError
from nondim.scaling import all_nondimensionalizations, analyze, nondimensionalize, verify_symbolically
from nondim.simulate import compare_trajectories

EXPECTED = {  # model -> (parameters, parameters after reduction, number of scalings)
    "logistic": (2, 0, 2),
    "sir": (3, 1, 2),
    "sir_noN": (2, 0, 2),
    "sir_reported": (3, 0, 3),
    "lotka_volterra": (4, 1, 3),
    "michaelis_menten": (4, 2, 2),
    "michaelis_menten_ic": (5, 3, 2),
    "rosenzweig_macarthur": (6, 3, 3),
    "spurious_original": (2, 1, 1),
    "spurious_substituted": (2, 0, 2),  # the fake extra symmetry
    "spurious_fixed": (2, 1, 1),  # removed again by the unit link
}


def test_every_model_has_an_expectation():
    assert set(EXPECTED) == set(models.ALL) == set(CATALOG)


@pytest.mark.parametrize("key", ALL_KEYS)
def test_counts_match_the_literature(key):
    m = models.ALL[key]()
    an = analyze(m)
    assert (len(m.params), an.min_params, an.n_scalings) == EXPECTED[key]


@pytest.mark.parametrize("key", ALL_KEYS)
def test_A_is_exactly_the_maximal_scaling_matrix(key):
    an = analyze(models.ALL[key]())
    n = len(an.model.variables)
    assert an.A * an.K == sp.zeros(an.A.shape[0], an.K.shape[1]), "rows of A are symmetries"
    assert an.A.rank() == an.A.shape[0], "rows of A are independent"
    assert an.A.shape[0] == n - an.K.rank(), "and there are n - rank K of them (rank-nullity): none is missing"
    assert an.rank_K == an.K.rank()


@pytest.mark.parametrize("key", ALL_KEYS)
def test_scalings_really_are_symmetries_of_the_vector_field(key):
    """Independent of the exponent-matrix machinery: plug scaled numbers into the equations.

    If x_i -> lam^{a_i} x_i then dz/dt must pick up the factor lam^{a_z - a_t}.
    """
    m = models.ALL[key]()
    an = analyze(m)
    rng = random.Random(0)
    V = m.variables
    for i in range(an.A.shape[0]):
        point = {v: sp.Rational(rng.randint(2, 9), rng.randint(1, 5)) for v in V}
        lam = sp.Rational(7, 3)
        scaled = {v: point[v] * lam ** an.A[i, j] for j, v in enumerate(V)}
        for z, f in zip(m.states, m.rhs):
            factor = lam ** (an.A[i, m.index(z)] - an.A[i, m.index(m.t)])
            assert sp.simplify(f.subs(scaled) - factor * f.subs(point)) == 0


@pytest.mark.parametrize("key", ALL_KEYS)
def test_every_maximal_choice_is_correct(key):
    m = models.ALL[key]()
    an = analyze(m)
    choices = all_nondimensionalizations(m, analysis=an)
    assert choices, "at least one reduction exists"
    for nd in choices:
        assert len(nd.normalized) == an.param_rank
        assert len(nd.reduced_params) == an.min_params
        assert all(r == 0 for r in verify_symbolically(nd)), "chain rule"
        assert nd.fully_invariant(), "new variables are dimensionless"
        assert compare_trajectories(nd, t_end=5.0) < 1e-6, "numerics agree"
        for s in nd.normalized:  # normalized parameters vanish from the reduced system
            assert all(s not in g.free_symbols for g in nd.reduced_rhs)


@pytest.mark.parametrize("key", ALL_KEYS)
def test_normalizable_iff_columns_independent_brute_force(key):
    """The core claim behind Framing 2, checked on every subset of parameters."""
    m = models.ALL[key]()
    an = analyze(m)
    for k in range(1, len(m.params) + 1):
        for S in itertools.combinations(m.params, k):
            independent = an.A[:, [m.index(s) for s in S]].rank() == k
            try:
                nd = nondimensionalize(m, list(S), analysis=an)
                ok = True
            except ValueError:
                ok = False
            assert ok == independent
            if ok:
                assert all(r == 0 for r in verify_symbolically(nd))
                assert len(nd.reduced_params) == len(m.params) - k


def test_new_variable_formula():
    """x_hat = x * prod s^e with A1[:, S] e = -A1[:, x]."""
    m = models.lotka_volterra()
    nd = nondimensionalize(m)
    S_idx = [m.index(s) for s in nd.normalized]
    for x in nd.new_expr:
        e = sp.Matrix([nd.exponents[x].get(s, 0) for s in nd.normalized])
        assert nd.A1[:, S_idx] * e == -nd.A1[:, m.index(x)]


def test_sir_textbook_form_gives_R0():
    m = models.sir()
    beta, gamma, N, S = P("beta"), P("gamma"), P("N"), P("S")
    nd = nondimensionalize(m, [gamma, N])
    assert sp.simplify(nd.new_expr[beta] - beta * N / gamma) == 0
    assert sp.simplify(nd.new_expr[m.t] - gamma * m.t) == 0
    assert sp.simplify(nd.new_expr[S] - S / N) == 0
    R0, X, Y = nd.new_symbol[beta], nd.new_symbol[S], nd.new_symbol[P("I")]
    assert sp.simplify(nd.reduced_rhs[0] + R0 * X * Y) == 0
    assert sp.simplify(nd.reduced_rhs[1] - (R0 * X * Y - Y)) == 0


def test_logistic_and_lotka_volterra_textbook_forms():
    nd = nondimensionalize(models.logistic())
    u = nd.new_symbol[P("N")]
    assert sp.simplify(nd.reduced_rhs[0] - u * (1 - u)) == 0
    m = models.lotka_volterra()
    nd = nondimensionalize(m, [P("a"), P("b"), P("d")])
    u, v, al = nd.new_symbol[P("x")], nd.new_symbol[P("y")], nd.new_symbol[P("c")]
    assert sp.simplify(nd.new_expr[P("c")] - P("c") / P("a")) == 0
    assert sp.simplify(nd.reduced_rhs[0] - u * (1 - v)) == 0
    assert sp.simplify(nd.reduced_rhs[1] - v * (u - al)) == 0


def test_keep_is_respected():
    m = models.lotka_volterra()
    nd = nondimensionalize(m, keep=[P("a")])
    assert P("a") not in nd.normalized and len(nd.normalized) == 3


def test_cannot_normalize_states_or_dependent_parameters():
    m = models.michaelis_menten_ic()
    with pytest.raises(ValueError):
        nondimensionalize(m, [P("e0"), P("s0")])  # both concentrations: eps = e0/s0 must survive
    with pytest.raises(ValueError):
        nondimensionalize(m, [P("s")])


def test_names_can_be_chosen():
    m = models.sir()
    nd = nondimensionalize(m, [P("gamma"), P("N")], names={m.t: "tau", P("S"): "X"})
    assert nd.new_symbol[m.t].name == "tau" and nd.new_symbol[P("S")].name == "X"


def test_spurious_symmetry_failure_mode():
    """Tanburn et al. Example 3.12: forgetting a unit link invents a symmetry."""
    orig, sub, fixed = (analyze(f()) for f in (models.spurious_original, models.spurious_substituted, models.spurious_fixed))
    assert (orig.n_scalings, sub.n_scalings, fixed.n_scalings) == (1, 2, 1)
    assert (orig.min_params, sub.min_params, fixed.min_params) == (1, 0, 1)


def test_out_of_scope_is_rejected_with_an_explanation():
    with pytest.raises(OutOfScopeError, match="monomials"):
        analyze(models.arrhenius_out_of_scope())


def test_summaries_mention_the_key_numbers():
    an = analyze(models.sir())
    assert "3 -> 1" in an.summary()
    assert "R" in nondimensionalize(models.sir()).summary()


# ------------------------------------------------------------ Buckingham Pi

def _dims(key):
    m = models.ALL[key]()
    return m, {m.symbol(k): v for k, v in CATALOG[key]["dims"].items()}


@pytest.mark.parametrize("key", ["sir", "lotka_volterra"])
def test_pi_groups_are_dimensionless_and_counted_by_rank_nullity(key):
    _, dims = _dims(key)
    D, bases, qs = dimension_matrix(dims)
    groups = pi_groups(dims)
    assert len(groups) == pi_count(dims) == len(qs) - D.rank()
    for g in groups:
        for b in bases:  # total exponent of each base dimension is zero
            assert sum(g.as_powers_dict().get(q, 0) * dims[q].get(b, 0) for q in qs) == 0


def test_declared_units_are_symmetries_of_the_equations():
    """Sanity of the catalog: the physical dimension vectors lie in the row space of A."""
    for key in ["sir", "lotka_volterra"]:
        m, dims = _dims(key)
        an = analyze(m)
        D, _, qs = dimension_matrix(dims)
        D = D[:, [qs.index(v) for v in m.variables]]
        assert D * an.K == sp.zeros(D.shape[0], an.K.shape[1])


def test_scaling_beats_buckingham_on_lotka_volterra():
    m, dims = _dims("lotka_volterra")
    an = analyze(m)
    assert pi_count(dims) == 5 and len(m.variables) - an.n_scalings == 4

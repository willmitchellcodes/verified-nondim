import pytest
import sympy as sp

from nondim import models
from nondim.model import Model, OutOfScopeError, exponent_matrix, invariance_columns, monomial_exponents

t, x, a, b = sp.symbols("t x a b", positive=True)
V = [t, x, a, b]


def test_monomial_exponents():
    assert monomial_exponents(3 * a * x**2 / b, V) == [0, 2, 1, -1]
    assert monomial_exponents(sp.Integer(5), V) == [0, 0, 0, 0]
    assert monomial_exponents(sp.sqrt(a), V) == [0, 0, sp.Rational(1, 2), 0]


@pytest.mark.parametrize("bad", [sp.exp(a), sp.log(x), sp.sin(a * t), a**b, sp.Symbol("zz")])
def test_monomial_exponents_rejects_out_of_scope(bad):
    with pytest.raises(OutOfScopeError):
        monomial_exponents(bad, V)


def test_invariance_columns_polynomial():
    assert sorted(invariance_columns(a * x + b, V)) == [[0, 0, 0, 1], [0, 1, 1, 0]]


def test_invariance_columns_rational_uses_differences():
    # a*x/(1 + b*x) is invariant iff a*x and b*x are each invariant (reference monomial: 1).
    cols = invariance_columns(a * x / (1 + b * x), V)
    assert sorted(cols) == sorted([[0, 1, 1, 0], [0, 1, 0, 1]])


def test_invariance_columns_of_zero_is_empty():
    assert invariance_columns(sp.Integer(0), V) == []


def test_exponent_matrix_logistic_by_hand():
    m = models.logistic()  # t*f/N = r*t - r*t*N/K ; variables t, N, r, K
    K = exponent_matrix(m)
    assert {tuple(K[:, j]) for j in range(K.shape[1])} == {(1, 0, 1, 0), (1, 1, 1, -1)}


def test_exponent_matrix_has_integer_entries_and_no_duplicate_columns():
    for f in models.ALL.values():
        K = exponent_matrix(f())
        cols = [tuple(K[:, j]) for j in range(K.shape[1])]
        assert all(e.is_Integer for e in K) and len(cols) == len(set(cols))


def test_extra_invariants_add_columns():
    with_n, without = exponent_matrix(models.sir()), exponent_matrix(models.sir_no_population())
    assert with_n.rank() - without.rank() == 2  # R equation + the unit links


def test_model_needs_one_rhs_per_state():
    with pytest.raises(ValueError):
        Model("bad", t, [x], [a], [])


def test_from_strings_matches_handwritten_model():
    m = Model.from_strings("SIR", {"S": "-beta*S*I", "I": "beta*S*I - gamma*I", "R": "gamma*I"},
                           "beta gamma N", same_units=[("S", "N"), ("I", "N"), ("R", "N")])
    ref = models.sir()
    assert m.rhs == ref.rhs and m.variables == ref.variables and m.extra_invariants == ref.extra_invariants


def test_from_strings_reports_unknown_symbols():
    with pytest.raises(ValueError, match="unknown symbol"):
        Model.from_strings("x", {"S": "-b*S"}, "beta")
    with pytest.raises(ValueError, match="unknown symbol"):
        Model.from_strings("x", {"S": "-beta*S"}, "beta", outputs={"y": "rho*S"})


def test_symbol_lookup_and_parse():
    m = models.sir()
    assert m.symbol("beta").name == "beta"
    assert m.parse("beta*N/gamma").free_symbols == {m.symbol("beta"), m.symbol("N"), m.symbol("gamma")}
    with pytest.raises(KeyError):
        m.symbol("nope")


def test_variable_order_is_time_states_params():
    m = models.lotka_volterra()
    assert [v.name for v in m.variables] == ["t", "x", "y", "a", "b", "c", "d"]

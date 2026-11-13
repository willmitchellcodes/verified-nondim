# MichaelisMentenIC

Expect 5 -> 3, e.g. the textbook (K, lambda, epsilon = e0/s0) after choosing invariants.

## The model

```
ds/dt = c*km1 - k1*s*(-c + e0)
dc/dt = -c*(k2 + km1) + k1*s*(-c + e0)
parameters: k1, km1, k2, e0, s0
unit links (must stay invariant): s/s0
```

## 1. Scaling symmetries

The exponent matrix K is 8×8 with rank 6, so there are 8 − 6 = **2 independent scalings** (rank–nullity):

| # | t | s | c | k1 | km1 | k2 | e0 | s0 |
|---|---|---|---|---|---|---|---|---|
| 1 | 0 | -1 | -1 | 1 | 0 | 0 | -1 | -1 |
| 2 | -1 | 1 | 1 | 0 | 1 | 1 | 1 | 1 |

(Row i says: multiply each variable by λ^entry.) On the parameter columns these rows have rank **2**, so the model reduces from **5 to 3 parameter(s)**, and no scaling can do better.

## 2. Every maximal choice (non-uniqueness)

| normalize to 1 | surviving parameters |
|---|---|
| k1, km1 | k2_hat = k2/km1, e0_hat = e0*k1/km1, s0_hat = k1*s0/km1 |
| k1, k2 | km1_hat = km1/k2, e0_hat = e0*k1/k2, s0_hat = k1*s0/k2 |
| k1, e0 | km1_hat = km1/(e0*k1), k2_hat = k2/(e0*k1), s0_hat = s0/e0 |
| k1, s0 | km1_hat = km1/(k1*s0), k2_hat = k2/(k1*s0), e0_hat = e0/s0 |
| km1, e0 | k1_hat = e0*k1/km1, k2_hat = k2/km1, s0_hat = s0/e0 |
| km1, s0 | k1_hat = k1*s0/km1, k2_hat = k2/km1, e0_hat = e0/s0 |
| k2, e0 | k1_hat = e0*k1/k2, km1_hat = km1/k2, s0_hat = s0/e0 |
| k2, s0 | k1_hat = k1*s0/k2, km1_hat = km1/k2, e0_hat = e0/s0 |

## 3. The reduction used

```
t_hat = k1*s0*t
s_hat = s/s0
c_hat = c/s0
km1_hat = km1/(k1*s0)
k2_hat = k2/(k1*s0)
e0_hat = e0/s0

ds_hat/dt_hat = c_hat*km1_hat + s_hat*(c_hat - e0_hat)
dc_hat/dt_hat = -c_hat*(k2_hat + km1_hat) - s_hat*(c_hat - e0_hat)
```

* chain-rule check (SymPy): pass
* numeric check, original vs. reduced trajectories: max relative error 1.1e-11
* every new variable dimensionless: True

## 4. Constraints

| request | verdict | why / how |
|---|---|---|
| `eliminate_at_least=2, keep=['k1']` | **SAT** | normalize ['km1', 'e0'] (removes 2 >= 2). |
| `eliminate_at_least=2, want={'eps': 'e0/s0', 'sigma': 'k1*s0/(km1 + k2)'}` | **UNSAT** | sigma = k1*s0/(k2 + km1) is not a product of powers, so it cannot be a scaling invariant chosen by this method (cf. Segel-Slemrod's e0/(s0 + Km)). |
| `eliminate_at_least=2, want={'eps': 'e0/s0', 'lam': 'k2/km1'}` | **SAT** | normalize ['k1', 'km1'] (removes 2 >= 2); groups eps = e0/s0, lam = k2/km1, e0_hat = e0*k1/km1. |
| `want={'a': 'e0/s0', 'b': 's0/e0'}` | **UNSAT** | the wanted groups are not independent (rank 1 < 2); at most 3 independent parameter groups exist. |

Regrouped with eps, lam:

```
eps = e0/s0
lam = k2/km1
e0_hat = e0*k1/km1
ds_hat/dt_hat = c_hat + s_hat*(c_hat - e0_hat)
dc_hat/dt_hat = -c_hat*(lam + 1) - s_hat*(c_hat - e0_hat)
unit links become: eps*s_hat/e0_hat
```

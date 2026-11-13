# Spurious_fixed

## The model

```
dx/dt = b + c*x
parameters: b, c
unit links (must stay invariant): b/c
```

## 1. Scaling symmetries

The exponent matrix K is 4×3 with rank 3, so there are 4 − 3 = **1 independent scalings** (rank–nullity):

| # | t | x | b | c |
|---|---|---|---|---|
| 1 | -1 | 0 | 1 | 1 |

(Row i says: multiply each variable by λ^entry.) On the parameter columns these rows have rank **1**, so the model reduces from **2 to 1 parameter(s)**, and no scaling can do better.

## 2. Every maximal choice (non-uniqueness)

| normalize to 1 | surviving parameters |
|---|---|
| b | c_hat = c/b |
| c | b_hat = b/c |

## 3. The reduction used

```
t_hat = b*t
x_hat = x
c_hat = c/b

dx_hat/dt_hat = c_hat*x_hat + 1
```

* chain-rule check (SymPy): pass
* numeric check, original vs. reduced trajectories: max relative error 8.8e-15
* every new variable dimensionless: True

## 4. Constraints

| request | verdict | why / how |
|---|---|---|
| `eliminate_at_least=2` | **UNSAT** | only 1 independent scaling direction(s) act on ['b', 'c'], so at most 1 of them can be removed (asked for 2). |

# Spurious_substituted

## The model

```
dx/dt = b + c*x
parameters: b, c
```

## 1. Scaling symmetries

The exponent matrix K is 4×2 with rank 2, so there are 4 − 2 = **2 independent scalings** (rank–nullity):

| # | t | x | b | c |
|---|---|---|---|---|
| 1 | 0 | 1 | 1 | 0 |
| 2 | -1 | -1 | 0 | 1 |

(Row i says: multiply each variable by λ^entry.) On the parameter columns these rows have rank **2**, so the model reduces from **2 to 0 parameter(s)**, and no scaling can do better.

## 2. Every maximal choice (non-uniqueness)

| normalize to 1 | surviving parameters |
|---|---|
| b, c | (none) |

## 3. The reduction used

```
t_hat = c*t
x_hat = c*x/b

dx_hat/dt_hat = x_hat + 1
```

* chain-rule check (SymPy): pass
* numeric check, original vs. reduced trajectories: max relative error 3.2e-13
* every new variable dimensionless: True

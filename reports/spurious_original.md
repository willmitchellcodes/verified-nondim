# Spurious_original

## The model

```
dx/dt = a*x + b*x + b
parameters: a, b
```

## 1. Scaling symmetries

The exponent matrix K is 4×3 with rank 3, so there are 4 − 3 = **1 independent scalings** (rank–nullity):

| # | t | x | a | b |
|---|---|---|---|---|
| 1 | -1 | 0 | 1 | 1 |

(Row i says: multiply each variable by λ^entry.) On the parameter columns these rows have rank **1**, so the model reduces from **2 to 1 parameter(s)**, and no scaling can do better.

## 2. Every maximal choice (non-uniqueness)

| normalize to 1 | surviving parameters |
|---|---|
| a | b_hat = b/a |
| b | a_hat = a/b |

## 3. The reduction used

```
t_hat = a*t
x_hat = x
b_hat = b/a

dx_hat/dt_hat = b_hat*x_hat + b_hat + x_hat
```

* chain-rule check (SymPy): pass
* numeric check, original vs. reduced trajectories: max relative error 1.6e-13
* every new variable dimensionless: True

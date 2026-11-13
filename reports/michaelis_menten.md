# MichaelisMenten

Expect 4 -> 2 (time and concentration scalings).

## The model

```
ds/dt = c*km1 - k1*s*(-c + e0)
dc/dt = -c*(k2 + km1) + k1*s*(-c + e0)
parameters: k1, km1, k2, e0
```

## 1. Scaling symmetries

The exponent matrix K is 7×7 with rank 5, so there are 7 − 5 = **2 independent scalings** (rank–nullity):

| # | t | s | c | k1 | km1 | k2 | e0 |
|---|---|---|---|---|---|---|---|
| 1 | 0 | -1 | -1 | 1 | 0 | 0 | -1 |
| 2 | -1 | 1 | 1 | 0 | 1 | 1 | 1 |

(Row i says: multiply each variable by λ^entry.) On the parameter columns these rows have rank **2**, so the model reduces from **4 to 2 parameter(s)**, and no scaling can do better.

## 2. Every maximal choice (non-uniqueness)

| normalize to 1 | surviving parameters |
|---|---|
| k1, km1 | k2_hat = k2/km1, e0_hat = e0*k1/km1 |
| k1, k2 | km1_hat = km1/k2, e0_hat = e0*k1/k2 |
| k1, e0 | km1_hat = km1/(e0*k1), k2_hat = k2/(e0*k1) |
| km1, e0 | k1_hat = e0*k1/km1, k2_hat = k2/km1 |
| k2, e0 | k1_hat = e0*k1/k2, km1_hat = km1/k2 |

## 3. The reduction used

```
t_hat = km1*t
s_hat = k1*s/km1
c_hat = c*k1/km1
k2_hat = k2/km1
e0_hat = e0*k1/km1

ds_hat/dt_hat = c_hat + s_hat*(c_hat - e0_hat)
dc_hat/dt_hat = -c_hat*(k2_hat + 1) - s_hat*(c_hat - e0_hat)
```

* chain-rule check (SymPy): pass
* numeric check, original vs. reduced trajectories: max relative error 1.3e-12
* every new variable dimensionless: True

# logistic

dN/dt = rN(1 - N/K). Expect 2 -> 0 parameters: u = N/K, tau = r t.

## The model

```
dN/dt = N*r*(1 - N/K)
parameters: r, K
```

## 1. Scaling symmetries

The exponent matrix K is 4×2 with rank 2, so there are 4 − 2 = **2 independent scalings** (rank–nullity):

| # | t | N | r | K |
|---|---|---|---|---|
| 1 | -1 | 0 | 1 | 0 |
| 2 | 0 | 1 | 0 | 1 |

(Row i says: multiply each variable by λ^entry.) On the parameter columns these rows have rank **2**, so the model reduces from **2 to 0 parameter(s)**, and no scaling can do better.

## 2. Every maximal choice (non-uniqueness)

| normalize to 1 | surviving parameters |
|---|---|
| r, K | (none) |

## 3. The reduction used

```
t_hat = r*t
N_hat = N/K

dN_hat/dt_hat = N_hat*(1 - N_hat)
```

* chain-rule check (SymPy): pass
* numeric check, original vs. reduced trajectories: max relative error 2.8e-13
* every new variable dimensionless: True

## 4. Constraints

| request | verdict | why / how |
|---|---|---|
| `eliminate_at_least=2` | **SAT** | normalize ['r', 'K'] (removes 2 >= 2). |
| `eliminate_at_least=3` | **UNSAT** | only 2 independent scaling direction(s) act on ['r', 'K'], so at most 2 of them can be removed (asked for 3). |

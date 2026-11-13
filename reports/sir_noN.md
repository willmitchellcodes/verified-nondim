# SIR_noN

2 -> 0 parameters; R0 then hides in the initial condition.

## The model

```
dS/dt = -I*S*beta
dI/dt = I*S*beta - I*gamma
parameters: beta, gamma
```

## 1. Scaling symmetries

The exponent matrix K is 5×3 with rank 3, so there are 5 − 3 = **2 independent scalings** (rank–nullity):

| # | t | S | I | beta | gamma |
|---|---|---|---|---|---|
| 1 | 0 | -1 | -1 | 1 | 0 |
| 2 | -1 | 1 | 1 | 0 | 1 |

(Row i says: multiply each variable by λ^entry.) On the parameter columns these rows have rank **2**, so the model reduces from **2 to 0 parameter(s)**, and no scaling can do better.

## 2. Every maximal choice (non-uniqueness)

| normalize to 1 | surviving parameters |
|---|---|
| beta, gamma | (none) |

## 3. The reduction used

```
t_hat = gamma*t
S_hat = S*beta/gamma
I_hat = I*beta/gamma

dS_hat/dt_hat = -I_hat*S_hat
dI_hat/dt_hat = I_hat*(S_hat - 1)
```

* chain-rule check (SymPy): pass
* numeric check, original vs. reduced trajectories: max relative error 1.1e-10
* every new variable dimensionless: True

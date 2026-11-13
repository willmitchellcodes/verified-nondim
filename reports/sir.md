# SIR

Expect 3 -> 1 parameter. Normalizing gamma and N gives R0 = beta N / gamma.

## The model

```
dS/dt = -I*S*beta
dI/dt = I*S*beta - I*gamma
dR/dt = I*gamma
parameters: beta, gamma, N
unit links (must stay invariant): S/N, I/N, R/N
```

## 1. Scaling symmetries

The exponent matrix K is 7×7 with rank 5, so there are 7 − 5 = **2 independent scalings** (rank–nullity):

| # | t | S | I | R | beta | gamma | N |
|---|---|---|---|---|---|---|---|
| 1 | 0 | -1 | -1 | -1 | 1 | 0 | -1 |
| 2 | -1 | 1 | 1 | 1 | 0 | 1 | 1 |

(Row i says: multiply each variable by λ^entry.) On the parameter columns these rows have rank **2**, so the model reduces from **3 to 1 parameter(s)**, and no scaling can do better.

Buckingham Pi from the declared physical units alone gives 5 dimensionless groups (`I/S, R/S, S*beta*t, gamma*t, N/S`); the scaling analysis gives 5 invariants.

## 2. Every maximal choice (non-uniqueness)

| normalize to 1 | surviving parameters |
|---|---|
| beta, gamma | N_hat = N*beta/gamma |
| beta, N | gamma_hat = gamma/(N*beta) |
| gamma, N | beta_hat = N*beta/gamma |

## 3. The reduction used

```
t_hat = gamma*t
S_hat = S/N
I_hat = I/N
R_hat = R/N
beta_hat = N*beta/gamma

dS_hat/dt_hat = -I_hat*S_hat*beta_hat
dI_hat/dt_hat = I_hat*(S_hat*beta_hat - 1)
dR_hat/dt_hat = I_hat
```

* chain-rule check (SymPy): pass
* numeric check, original vs. reduced trajectories: max relative error 3.3e-11
* every new variable dimensionless: True

## 4. Constraints

| request | verdict | why / how |
|---|---|---|
| `eliminate_at_least=2, keep=['beta']` | **SAT** | normalize ['gamma', 'N'] (removes 2 >= 2). |
| `eliminate_at_least=3` | **UNSAT** | only 2 independent scaling direction(s) act on ['beta', 'gamma', 'N'], so at most 2 of them can be removed (asked for 3). |
| `eliminate_at_least=2, keep=['gamma', 'N']` | **UNSAT** | only 1 independent scaling direction(s) act on ['beta'], so at most 1 of them can be removed (asked for 2). |
| `at_most_params=1, want={'R0': 'beta*N/gamma'}` | **SAT** | normalize ['beta', 'gamma'] (removes 2 >= 2); groups R0 = N*beta/gamma. |
| `want={'force': 'beta*N'}` | **UNSAT** | force = N*beta is not dimensionless: scaling #2 multiplies it by lambda^1. |

Regrouped with R0:

```
R0 = N*beta/gamma
dS_hat/dt_hat = -I_hat*S_hat
dI_hat/dt_hat = I_hat*(S_hat - 1)
dR_hat/dt_hat = I_hat
unit links become: S_hat/R0, I_hat/R0, R_hat/R0
```

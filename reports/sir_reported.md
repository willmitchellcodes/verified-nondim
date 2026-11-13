# SIR_reported

Identifiability example: beta and rho cannot be told apart from y alone.

## The model

```
dS/dt = -I*S*beta
dI/dt = I*S*beta - I*gamma
parameters: beta, gamma, rho
```

## 1. Scaling symmetries

The exponent matrix K is 6×3 with rank 3, so there are 6 − 3 = **3 independent scalings** (rank–nullity):

| # | t | S | I | beta | gamma | rho |
|---|---|---|---|---|---|---|
| 1 | 0 | -1 | -1 | 1 | 0 | 0 |
| 2 | -1 | 1 | 1 | 0 | 1 | 0 |
| 3 | 0 | 0 | 0 | 0 | 0 | 1 |

(Row i says: multiply each variable by λ^entry.) On the parameter columns these rows have rank **3**, so the model reduces from **3 to 0 parameter(s)**, and no scaling can do better.

## 2. Every maximal choice (non-uniqueness)

| normalize to 1 | surviving parameters |
|---|---|
| beta, gamma, rho | (none) |

## 3. The reduction used

```
t_hat = gamma*t
S_hat = S*beta/gamma
I_hat = I*beta/gamma

dS_hat/dt_hat = -I_hat*S_hat
dI_hat/dt_hat = I_hat*(S_hat - 1)
```

* chain-rule check (SymPy): pass
* numeric check, original vs. reduced trajectories: max relative error 8.5e-11
* every new variable dimensionless: True

## 5. Identifiability from the measured outputs

```
Identifiability of SIR_reported from outputs y = I*rho
  data unchanged by:  S -> lambda^-1 S,  I -> lambda^-1 I,  beta -> lambda^1 beta,  rho -> lambda^1 rho
  NOT identifiable (moved by a scaling): ['beta', 'rho']
  not flagged by this test:              ['gamma']
  states with unobservable scale:        ['S', 'I']
  parameter groups the data can see:     ['gamma', 'rho/beta']
  (one-way test: 'not flagged' does not prove identifiable)
```

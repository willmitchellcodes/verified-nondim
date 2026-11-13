# RosenzweigMacArthur

Rational right-hand side. Expect 6 -> 3.

## The model

```
dN/dt = -N*P*a/(N*a*h + 1) + N*r*(1 - N/K)
dP/dt = N*P*a*e/(N*a*h + 1) - P*m
parameters: r, K, a, h, e, m
```

## 1. Scaling symmetries

The exponent matrix K is 9×9 with rank 6, so there are 9 − 6 = **3 independent scalings** (rank–nullity):

| # | t | N | P | r | K | a | h | e | m |
|---|---|---|---|---|---|---|---|---|---|
| 1 | -1 | 0 | 1 | 1 | 0 | 0 | 0 | 1 | 1 |
| 2 | 0 | 1 | 0 | 0 | 1 | 0 | -1 | -1 | 0 |
| 3 | 0 | 0 | -1 | 0 | 0 | 1 | -1 | -1 | 0 |

(Row i says: multiply each variable by λ^entry.) On the parameter columns these rows have rank **3**, so the model reduces from **6 to 3 parameter(s)**, and no scaling can do better.

## 2. Every maximal choice (non-uniqueness)

| normalize to 1 | surviving parameters |
|---|---|
| r, K, a | h_hat = K*a*h, e_hat = K*a*e/r, m_hat = m/r |
| r, K, h | a_hat = K*a*h, e_hat = e/(h*r), m_hat = m/r |
| r, K, e | a_hat = K*a*e/r, h_hat = h*r/e, m_hat = m/r |
| r, a, h | K_hat = K*a*h, e_hat = e/(h*r), m_hat = m/r |
| r, a, e | K_hat = K*a*e/r, h_hat = h*r/e, m_hat = m/r |
| K, a, e | r_hat = r/(K*a*e), h_hat = K*a*h, m_hat = m/(K*a*e) |
| K, a, m | r_hat = r/m, h_hat = K*a*h, e_hat = K*a*e/m |
| K, h, e | r_hat = h*r/e, a_hat = K*a*h, m_hat = h*m/e |
| K, h, m | r_hat = r/m, a_hat = K*a*h, e_hat = e/(h*m) |
| K, e, m | r_hat = r/m, a_hat = K*a*e/m, h_hat = h*m/e |
| a, h, e | r_hat = h*r/e, K_hat = K*a*h, m_hat = h*m/e |
| a, h, m | r_hat = r/m, K_hat = K*a*h, e_hat = e/(h*m) |
| a, e, m | r_hat = r/m, K_hat = K*a*e/m, h_hat = h*m/e |

## 3. The reduction used

```
t_hat = r*t
N_hat = N/K
P_hat = P*a/r
h_hat = K*a*h
e_hat = K*a*e/r
m_hat = m/r

dN_hat/dt_hat = N_hat*(-P_hat - (N_hat - 1)*(N_hat*h_hat + 1))/(N_hat*h_hat + 1)
dP_hat/dt_hat = P_hat*(N_hat*e_hat - m_hat*(N_hat*h_hat + 1))/(N_hat*h_hat + 1)
```

* chain-rule check (SymPy): pass
* numeric check, original vs. reduced trajectories: max relative error 3.0e-09
* every new variable dimensionless: True

## 4. Constraints

| request | verdict | why / how |
|---|---|---|
| `eliminate_at_least=3, keep=['r', 'm']` | **SAT** | normalize ['K', 'a', 'e'] (removes 3 >= 3). |
| `at_most_params=3, want={'H': 'a*h*K', 'ratio': 'e*a*K/m'}` | **SAT** | normalize ['r', 'K', 'a'] (removes 3 >= 3); groups H = K*a*h, ratio = K*a*e/m, e_hat = K*a*e/r. |

Regrouped with H, ratio:

```
H = K*a*h
ratio = K*a*e/m
e_hat = K*a*e/r
dN_hat/dt_hat = -N_hat*(P_hat + (N_hat - 1)*(H*N_hat + 1))/(H*N_hat + 1)
dP_hat/dt_hat = P_hat*e_hat*(-H*N_hat + N_hat*ratio - 1)/(ratio*(H*N_hat + 1))
```

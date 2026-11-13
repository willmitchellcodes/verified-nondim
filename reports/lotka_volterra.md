# LotkaVolterra

Expect 4 -> 1 (three scalings: time, prey units, predator units).

## The model

```
dx/dt = a*x - b*x*y
dy/dt = -c*y + d*x*y
parameters: a, b, c, d
```

## 1. Scaling symmetries

The exponent matrix K is 7×4 with rank 4, so there are 7 − 4 = **3 independent scalings** (rank–nullity):

| # | t | x | y | a | b | c | d |
|---|---|---|---|---|---|---|---|
| 1 | -1 | 1 | 1 | 1 | 0 | 1 | 0 |
| 2 | 0 | 0 | -1 | 0 | 1 | 0 | 0 |
| 3 | 0 | -1 | 0 | 0 | 0 | 0 | 1 |

(Row i says: multiply each variable by λ^entry.) On the parameter columns these rows have rank **3**, so the model reduces from **4 to 1 parameter(s)**, and no scaling can do better.

Buckingham Pi from the declared physical units alone gives 5 dimensionless groups (`y/x, a*t, b*t*x, c*t, d*t*x`); the scaling analysis gives 4 invariants.

## 2. Every maximal choice (non-uniqueness)

| normalize to 1 | surviving parameters |
|---|---|
| a, b, d | c_hat = c/a |
| b, c, d | a_hat = a/c |

## 3. The reduction used

```
t_hat = a*t
x_hat = d*x/a
y_hat = b*y/a
c_hat = c/a

dx_hat/dt_hat = x_hat*(1 - y_hat)
dy_hat/dt_hat = y_hat*(-c_hat + x_hat)
```

* chain-rule check (SymPy): pass
* numeric check, original vs. reduced trajectories: max relative error 9.1e-11
* every new variable dimensionless: True

## 4. Constraints

| request | verdict | why / how |
|---|---|---|
| `eliminate_at_least=3, keep=['c']` | **SAT** | normalize ['a', 'b', 'd'] (removes 3 >= 3). |
| `eliminate_at_least=4` | **UNSAT** | only 3 independent scaling direction(s) act on ['a', 'b', 'c', 'd'], so at most 3 of them can be removed (asked for 4). |
| `want={'alpha': 'c/a'}` | **SAT** | normalize ['a', 'b', 'd'] (removes 3 >= 0); groups alpha = c/a. |

Regrouped with alpha:

```
alpha = c/a
dx_hat/dt_hat = x_hat*(1 - y_hat)
dy_hat/dt_hat = y_hat*(-alpha + x_hat)
```

## 5. Identifiability from the measured outputs

```
Identifiability of LotkaVolterra from outputs prey_count = x
  data unchanged by:  y -> lambda^-1 y,  b -> lambda^1 b
  NOT identifiable (moved by a scaling): ['b']
  not flagged by this test:              ['a', 'c', 'd']
  states with unobservable scale:        ['y']
  parameter groups the data can see:     ['a', 'c', 'd']
  (one-way test: 'not flagged' does not prove identifiable)
```

<p align="center"><img src="https://raw.githubusercontent.com/willmitchellcodes/verified-nondim/main/assets/logo.svg" width="88" alt="verified-nondim logo"></p>

# verified-nondim

Nondimensionalize ODE models automatically, and let Lean 4 check the result.

```bash
pip install verified-nondim
```

## Three parameters, one that matters

```python
from nondim import Model, nondimensionalize

sir = Model.from_strings(
    "SIR",
    equations={"S": "-beta*S*I", "I": "beta*S*I - gamma*I"},
    params="beta gamma N",
    same_units=[("S", "N"), ("I", "N")],  # S and I are counted in the same units as N
)
reduced = nondimensionalize(sir, ["gamma", "N"], names={"t": "tau", "S": "X", "I": "Y", "beta": "R0"})
print(reduced.summary())
```

```text
    tau = gamma*t
    X = S/N
    Y = I/N
    R0 = N*beta/gamma
  reduced system:
    dX/dtau = -R0*X*Y
    dY/dtau = Y*(R0*X - 1)
  parameters 3 -> 1: R0
```

The tool reads the equations, finds every change of units they allow, and uses those to set
parameters to 1. The number it can remove is a matrix rank, so it is the best possible.

## Ask for what you want

```python
from nondim import solve

print(solve(sir, eliminate_at_least=2, keep=["beta"]))
print(solve(sir, eliminate_at_least=3))
print(solve(sir, want={"x": "beta*N"}))
```

```text
SAT: normalize ['gamma', 'N'] (removes 2 >= 2).
UNSAT: only 2 independent scaling direction(s) act on ['beta', 'gamma', 'N'], so at most 2 of them can be removed (asked for 3).
UNSAT: x = N*beta is not dimensionless: scaling #2 multiplies it by lambda^1.
```

## Ask what data can tell you

```python
from nondim import analyze_identifiability

observed = Model.from_strings(
    "SIR_reported",
    equations={"S": "-beta*S*I", "I": "beta*S*I - gamma*I"},
    params="beta gamma rho",
    outputs={"y": "rho*I"},  # we only see a fraction rho of cases
)
print(analyze_identifiability(observed).summary())
```

```text
  NOT identifiable (moved by a scaling): ['beta', 'rho']
  parameter groups the data can see:     ['gamma', 'rho/beta']
```

## Let Lean check it

```bash
nondim init-lean proofs        # a Lean 4 + Mathlib project with the certificates
cd proofs && lake exe cache get && lake build
```

Every claim above becomes a theorem that Lean re-proves. From the SIR certificate:

```lean
theorem symmetries : Amat * Kmat = 0 := by decide +kernel
theorem rank_Apar : Apar.rank = 2 := by unfold Apar; eval_rank
theorem constraint2_unsat : 3 > Acand2.rank := by have h := constraint2_rank; omega
```

The Python code is never trusted: if it were wrong, the Lean build would fail.

## Check desr, too

[desr](https://github.com/ofloveandhate/desr) is the reference tool for this algorithm.
`nondim desr lotka_volterra` runs it, compares it with the solver above, and `nondim certify`
turns its answer into Lean theorems: its scalings are symmetries, and along every positive
solution its new variables satisfy its reduced equations. `nondim audit --fetch` runs the
solver over 190 published BioModels systems ([what it found](https://github.com/willmitchellcodes/verified-nondim/blob/main/docs/ODEBASE.md)).

## More

- `nondim tour` walks through all of this in seven steps; `nondim list` shows the built-in models.
- [Guide](https://github.com/willmitchellcodes/verified-nondim/blob/main/docs/GUIDE.md) · [the general theorems](https://github.com/willmitchellcodes/verified-nondim/blob/main/docs/THEORY.md) · [certifying desr](https://github.com/willmitchellcodes/verified-nondim/blob/main/docs/DESR.md) · [the math by hand](https://github.com/willmitchellcodes/verified-nondim/blob/main/docs/BACKGROUND.md) · [design decisions and sources](https://github.com/willmitchellcodes/verified-nondim/blob/main/docs/DECISIONS.md) · [testing](https://github.com/willmitchellcodes/verified-nondim/blob/main/docs/TESTING.md) · [examples](https://github.com/willmitchellcodes/verified-nondim/tree/main/examples/)
- Scope: right-hand sides built from products, quotients and sums of powers (no `exp` or `log`).
  Results are verified relative to the equations and unit links you supply.

MIT license.

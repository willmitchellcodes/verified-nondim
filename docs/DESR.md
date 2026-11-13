# Certifying desr

[desr](https://github.com/ofloveandhate/desr) is the reference implementation of the
Hubert–Labahn nondimensionalization algorithm, by the authors of Tanburn et al. (2025). This
package's own solver does the same job less generally. So instead of competing with desr, the
package can now **check desr's answers in Lean**: desr computes, Lean verifies, and neither
desr nor this package's Python has to be trusted.

```bash
pip install git+https://github.com/ofloveandhate/desr     # desr is not on PyPI
nondim desr lotka_volterra        # run desr, cross-check against our solver
nondim compare                    # both tools on every built-in model -> reports/desr_comparison.md
nondim certify                    # write Lean certificates, including desr's
cd lean && lake build             # Lean checks them
```

Without desr installed everything else works; the desr commands say how to install it and the
desr tests skip. Tested against desr 3.0.0 (commit `deff1c0`, Apache-2.0).

## The pipeline

```
 your model ──► desr ──► matrices A, V, W        ──► from_desr()  ──► HLReduction ──► Lean file
 (equations)            reduced equations            (adapter)        (checked,        (theorems Lean
                                                                       exact)           must prove)
                                                          ▲
 your model ──► our solver ─────────────────────────── from_nondim()   same form, same theorems
```

| Step | File | What happens |
|---|---|---|
| run desr | `nondim/desr_bridge.py` `to_desr`, `from_desr` | the model is rebuilt with desr's own classes; desr returns its scaling matrix, Hermite multiplier `V`, its inverse `W`, and the reduced system |
| neutral form | `nondim/hlform.py` `HLReduction` | time is separated from the other variables; `V` is split into auxiliary columns `Vi` and invariant columns `Vn`; a left-inverse certificate `G, d` is computed |
| check in Python | `HLReduction.check()` | every relation the Lean file will state is re-derived in exact arithmetic first, so a failure is reported with a readable reason |
| write Lean | `nondim/lean_export2.py` `certificate` | the theorems listed in `docs/THEORY.md` §6 |
| check in Lean | `lake build` | the only step that counts as proof |

The same `HLReduction` is produced from this package's solver (`from_nondim`), so both tools
are held to the same theorems and can be compared file by file
(`Certified/Desr/…` next to `Certified/Own/…`).

## What Lean proves about desr's answer

For Lotka–Volterra (`lean/NondimVerify/Certified/Desr/LotkaVolterra.lean`), in words:

1. The Lean data is the system `dx/dt = a x − b x y`, `dy/dt = −c y + d x y` (`eq_x`, `eq_y`).
2. desr's three scalings are symmetries of that system (`symmetry`).
3. desr's new variables `κ = c/a`, `ν₀ = d x/a`, `ν₁ = b y/a` do not change under any of them
   (`invariant`), and together with `a t` they are **all** there is: any unit-independent
   quantity is a function of them (`invariants_complete`, Buckingham Pi).
4. **Along every positive solution of the original system, `ν₀` and `ν₁`, followed in the new
   time `τ = a t`, satisfy `dν₀/dτ = ν₀ − ν₀ν₁`, `dν₁/dτ = −κν₁ + ν₀ν₁`** (`reduction_correct`).
5. The original solution can be rescaled to a solution of the same equations with `a = b = d = 1`
   and the same invariants (`cross_section`).
6. desr found as many scalings as exist, by an exponent matrix this package derives on its own
   (`kills_K`, `rank_K`, `rank_A`).

Point 4 is desr's actual claim, stated about the model's own solutions.

## desr and our solver, side by side

`nondim compare` regenerates this table (`reports/desr_comparison.md`).

| model | parameters | scalings (ours / desr) | left after (ours / desr) | same scalings | status |
|---|---|---|---|---|---|
| logistic | 2 | 2 / 2 | 0 / 0 | yes | certified |
| SIR without `N` | 2 | 2 / 2 | 0 / 0 | yes | certified |
| Lotka–Volterra | 4 | 3 / 3 | 1 / 1 | yes | certified |
| Michaelis–Menten | 4 | 2 / 2 | 2 / 2 | yes | certified |
| spurious (original) | 2 | 1 / 1 | 1 / 1 | yes | certified |
| spurious (substituted) | 2 | 2 / 2 | 0 / 0 | yes | certified |
| SIR with `N`, Michaelis–Menten with `s₀`, spurious (fixed) | | | | | not yet: unit links |
| SIR with reporting rate `ρ` | 3 | | | | not passed to desr: `ρ` is not in the equations |
| Rosenzweig–MacArthur | 6 | | | | not yet: rational right-hand side |

"Same scalings" means the two scaling matrices have the same row space. The two tools may
pick, order and name the invariants differently; that is a free choice, and each tool's choice
is certified in its own file.

A property test runs both tools on 120 randomly generated polynomial models. Whenever desr's
answer is in scope (59 of the 120 with the fixed seed) it must pass every check, be maximal,
and agree with ours on the scalings and the parameter count
(`test_random_models_desr_and_our_solver_agree`). Nine of desr's random-model answers are also
sent through Lean (`test_desr_on_models_nobody_hand_picked_is_accepted`).

## What the tests found

Three findings came out of testing rather than out of design. They are the best evidence that
the tests test something.

**1. The first certificate format was too narrow.** It stated desr's reduced equations for the
solution after rescaling onto the cross-section (auxiliary monomials set to 1). On the six
hand-picked models that is the same thing as desr's new variables. On random model 21,

    dx/dt = −a y − c x y²,      dy/dt = b x y − c x²,

desr returns `κ = a c⁴/b⁵`, `ν₀ = c³x/b³`, `ν₁ = c²y/b²`, `τ = a c t/b` and the reduced system
`dν₀/dτ = −ν₁ − ν₀ν₁²/κ`, `dν₁/dτ = −ν₀²/κ + ν₀ν₁/κ`. That is correct (checked by hand and now
by Lean). But on the cross-section `x = ν₀/κ³`, not `ν₀`, so the old statement was false for
this model and the check refused a right answer. No wrong certificate was ever produced; a
correct one could not be. The format was changed to state the claim for desr's own variables
along the original solution, which needed one new general theorem
(`hasDerivAt_newVariable`, `docs/THEORY.md` §5b). The model is kept as a regression test
(`test_regression_invariants_that_are_not_cross_section_coordinates`) and as Limits §10.

**2. desr reports a scaling that is not one.** For `dx/dt = 1 − x`, which has no scaling
symmetry, desr 3.0.0 returns a scaling matrix with one all-zero row. The adapter measures the
rank and reports "no scaling symmetry"
(`test_desr_reports_a_zero_scaling_for_a_model_without_symmetry`).

**3. A parameter that appears only in a measurement is invisible to desr.** For SIR with a
reporting rate, `ρ` occurs in the output `y = ρI` and not in the equations, so desr's system
has no `ρ`. The adapter refuses rather than certify a reduction of a different model.

## Scope, and how each limit is reported

Out-of-scope inputs raise `NotSupported` with a reason. They are never mis-certified, and
`nondim compare` prints the reason in the table.

| Not supported yet | Message contains | Why |
|---|---|---|
| unit links (`same_units`) | "unit links" | not yet expressed in the general Lean theory; desr handles them through initial conditions, which the adapter does not pass yet |
| rational right-hand sides | "polynomial" | `LaurentSystem` has monomial terms only |
| time in the equations | "autonomous" | the theory is for `dx/dt = f(x)` |
| desr's `dep_var` and `general` schemes | "scheme" | the new variables are then not "one state × parameters" (`docs/THEORY.md` §5b) |
| no scaling symmetry | "no scaling symmetry" | nothing to reduce |
| fractional powers (own solver) | "fractional powers" | the Hubert–Labahn form uses integer matrices |
| a parameter absent from the equations | "do not appear" | see finding 3 |

## What is trusted, and what is not

Not trusted: desr, SymPy, the adapter, the exporter. If any of them is wrong in a way that
matters, a Lean theorem fails to compile. Eighteen corruptions of a certificate, one defect
each, are all rejected (`test_corrupted_general_certificate_is_rejected`), and so is
a wrong reduced equation attributed to desr
(`test_a_wrong_answer_attributed_to_desr_is_rejected`).

Trusted: Lean's kernel and Mathlib; that the equations you typed are the model you meant; and
the reading of the theorem statements. The last one is why each certificate starts by proving
that its data is the equation in ordinary notation, and why the header comment of each file
restates the model, the invariants and the reduced system in plain text.

One statement is weaker than it looks: "no scaling was missed" compares desr with an exponent
matrix printed by this package's Python (re-derived independently in a test), not one derived
inside Lean. See `docs/THEORY.md` §7.

## Adding a model

```python
from nondim import Model
from nondim.desr_bridge import from_desr
from nondim.lean_export2 import write_certificate

m = Model.from_strings("Chemostat", {"s": "d*s0 - d*s - k*s*x", "x": "k*s*x - d*x"}, "d s0 k")
red = from_desr(m)                     # raises NotSupported with a reason if out of scope
print(red.summary())
write_certificate(red, "lean/NondimVerify/Certified/Desr/Chemostat.lean", "Desr.Chemostat")
```

Then add `import NondimVerify.Certified.Desr.Chemostat` to `lean/NondimVerify/Certified.lean`
(or add the model to `GENERAL` in `nondim/catalog.py` and run `nondim certify`) and `lake build`.

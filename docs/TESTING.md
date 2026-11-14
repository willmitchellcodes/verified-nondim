# Testing

Three layers, each mirroring the pipeline. Run everything with `./setup.sh`, or separately:

```bash
cd python && python -m pytest -q             # Python + bridge (Lean-dependent tests skip if Lean is missing)
python -m pytest -q -m "not lean"            # Python only, ~1 min
python -m pytest -q -m lean                  # only the tests that call Lean (several minutes)
cd ../lean && lake build                     # library + Lean unit tests
```

## 1. Python (`python/tests/`)

| File | What it pins down | How |
|---|---|---|
| `test_intlinalg.py` | exact integer linear algebra | 130 random matrices: `U·M = H`, `det U = ±1`, echelon shape, exact and complete kernels, lattice (not just rational) bases |
| `test_model.py` | equations → exponent matrix K | hand-computed exponent vectors, rational functions, rejection of exp/log/symbolic powers, `from_strings` |
| `test_scaling.py` | Framing 1 (solver) | parameter counts vs. literature for all models; `A·K = 0`; maximality `r = n − rank K`; scalings plugged directly into the equations; **every** maximal choice checked symbolically and numerically; normalizable ⇔ independent, by brute force over all subsets; textbook forms; Buckingham Pi |
| `test_constraints.py` | Framing 2 | SAT/UNSAT for **every keep-set and every k** of every model vs. exhaustive search; every failure reason for named groups; regrouped equations checked numerically |
| `test_identifiability.py` | Framing 3 | predicted non-identifiable directions = numerical null space of the sensitivity matrix (and nothing else is null); scaled parameters give identical data; experiment headline numbers |
| `test_hlform.py` | the solver-independent form of a reduction and the general-form Lean text | terms rebuild the equations exactly; no zero terms; every relation re-checked; **12 corruptions each rejected** before export; relations and the symmetry check redone from the Lean text by an independent reader; every out-of-scope input refused with its reason |
| `test_desr_bridge.py` (skips without desr) | certifying desr | desr's output passes every check and is maximal; desr and our solver agree on all supported models and on **120 random models**; textbook invariants and reduced systems; a wrong matrix or reduced equation "from desr" is caught; two regressions found by testing (see `docs/DESR.md`) |
| `test_sections.py` | unit links, minimal parameter count, identifiability, goal queries, rational systems (Python side and Lean text) | SIR keeps `R₀`; every scaling respects every link; the rank Lean is told equals the solver's; flagged parameters equal the Python analysis and nothing else is flagged; **each goal gets the theorem kind its answer calls for** and each "possible" carries a valid left inverse; quotients rebuild the rational equations exactly |
| `test_odebase.py` | the ODEbase pilot | the parser reads arithmetic and **refuses 13 code-like inputs**; made-up models in the real file format give the expected rows; totals in the report are consistent; unreadable files are reported, not guessed; runs on real files when a local clone exists |
| `test_notebook.py` | the teaching notebook | every code cell runs; the outputs the prose refers to are there |
| `test_cli.py` | usability | every command and every model's report runs and contains the key facts |
| `test_packaging.py` | what other people get | README examples are executed and must print what the README shows; the wheel builds, passes `twine check`, and contains the Lean project and the `nondim` command; `init-lean` copies a complete project; the publish scripts' dry runs push nothing |

## 2. Lean (`lean/NondimVerifyTest/`)

Lean tests are `example`s: if the file compiles, they pass.

| File | What it pins down |
|---|---|
| `Basic.lean` | `monomial` and `scale` evaluate correctly on numbers; `monomial_scale` on a toy system; a non-invariant monomial really changes |
| `Tactics.lean` | `rhs_check`, `decide +kernel`, `eval_rank` prove true claims of each generated shape, and the *negations* of wrong claims |
| `Theory.lean` | rank–nullity and maximality on a 2-quantity system small enough to check by eye |
| `SIR.lean` | definitions at concrete numbers; disease-free equilibrium; threshold both ways; a constant solution maps to a constant solution |
| `Certificates.lean` | generated certificates + general lemmas ⇒ "R0 is invariant under every scaling of SIR", textbook counts for all six certified models |
| `System.lean` | a model as data evaluates to its equation; symmetries accepted and wrong ones refused by computation; an explicit solution (`x₀ + k t`) carried by `map_solution` to the solution with rate `k/λ`; `param_const`; normalizing; the empty cases (no scalings, nothing to normalize) |
| `Criterion.lean` | clearing denominators; both certificates and their exclusivity; the equivalence on a 2×3 scaling matrix (any two parameters yes, all three no); rank form at `k = 0` and `r = 0` |
| `BuckinghamPi.lean` | the pendulum: `T²g/L` is the only group, **the period law cannot involve the mass**; factorized form; the count 4 − 3 = 1; a dimensional quantity is not unit-invariant |
| `Reduction.lean` | the logistic model by hand through both reduction theorems; desr's certificates used as facts (reduced SIR, `κ = c/a`, Pi-completeness); desr and our solver found equally many scalings |
| `Identifiability.lean` | the SIR conservation law is homogeneous under the reduction's scalings and not under "scale `S, I, R` but not `N`", which is nevertheless a symmetry of the equations (a spurious reduction, made concrete); a three-variable model where the gain and the rate are proved non-identifiable; the generated SIR-with-reporting certificate |
| `Rational.lean` | a saturating response by hand: symmetries accepted and refused from numerator and denominator; the general theorems applied; `frac_reduce`; empty numerator and denominator; the Rosenzweig–MacArthur certificates of both tools |
| `Limits.lean` | **every hypothesis is needed**: fourteen sections, each a concrete case where a hypothesis fails and the conclusion fails with it (see below) |

## 3. The bridge between Python and Lean

| Test | Needs Lean? | What it shows |
|---|---|---|
| `test_lean_export.py::test_every_theorem_is_understood_and_true` | no | An independent reader (`tests/lean_reader.py`, no shared code with the exporter) re-parses every certificate, for **every choice of every model**, and re-checks every theorem. Unrecognized theorem shapes fail the test. |
| `…::test_certificates_on_disk_are_up_to_date` | no | The `.lean` files in the repo are byte-identical to what the solver produces now |
| `…::test_to_lean_round_trips_numerically` | no | The expression printer preserves values |
| `test_lean_build.py::test_lake_build_passes` | yes | Lean accepts everything |
| `…::test_every_choice_of_every_model_is_accepted` | yes | Lean accepts the certificate of each of the 39 maximal reductions of the built-in models, not just the six in the catalog |
| `…::test_key_theorems_do_not_depend_on_sorry` | yes | `#print axioms` on the main theorems and sample certificate theorems shows no `sorryAx` |
| `…::test_corrupted_certificate_is_rejected` | yes | Twelve one-defect mutations of the SIR certificate (wrong scaling, wrong rank, sign error, UNSAT claimed SAT, …) are each **rejected**. This is the test that shows the checker has teeth. |

| `test_lean_build.py::test_corrupted_general_certificate_is_rejected` | yes | Eighteen one-defect mutations of a general-form certificate (data is not the equation, scaling not a symmetry, invariant with units, wrong time factor, factor that uses a state, sign error or dropped term in a reduced equation, incomplete Pi certificate, overclaimed ranks, …) are each **rejected** |
| `…::test_corrupted_section_is_rejected` | yes | Seventeen more one-defect mutations, of the optional sections and of a rational certificate (a link a scaling breaks, an overclaimed parameter rank, "two cannot be removed" when they can, a goal certificate that does not certify, a dimensionless claim for a group with units, an output scaling that changes the data, identifiability claimed for an unmoved parameter, a changed denominator, a sign error in a reduced numerator, …) are each **rejected** |
| `…::test_certificate_with_optional_sections_is_accepted` | yes | the unmutated certificates of SIR, SIR with reporting, Rosenzweig–MacArthur and Michaelis–Menten with initial conditions compile |
| `…::test_edge_models_are_accepted_in_the_general_form` | yes | Boundary inputs (negative exponents, rational coefficients, a single scaling, higher powers, Holling II, a Hill function, repression) produce certificates Lean accepts |
| `…::test_desr_on_models_nobody_hand_picked_is_accepted` | yes, and desr | desr's answers for 8 random models and for the regression model compile |
| `…::test_a_wrong_answer_attributed_to_desr_is_rejected` | yes, and desr | changing one of desr's reduced equations makes the build fail |

## The limits file (`lean/NondimVerifyTest/Limits.lean`)

A theorem whose hypothesis could be dropped is stated too weakly, and a test suite that never
shows a conclusion failing is not testing the hypotheses. Each section is a counterexample
checked by Lean.

| § | Hypothesis | What goes wrong without it |
|---|---|---|
| 1 | the scaling is a symmetry | `dx/dt = 1`: doubling `x` turns the solution `t` into `2t`, which is not a solution |
| 2 | (definition) symmetry is checked on the written terms | `0·x⁵` fails the check though its solutions are preserved: sufficient, not necessary |
| 3 | parameter values are positive | 0 and negative values cannot be scaled to 1 |
| 4 | the parameters in `S` are distinct | listing one parameter twice gives a kernel vector, yet normalizing is possible |
| 5 | `d ≠ 0` in the left-inverse certificate | with `d = 0` the certificate is vacuous; with `d = 2` it is genuine and needs a square root |
| 6 | the groups span | forget the ratio of two lengths and a unit-free quantity is not a function of the (zero) groups |
| 7 | quantities are positive | "is it positive?" is unit-free and separates `1` from `−1` |
| 8 | (generality) spanning, not unimodularity | `(ab)²` is a valid single group although `(2,2)` is not primitive |
| 9 | (boundary) no scalings | reduction is the identity |
| 10 | (design) cross-section coordinates ≠ the tool's variables | desr's matrix for the regression model gives `x = ν₀/κ³` |
| 11 | (one-way) no scaling moves the parameter | `dx/dt = a − b` seen through `x`: no output-preserving scaling moves `a`, yet `a` is not identifiable |
| 12 | the output-preserving scaling does not rescale time | `dx/dt = k` seen through `x`: the time-unit scaling fixes the value of `x`, yet `k` **is** identifiable |
| 13 | "for every positive value" in the count | two parameters that scale together can both be normalized when their values happen to be equal |
| 14 | (definition) denominators are nonzero | a quotient with a vanishing denominator evaluates to 0; the theorems hold there and say nothing |

## What the tests do not show

Tests on eleven built-in and a few hundred random models are evidence, not proof, of the general
claims; the general proofs are in `System`, `Criterion`, `BuckinghamPi`, `Reduction` and
`Theory`, and what remains open is listed in `docs/THEORY.md` §11. Nothing here
validates the biological meaning of a model or of a chosen scaling.

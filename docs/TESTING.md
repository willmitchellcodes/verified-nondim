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

## What the tests do not show

Tests on eleven models are evidence, not proof, of the general claims; the general proofs
that exist are in `Theory.lean`, and the open ones are in `Exercises.lean`. Nothing here
validates the biological meaning of a model or of a chosen scaling.

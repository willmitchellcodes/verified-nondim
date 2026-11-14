# Decision record: how and why things are done this way

Each entry gives the decision, the reason, the evidence, and the source. Evidence is one of:

* **[tested]**: checked by a test in this repository (the test is named);
* **[proved]**: a Lean theorem in `lean/` (the theorem is named);
* **[literature]**: taken from a paper. Theorem and example numbers were collected during
  background research and have **not** been re-checked against the PDFs line by line. Check
  them before quoting them in the proposal or report.
* **[synthesis]**: our own formulation, not a published result.

Sources are listed in full at the end, keyed like [HL13].

## Status on 2026-11-13

* `python -m pytest -q`: **847 tests pass** (783 Python/bridge/packaging + 64 that call Lean).
  Without desr installed: 782 pass and 3 skip (the desr test module and two Lean tests).
* `lake build`: **passes** with Lean 4.35.0 / Mathlib v4.35.0 (2512 jobs): the general theory
  (`System`, `Criterion`, `BuckinghamPi`, `Reduction`, `Rational`, `Identifiability`), 28
  certificates in the general form (11 from this package's solver, 7 from desr, 10 for
  published ODEbase models), the 6 matrix-level certificates of the first release, `Basic`,
  `Theory`, `SIR`, and 12 Lean test files. No `sorry` outside `Exercises.lean`;
  `#print axioms` on 57 theorems shows only Lean's three standard axioms.
* Where this was run: the numbers above are from the assistant's cloud workspace, with desr
  3.0.0 installed from source. Natively on the Mac (2026-11-13, branch `general-theory`,
  Python 3.13, commit `d6547d3`): `lake build` passed (2493 jobs) and the suite gave 613
  passed, 3 skipped, without desr. **Everything after that commit (D32–D39) has been built and
  tested only in the cloud workspace**, as have all tests that need desr.
* Packaging: unchanged from 0.1.0; the new Lean files are bundled with the wheel through the
  existing directory rule, and `test_wheel_contains_…` still passes.
* **Not yet exercised:** the GitHub Actions workflows with the desr step (template in
  `scripts/workflows/ci.yml`), and any release after 0.1.0.

---

## Architecture

### D1. Untrusted solver (Python) + trusted checker (Lean)
**Decision.** Python computes the nondimensionalization. Lean never runs the algorithm; it
only re-proves the *answers* (matrix identities, ranks, equations).
**Why.** Verifying a Hermite-normal-form algorithm in Lean is research-level work. Checking
its output is a few matrix products. This is the standard "certificate checking" pattern, and
Mathlib's own `linarith`, `linear_combination` and `eval_rank` work this way.
**Evidence.** [tested] `test_lean_build.py::test_corrupted_certificate_is_rejected`: twelve
single-defect corruptions of the SIR certificate are each rejected by Lean, so a solver bug
of any of those kinds cannot pass silently. `test_every_choice_of_every_model_is_accepted`:
Lean accepts the certificate of every one of the 39 maximal reductions of the built-in models.
**Source.** Mathlib tactic docs [ML].

### D2. Scaling symmetries, not just Buckingham Pi
**Decision.** Read the scalings off the *equations* (exponent matrix K, scalings = integer left
kernel of K) instead of only from declared physical units.
**Why.** The equations can admit more scalings than there are physical units, which removes
more parameters. Lotka–Volterra has 2 physical units (time, individuals) but 3 scalings,
because prey and predator counts rescale independently: 4 parameters → 1, not 2.
**Evidence.** [tested] `test_scaling.py::test_scaling_beats_buckingham_on_lotka_volterra`
(5 Pi groups vs. 4 invariants); `test_declared_units_are_symmetries_of_the_equations` (the
physical units are always among the scalings found).
**Source.** [HL13] (maximal scaling matrix via Hermite normal form); [T25] (biology-facing
version, "structural" units).

### D3. Invariance test: every monomial of `t·f_i/z_i` must be invariant
**Decision.** Build K from the monomials of `t·f_i/z_i`; for rational right-hand sides use
exponent *differences* against a reference monomial of the denominator.
**Why.** A scaling maps solutions to solutions exactly when each `t·f_i/z_i` is invariant.
**Evidence.** [tested] `test_scalings_really_are_symmetries_of_the_vector_field` plugs scaled
numbers straight into the original equations, independently of K, for every model.
[proved] `NondimVerify.monomial_scale`: if `A *ᵥ k = 0` then the monomial with exponents `k`
is unchanged by the scalings `A`, for all nonzero scale factors.
**Source.** [T25] Lemma 3.1 [literature].

### D4. Integer row reduction with a unimodular transform
**Decision.** `intlinalg.int_row_echelon` returns `U` with `det U = ±1` and `U·M = H`; the
kernel basis is the rows of `U` below the pivots.
**Why.** Gaussian elimination over ℚ gives a rational basis. A unimodular `U` gives a basis of
the integer *lattice*, so no exponent is needlessly fractional and no symmetry is lost.
**Evidence.** [tested] `test_intlinalg.py`: 60 random matrices checked for `U·M = H`,
`|det U| = 1`, echelon shape; 40 for exact, complete kernels;
`test_kernel_basis_is_a_lattice_basis_not_just_a_rational_one`.
**Source.** [HL13] §2 (Hermite normal forms) [literature].

### D5. Reduce by "normalize a chosen set S of parameters to 1"
**Decision.** Choose S with independent columns in A; each kept variable becomes
`x̂ = x·∏ s^{e_s}` with `A_S e = −A_x`; the reduced right-hand side is the old one with
`s := 1`.
**Why.** It is the form used in textbooks (τ = γt, X = S/N), every output is easy to read,
and all choices S are enumerable, which makes non-uniqueness visible.
**Trade-off.** [HL13]/[T25] instead take a Hermite multiplier `V` and get integer-exponent
invariants by construction. Our form can give fractional exponents when `A_S` is not
unimodular. It did not happen in any built-in model; the code detects it
(`integer_exponents()`) and then skips the Lean equation check rather than emit a wrong one.
**Evidence.** [tested] `test_every_maximal_choice_is_correct` (all 39 maximal choices across all
models: chain rule, dimensionless, numerics); `test_new_variable_formula`;
`test_sir_textbook_form_gives_R0`.

### D6. Unit links are explicit model input (`same_units` / `extra_invariants`)
**Decision.** The modeler states which quantities share units when the equations do not force
it (totals, initial values, lumped sums).
**Why.** Without them the algorithm can find *spurious* symmetries. `dx/dt = (a+b)x + b`
rewritten with `c = a+b` appears to lose both parameters; the truth is one.
**Evidence.** [tested] `test_spurious_symmetry_failure_mode` (1 → 2 → 1 scalings).
**Source.** [T25] Example 3.12 and Theorem 3.14 [literature].
**Consequence.** This is the main trust assumption of the whole pipeline. Lean verifies the
reduction *relative to* the unit links supplied (see D15).

---

## Framing 2: constraints

### D7. Rank criterion for "eliminate ≥ k while keeping P"
**Decision.** SAT iff `rank(A restricted to parameter columns not in P) ≥ k`.
**Why.** With positive parameters, a set S can be normalized together iff its columns of A
are independent. Independent column sets form a matroid, so greedy selection is optimal and
no SAT/ILP solver is needed. Both verdicts have small certificates: a rank.
**Evidence.** [tested] `test_normalizable_iff_columns_independent_brute_force` (every subset
of parameters of every model); `test_rank_criterion_agrees_with_brute_force_for_every_keep_set`
(every keep-set and every k of every model, against exhaustive search).
[proved, per model] `constraintN_enough` / `constraintN_unsat` in each certificate.
**Status.** [synthesis] from [HL13] Thm 7.1 and [T25] Thm 3.5. The general "iff" is stated as
Exercises 2–3 in `lean/NondimVerify/Exercises.lean` and is **not yet proved in Lean**. What
*is* proved in general (`Theory.lean`): the scalings form a space of dimension `n − rank K`
(`finrank_scalingSpace`), and independent scalings of that number span all of them
(`maximal_of_rank`).

### D8. What "keep p" means
**Decision.** `keep=[p]` means *p is not normalized to 1*. Each surviving group then contains
exactly one un-normalized parameter (to the first power) times normalized ones, e.g. keeping
`c` in Lotka–Volterra leaves `c/a`.
**Why.** It is the weakest useful meaning and it has a clean rank test. The stronger request
"this exact expression must be a parameter" is D9.

### D9. Named groups (`want={"R0": "beta*N/gamma"}`)
**Decision.** Wanted groups are accepted iff each is a parameter-only monomial, each is
invariant (`A·w = 0`), and together they are independent. The reduced parameters are then
re-expressed through an invertible exponent matrix `M`; if `M` is unimodular no fractional
powers are needed.
**Why.** This is the practically important constraint: the modeler wants R₀ or ε to appear.
**Evidence.** [tested] `test_wanted_group_verdicts_on_sir` (11 cases, every failure reason);
`test_regrouping_is_correct` (7 cases, numeric identity + invariance + invertibility);
`test_non_primitive_group_needs_fractional_powers`.
[proved, per model] `constraintN_want_invariant`, `_want_independent`, `_regroup_unimodular`,
`_regroup_<state>`; for UNSAT: `_want_not_invariant`, `_want_dependent`.
**Source.** Modeled on [T25] Theorem 3.8 (preferred invariants extend to a unimodular matrix,
tested with Smith normal form) [literature]. Ours is a simplified rational-exponent version
[synthesis].
**Known limit.** Non-monomial groups such as Segel–Slemrod's `e0/(s0 + Km)` are rejected
(`not_monomial`) with no Lean certificate, because the claim "outside the method" is not a
matrix fact. [SS89]

---

## Framing 3: identifiability and data

### D10. One-way symbolic test
**Decision.** Parameters moved by a scaling that fixes time and all outputs are reported "NOT
identifiable"; the rest are reported only as "not flagged".
**Why.** A scaling symmetry of the outputs proves non-identifiability. Its absence proves
nothing, because other Lie symmetries exist.
**Evidence.** [tested] `test_predicted_directions_are_exactly_the_numerical_null_space`: for
SIR-with-reporting and for Lotka–Volterra observing prey, the predicted directions are null
vectors of the numerical sensitivity matrix, and the numerical nullity equals the number of
predicted scalings. `test_lotka_volterra_observing_prey_only` reproduces the known
`b → λb, y → y/λ` example.
**Source.** [MV20], [VM21] (warning that scaling-only tests can mislead);
StructuralIdentifiability.jl docs [SI] for the Lotka–Volterra example [literature].

### D11. Synthetic-data experiment, deterministic seeds
**Decision.** `experiment_sir.py` fits SIR with unknown reporting fraction to synthetic data:
multi-start fits, loss along vs. across the symmetry, and reduced-model fits under sparse,
truncated and noisy data.
**Why.** It ties the algebra to the course's theme (fitting models, robustness to missing
data) and makes "non-identifiable" visible. Synthetic data are used because the truth is known.
**Evidence.** [tested] `test_experiment_headline_results`: raw parameters differ by >2× across
equally good fits while invariant groups agree to <1%; loss is flat (<1e-6) along the scaling.
**Caveat.** Raw-parameter fits are confined to within 100× of the truth; the reported spread
(≈20×) depends on that box and on the random starts. The qualitative conclusion does not.

---

## Lean

### D12. Dimensions as plain integer vectors, not dependent types
**Decision.** Quantities are indexed `Fin n`; exponents are `Fin n → ℤ`; no dimension-typed reals.
**Why.** Existing Lean unit libraries report friction from types like `Scalar (d₁+d₂)` vs.
`Scalar (d₂+d₁)`. Matrix facts are all this project needs.
**Source.** [B25]; Tao's `UnitsSystem.lean` comments [TAO] [literature].

### D13. Proof methods per claim
| claim | tactic | reason |
|---|---|---|
| integer matrix identity | `decide +kernel` | small, closed, decidable; checked by the kernel |
| rank of an integer matrix | `eval_rank` | Mathlib tactic that builds and checks an elimination certificate |
| reduced equation = rescaled original | `rhs_check` (`ring1`, else `field_simp; ring1`) | identity of rational functions with positive variables |
| inequalities on ranks | `omega` after the rank theorem | linear arithmetic over ℕ |

`polyrith` is not used: its external server was shut down [ML].

### D14. Pinned versions, narrow imports
**Decision.** Lean 4.35.0 and Mathlib `v4.35.0` are pinned (`lean-toolchain`, `lakefile.toml`,
`lake-manifest.json`). `Basic.lean` imports only the Mathlib modules it needs.
**Why.** Mathlib changes weekly; `eval_rank` is recent. Pinning makes results reproducible.

### D15. What is and is not verified (the verification gap)
*Updated after D23–D31; items 3 and 4 of the original list are now closed.*

Verified by Lean, per model: checks 1–8 in the README table, plus constraint verdicts.
Verified by Lean, in general: `monomial_scale`, `finrank_scalingSpace`, `maximal_of_rank`,
and for SIR the two-way correspondence of solutions and equilibria and the R₀ threshold.

**Not** verified:
1. that the equations and unit links typed into Python are the intended model (D6);
2. that the exporter printed the same model the solver analysed. Mitigation: [tested]
   `test_lean_export.py` re-parses every certificate with an independent reader and re-checks
   every theorem, and `test_certificates_on_disk_are_up_to_date` catches stale files;
3. ~~the general rank criterion (D7)~~ now [proved]: `normalizable_iff_rank` (D25);
4. ~~solution correspondence for models other than SIR~~ now [proved] for every polynomial
   system (`IsSymmetry.solution_iff`, D24), and the reduced equations for every model with a
   general-form certificate (`reduction_correct`, D28), which since D33 and D36 includes the
   models with unit links and with rational right-hand sides;
5. anything numerical: floating point, ODE solvers, fits;
6. that a reduction is *useful* (interpretable, right small parameter);
7. that the exponent matrix used for "no scaling was missed" is the model's: it is still a
   literal printed by Python (D29).

---

## Testing

### D16. Three layers, mirrored on the pipeline
* Python unit tests (`python/tests/test_*.py`): each module, plus brute-force cross-checks.
* Lean unit tests (`lean/NondimVerifyTest/`): definitions, tactics, theorems on tiny cases,
  and certificates combined with general theorems.
* Bridge tests: without Lean (`test_lean_export.py`, independent re-reader) and with Lean
  (`test_lean_build.py`, full build + corrupted certificates must fail).

See `docs/TESTING.md`.

### D17. A bug the tests caught
While adding named groups, the exporter paired a constraint's regrouped equations with the
*file's* main reduction instead of the constraint's own witness. The independent re-reader
flagged `constraint4_regroup_S` as false before Lean ever ran. Fix: the constraint section
now uses `c.witness`. This is the reason the re-reader shares no code with the exporter.

---

## Packaging and release

### D18. Names, license, author (chosen by the project owner, 2026-11-13)
**Decision.** PyPI distribution `verified-nondim`; import name and command `nondim`; GitHub
repository `verified-nondim`, public; MIT license; author shown as name only, no email.
**Evidence.** PyPI's JSON API returned 404 for `verified-nondim` and `nondim` on 2026-11-13, so
both were unclaimed that day. [tested] `test_wheel_contains_package_lean_template_and_entry_point`
checks the built metadata (name, `License-Expression: MIT`, author, no email address).

### D19. The Lean project ships inside the wheel
**Decision.** The wheel contains the whole `lean/` project as `nondim/_lean_template/`;
`nondim init-lean DIR` copies it out.
**Why.** A certificate is only useful next to the Lean library that states what it means.
Without bundling, `pip install` would give a solver whose output nobody could check.
**Evidence.** [tested] `test_init_lean_copies_a_complete_project` (byte-identical to `lean/`),
`test_cli_init_lean_then_certify_into_it`. Run once by hand: wheel installed in a clean
environment, `nondim init-lean`, `lake build` → 2459 jobs, no errors.

### D20. Publishing runs under the owner's accounts, with a preview and a confirmation
**Decision.** `scripts/publish_github.sh` and `scripts/publish_pypi.sh` are run by the owner in
their own Terminal. Both have a no-upload mode (`DRY_RUN=1`, `check`) and ask "Type yes" before
anything public. PyPI can also be reached with no stored secret through trusted publishing
(`scripts/workflows/publish.yml`). The GitHub Actions files are kept as templates in
`scripts/workflows/`; the owner copies them into `.github/` by hand, because the assistant's
file tools are not permitted to write there.
**Why.** A public repository and a PyPI release are effectively permanent, so the person whose
name is on them should trigger them.
**Evidence.** [tested] `test_publish_github_dry_run_commits_locally_and_pushes_nothing`,
`test_publish_github_dry_run_with_gh_never_creates_a_repository`,
`test_set_repo_url_is_idempotent_and_makes_links_absolute`.
**Source.** [PYPI-TP], [PYPA-GUIDE] for trusted publishing; [LEAN-ACTION] for the CI Lean job.
The workflow files follow those documents but have not run yet.

### D21. A short README whose examples are executed by the tests
**Decision.** `README.md` is under 110 lines and built from four examples; the long guide moved
to `docs/GUIDE.md`.
**Evidence.** [tested] `test_readme_python_examples_run_and_print_what_the_readme_shows` runs
every Python block and requires every output line shown in the README to be printed;
`test_readme_lean_snippet_is_taken_from_the_real_certificate`.

### D22. Personal course notes stay out of the public repository
**Decision.** `docs/PROPOSAL_NOTES.md` is listed in `.gitignore` and excluded from the source
archive. It stays on disk.

---

## General theory and desr (after 0.1.0)

Guides: `docs/THEORY.md` (the theorems) and `docs/DESR.md` (certifying desr).

### D23. Certify desr instead of competing with it
**Decision.** Add an adapter that runs desr and turns its output into a Lean certificate;
keep this package's solver as a second, independent implementation held to the same theorems.
**Reason.** desr is the reference implementation of [HL13]/[T25] and is more general than our
solver (initial conditions, three reduction schemes, large models). A second solver adds
little; a proof that the reference tool's answer is right adds something no tool in this area
offers. Two independent implementations that must agree are also a strong test of both.
**Evidence.** [tested] `test_desr_and_our_solver_agree`, `test_random_models_desr_and_our_solver_agree`
(59 random models in scope, all agree); [proved] `Certified/Desr/*.lean`.
[literature] a web search for proof-assistant verification of nondimensionalization or of
scaling-symmetry reduction of ODEs found none; this is a limited search, not a survey.

### D24. A model is data (`LaurentSystem`), and symmetry is decided from the data
**Decision.** Represent a system as lists of terms (coefficient, integer exponent vector), not
as Lean functions. Each certificate proves the data evaluates to the written equation.
**Reason.** With data, "is this scaling a symmetry?" is a finite computation Lean decides
itself (`decide`), so the symmetry claim no longer depends on an exponent matrix supplied by
Python, and the general theorems can quantify over all systems. Integer exponents (Laurent
terms) cover every in-scope model, including ones with division by a state.
**Cost.** Rational right-hand sides do not fit and keep their 0.1.0 certificates.
**Evidence.** [proved] `IsSymmetry.map_solution`, `solution_iff`; [tested]
`test_terms_rebuild_the_equations_exactly`, `test_symmetry_can_be_rechecked_from_the_lean_text`,
mutations `data_is_not_the_equation_*`.

### D25. The constraint criterion as an equivalence, with certificates for both answers
**Decision.** Prove "yes" from a left inverse `G·A_S = d·1`, "no" from a kernel vector, and
that one of the two always exists; conclude `normalizable_iff` and `normalizable_iff_rank`.
**Reason.** A left inverse or kernel vector is checked by one integer matrix product, which is
cheaper and more transparent than a rank computation, and both are explicit witnesses a reader
can inspect. The dichotomy turns two implications into the equivalence D7 relied on. `d ≠ 1`
covers scalings that need roots, which unimodular (Hermite) methods cannot express.
**Evidence.** [proved] `exists_normalizing_scaling`, `not_normalizable_of_kernel_vector`,
`left_inverse_or_kernel`, `normalizable_iff_rank`; Limits §3–§5 show each hypothesis is needed.
[synthesis] the statement and proof are ours; the underlying fact is standard linear algebra.

### D26. Buckingham Pi in the form "unit-independent ⟹ function of the groups"
**Decision.** Prove the theorem for arbitrary functions on positive quantities, with the
spanning hypothesis dischargeable from integer identities (`spans_kernel_of_certificate`).
**Reason.** The counting half (number of groups = n − rank) is what tools compute; the
half about functions is what users rely on when they say the reduced model "loses nothing".
[literature] [B25] sets up dimensions in Lean 4 and states that it implements the theorem; from
its abstract and text this is the counting/kernel side. [BJ23] treats the theorem in a
dependently typed language and discusses why the textbook statement is not constructive. Two
web searches found no Lean proof of the function half. Not checked against the PDFs line by
line: verify before claiming priority.
**Evidence.** [proved] `buckingham_pi`, `buckingham_pi_factorization`; [tested] the pendulum
(`mass_is_irrelevant`), Limits §6–§8.

### D27. Parameters are constant: proved, not assumed
**Decision.** Derive constancy of parameters from the system (zero derivative ⟹ constant).
**Reason.** An assumed hypothesis is one more thing a reader must trust. Cost: ten more Mathlib
modules (mean value theorem) in the import closure.
**Evidence.** [proved] `IsSolution.param_const`.

### D28. State the reduced equations for the tool's own variables along the original solution
**Decision.** `reduction_correct` says: along every positive solution of the original system,
the tool's new variables, in the tool's new time, satisfy the tool's reduced equations. The
cross-section statement is kept as a separate theorem (`cross_section`).
**Reason.** The first format stated the reduced equations on the cross-section. That coincides
with the tool's variables for all textbook models and fails in general (D31). The new statement
is the claim the tool actually makes and needs one identity per equation.
**Evidence.** [proved] `IsSolution.hasDerivAt_newVariable`; [tested]
`test_regression_invariants_that_are_not_cross_section_coordinates`; Limits §10.

### D29. Scope of the first version, and how limits are reported
*Superseded in part: unit links (for this package's solver) by D33, rational right-hand sides by D36.*
**Decision.** Support desr's "parameter" scheme on autonomous polynomial systems without unit
links. Everything else raises `NotSupported` with a reason and appears in the comparison table.
**Reason.** In the parameter scheme each new state variable is one state times parameters,
which is what D28's theorem needs. Unit links need initial conditions passed to desr and a
Lean notion of "same units"; both are possible and neither is small.
**Known gap.** "No scaling was missed" uses a literal exponent matrix (D15 item 7).
**Evidence.** [tested] `test_unsupported_models_are_refused_with_a_reason`,
`test_edge_models_are_refused_with_a_reason`, `test_compare_never_raises_on_any_builtin_model`.

### D30. desr is an optional dependency installed from source
**Decision.** No entry in `pyproject.toml`; the commands print the install line and the tests
skip when desr is missing.
**Reason.** desr is not on PyPI, and PyPI rejects packages whose metadata depends on a direct
URL. Pinning a commit in documentation (`deff1c0`, version 3.0.0) keeps results reproducible.
**Evidence.** [tested] the suite passes without desr (782 passed, 3 skipped) and with it (847),
both in the cloud workspace; natively without desr at commit `d6547d3` (613 passed, 3 skipped).

### D31. Three things the tests found
1. **A too-narrow certificate format** (D28): random model 21 has a correct desr answer the
   first format could not certify. Found by `test_random_models_desr_and_our_solver_agree`.
2. **desr reports an all-zero scaling** for a model with no symmetry (`dx/dt = 1 − x`). The
   adapter uses the rank. `test_desr_reports_a_zero_scaling_for_a_model_without_symmetry`.
3. **A parameter that appears only in an output** never reaches desr; the adapter refuses.
These are recorded because each was invisible on the hand-picked models (compare D17).

---

## After the literature search (2026-11-13)

A literature search was run to answer "what would make this novel, or better, useful". Its
report ranked seven directions. D32 records which were taken and why; D33–D38 record how.
Guides: `docs/THEORY.md` §6–§9, `docs/ODEBASE.md`, `examples/walkthrough.ipynb`.

### D32. Which directions were implemented
| Direction from the search | Done? | Why |
|---|---|---|
| Certified audit of ODEbase | pilot (D37) | the clearest opening for an empirical contribution; a pilot shows the pipeline runs on real models |
| Proved "scaling ⟹ non-identifiable" | yes (D34) | identifiability is the downstream use with real users, and the one-way nature can be proved, not just stated |
| Goal-directed reductions with SAT/UNSAT certificates | algebraic part (D35) | "why can this not be done" is what existing tools do not explain |
| Unit links, conservation laws, SIR with `R₀` | yes (D33) | needed for the course's central example |
| Tanburn et al.'s change-of-variables theorem | **no** | its exact statement was not read; formalizing a paraphrase would be dishonest |
| Rational right-hand sides | yes (D36) | most models in the course text and in BioModels are rational |
| Lean-native `#nondim` command | **no** | the search rated it small marginal value |
| Cross-check with StructuralIdentifiability.jl | **no** | needs Julia; recorded as the next step for D34 |
| Teaching notebook | yes (D38) | the right course deliverable |
**Evidence.** [literature] the search report (summarized in `docs/CONTRIBUTIONS.md`); its own
caveats apply: about twenty searches, several sources read through abstracts.

### D33. Unit links as invariant ratios; conservation laws as homogeneous relations
**Decision.** A link "`a` is measured like `b`" is the exponent vector of `a/b`, and a
certificate proves `A * Links = 0`. A polynomial relation is respected when it is homogeneous
(`IsHomogeneous`, decidable), and then `poly_scale_eq_zero_iff` says scaling preserves it.
**Reason.** Both are finite checks on exponents, so Lean decides them from the data; and they
are the same condition, which lets the ODEbase importer turn laws into links without new theory.
With links in the general form, SIR with `N` is certified with `R₀ = βN/γ` as the surviving
parameter. [T25] is the source for why this matters (spurious reductions).
**Evidence.** [proved] `IsHomogeneous.poly_scale_eq_zero_iff`, `Certified.Own.SIR.links_respected`;
[tested] `test_every_scaling_respects_every_unit_link`, the SIR example in
`NondimVerifyTest/Identifiability.lean` (a symmetry of the equations that breaks `S+I+R=N`).

### D34. Identifiability: prove the one direction, and prove that it is only one direction
**Decision.** Theorem `IsSymmetry.not_identifiable` (output-preserving, time-fixing scaling ⟹
twin solution). Two Lean counterexamples fence it: a non-identifiable parameter no scaling
moves (Limits §11), and an identifiable parameter moved by a scaling that rescales time
(Limits §12).
**Reason.** [CdB20] proposed testing identifiability by scalings; [VM21] showed it can miss
non-identifiability, and the authors agreed it is a necessary condition only. A tool that
states the sound direction and machine-checks its blind spot cannot be misread as a complete
test. `Identifiable` is defined globally (all solutions, all times), which is stronger than the
usual generic notion; the theorem is stated in the "every solution has a twin" form, which
does not depend on that choice.
**Evidence.** [proved] the theorem and both counterexamples; [tested]
`test_identifiability_section_agrees_with_the_python_analysis`. [literature] no formalization
of identifiability in a proof assistant was found (one search; low confidence).

### D35. Every goal answered with a proof; the minimal parameter count
**Decision.** Each request in the catalog becomes `goal<k>_possible` or `goal<k>_impossible`
in the model's certificate, and every certificate proves `cannot_remove_more`.
**Reason.** A "yes" with scale factors and a "no" with the obstruction are both checkable by
a single matrix identity or rank, so the answer does not rest on the solver. The count is the
statement users quote ("at least `p − ρ` parameters remain"); Hawi & Wechselberger [HW26]
compute such counts, here it is proved per model.
**Not done.** Non-algebraic goals (small parameters, variables of order one), which [HW26]'s
tool addresses heuristically.
**Evidence.** [proved] `not_normalizable_of_rank_lt`, `monomial_not_invariant`; [tested]
`test_every_goal_gets_the_theorem_its_answer_calls_for`, nine goal mutations rejected by Lean.

### D36. Rational systems as a second structure with the proofs repeated
**Decision.** `RatSystem` (sums of quotients of polynomials) next to `LaurentSystem`. Only
`rhs_scale` is new mathematics; the later theorems are textual copies of the polynomial ones.
Certificates reduce each quotient with two division-free identities and `frac_reduce`.
**Reason.** Abstracting both over "a vector field covariant under the scaling" is cleaner but
would have touched every existing statement, certificate and test. Copying kept 675 passing
tests untouched. No nonzero-denominator hypothesis is needed (division by zero is zero on
both sides), which avoids asking generated proofs to show denominators positive.
**Cost.** Duplicated proofs (about 150 lines) to be unified later; for rational models the
equality between the quotient form and the tool's printed reduced equation is checked by
SymPy, not Lean; the identifiability theorem is not yet stated for `RatSystem`.
**Evidence.** [proved] `RatSystem.IsSymmetry.solution_iff`, `Certified.{Own,Desr}.RosenzweigMacArthur`;
[tested] Holling II, Hill and repression models through Lean; four rational mutations rejected.

### D37. The ODEbase pilot: read safely, store nothing, claim little
**Decision.** Parse the model files with a whitelist arithmetic parser, never execute them;
keep no model data in the repository; report coverage and failures alongside results; certify
only the ten smallest models in Lean.
**Reason.** The files are third-party Julia source, so evaluating them would run untrusted
code. Statistics and ten certificates (each crediting its source) are enough to show the
pipeline works on published models; the data stays with its maintainers. Results are in
`docs/ODEBASE.md` with their limits (one solver, polynomial models, 28 files not analysed).
**Evidence.** [tested] `tests/test_odebase.py` (code-like input refused; synthetic models in
the same format); [proved] `Certified/ODEbase/*.lean`; desr agreed on 25 of 25 small models.

### D38. A teaching notebook that is tested like code
**Decision.** `examples/walkthrough.ipynb`: four course models, each with scalings, reduced
model, a goal query or identifiability statement, and the Lean theorem. A test executes every
code cell without Jupyter and checks the outputs the prose refers to.
**Reason.** A notebook that silently stops matching the library is worse than none.
**Evidence.** [tested] `tests/test_notebook.py`.

### D39. What may be claimed about priority
[literature] The search's verdict, with its stated confidence: the solution correspondence
(medium), the rank criterion in this form (medium), Buckingham Pi in the forward direction
(medium), the Hubert–Labahn reduction (medium–high) and checking desr (high that the technique
is standard, medium that the domain is new) appear to be first formalizations of known results.
It read [B25] through the paper and supplement rather than the repository, and did not cover
every proof-assistant library. **Claim "to our knowledge, first machine-checked proofs";
never "novel mathematics" and never "first" without that qualifier.** Certificate checking of
computer-algebra output is an established pattern (Mathlib's `polyrith`, Isabelle's Smith
normal form checker); the domain is what is new here.

---

## Sources

* **[HL13]** E. Hubert, G. Labahn. "Scaling invariants and symmetry reduction of dynamical
  systems." *Found. Comput. Math.* 13:479–516, 2013. https://link.springer.com/article/10.1007/s10208-013-9165-9
* **[T25]** Tanburn, Hendron, Maini, Amethyst, Dufresne, Harrington. "Nondimensionalization is
  More Science than Art." arXiv:2512.13455, 2025 (preprint). https://arxiv.org/abs/2512.13455 — code: https://github.com/ofloveandhate/desr
* **[HW26]** Hawi, Wechselberger. arXiv:2611.04127, 2026 (preprint; minimal parameter counts for
  polynomial/CRN models; not used in the code). https://arxiv.org/abs/2611.04127
* **[B25]** Bobbin, Jones, Velkey, Josephson. "Formalizing dimensional analysis using the Lean
  theorem prover." arXiv:2509.13142, 2025. https://arxiv.org/abs/2509.13142
* **[BJ23]** N. Botta et al. "Types, equations, dimensions and the Pi theorem." arXiv:2308.09481
  (dimensional analysis and the Pi theorem in a dependently typed setting). https://arxiv.org/abs/2308.09481
* **[HS06]** É. Hubert, A. Sedoglavic. "Polynomial Time Nondimensionalisation of Ordinary
  Differential Equations via their Lie Point Symmetries." arXiv:cs/0604060, 2006. https://arxiv.org/abs/cs/0604060
* **[CdB20]** M. Castro, R. J. de Boer. "Testing structural identifiability by a simple scaling
  method." *PLOS Computational Biology*, 2020. (Cited from the literature search; not re-read.)
* **[VM21]** A. F. Villaverde, G. Massonis. "On testing structural identifiability by a simple
  scaling method: relying on scaling symmetries can be misleading." *PLOS Computational Biology*
  17(10): e1009032, 2021. (Cited from the literature search; not re-read.)
* **[ODEbase]** C. Lüders, T. Sturm, O. Radulescu. "ODEbase: a repository of ODE systems for
  systems biology." *Bioinformatics Advances*, 2022. https://odebase.org . Model files read from
  https://github.com/yuvraj-singh-math/OscarODEbase (MIT licence).
* **[DESR]** desr, version 3.0.0, commit `deff1c066198befb3454db45c9e802c266ab19ed`, Apache-2.0.
  https://github.com/ofloveandhate/desr
* **[TAO]** T. Tao, `Analysis/Misc/UnitsSystem.lean`. https://github.com/teorth/analysis/blob/main/Analysis/Misc/UnitsSystem.lean
* **[ML]** Mathlib documentation: tactics https://leanprover-community.github.io/mathlib4_docs/tactics.html ;
  rank–nullity https://leanprover-community.github.io/mathlib4_docs/Mathlib/LinearAlgebra/FiniteDimensional/Lemmas.html
* **[SS89]** L. Segel, M. Slemrod. "The quasi-steady-state assumption: a case study in
  perturbation." *SIAM Review* 31(3):446–477, 1989.
* **[MV20]** G. Massonis, A. F. Villaverde. "Finding and breaking Lie symmetries: implications
  for structural identifiability and observability in biological modelling." *Symmetry* 12(3):469, 2020.
* **[VM21]** A. F. Villaverde, G. Massonis. *PLoS Comput. Biol.* 17(10):e1009032, 2021.
* **[SI]** StructuralIdentifiability.jl documentation. https://docs.sciml.ai/StructuralIdentifiability/stable/
* **[EG]** S. Ellner, J. Guckenheimer. *Dynamic Models in Biology*, Princeton UP, 2006. §6.2
  (SIR rescaling to R₀), Ch. 4 (rescaling), Ch. 8 (time scales, sensitivity).
* **[PYPI-TP]** PyPI documentation, "Publishing with a Trusted Publisher." https://docs.pypi.org/trusted-publishers/using-a-publisher/
* **[PYPA-GUIDE]** Python Packaging User Guide, "Publishing package distribution releases using
  GitHub Actions CI/CD workflows." https://packaging.python.org/en/latest/guides/publishing-package-distribution-releases-using-github-actions-ci-cd-workflows/
* **[LEAN-ACTION]** `leanprover/lean-action`, GitHub Action for Lean projects. https://github.com/leanprover/lean-action
* **[K09]** A. Kennedy. "Types for Units-of-Measure: Theory and Practice." CEFP 2009, LNCS 6299.

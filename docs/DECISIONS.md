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

* `python -m pytest -q`: **471 tests pass** (452 Python/bridge/packaging + 19 that call Lean).
* `lake build`: **passes** with Lean 4.35.0 / Mathlib v4.35.0: 6 generated certificates,
  `Basic`, `Theory`, `SIR`, and 5 Lean test files. No `sorry` outside `Exercises.lean`
  (`test_key_theorems_do_not_depend_on_sorry` checks this with `#print axioms`).
* Where this was run: natively on the Mac via `./setup.sh` (before packaging: 425 Python tests,
  `lake build` of 2459 jobs, 19 Lean bridge tests) and in the assistant's cloud workspace
  (after packaging: all 471).
* Packaging: the wheel and source archive build, pass `twine check --strict`, install into a
  clean virtual environment, and the Lean project that `nondim init-lean` copies out of the
  installed wheel builds completely.
* **Not yet exercised:** the GitHub Actions workflows (templates in `scripts/workflows/`; they
  first run after the owner copies them into `.github/` and pushes) and any real upload to
  GitHub or PyPI.

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
Verified by Lean, per model: checks 1–8 in the README table, plus constraint verdicts.
Verified by Lean, in general: `monomial_scale`, `finrank_scalingSpace`, `maximal_of_rank`,
and for SIR the two-way correspondence of solutions and equilibria and the R₀ threshold.

**Not** verified:
1. that the equations and unit links typed into Python are the intended model (D6);
2. that the exporter printed the same model the solver analysed. Mitigation: [tested]
   `test_lean_export.py` re-parses every certificate with an independent reader and re-checks
   every theorem, and `test_certificates_on_disk_are_up_to_date` catches stale files;
3. the general rank criterion (D7) and the ℤ-vs-ℚ rank bridge (Exercises);
4. solution correspondence for models other than SIR (only the right-hand-side identity);
5. anything numerical: floating point, ODE solvers, fits;
6. that a reduction is *useful* (interpretable, right small parameter).

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

## Sources

* **[HL13]** E. Hubert, G. Labahn. "Scaling invariants and symmetry reduction of dynamical
  systems." *Found. Comput. Math.* 13:479–516, 2013. https://link.springer.com/article/10.1007/s10208-013-9165-9
* **[T25]** Tanburn, Hendron, Maini, Amethyst, Dufresne, Harrington. "Nondimensionalization is
  More Science than Art." arXiv:2512.13455, 2025 (preprint). https://arxiv.org/abs/2512.13455 — code: https://github.com/ofloveandhate/desr
* **[HW26]** Hawi, Wechselberger. arXiv:2611.04127, 2026 (preprint; minimal parameter counts for
  polynomial/CRN models; not used in the code). https://arxiv.org/abs/2611.04127
* **[B25]** Bobbin, Jones, Velkey, Josephson. "Formalizing dimensional analysis using the Lean
  theorem prover." arXiv:2509.13142, 2025. https://arxiv.org/abs/2509.13142
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

# What this project contributes, on one page

Written 2026-11-13, after the general theorems and the desr adapter were added. Every claim
below points to the theorem or test that backs it. The limits are in the last section and
matter as much as the claims.

## The question

Nondimensionalizing an ODE model by scaling symmetries is a solved computational problem:
Hubert & Labahn (2013) gave the algorithm and Tanburn et al. (2025) the tool, desr. A second
solver is not a contribution. The open spot is **assurance**: when a tool says "these are the
dimensionless variables and this is the reduced model", what exactly has been established, and
by whom?

## Three things this repository now does

**1. It proves the theory once, in Lean, for every polynomial ODE system.**
(`docs/THEORY.md`)

| Result | Lean | In words |
|---|---|---|
| Solutions correspond | `IsSymmetry.solution_iff` | rescaling by a symmetry is a one-to-one map between solutions |
| The constraint criterion | `normalizable_iff_rank` | "these `k` parameters can be scaled to 1 for every positive value" ⟺ their columns have rank `k` |
| Buckingham Pi | `buckingham_pi_factorization` | a unit-independent quantity is a function of the dimensionless groups |
| Reduction | `IsSymmetry.reduction`, `hasDerivAt_newVariable` | every positive solution rescales to one with the removed groups equal to 1, and the new variables satisfy the reduced equations |

The second row answers the question the project started with: for a constraint such as
"remove at least `k` parameters and keep these", satisfiability is decided by a rank, and that
rank test is now proved to be exactly right, in both directions.

**2. It checks the reference tool's answers instead of replacing the tool.**
(`docs/DESR.md`)

`nondim certify` turns desr's output for a model into a Lean file. Lean then proves that desr's
scalings are symmetries, that its invariants are complete, and that along every positive
solution its new variables satisfy its reduced equations. desr is not trusted, and neither is
this package's Python: a wrong answer makes the build fail (18 corrupted certificates and one
corrupted desr answer are each rejected in the tests).

**3. It shows where the theory stops.**
(`lean/NondimVerifyTest/Limits.lean`, `docs/TESTING.md`)

For each hypothesis of each general theorem there is a concrete case, checked by Lean, in which
the hypothesis fails and the conclusion fails with it.

## Evidence that it works

| Claim | Evidence |
|---|---|
| The general theorems are proved | `lake build` passes; `#print axioms` on 36 theorems shows only Lean's three standard axioms |
| desr's answers are certified | 6 built-in models and 9 unplanned ones (8 random, 1 regression) compile |
| Two independent solvers agree | all supported built-in models and 59 random models: same scalings, same parameter count |
| The checker rejects wrong input | 12 + 18 single-defect certificate mutations rejected by Lean; 12 corruptions rejected before export |
| The tests can find real problems | they found three (`docs/DESR.md`, "What the tests found"), one of which changed the main theorem statement |

675 tests in total (633 in Python, 42 that call Lean). Without desr installed, 613 run and
the desr tests skip.

## What can honestly be said about novelty

* A search for prior formal verification of nondimensionalization or of scaling-symmetry
  reduction of ODEs found none. It was a short web search, not a literature review.
* Dimensional analysis has been formalized in Lean 4 before (Bobbin et al. 2025), including the
  counting side of Buckingham Pi. The statement about functions proved here was not found
  there or elsewhere, but their paper was not checked line by line. Botta et al. (2023) treat
  the theorem in a dependently typed language.
* The mathematics is not new. Every theorem here is known; what is new, if anything, is that a
  proof assistant checks them and checks a tool's output against them.

A fair one-sentence summary: *a small verified checker for an existing algorithm, plus
machine-checked proofs of the three facts users of that algorithm rely on.*

## What it does not do

1. Unit links and initial conditions (SIR with `N`, Michaelis–Menten with `s₀`) and rational
   right-hand sides are not in the general theory yet. They keep the first release's
   matrix-level certificates.
2. Only desr's "parameter" scheme is certified.
3. "No scaling was missed" still relies on an exponent matrix printed by Python.
4. Solutions are assumed positive and defined for all time.
5. Nothing here says a reduction is the *useful* one: which small parameter matters is a
   modelling judgement.
6. The tests that need desr (60 in Python, 2 with Lean) have been run only in the assistant's
   cloud workspace. Everything else was also run on the project owner's Mac on 2026-11-13:
   `lake build` passes (2493 jobs) and the test suite gives 613 passed, 3 skipped.

## If there is time for one more step

Derive the exponent matrix inside Lean from the model data (closes limit 3), or express unit
links in `LaurentSystem` (closes limit 1 and brings SIR with `R₀` into the general form). The
second is the one a mathematical biology audience would notice.

# What this project contributes, on one page

Updated 2026-11-13 after a literature search on prior art and the work that followed from it.
Every claim points to the theorem, test or source that backs it. The limits are in the last
two sections and matter as much as the claims.

## The question

Nondimensionalizing an ODE model by scaling symmetries is a solved computational problem:
Hubert & Labahn (2013) gave the algorithm and Tanburn et al. (2025) the tool, desr. A second
solver is not a contribution. The open spot is **assurance and what follows from it**: when a
tool says "these are the dimensionless variables and this is the reduced model", what exactly
has been established, and what does it let a modeller conclude?

## What this repository does

**1. It proves the theory once, in Lean, for every model built from polynomials and quotients
of polynomials.** (`docs/THEORY.md`)

| Result | Lean | In words |
|---|---|---|
| Solutions correspond | `IsSymmetry.solution_iff` | rescaling by a symmetry is a one-to-one map between solutions |
| The constraint criterion | `normalizable_iff_rank` | "these `k` parameters can be scaled to 1 for every positive value" ⟺ their columns have rank `k` |
| Buckingham Pi | `buckingham_pi_factorization` | a unit-independent quantity is a function of the dimensionless groups |
| Reduction | `IsSymmetry.reduction`, `hasDerivAt_newVariable` | every positive solution rescales to one with the removed groups equal to 1, and the new variables satisfy the reduced equations |
| Constraints | `IsHomogeneous.poly_scale_eq_zero_iff` | a conservation law is preserved exactly by the scalings that give all its terms one weight |
| Identifiability (one way) | `IsSymmetry.not_identifiable` | a scaling that leaves time and the data unchanged gives every solution a twin with the same data and different parameters |

**2. It checks the reference tool's answers instead of replacing the tool.** (`docs/DESR.md`)
`nondim certify` turns desr's output into Lean theorems. Seven models are certified for desr,
including a rational one (Rosenzweig–MacArthur).

**3. It answers a modeller's requests with proofs both ways.** (`docs/THEORY.md` §9)
"Remove three parameters from SIR" is proved impossible. "Keep `R₀`" is proved possible.
"Use `βN` as a group" is proved impossible because it has units. Every certificate proves the
smallest number of parameters any scaling reduction can leave.

**4. It says what data cannot determine, and proves where that test stops.**
For SIR observed through `y = ρI`, Lean proves `β` and `ρ` cannot be told apart. Two Lean
counterexamples show the test is one-way and that its hypotheses are needed.

**5. It has been run on published models.** (`docs/ODEBASE.md`)
162 polynomial BioModels systems from ODEbase: 98% have scaling symmetries, which can remove
19% of the parameters; desr agreed on all 25 small models given to both; ten have Lean
certificates.

## Evidence that it works

| Claim | Evidence |
|---|---|
| The theorems are proved | `lake build` passes (2512 jobs); `#print axioms` on 57 theorems shows only Lean's three standard axioms |
| The checker rejects wrong input | 47 single-defect certificate mutations rejected by Lean; more rejected in Python before export |
| Two independent solvers agree | all supported built-in models, 59 random models, 25 published models |
| Each hypothesis is needed | `NondimVerifyTest/Limits.lean`: 14 counterexamples checked by Lean |
| The tests find real problems | three findings in `docs/DESR.md`, one of which changed the main theorem statement |

847 tests in total (783 in Python, 64 that call Lean). Without desr installed, 782 run.

## What the literature search found about priority

A search on 2026-11-13 (about twenty queries; several sources read through abstracts or
supplements, not code) reported:

| Result here | Closest earlier formal work | Verdict | Confidence |
|---|---|---|---|
| Solution correspondence under scaling symmetries | none found; libraries have ODE existence theory, nothing on symmetries of models | likely first | medium |
| Rank criterion with certificates | standard linear algebra; verified Hermite and Smith normal forms exist in Isabelle | likely first in this form | medium |
| Buckingham Pi, "unit-independent ⟹ function of the groups" | Bobbin et al. (Lean 4) define the count and kernel only; Botta & Jansson (Idris/Agda) prove the converse and argue the textbook form is not constructive | likely first proof of this direction | medium |
| Hubert–Labahn reduction | none found | likely first | medium–high |
| Checking desr | the pattern is established (Mathlib's `polyrith`, Isabelle's Smith normal form checker) | new domain, known technique | high / medium |
| Identifiability in a proof assistant | none found | unknown | low (one search) |

So the accurate sentence is: *to our knowledge these are the first machine-checked proofs of
these statements; the mathematics itself is known.* Not "novel mathematics", and not "first"
without the qualifier.

The search also found that the crowded part of this area is units typing and Buckingham Pi
bookkeeping (several Lean libraries), and that the open part is the link between scaling
symmetries and what modellers do next: reduced equations, identifiability, choice of
reduction, and real model collections. Items 3–5 above are aimed there.

## What it does not do

1. **The ODEbase numbers are a pilot.** One solver, polynomial models only, 28 of 190 files not
   analysed, ten models certified in Lean. Not a study.
2. **Identifiability is one-way and global.** It is not a replacement for a complete tool such
   as StructuralIdentifiability.jl, and it has not been cross-checked against one.
3. **Unit links are not passed to desr**, and only desr's "parameter" scheme is certified.
4. **For rational models** the last step (the reduced equation in the tool's printed form) is
   checked by SymPy, not Lean.
5. **"No scaling was missed"** still relies on an exponent matrix printed by Python.
6. **Goals that are not algebraic** (which parameter is small, which variables are of order
   one) are out of reach, and so is the question of which reduction is useful.
7. Solutions are assumed positive and defined for all time.
8. **Where it was run.** Everything was built and tested in the assistant's cloud workspace.
   On the project owner's Mac the state of the `general-theory` branch before this round was
   built and tested (613 passed, 3 skipped); the additions of this round still need
   `lake build` and the test suite there.

## If this were taken further

The search's recommendation, which matches what the pilot suggests: combine items 4 and 5 into
*certified scaling reductions and scaling non-identifiability across ODEbase*. That needs the
rational models (available from odebase.org), a comparison with StructuralIdentifiability.jl
and with Hawi & Wechselberger's parameter counts, and Lean certificates at scale. It would be
an empirical paper with a formal core. Nothing in this repository claims to be that yet.

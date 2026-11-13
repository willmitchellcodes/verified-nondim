# Reading list (in order)

Several key sources are recent preprints (marked ⚠). Their results may change after peer
review, so check the latest versions before quoting.

## Start here

1. **Ellner & Guckenheimer, *Dynamic Models in Biology*, §6.2 (Rescaling the SIR model) and
   the Ch. 4 rescaling examples.** Redo the SIR → R₀ computation by hand,
   then compare with `docs/BACKGROUND.md` §2–4.
2. **BYU ACME lab, "Buckingham Pi"** — a short linear-algebra view of dimensional analysis
   (dimension matrix, null space, rank–nullity).
   https://labs.acme.byu.edu/Volume4/BuckinghamPi/BuckinghamPi.html
3. ⚠ **Tanburn, Hendron, Maini, Amethyst, Dufresne & Harrington (2025), "Nondimensionalization
   is More Science than Art"**, arXiv:2512.13455. *The* paper for this project. Read §2–3: the
   algorithm, Theorem 3.5 (reduced parameter count = p − rank), Theorem 3.8 (preferred groups),
   and Example 3.12 (spurious symmetries). §4 covers Michaelis–Menten. Their code is
   [desr](https://github.com/ofloveandhate/desr). https://arxiv.org/abs/2512.13455
4. **Bobbin, Jones, Velkey & Josephson (2025), "Formalizing dimensional analysis using the Lean
   theorem prover"**, arXiv:2509.13142. Shows what exists in Lean: dimensions as an abelian
   group, while Buckingham Pi appears only as *definitions*, not theorems. That gap is part of
   the motivation for this project. https://arxiv.org/abs/2509.13142

## Theory and tools

5. **Hubert & Labahn (2013), "Scaling invariants and symmetry reduction of dynamical systems"**,
   *Found. Comput. Math.* 13:479–516. The rigorous foundation: maximal scaling matrix via Hermite
   normal forms (Prop. 5.1), parameter count (Thm 7.1). Skim proofs; focus on the definitions.
   https://link.springer.com/article/10.1007/s10208-013-9165-9
6. **Lean:** *Mathematics in Lean* (chapters 1–3, plus the linear algebra chapter)
   https://leanprover-community.github.io/mathematics_in_lean/ and *Theorem Proving in Lean 4*
   https://lean-lang.org/theorem_proving_in_lean4/ for reference.
7. **Mathlib API you will use:** `Matrix.rank`, `LinearMap.finrank_range_add_finrank_ker`
   (rank–nullity, for Exercise 1), `HasDerivAt.comp` (chain rule), and the `eval_rank` tactic.
   Docs: https://leanprover-community.github.io/mathlib4_docs/Mathlib/LinearAlgebra/FiniteDimensional/Lemmas.html
8. ⚠ **Hawi & Wechselberger (Nov 2026)**, arXiv:2611.04127. A closed-form minimum number of
   parameters for polynomial/chemical-reaction-network models, plus a rule for picking the
   "best" scaling among the minimal ones (tool: CRNNondim, https://github.com/georgio-hawi/crnnondim).
   Very new and not yet peer-reviewed, so check its hypotheses in the full text.
   https://arxiv.org/abs/2611.04127

## For the "limits and failure modes" section

9. **Segel & Slemrod (1989), "The quasi-steady-state assumption: a case study in perturbation"**,
   *SIAM Review* 31(3). How the choice of scales decides which small parameter you see in
   Michaelis–Menten. The best source for "correct is not the same as useful".
10. **Massonis & Villaverde (2020), "Finding and breaking Lie symmetries: implications for
    structural identifiability and observability in biological modelling"**, *Symmetry* 12(3):469.
11. **Villaverde & Massonis (2021)**, *PLoS Comput. Biol.* 17(10):e1009032. Warns that treating
    scaling symmetries as the only cause of non-identifiability can mislead.
12. **StructuralIdentifiability.jl** docs, for a complete identifiability analysis:
    https://docs.sciml.ai/StructuralIdentifiability/stable/

## Formal-methods background (optional, good for related work)

13. **Kennedy, "Types for Units-of-Measure: Theory and Practice"** (CEFP 2009, LNCS 6299)
    https://link.springer.com/chapter/10.1007/978-3-642-17685-2_8 — and his POPL 1997 paper
    *Relational Parametricity and Units of Measure*, which derives the Pi theorem from
    parametricity. This is the most elegant "formal" Buckingham Pi.
14. **Foster & Wolff, "A Sound Type System for Physical Quantities, Units, and Measurements"**,
    Isabelle AFP entry https://isa-afp.org/entries/Physical_Quantities.html (paper: arXiv:2302.07629).
15. **Boulier, Lefranc, Lemaire, Morant & Ürgüplü** — MABSys, the older Maple tool for
    scaling reduction of biochemical models. https://hal.science/hal-00307915v1/document
16. Verified normal forms (if you want to verify the solver itself, not just its output):
    Divasón & Thiemann (Isabelle, *J. Automated Reasoning* 2022); Cano, Cohen, Dénès, Mörtberg
    & Siles (Coq, *LMCS* 2016).

## Methods to get comfortable with

* **Integer linear algebra:** kernel/null space, rank–nullity, Hermite normal form and
  unimodular matrices (why an integer basis needs more than Gaussian elimination).
* **Chain rule for rescaled time:** `dX/dτ = (dX/dt)/(dτ/dt)`. This is what `rhs_*` and
  `trajectory_*` formalize.
* **Certificate checking:** let an untrusted program find an answer, then verify only the answer.
  Mathlib's `linarith`, `linear_combination` and `eval_rank` all work this way.
* **Lean tactics in this repo:** `decide +kernel`, `eval_rank`, `field_simp`, `ring`,
  `HasDerivAt` lemmas, `unfold`, `rw`, `simp`.

## For the general theorems and the desr certificates

Read in this order; each item names the file where the idea is used.

1. **Hubert & Labahn (2013)**, §2–3: scaling matrix, Hermite multiplier `V = [Vi | Vn]`, its
   inverse `W`, invariants as the columns of `Vn`, and reduction on a cross-section. This is
   the form `nondim/hlform.py` stores and `Reduction.lean` gives meaning to.
2. **Tanburn et al. (2025)**, §3: what desr computes and returns, and its three reduction
   schemes. Only the "parameter" scheme is certified so far (`docs/DESR.md`, Scope).
3. **A proof of the Buckingham Pi theorem that goes through logarithms.** The Wikipedia article
   "Buckingham π theorem" has a short formal proof; compare it with `exists_scaling_of_piGroups_eq`
   in `BuckinghamPi.lean`, where the key step is "orthogonal to the kernel ⟹ in the row space".
4. **Botta et al. (2023), "Types, equations, dimensions and the Pi theorem"**, arXiv:2308.09481.
   Why the textbook statement of the Pi theorem is hard to make constructive. Useful for
   placing `buckingham_pi_factorization` (which uses classical choice). https://arxiv.org/abs/2308.09481
5. **Mathlib pieces worth opening:** `is_const_of_deriv_eq_zero` (mean value theorem, used for
   "parameters are constant"), `LinearMap.exists_leftInverse_of_injective` and
   `Submodule.exists_dual_map_eq_bot_of_notMem` (the two linear-algebra facts behind the
   criterion and the Pi theorem), `HasDerivAt.comp` (the chain rule).

Methods to add to the list above: **decidable propositions** (`decide +kernel` proving
`sys.IsSymmetry A tau` by evaluation), **certificates for linear algebra** (a left inverse or a
kernel vector instead of a rank), and **property-based testing** (random models as a second
opinion on a design; it changed this one, see `docs/DESR.md`).

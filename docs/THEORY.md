# The general theorems

The first release proved facts about one model at a time. This part of the Lean library proves
the facts **once, for every model of a given shape**, so that a per-model certificate only has
to supply integer matrices and a few polynomial identities.

Everything here is in `lean/NondimVerify/`. Each section gives the statement in plain words,
the Lean name, the idea of the proof, what the theorem does *not* say, and where it is tested.
The statements below paraphrase the Lean; the Lean files are the authority.

```
            Basic.lean          monomials, scalings, monomial_scale
               |
            System.lean         a model as data · symmetry · solutions map to solutions
             /      \           · parameters are constant · normalizing parameters
   Criterion.lean   BuckinghamPi.lean
   (the iff)        (Pi theorem)
             \      /
            Reduction.lean      reduction to invariants · the reduced equations
               |
            Certified/*.lean    one file per model and per tool (desr, or our solver)
```

## 0. The setting

**A model is data** (`LaurentSystem n`). There are `n` variables. Each has a list of terms
`coefficient · ∏ x_j ^ e_j` with integer exponents (negative ones allowed). A variable with no
terms is a **parameter**. The system is `dx_i/dt = (sum of the terms of i)`.

```lean
structure Term (n : ℕ) where
  coeff : ℝ
  exps : Fin n → ℤ
structure LaurentSystem (n : ℕ) where
  terms : Fin n → List (Term n)
```

SIR with variables `β, γ, I, S` is
`![[], [], [⟨-1, ![0,1,1,0]⟩, ⟨1, ![1,0,1,1]⟩], [⟨-1, ![1,0,1,1]⟩]]`.

Why data and not Lean functions: a property of data can be *computed*. Whether a scaling is a
symmetry becomes a finite check on exponents that Lean decides by evaluation, with no exponent
matrix handed in from outside. Each certificate also proves that the data evaluates to the
equation as a person would write it (`eq_S`, `eq_I`, …), so the data cannot quietly be a
different model.

**A scaling** is a matrix `A` (one row per scaling, one column per variable) and a vector `τ`.
With factors `λ_j > 0` it acts by `x_i ↦ (∏_j λ_j ^ A_ji) · x_i` and `t ↦ (∏_j λ_j ^ τ_j) · t`.
Changing units is exactly this.

**A solution** (`IsSolution`) is a curve `x : ℝ → (Fin n → ℝ)` with the prescribed derivative
at every time.

Scope, stated once: autonomous systems, right-hand sides that are sums of monomials with
integer exponents, solutions defined for all time, positive values where a theorem divides or
takes logarithms. Rational right-hand sides (Rosenzweig–MacArthur) are outside this part and
stay with the first release's matrix-level certificates.

---

## 1. A symmetry maps solutions to solutions

**Statement.** If every term of every equation has the same weight as the left-hand side
(`IsSymmetry`), then for every choice of nonzero factors the rescaled curve is again a solution
of the same system. And conversely: the rescaled curve is a solution **only if** the original
is. Rescaling is a one-to-one correspondence between solutions.

| Lean | |
|---|---|
| `LaurentSystem.IsSymmetry sys A τ` | `∀ i, ∀ t ∈ terms i, ∀ j, (A·exps t)_j + τ_j = A_ji` (decidable) |
| `IsSymmetry.rhs_scale` | `f_i(scaled x) = (∏ λ_j ^ (A_ji − τ_j)) · f_i(x)` |
| `IsSymmetry.map_solution` | rescaled solutions are solutions |
| `IsSymmetry.solution_iff` | …if and only if |

**Proof idea.** A monomial of a scaled point is the monomial times `∏ λ^(A·exps)`
(`monomial_scale_eq`). The symmetry condition makes that factor the same for every term of
equation `i`, so it comes out of the sum. The chain rule supplies the time factor. The converse
applies the same theorem to the inverse factors `1/λ_j`.

**Replaces:** in the first release this was proved for SIR only, by hand, in `SIR.lean`.

**Limits.** `IsSymmetry` is a check on the terms *as written*. It is sufficient, not necessary:
`dx/dt = 0·x⁵` fails the check although every scaling preserves its solutions
(`NondimVerifyTest/Limits.lean` §2). The exporter never writes zero terms, and a Python test
enforces that. The converse "a scaling that maps solutions to solutions is a symmetry of the
terms" is not proved.

---

## 2. Parameters are constant

**Statement.** A variable with no terms keeps its initial value along every solution.

`LaurentSystem.IsSolution.param_const`, and for monomials in parameters `paramMonomial_const`.

**Proof idea.** Its derivative is zero everywhere; a function with zero derivative on the line
is constant (mean value theorem, `is_const_of_deriv_eq_zero` in Mathlib).

**Why it matters.** Without it, every later theorem would need the hypothesis "the parameters
do not change", which a reader has to take on trust. With it, the theorems speak about every
positive solution of the system as given.

---

## 3. The constraint criterion

This is the question the project started from: *given a constraint such as "remove these `k`
parameters", is there a nondimensionalization that satisfies it?*

**Statement** (`normalizable_iff`, `normalizable_iff_rank`). Let `S` be a list of `k` distinct
parameters. The following are equivalent:

1. for **every** positive choice of values there are positive scale factors making all the
   parameters in `S` equal to 1;
2. the columns `S` of the scaling matrix are linearly independent;
3. those columns have rank `k`.

Statement 3 is the test the Python solver runs (`constraints.solve`). The theorem says that
test is exactly right: it never refuses a possible request and never accepts an impossible one.

| Lean | |
|---|---|
| `exists_normalizing_scaling` | "yes" from a certificate: integer `G`, `d ≠ 0` with `G · A_S = d · 1` |
| `not_normalizable_of_kernel_vector` | "no" from a certificate: integer `v ≠ 0` with `A_S · v = 0` |
| `left_inverse_or_kernel` | one of the two certificates always exists |
| `normalizable_iff`, `normalizable_iff_rank` | the equivalences |
| `IsSymmetry.nondimensionalize` | the consequence for solutions: any solution rescales to one with those parameters equal to 1 |

**Proof idea.** Take logarithms: `scale … = 1` for all of `S` is the linear system
`A_Sᵀ μ = −log c` in `μ = log λ`. A left inverse of `A_S` solves it explicitly
(`λ_j = exp(−Σ_l G_lj log c_l / d)`). A kernel vector gives a monomial that no scaling can
change, so choosing values that make it `≠ 1` blocks normalization. That one of the two exists
is linear algebra over ℚ plus clearing denominators (`exists_common_denominator`).

**Why certificates and not ranks in the per-model files.** A left inverse or a kernel vector is
checked by one integer matrix product (`decide`). It also covers a case integer-only methods
cannot express: `x ↦ λ²x` is normalizable with `d = 2`, i.e. with a square root (Limits §5).

**Limits.** Positive values only: a parameter equal to 0 stays 0 (Limits §3). "For every choice
of values" matters: for particular values a dependent set can happen to be normalizable. The
"no" direction needs the parameters to be distinct (Limits §4).

---

## 4. Buckingham Pi

**Statement** (`buckingham_pi`, `buckingham_pi_factorization`). Let `D` be the dimension matrix
(rows: units, columns: quantities) and let the columns of `P` span all dimensionless
combinations. If a function `f` of positive quantities does not depend on the choice of units
(`UnitInvariant D f`), then `f` depends on the quantities only through the groups `piGroups P`:
equal groups give equal values, and `f = F ∘ piGroups P` for some `F`.

| Lean | |
|---|---|
| `pi_group_invariant` | each column of `P` with `D · P = 0` is unchanged by a change of units |
| `exists_scaling_of_piGroups_eq` | two positive points with the same groups differ by a change of units |
| `buckingham_pi`, `buckingham_pi_factorization` | the theorem, in both forms |
| `spans_kernel_of_certificate` | the spanning hypothesis from integer identities `V₁W₁ + PW₂ = 1`, `DP = 0`, `L(DV₁) = d·1` |
| `finrank_dimensionless` | the count: (number of quantities) − rank `D` |

**Proof idea.** The middle row is the heart. In logarithms, "same groups" says the difference
`y = log q' − log q` is orthogonal to the kernel of `D`. A vector orthogonal to the kernel of a
matrix is a combination of its rows (a dual-space argument in `exists_row_combination`), and
the coefficients of that combination are the logarithms of the unit change.

**What is and is not new here.** The counting half ("there are `n − rank` groups") is standard
and has been set up in Lean before (Bobbin et al. 2025, as far as their abstract and text show;
not re-checked line by line). What this file adds is the half that says something about
functions: unit-independence implies dependence on the groups alone. Two web searches found no
earlier proof of that half in Lean. That is weak evidence of novelty, not a claim of it; Botta
et al. (2023) discuss the theorem in a dependently typed setting and should be read before
anyone writes "first".

**Limits.** Positive quantities only (Limits §7: "is this length positive?" is unit-independent
and is not a function of zero groups). The groups must span (Limits §6: leave out the ratio of
two lengths and the conclusion fails). They need not form an integer basis (Limits §8).

---

## 5. Reduction to invariants

A tool like desr returns the scalings `A` and a unimodular matrix `V = [Vi | Vn]` with inverse
`W = [Wu ; Wd]`. Columns of `Vn` are the **invariants** (the new, dimensionless variables).
Columns of `Vi` are **auxiliary monomials**. Two theorems give this meaning.

### 5a. The cross-section (`IsSymmetry.reduction`, `reduction_of_parameters`)

**Statement.** Suppose `Vi·Wu + Vn·Wd = 1`, `A·Vn = 0`, `G·(A·Vi) = d·1` with `d ≠ 0`, and the
auxiliary monomials involve parameters only. Then every positive solution can be rescaled, by
an explicit choice of scale factors, to a solution `y` of the **same** system such that

* every auxiliary monomial of `y` equals 1,
* `y` has the same invariants as the original solution (at the rescaled time),
* `y` is determined by its invariants: `y = reconstruct Wd (invariants of y)`.

**Proof idea.** §3 gives factors that send the auxiliary monomials to 1. §1 says the result is
a solution. Invariance is `A·Vn = 0`. The last point is `eq_reconstruct_of_section`: because
`V·W = 1`, each variable is a product of auxiliary monomials (all 1) and invariants.

### 5b. The reduced equations (`IsSolution.hasDerivAt_newVariable`)

**Statement.** Let `ν = x_i · (monomial in the parameters)` be a new variable and let the new
time be `τ = T·t` with `T` a monomial in the parameters. If the algebraic identity

    (factor of ν) · f_i  =  T · g        holds at every positive point,

then along every positive solution, `ν` as a function of `τ` has derivative `g`.

**Proof idea.** Both factors are constant (§2), so `ν(τ) = C · x_i(τ/T)` and the chain rule
gives derivative `C · f_i / T`, which the identity turns into `g`.

**Why two theorems.** 5a says the reduced model is *equivalent* to the original one. 5b says
the tool's reduced *equations* are right. They are different claims. For the textbook models
the cross-section coordinates coincide with the tool's new variables, and it is tempting to
state the reduced equations on the cross-section. That is wrong in general: for
`dx/dt = −a y − c x y²`, `dy/dt = b x y − c x²` desr's new variable is `ν₀ = c³x/b³` while the
cross-section has `x = ν₀/κ³`. A random-model test found this (see `docs/DESR.md`, "What the
tests found"); Limits §10 records it in Lean.

**Limits.** 5b needs each new state variable to be *one state* times parameters, which is
desr's "parameter" scheme and this package's solver. Reductions that mix states into one
another are not covered. Solutions must be positive.

---

## 6. What a per-model certificate now contains

`lean/NondimVerify/Certified/Desr/<Model>.lean` (desr's answer) and
`Certified/Own/<Model>.lean` (this package's answer) have the same shape:

| Theorem | Says | Proved by |
|---|---|---|
| `eq_<state>` | the data is the equation you wrote | `simp`, `ring` |
| `symmetry` | the tool's scalings are symmetries | `decide`, read off the data |
| `unimodular`, `invariant`, `auxiliaries_free`, `auxiliaries_are_parameters` | the hypotheses of §5a | `decide` |
| `reduced_identity_<state>` | the identity of §5b | `simp`, `field_simp`, `ring` |
| `reduction_correct` | **along every positive solution, the tool's new variables satisfy the tool's reduced equations in the tool's new time** | §5b |
| `cross_section` | the solution rescales to one with all auxiliary monomials equal to 1 | §5a |
| `invariants_complete` | everything unit-independent is a function of the tool's invariants | §4 |
| `kills_K`, `rank_K`, `rank_A` | no scaling was missed | `decide`, `eval_rank` |

Every general theorem and a sample of certificate theorems are checked with `#print axioms`:
they rest on Lean's three standard axioms (`propext`, `Classical.choice`, `Quot.sound`) and on
nothing else (`test_key_theorems_do_not_depend_on_sorry`).

## 7. What is still not proved

1. **"No scaling was missed" still uses an exponent matrix printed by Python.** `symmetry` is
   read off the Lean data, but `kills_K`/`rank_K` refer to a literal `Kmat`. A test re-derives
   it independently; Lean does not yet derive it from `sys`.
2. **Models with unit links** (SIR with `N`, Michaelis–Menten with `s₀`) are not expressed in
   the general form. They keep their first-release certificates.
3. **Rational right-hand sides** are outside `LaurentSystem`.
4. **The converse of §1** (solution-preserving scalings are symmetries of the terms).
5. **Solutions on an interval.** `IsSolution` asks for a derivative at every real time, which
   excludes solutions that blow up in finite time.
6. Whether the equations typed in are the intended model. No proof can settle that.

Sources: Hubert & Labahn 2013 [HL13] for the algorithm and the moving-frame view behind §5;
Tanburn et al. 2025 [T25] for the form desr returns; Bobbin et al. 2025 [B25] and Botta et al.
2023 [BJ23] for earlier formal work on dimensions. Full references in `docs/DECISIONS.md`.

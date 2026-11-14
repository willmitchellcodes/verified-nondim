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
               |        \
               |     Rational.lean        the same for quotients of polynomials
               |     Identifiability.lean constraints · outputs · what scalings hide
               |
            Certified/*.lean    one file per model and per source (desr, our solver, ODEbase)
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
integer exponents (§1–§5) or sums of quotients of such polynomials (§6), solutions defined for
all time, positive values where a theorem divides or takes logarithms.

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

**What is and is not new here.** A literature search (2026-11-13, summarized in
`docs/CONTRIBUTIONS.md`) reports that Bobbin et al. (Lean 4, 2025) *define* the count
`n − rank` and the kernel but prove no statement about functions, and that Botta & Jansson
(Idris/Agda) state the theorem as a type, argue the textbook form is not constructive, and
prove the converse direction (functions built from Pi groups are covariant). The search found
no machine-checked proof of the direction proved here, "unit-independent ⟹ function of the
groups". Its confidence was moderate: it read the Lean code of Bobbin et al. through their
paper, not the repository, and could not cover every proof-assistant library. So: probably a
first formal proof of a known theorem, not established as one. Note that
`buckingham_pi_factorization` uses classical choice, consistent with Botta & Jansson's remark.

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

## 6. Rational right-hand sides

Holling type II predation `a N P / (1 + a h N)` and Michaelis–Menten kinetics are quotients, not
polynomials. `Rational.lean` repeats the theory for systems whose right-hand sides are **sums of
quotients of polynomials** (`RatSystem`).

**Symmetry** (`RatSystem.IsSymmetry`, decidable). In every quotient of equation `i`, each
numerator term and each denominator term have weights that differ by the weight of `dx_i/dt`.
In particular the numerator and the denominator are each homogeneous: `1 + a h N` forces
`a h N` to be dimensionless.

**Statements.** `rhs_scale`, `map_solution`, `solution_iff`, `param_const`, `nondimensionalize`,
`reduction`, `reduction_of_parameters` and `hasDerivAt_newVariable` hold word for word as in
§1, §2 and §5.

**Proof idea.** Only `rhs_scale` is new: numerator and denominator each pick up a power of the
scale factors, and the quotient picks up the ratio (`Frac.eval_scale`). No hypothesis that
denominators are nonzero is needed, because Lean's `x / 0 = 0` makes both sides zero.
Everything after `rhs_scale` uses the system only through that identity.

**How a certificate avoids dividing.** Each quotient `N/D` is reduced by two identities without
division, `D = m · D'(invariants)` and `(factor) · N = T · m · N'(invariants)` with `m` a
monomial of `D`, and `frac_reduce` combines them. The equation is the sum of its quotients.

**Limits.** Where a denominator vanishes the statements are true and say nothing (Limits §14).
For rational models Lean certifies the reduced equation in sum-of-quotients form; that this
equals the form the tool printed is checked by SymPy, not by Lean. The proofs after `rhs_scale`
are repeated, not shared with the polynomial case (a refactoring debt, D36).

---

## 7. Constraints and unit links

A reduction may only use scalings that respect what the model says about units. Two forms:

* **A unit link**: "`N` is measured like `S`". Formally, the ratio `S/N` must be unchanged by
  every scaling. In a certificate: `links_respected : A * Links = 0` (by `pi_group_invariant`
  each linked ratio is then invariant).
* **A polynomial relation** such as a conservation law `S + I + R − N = 0`.
  `IsHomogeneous A p` (decidable) says all its terms have the same weight, and
  `IsHomogeneous.poly_scale_eq_zero_iff` says the rescaled point satisfies the relation exactly
  when the original one does.

The two are the same condition: a relation is homogeneous exactly when all ratios of its terms
are invariant. The ODEbase importer uses that to turn conservation laws into links.

**Why it matters.** `N` does not occur in the SIR differential equations, so "scale `S, I, R`
but not `N`" is a symmetry of the equations. It sends a state with `S + I + R = N` to one
without. Dropping the link is how a *spurious* nondimensionalization arises (Tanburn et al.
2025). `NondimVerifyTest/Identifiability.lean` has this as a worked example.

**Not done.** Tanburn et al.'s general theorem that dimensionally consistent changes of
variables preserve the dimension of the maximal scaling symmetry is not formalized.

---

## 8. What scalings say about identifiability

**Statement** (`IsSymmetry.not_identifiable`). Suppose a scaling is a symmetry, does not rescale
time, and leaves every measured output unchanged (`OutputInvariant`, decidable). If it acts on
variable `i`, then every solution with `x_i ≠ 0` has a twin: another solution with the same
outputs at all times, a different value of `x_i`, and the same signs. Hence `i` is not
identifiable from those outputs (`not_identifiable'`, with `Identifiable` defined as "equal
data at all times implies equal `x_i`").

**Proof idea.** Apply the scaling with factor 2 on one row. §1 gives a solution, the time factor
is 1 so the output curve is literally the same function of time, and `2^k ≠ 1` moves `x_i`.

**This is a one-way test, and the limits are proved, not just stated.**

* Limits §11: for `dx/dt = a − b` observed through `x`, *no* scaling symmetry that fixes time
  and the output moves `a`, yet `a` is not identifiable. A method that looks only at scalings
  reports nothing there. This is the point Villaverde & Massonis (2021) made against reading
  the scaling test of Castro & de Boer (2020) as a complete one.
* Limits §12: the hypothesis "time is not rescaled" cannot be dropped. For `dx/dt = k` observed
  through `x`, changing the time unit is a symmetry that leaves the value of `x` alone, and `k`
  *is* identifiable.

**Limits.** `Identifiable` is global and exact (all solutions, all times); the usual structural
notion is generic. Only polynomial systems (`LaurentSystem`) have this theorem so far.

---

## 9. Goal queries and the minimal parameter count

A request such as "remove at least `k` parameters, keep these, and let `R₀` appear" gets an
answer with a proof either way.

| Answer | Lean | Certificate supplied by the solver |
|---|---|---|
| possible: these parameters can be scaled to 1 | `exists_normalizing_scaling` | left inverse `G`, factor `d` |
| the requested group is dimensionless | `A *ᵥ g = 0` | none (`decide`) |
| impossible: too many parameters asked for | `not_normalizable_of_rank_lt` | the rank of the candidate columns |
| impossible: the group has units | `monomial_not_invariant` | the scaling that moves it |
| impossible: the groups are dependent | `W *ᵥ c = 0`, `c ≠ 0` | the relation `c` |

**The count.** `not_normalizable_of_rank_lt`: if the parameter columns of the scaling matrix
have rank `ρ`, no `ρ + 1` distinct parameters can all be scaled to 1 for every positive choice
of values. Each certificate proves this for its model (`cannot_remove_more`) next to a
reduction that removes exactly `ρ`. So `p − ρ` is the smallest number of parameters any
nondimensionalization by scaling can leave.

**Limits.** "For every positive choice of values" is essential (Limits §13). Requests that are
not algebraic ("make ε small", "bring variables near 1") are outside this; so are requests
rejected before any linear algebra (a group that is not a monomial), which get no Lean
statement.

---

## 10. What a per-model certificate contains

`lean/NondimVerify/Certified/` has one file per model and source: `Desr/` (desr's answer),
`Own/` (this package's), `ODEbase/` (ten published models). All have the same shape.

| Theorem | Says | Proved by |
|---|---|---|
| `eq_<state>` | the data is the equation you wrote | `simp`, `ring` |
| `symmetry` | the tool's scalings are symmetries | `decide`, read off the data |
| `unimodular`, `invariant`, `auxiliaries_free`, `auxiliaries_are_parameters` | the hypotheses of §5a | `decide` |
| `reduced_identity_<state>` | the identity of §5b | `simp`, `field_simp`, `ring` (rational: `frac_reduce`) |
| `reduction_correct` | **along every positive solution, the tool's new variables satisfy the tool's reduced equations in the tool's new time** | §5b |
| `cross_section` | the solution rescales to one with all auxiliary monomials equal to 1 | §5a |
| `invariants_complete` | everything unit-independent is a function of the tool's invariants | §4 |
| `kills_K`, `rank_K`, `rank_A` | no scaling was missed | `decide`, `eval_rank` |
| `links_respected` (if the model has unit links) | the scalings respect them | §7 |
| `cannot_remove_more` | the minimal parameter count | §9 |
| `not_identifiable_<parameter>` (if the model has outputs) | the outputs cannot determine it | §8 |
| `goal<k>_possible` / `goal<k>_impossible` (own solver, if goals are listed) | the answer to each request | §9 |

Every general theorem and a sample of certificate theorems are checked with `#print axioms`:
they rest on Lean's three standard axioms (`propext`, `Classical.choice`, `Quot.sound`) and on
nothing else (`test_key_theorems_do_not_depend_on_sorry`).

## 11. What is still not proved

1. **"No scaling was missed" still uses an exponent matrix printed by Python.** `symmetry` is
   read off the Lean data, but `kills_K`/`rank_K` refer to a literal `Kmat`. A test re-derives
   it independently; Lean does not yet derive it from `sys`.
2. **For rational models, "the reduced equation equals the one the tool printed"** is checked by
   SymPy. Lean certifies the sum-of-quotients form.
3. **Unit links are not passed to desr.** Models with links are certified for this package's
   solver only.
4. **The identifiability theorem is one-way** (by nature, §8) and exists for polynomial systems
   only; the notion used is global, not generic.
5. **The converse of §1** (solution-preserving scalings are symmetries of the terms).
6. **Solutions on an interval.** `IsSolution` asks for a derivative at every real time, which
   excludes solutions that blow up in finite time.
7. **Tanburn et al.'s change-of-variables theorem** and anything about non-scaling symmetries.
8. Whether the equations typed in are the intended model. No proof can settle that.

Sources: Hubert & Labahn 2013 [HL13] for the algorithm and the moving-frame view behind §5;
Tanburn et al. 2025 [T25] for the form desr returns and for spurious reductions (§7); Castro &
de Boer 2020 [CdB20] and Villaverde & Massonis 2021 [VM21] for §8; Bobbin et al. 2025 [B25] and
Botta & Jansson [BJ23] for earlier formal work on dimensions. Full references in
`docs/DECISIONS.md`.

import NondimVerify.Reduction
import NondimVerify.Criterion
import NondimVerify.Identifiability
import NondimVerify.Rational

/-! # Where the theory stops: every hypothesis is needed

Each general theorem has hypotheses. A hypothesis that could be dropped would be a sign that
the theorem is stated too weakly; a conclusion that survives when a hypothesis fails would be
a sign the tests are not testing anything. This file gives, for each hypothesis, a concrete
situation in which it fails *and the conclusion fails with it*. It also records the two
places where the definitions are deliberately stricter than the mathematics.

Nothing here is used by the library. These are the fences around it.
-/

open NondimVerify Matrix

namespace NondimVerifyTest.Limits

/-! ## 1. `map_solution` needs a symmetry

`dx/dt = 1` has the solution `x(t) = t`. Doubling `x` without touching time is not a symmetry,
and the doubled curve `2t` is not a solution. -/

noncomputable def clock : LaurentSystem 1 where
  terms := ![[⟨1, ![0]⟩]]

def doubling : Matrix (Fin 1) (Fin 1) ℤ := !![1]

theorem doubling_not_symmetry : ¬ clock.IsSymmetry doubling ![0] := by decide +kernel

theorem clock_solution : clock.IsSolution fun t => ![t] := by
  intro i t
  fin_cases i
  simpa [LaurentSystem.rhs, Term.eval, monomial, clock] using hasDerivAt_id' t

theorem doubled_not_solution :
    ¬ clock.IsSolution fun s => scale doubling ![2] (![s / timeFactor ![(2 : ℝ)] ![0]]) := by
  intro h
  have h1 := h 0 0
  have h2 : HasDerivAt (fun s : ℝ => s * 2) 2 0 := by simpa using (hasDerivAt_id' (0 : ℝ)).mul_const 2
  simp [LaurentSystem.rhs, Term.eval, monomial, clock, scale, doubling, timeFactor] at h1
  have := h1.unique h2
  norm_num at this

-- The right scaling of this system changes x and t together, and that one *is* a symmetry.
example : clock.IsSymmetry doubling ![1] := by decide +kernel

/-! ## 2. `IsSymmetry` is a check on the written terms (sufficient, not necessary)

`dx/dt = 0 · x⁵` is the same vector field as `dx/dt = 0`, for which every scaling is a symmetry.
But the check reads the exponents of the term as written and says no. The exporter never emits
zero terms (tested on the Python side), so certificates are unaffected; the point is that a
"no" from `IsSymmetry` is a statement about the data, a "yes" is a statement about solutions. -/

noncomputable def zeroTerm : LaurentSystem 1 where
  terms := ![[⟨0, ![5]⟩]]

example (x : Fin 1 → ℝ) : zeroTerm.rhs 0 x = 0 := by simp [LaurentSystem.rhs, Term.eval, zeroTerm]
example : ¬ zeroTerm.IsSymmetry doubling ![0] := by decide +kernel
example : (⟨![[]]⟩ : LaurentSystem 1).IsSymmetry doubling ![0] := by decide +kernel

/-! ## 3. Normalizing needs positive values

Scalings multiply by positive numbers, so a parameter equal to zero stays zero and a negative
one stays negative. -/

example (lam : Fin 1 → ℝ) : scale doubling lam ![0] 0 ≠ 1 := by simp [scale]

example (lam : Fin 1 → ℝ) (h : ∀ j, 0 < lam j) : scale doubling lam ![-3] 0 ≠ 1 := by
  have : scale doubling lam ![-3] 0 < 0 := by
    simp [scale, doubling]
    exact h 0
  exact fun h1 => by rw [h1] at this; norm_num at this

/-! ## 4. The "no" direction needs distinct parameters

If the same parameter is listed twice, the selected columns are dependent (kernel vector
`(1, -1)`), yet normalization is of course possible. So `not_normalizable_of_kernel_vector`
would be false without `Function.Injective S`. -/

theorem duplicate_has_kernel_vector :
    (doubling.submatrix id ![0, 0]) *ᵥ ![1, -1] = 0 := by decide +kernel

theorem duplicate_still_normalizable (c : Fin 1 → ℝ) (hc : 0 < c 0) :
    ∃ lam : Fin 1 → ℝ, (∀ j, 0 < lam j) ∧ ∀ i, scale doubling lam c ((![0, 0] : Fin 2 → Fin 1) i) = 1 := by
  refine ⟨![(c 0)⁻¹], fun j => by fin_cases j; simpa using hc, fun i => ?_⟩
  fin_cases i <;> simp [scale, doubling, hc.ne']

example : ¬ Function.Injective (![0, 0] : Fin 2 → Fin 1) := by decide

/-! ## 5. The left inverse needs `d ≠ 0`, and `d` need not be 1

With `d = 0` the "certificate" `G = 0` exists for every matrix and proves nothing. With `d = 2`
the certificate is genuine: `x ↦ λ² x` can still be normalized, using a square root. An
integer-only method (unimodular matrices, as in the Hermite normal form) cannot express that
scaling; the left-inverse certificate can. -/

example (B : Matrix (Fin 2) (Fin 2) ℤ) :
    (0 : Matrix (Fin 2) (Fin 2) ℤ) * B = (0 : ℤ) • (1 : Matrix (Fin 2) (Fin 2) ℤ) := by simp

example (c : Fin 1 → ℝ) (hc : 0 < c 0) :
    ∃ lam : Fin 1 → ℝ, (∀ j, 0 < lam j) ∧ ∀ i, scale (!![2] : Matrix (Fin 1) (Fin 1) ℤ) lam c (id i) = 1 :=
  exists_normalizing_scaling !![2] id !![1] 2 (by decide) (by decide +kernel) c
    (fun i => by fin_cases i; exact hc)

/-! ## 6. Buckingham Pi needs the groups to span

Two lengths `a`, `b`. Their ratio is unit-independent. If we forget to list it (`P` has no
columns), the "groups" of any two configurations agree vacuously but the ratio does not. -/

def lengths : Matrix (Fin 1) (Fin 2) ℤ := !![1, 1]
def noGroups : Matrix (Fin 2) (Fin 0) ℤ := Matrix.of fun _ j => j.elim0

theorem ratio_unitInvariant : UnitInvariant lengths fun q => q 0 / q 1 := by
  intro lam q hlam hq
  have h := (hlam 0).ne'
  have h1 := (hq 1).ne'
  simp [scale, lengths]
  field_simp

theorem pi_fails_without_spanning :
    piGroups noGroups ![1, 1] = piGroups noGroups ![2, 1] ∧
      (fun q : Fin 2 → ℝ => q 0 / q 1) ![1, 1] ≠ (fun q : Fin 2 → ℝ => q 0 / q 1) ![2, 1] :=
  ⟨funext fun j => j.elim0, by norm_num⟩

-- and indeed the spanning hypothesis is false for the empty list of groups
example : ¬ ∀ v : Fin 2 → ℝ, toReal lengths *ᵥ v = 0 → ∃ w : Fin 0 → ℝ, v = toReal noGroups *ᵥ w := by
  intro h
  obtain ⟨w, hw⟩ := h ![1, -1] (by
    funext i; fin_cases i; simp [toReal, lengths, Matrix.mulVec, dotProduct, Fin.sum_univ_succ])
  have := congrFun hw 0
  simp [Matrix.mulVec, dotProduct] at this

/-! ## 7. Buckingham Pi lives on positive quantities

One length, nothing dimensionless. "Is it positive?" is unit-independent (units are positive),
has no dimensionless group to depend on, and still distinguishes `1` from `-1`. The theorem
does not apply because `-1` is not positive: scalings cannot change a sign. -/

def oneLength : Matrix (Fin 1) (Fin 1) ℤ := !![1]

theorem sign_unitInvariant : UnitInvariant oneLength fun q => decide (0 < q 0) := by
  intro lam q hlam hq
  have : 0 < scale oneLength lam q 0 := by
    simp [scale, oneLength]
    exact mul_pos (hq 0) (hlam 0)
  simp [this, hq 0]

example : (fun q : Fin 1 → ℝ => decide (0 < q 0)) ![1] ≠ (fun q : Fin 1 → ℝ => decide (0 < q 0)) ![-1] := by
  simp

/-! ## 8. Spanning is weaker than unimodularity (and that is fine)

For the Pi theorem the groups only need to span over the reals. `(a b)²` is a legitimate single
group for `D = (1, -1)` even though `(2, 2)` is not a primitive integer vector, so no unimodular
certificate exists for it. The theorem still applies, with the spanning proved directly. -/

def recip : Matrix (Fin 1) (Fin 2) ℤ := !![1, -1]
def squared : Matrix (Fin 2) (Fin 1) ℤ := !![2; 2]

theorem squared_spans : ∀ v : Fin 2 → ℝ, toReal recip *ᵥ v = 0 → ∃ w : Fin 1 → ℝ, v = toReal squared *ᵥ w := by
  intro v hv
  have h := congrFun hv 0
  simp [toReal, recip, Matrix.mulVec, dotProduct, Fin.sum_univ_succ] at h
  refine ⟨![v 0 / 2], ?_⟩
  funext i
  fin_cases i <;> simp [toReal, squared, Matrix.mulVec, dotProduct] <;> linarith

example (f : (Fin 2 → ℝ) → ℝ) (hf : UnitInvariant recip f) (q q' : Fin 2 → ℝ)
    (hq : ∀ i, 0 < q i) (hq' : ∀ i, 0 < q' i) (h : piGroups squared q = piGroups squared q') :
    f q = f q' :=
  buckingham_pi recip squared squared_spans f hf q q' hq hq' h

/-! ## 9. With no scalings, reduction is the identity

`r = 0`: there are no auxiliary monomials, every variable is its own invariant, and
reconstruction returns the point unchanged. -/

example (π : Fin 2 → ℝ) : reconstruct (1 : Matrix (Fin 2) (Fin 2) ℤ) π = π := by
  funext p; fin_cases p <;> simp [reconstruct, monomial, Matrix.one_apply]

example (A : Matrix (Fin 0) (Fin 2) ℤ) (lam : Fin 0 → ℝ) (x : Fin 2 → ℝ) : scale A lam x = x := by
  funext i; simp [scale]

/-! ## 10. The cross-section's coordinates need not be the tool's new variables

On the cross-section (auxiliary monomials = 1) a state is recovered from the invariants through
`Wd`. For the textbook models that gives `x = ν` exactly. In general it does not: the matrix
below is what desr returns for `dx/dt = -a y - c x y²`, `dy/dt = b x y - c x²` (variables
`a, b, c, x, y`; invariants `κ, ν₀, ν₁`), and there `x = ν₀ / κ³` on the cross-section.

A randomly generated model exposed this: an earlier certificate format stated the reduced
equations for the cross-section coordinates and could not certify this (correct) answer. The
certificates now state them for the tool's own new variables along the original solution
(`IsSolution.hasDerivAt_newVariable`), which needs no such coincidence. -/

def WdSkew : Matrix (Fin 3) (Fin 5) ℤ := !![0, 3, 4, -3, -2; 0, 0, 0, 1, 0; 0, 0, 0, 0, 1]

example (π : Fin 3 → ℝ) : reconstruct WdSkew π 3 = π 1 / π 0 ^ 3 := by
  simp [reconstruct, monomial, WdSkew, Fin.prod_univ_succ]
  ring

-- so the state and its new variable differ there unless κ = 1
example : reconstruct WdSkew ![2, 1, 1] 3 ≠ (![2, 1, 1] : Fin 3 → ℝ) 1 := by
  simp [reconstruct, monomial, WdSkew, Fin.prod_univ_succ]
  norm_num

/-! ## 11. The identifiability test goes one way only

`dx/dt = a - b`, measured `x`. Only the difference `a - b` matters, so `a` is not identifiable.
But no scaling shows it: every scaling symmetry that fixes time and the output has weight zero
on `a`. A method that looks only at scalings reports nothing here, which must not be read as
"identifiable" (the point of Villaverde & Massonis's reply to Castro & de Boer). -/

noncomputable def difference : LaurentSystem 3 where
  terms := ![[⟨1, ![0, 1, 0]⟩, ⟨-1, ![0, 0, 1]⟩], [], []]

noncomputable def seeX : List (Term 3) := [⟨1, ![1, 0, 0]⟩]

theorem no_scaling_moves_a (A : Matrix (Fin 1) (Fin 3) ℤ) (hsym : difference.IsSymmetry A 0)
    (hout : OutputInvariant A [seeX]) : A 0 1 = 0 := by
  have h1 := hsym 0 ⟨1, ![0, 1, 0]⟩ (by simp [difference]) 0
  have h2 := hout seeX (by simp) ⟨1, ![1, 0, 0]⟩ (by simp [seeX]) 0
  simp [Matrix.mulVec, dotProduct, Fin.sum_univ_succ] at h1 h2
  omega

theorem a_not_identifiable : ¬ difference.Identifiable [seeX] 1 := by
  intro hid
  -- two solutions with the same x and different a: (x, a, b) = (1, 1, 1) and (1, 2, 2)
  have sol : ∀ c : ℝ, difference.IsSolution fun _ => ![1, c, c] := fun c i t => by
    fin_cases i
    · simpa [LaurentSystem.rhs, Term.eval, monomial, difference, Fin.prod_univ_succ]
        using hasDerivAt_const t (1 : ℝ)
    · simpa [LaurentSystem.rhs, difference] using hasDerivAt_const t c
    · simpa [LaurentSystem.rhs, difference] using hasDerivAt_const t c
  have := hid (fun _ => ![1, 1, 1]) (fun _ => ![1, 2, 2]) (sol 1) (sol 2)
    (fun t o ho => by simp at ho; subst ho; simp [poly, Term.eval, monomial, seeX, Fin.prod_univ_succ])
  norm_num at this

/-! ## 12. An output-preserving scaling must not rescale time

`dx/dt = k`, measured `x`. Changing the unit of time (`t ↦ λ t`, `k ↦ k / λ`) is a symmetry and
does not change the *value* of `x`, but it changes when each value occurs. And indeed `k` is
identifiable here: it is the slope of the measured curve. The hypothesis `τ = 0` in
`IsSymmetry.not_identifiable` cannot be dropped. -/

noncomputable def growth : LaurentSystem 2 where
  terms := ![[⟨1, ![0, 1]⟩], []]

noncomputable def seeX₂ : List (Term 2) := [⟨1, ![1, 0]⟩]

def timeUnit : Matrix (Fin 1) (Fin 2) ℤ := !![0, -1]

theorem timeUnit_symmetry : growth.IsSymmetry timeUnit ![1] := by decide +kernel
theorem timeUnit_output : OutputInvariant timeUnit [seeX₂] := by decide +kernel

theorem slope_identifiable : growth.Identifiable [seeX₂] 1 := by
  intro x x' hx hx' hsame
  have hfun : (fun s => x' s 0) = fun s => x s 0 := funext fun s => by
    have := hsame s seeX₂ (by simp)
    simpa [poly, Term.eval, monomial, seeX₂, Fin.prod_univ_succ] using this
  have h1 := hx 0 0
  have h2 := hx' 0 0
  rw [hfun] at h2
  have := h2.unique h1
  simpa [LaurentSystem.rhs, Term.eval, monomial, growth, Fin.prod_univ_succ] using this

/-! ## 13. "For every positive value" matters in the parameter count

Two parameters that always scale together cannot both be normalized in general
(`not_normalizable_of_kernel_vector`), but for particular values, here equal ones, they can.
The count theorems are statements about all values, not about one data set. -/

example : ∃ lam : Fin 1 → ℝ, (∀ j, 0 < lam j) ∧
    ∀ i, scale (!![1, 1] : Matrix (Fin 1) (Fin 2) ℤ) lam ![3, 3] i = 1 := by
  refine ⟨![1 / 3], fun j => by fin_cases j; norm_num, fun i => ?_⟩
  fin_cases i <;> simp [scale]

/-! ## 14. Where a denominator vanishes, the rational theory says nothing useful

Lean's division by zero is zero, so a quotient with a vanishing denominator evaluates to `0` and
the theorems hold there trivially. A model is only meaningful where its denominators are
nonzero; the theory does not check that for you. -/

example : (⟨[⟨1, ![0]⟩], [⟨1, ![1]⟩]⟩ : Frac 1).eval ![0] = 0 := by
  simp [Frac.eval, poly, Term.eval, monomial]

end NondimVerifyTest.Limits

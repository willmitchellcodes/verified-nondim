import Mathlib.Tactic.NormRank
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Ring
import Mathlib.Tactic.Positivity
import Mathlib.LinearAlgebra.Matrix.Rank
import Mathlib.LinearAlgebra.Matrix.ToLin
import Mathlib.LinearAlgebra.Matrix.Notation
import Mathlib.Analysis.Calculus.Deriv.Comp
import Mathlib.Analysis.Calculus.Deriv.Mul
import Mathlib.Analysis.SpecialFunctions.Exp

/-!
# Basic definitions for verified nondimensionalization

Conventions (shared with the Python solver in `python/nondim`):

* The model's quantities are numbered `0, …, n-1` in the order `t, states…, params…`.
* A *scaling* is an integer vector `a`: quantity `i` is multiplied by `λ ^ a i`.
  A family of `r` scalings is a matrix `A : Matrix (Fin r) (Fin n) ℤ` (one scaling per row).
* The *exponent matrix* `K : Matrix (Fin n) (Fin m) ℤ` has one column per monomial that
  must stay invariant. The scalings are exactly the rows `a` with `a ᵥ* K = 0`, i.e. `A * K = 0`.

Where things live:

* `Basic.lean` (this file): `monomial`, `scale`, and `monomial_scale`: if `A *ᵥ k = 0`, the
  monomial with exponents `k` is unchanged by every scaling in `A`. This is "dimensionless".
* `Theory.lean`: the general linear algebra (rank–nullity for scalings, maximality).
* `SIR.lean`: hand-written proofs that solutions of the SIR model and its reduction correspond.
* `Cert/*.lean`: generated certificates, one per model.
* `Exercises.lean`: open problems for you, not part of the default build.
-/

namespace NondimVerify

open Matrix

/-! ## A tactic for the generated chain-rule checks -/

/-- Close an identity between rational expressions in nonzero real variables.
Tries plain `ring` first, then clears denominators with `field_simp`. -/
macro "rhs_check" : tactic =>
  `(tactic| first | ring1 | (field_simp; ring1) | field_simp)

/-! ## Scalings act on monomials -/

/-- The monomial `∏ i, x i ^ k i` with integer exponents `k`. -/
noncomputable def monomial {n : ℕ} (x : Fin n → ℝ) (k : Fin n → ℤ) : ℝ :=
  ∏ i, x i ^ k i

/-- Apply the scalings with exponent matrix `A` and scale factors `lam` to the point `x`:
quantity `i` is multiplied by `∏ j, lam j ^ A j i`. -/
noncomputable def scale {r n : ℕ} (A : Matrix (Fin r) (Fin n) ℤ) (lam : Fin r → ℝ)
    (x : Fin n → ℝ) : Fin n → ℝ :=
  fun i => x i * ∏ j, lam j ^ A j i

lemma zpow_sum_of_ne_zero {ι : Type*} (s : Finset ι) {a : ℝ} (ha : a ≠ 0) (f : ι → ℤ) :
    a ^ (∑ i ∈ s, f i) = ∏ i ∈ s, a ^ f i := by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | insert i s hi ih => rw [Finset.sum_insert hi, Finset.prod_insert hi, zpow_add₀ ha, ih]

/-- **Invariance lemma** (Tanburn et al. 2025, Lemma 3.1, monomial case).
If `A *ᵥ k = 0` then the monomial with exponent vector `k` takes the same value before and
after scaling, for every choice of nonzero scale factors. -/
theorem monomial_scale {r n : ℕ} (A : Matrix (Fin r) (Fin n) ℤ) (lam : Fin r → ℝ)
    (hlam : ∀ j, lam j ≠ 0) (x : Fin n → ℝ) (k : Fin n → ℤ) (hk : A *ᵥ k = 0) :
    monomial (scale A lam x) k = monomial x k := by
  unfold monomial scale
  simp_rw [mul_zpow, Finset.prod_mul_distrib]
  suffices h : ∏ i, (∏ j, lam j ^ A j i) ^ k i = 1 by rw [h, mul_one]
  calc ∏ i, (∏ j, lam j ^ A j i) ^ k i
      = ∏ i, ∏ j, lam j ^ (A j i * k i) := by
        refine Finset.prod_congr rfl fun i _ => ?_
        rw [← Finset.prod_zpow]
        refine Finset.prod_congr rfl fun j _ => ?_
        rw [zpow_mul]
    _ = ∏ j, ∏ i, lam j ^ (A j i * k i) := Finset.prod_comm
    _ = ∏ j, lam j ^ (A *ᵥ k) j := by
        refine Finset.prod_congr rfl fun j _ => ?_
        rw [show (A *ᵥ k) j = ∑ i, A j i * k i from rfl, zpow_sum_of_ne_zero _ (hlam j)]
    _ = 1 := by simp [hk]

end NondimVerify

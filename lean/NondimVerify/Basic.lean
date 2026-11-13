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

/-- **Weighted scaling lemma.** Scaling multiplies the monomial with exponents `k` by
`∏ j, lam j ^ (A *ᵥ k) j`: the vector `A *ᵥ k` lists the *weights* of the monomial under each
scaling. (`monomial_scale` is the special case where all weights are zero.) -/
theorem monomial_scale_eq {r n : ℕ} (A : Matrix (Fin r) (Fin n) ℤ) (lam : Fin r → ℝ)
    (hlam : ∀ j, lam j ≠ 0) (x : Fin n → ℝ) (k : Fin n → ℤ) :
    monomial (scale A lam x) k = (∏ j, lam j ^ (A *ᵥ k) j) * monomial x k := by
  unfold monomial scale
  simp_rw [mul_zpow, Finset.prod_mul_distrib]
  rw [mul_comm]
  congr 1
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

/-! ## Monomials of monomials -/

lemma monomial_pos {n : ℕ} (x : Fin n → ℝ) (hx : ∀ i, 0 < x i) (k : Fin n → ℤ) : 0 < monomial x k :=
  Finset.prod_pos fun i _ => zpow_pos (hx i) _

lemma monomial_add {n : ℕ} (x : Fin n → ℝ) (hx : ∀ i, x i ≠ 0) (k l : Fin n → ℤ) :
    monomial x (k + l) = monomial x k * monomial x l := by
  unfold monomial
  rw [← Finset.prod_mul_distrib]
  exact Finset.prod_congr rfl fun i _ => zpow_add₀ (hx i) _ _

lemma monomial_single {n : ℕ} (x : Fin n → ℝ) (p : Fin n) :
    monomial x (fun i => if i = p then 1 else 0) = x p := by
  unfold monomial
  rw [Finset.prod_eq_single p]
  · simp
  · intro i _ hne; simp [hne]
  · intro h; exact absurd (Finset.mem_univ _) h

/-- A monomial in monomials is a monomial: exponents compose by the matrix–vector product. -/
theorem monomial_monomial {n m : ℕ} (V : Matrix (Fin n) (Fin m) ℤ) (x : Fin n → ℝ)
    (hx : ∀ i, x i ≠ 0) (k : Fin m → ℤ) :
    monomial (fun j => monomial x fun i => V i j) k = monomial x (V *ᵥ k) := by
  unfold monomial
  calc ∏ j, (∏ i, x i ^ V i j) ^ k j
      = ∏ j, ∏ i, x i ^ (V i j * k j) := by
        refine Finset.prod_congr rfl fun j _ => ?_
        rw [← Finset.prod_zpow]
        exact Finset.prod_congr rfl fun i _ => by rw [zpow_mul]
    _ = ∏ i, ∏ j, x i ^ (V i j * k j) := Finset.prod_comm
    _ = ∏ i, x i ^ (V *ᵥ k) i := by
        refine Finset.prod_congr rfl fun i _ => ?_
        rw [show (V *ᵥ k) i = ∑ j, V i j * k j from rfl, zpow_sum_of_ne_zero _ (hx i)]

/-- A monomial only looks at the coordinates where its exponent is nonzero. -/
lemma monomial_congr_of_support {n : ℕ} (x x' : Fin n → ℝ) (k : Fin n → ℤ)
    (h : ∀ i, k i ≠ 0 → x i = x' i) : monomial x k = monomial x' k := by
  unfold monomial
  refine Finset.prod_congr rfl fun i _ => ?_
  by_cases hk : k i = 0
  · simp [hk]
  · rw [h i hk]

lemma exp_zpow (x : ℝ) (m : ℤ) : Real.exp x ^ m = Real.exp (m * x) := by
  obtain ⟨k, rfl | rfl⟩ := m.eq_nat_or_neg
  · simp [Real.exp_nat_mul]
  · simp [Real.exp_nat_mul, Real.exp_neg]

end NondimVerify

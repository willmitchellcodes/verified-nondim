import NondimVerify.System
import Mathlib.LinearAlgebra.Basis.VectorSpace

/-!
# The constraint criterion, as one equivalence

"Can these `k` parameters all be scaled to 1?" has a linear-algebra answer:

    for every positive choice of values there is a scaling making them 1
      ⟺  the chosen columns of the scaling matrix are linearly independent
      ⟺  those columns have rank `k`.

`System.lean` proves the two directions from explicit certificates (a left inverse for "yes",
a kernel vector for "no"). This file proves that one of the two certificates always exists
(`left_inverse_or_kernel`), which turns the two implications into equivalences
(`normalizable_iff`, `normalizable_iff_rank`).
-/

namespace NondimVerify

open Matrix

/-- A rational number times a multiple of its denominator is an integer. -/
lemma exists_int_eq_mul (q : ℚ) (D : ℤ) (h : (q.den : ℤ) ∣ D) : ∃ z : ℤ, (z : ℚ) = q * D := by
  obtain ⟨e, rfl⟩ := h
  refine ⟨q.num * e, ?_⟩
  push_cast
  rw [← mul_assoc, Rat.mul_den_eq_num]

/-- Clearing the denominators of finitely many rational numbers at once. -/
lemma exists_common_denominator {ι : Type*} [Fintype ι] (q : ι → ℚ) :
    ∃ D : ℤ, D ≠ 0 ∧ ∀ i, ∃ z : ℤ, (z : ℚ) = q i * D := by
  refine ⟨∏ i, ((q i).den : ℤ), Finset.prod_ne_zero_iff.mpr fun i _ => ?_, fun i => ?_⟩
  · exact_mod_cast (q i).den_nz
  · exact exists_int_eq_mul _ _ (Finset.dvd_prod_of_mem _ (Finset.mem_univ i))

variable {r k : ℕ}

/-- The rational kernel of an integer matrix is trivial exactly when its integer kernel is. -/
theorem ker_eq_bot_iff_int (B : Matrix (Fin r) (Fin k) ℤ) :
    LinearMap.ker (B.map (Int.castRingHom ℚ)).mulVecLin = ⊥ ↔
      ∀ v : Fin k → ℤ, B *ᵥ v = 0 → v = 0 := by
  constructor
  · intro hker v hBv
    have hmem : (fun i => (v i : ℚ)) ∈ LinearMap.ker (B.map (Int.castRingHom ℚ)).mulVecLin := by
      rw [LinearMap.mem_ker, Matrix.mulVecLin_apply]
      funext a
      have := congrArg (Int.cast : ℤ → ℚ) (congrFun hBv a)
      simpa [Matrix.mulVec, dotProduct] using this
    rw [hker, Submodule.mem_bot] at hmem
    funext i
    have := congrFun hmem i
    simpa using this
  · intro hint
    rw [Submodule.eq_bot_iff]
    intro v hv
    rw [LinearMap.mem_ker, Matrix.mulVecLin_apply] at hv
    obtain ⟨D, hD, hz⟩ := exists_common_denominator v
    choose w hw using hz
    have hD' : (D : ℚ) ≠ 0 := by exact_mod_cast hD
    have hw0 : w = 0 := by
      apply hint
      funext a
      apply Int.cast_injective (α := ℚ)
      have h1 := congrFun hv a
      simp only [Matrix.mulVec, dotProduct, Matrix.map_apply, Int.coe_castRingHom,
        Pi.zero_apply] at h1 ⊢
      push_cast
      simp only [hw]
      calc ∑ j, (B a j : ℚ) * (v j * D) = (∑ j, (B a j : ℚ) * v j) * D := by
            rw [Finset.sum_mul]; exact Finset.sum_congr rfl fun j _ => by ring
        _ = 0 := by rw [h1, zero_mul]
    funext i
    have := hw i
    rw [hw0] at this
    simp only [Pi.zero_apply, Int.cast_zero] at this
    rcases mul_eq_zero.mp this.symm with h | h
    · exact h
    · exact absurd h hD'

/-- **One of the two certificates always exists.** An integer matrix either has a left inverse
up to a nonzero factor (its columns are independent) or a nonzero integer kernel vector. -/
theorem left_inverse_or_kernel (B : Matrix (Fin r) (Fin k) ℤ) :
    (∃ (G : Matrix (Fin k) (Fin r) ℤ) (d : ℤ), d ≠ 0 ∧ G * B = d • (1 : Matrix (Fin k) (Fin k) ℤ)) ∨
      ∃ v : Fin k → ℤ, v ≠ 0 ∧ B *ᵥ v = 0 := by
  by_cases hint : ∀ v : Fin k → ℤ, B *ᵥ v = 0 → v = 0
  · left
    have hker := (ker_eq_bot_iff_int B).mpr hint
    obtain ⟨g, hg⟩ := (B.map (Int.castRingHom ℚ)).mulVecLin.exists_leftInverse_of_injective hker
    have hL : LinearMap.toMatrix' g * B.map (Int.castRingHom ℚ) = 1 := by
      have h1 : LinearMap.toMatrix' (g ∘ₗ (B.map (Int.castRingHom ℚ)).mulVecLin) = 1 := by
        rw [hg, LinearMap.toMatrix'_id]
      rwa [LinearMap.toMatrix'_comp, ← Matrix.toLin'_apply', LinearMap.toMatrix'_toLin'] at h1
    obtain ⟨D, hD, hz⟩ := exists_common_denominator
      (fun p : Fin k × Fin r => LinearMap.toMatrix' g p.1 p.2)
    choose G hG using hz
    refine ⟨Matrix.of fun a j => G (a, j), D, hD, ?_⟩
    ext a b
    apply Int.cast_injective (α := ℚ)
    have h1 := congrFun (congrFun hL a) b
    simp only [Matrix.mul_apply, Matrix.map_apply, Int.coe_castRingHom] at h1
    simp only [Matrix.mul_apply, Matrix.of_apply, Matrix.smul_apply, smul_eq_mul]
    push_cast
    simp only [hG]
    have hone : (((1 : Matrix (Fin k) (Fin k) ℤ) a b : ℤ) : ℚ) = (1 : Matrix (Fin k) (Fin k) ℚ) a b := by
      simp only [Matrix.one_apply]; split_ifs <;> simp
    rw [hone, ← h1, Finset.mul_sum]
    exact Finset.sum_congr rfl fun j _ => by ring
  · right
    obtain ⟨v, hv'⟩ := not_forall.mp hint
    obtain ⟨hBv, hv⟩ := Classical.not_imp.mp hv'
    exact ⟨v, hv, hBv⟩

/-- **The constraint criterion.** The parameters `S` can be scaled to 1 for *every* positive
choice of values if and only if the columns `S` of the scaling matrix are linearly independent. -/
theorem normalizable_iff {n : ℕ} (A : Matrix (Fin r) (Fin n) ℤ) (S : Fin k → Fin n)
    (hS : Function.Injective S) :
    (∀ c : Fin n → ℝ, (∀ i, 0 < c i) →
        ∃ lam : Fin r → ℝ, (∀ j, 0 < lam j) ∧ ∀ i, scale A lam c (S i) = 1) ↔
      ∀ v : Fin k → ℤ, A.submatrix id S *ᵥ v = 0 → v = 0 := by
  constructor
  · intro h v hAv
    by_contra hv
    obtain ⟨c, hc, hno⟩ := not_normalizable_of_kernel_vector A S hS v hv hAv
    obtain ⟨lam, hlam, h1⟩ := h c hc
    exact hno lam (fun j => (hlam j).ne') h1
  · intro h c hc
    rcases left_inverse_or_kernel (A.submatrix id S) with ⟨G, d, hd, hG⟩ | ⟨v, hv, hAv⟩
    · exact exists_normalizing_scaling A S G d hd hG c fun i => hc _
    · exact absurd (h v hAv) hv

/-- Independence of the columns of an integer matrix, as a rank over `ℚ`. -/
theorem independent_iff_rank (B : Matrix (Fin r) (Fin k) ℤ) :
    (∀ v : Fin k → ℤ, B *ᵥ v = 0 → v = 0) ↔ (B.map (Int.castRingHom ℚ)).rank = k := by
  rw [← ker_eq_bot_iff_int]
  have h := LinearMap.finrank_range_add_finrank_ker (B.map (Int.castRingHom ℚ)).mulVecLin
  rw [Module.finrank_pi, Fintype.card_fin] at h
  have hr : Module.finrank ℚ (LinearMap.range (B.map (Int.castRingHom ℚ)).mulVecLin)
      = (B.map (Int.castRingHom ℚ)).rank := rfl
  rw [← Submodule.finrank_eq_zero]
  omega

/-- **The constraint criterion, as a rank.** This is the test the solver runs
(`constraints.solve`): the selected columns must have full column rank. -/
theorem normalizable_iff_rank {n : ℕ} (A : Matrix (Fin r) (Fin n) ℤ) (S : Fin k → Fin n)
    (hS : Function.Injective S) :
    (∀ c : Fin n → ℝ, (∀ i, 0 < c i) →
        ∃ lam : Fin r → ℝ, (∀ j, 0 < lam j) ∧ ∀ i, scale A lam c (S i) = 1) ↔
      ((A.submatrix id S).map (Int.castRingHom ℚ)).rank = k := by
  rw [normalizable_iff A S hS, independent_iff_rank]

end NondimVerify

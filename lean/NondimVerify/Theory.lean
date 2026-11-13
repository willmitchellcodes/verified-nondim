import NondimVerify.Basic

/-!
# General theory: why the certificates mean what we say they mean

Each generated certificate proves three facts about concrete integer matrices:

    symmetries : A * K = 0        rank_K : K.rank = ρ        rank_A : A.rank = r   (with r = n - ρ)

This file proves, once and for all, what follows from facts of that shape:

* `finrank_scalingSpace`: the scalings of a system form a space of dimension `n - rank K`
  (rank–nullity).
* `maximal_of_rank`: if `A * K = 0`, the rows of `A` are independent, and there are
  `n - rank K` of them, then **every** scaling is a combination of rows of `A`. So the
  untrusted solver did not miss a symmetry, and no scaling can remove more parameters.

These are stated over `ℚ`; the certificates use `ℤ` matrices (see `Exercises.lean` for the bridge).
-/

namespace NondimVerify

open Matrix Module

/-- All rational scalings of a system with exponent matrix `K`: row vectors `a` with
`a ᵥ* K = 0`. -/
def scalingSpace {n m : ℕ} (K : Matrix (Fin n) (Fin m) ℚ) : Submodule ℚ (Fin n → ℚ) :=
  LinearMap.ker K.vecMulLinear

lemma mem_scalingSpace {n m : ℕ} (K : Matrix (Fin n) (Fin m) ℚ) (a : Fin n → ℚ) :
    a ∈ scalingSpace K ↔ a ᵥ* K = 0 := by
  simp [scalingSpace, LinearMap.mem_ker]

/-- **Rank–nullity for scalings.** The scalings form a space of dimension `n - rank K`. -/
theorem finrank_scalingSpace {n m : ℕ} (K : Matrix (Fin n) (Fin m) ℚ) :
    finrank ℚ (scalingSpace K) = n - K.rank := by
  have h := LinearMap.finrank_range_add_finrank_ker K.vecMulLinear
  have hr : finrank ℚ (LinearMap.range K.vecMulLinear) = K.rank := by
    rw [← Matrix.rank_transpose K, Matrix.rank, Matrix.mulVecLin_transpose]
  rw [hr, Module.finrank_pi, Fintype.card_fin] at h
  unfold scalingSpace
  omega

/-- **Maximality.** Independent scalings, `n - rank K` of them, span all scalings. -/
theorem maximal_of_rank {r n m : ℕ} (A : Matrix (Fin r) (Fin n) ℚ)
    (K : Matrix (Fin n) (Fin m) ℚ) (hAK : A * K = 0) (hA : A.rank = r)
    (hr : r = n - K.rank) :
    Submodule.span ℚ (Set.range A.row) = scalingSpace K := by
  have hle : Submodule.span ℚ (Set.range A.row) ≤ scalingSpace K := by
    rw [Submodule.span_le]
    rintro _ ⟨i, rfl⟩
    rw [SetLike.mem_coe, mem_scalingSpace]
    show A.row i ᵥ* K = 0
    exact congrFun hAK i
  refine Submodule.eq_of_le_of_finrank_eq hle ?_
  rw [finrank_scalingSpace, ← hr, ← Matrix.rank_eq_finrank_span_row, hA]

end NondimVerify

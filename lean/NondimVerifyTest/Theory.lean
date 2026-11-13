import NondimVerify.Theory

/-! # Unit tests: the general theorems applied to tiny hand-checkable systems -/

open NondimVerify Matrix

/-- One quantity `t` and one rate `r`, one monomial `r * t`: exponent matrix `K = (1, 1)ᵀ`. -/
def Ktoy : Matrix (Fin 2) (Fin 1) ℚ := !![1; 1]

/-- The single scaling: `t ↦ λ t`, `r ↦ r / λ`. -/
def Atoy : Matrix (Fin 1) (Fin 2) ℚ := !![1, -1]

example : (![1, -1] : Fin 2 → ℚ) ∈ scalingSpace Ktoy := by
  rw [mem_scalingSpace]; decide +kernel

example : (![1, 0] : Fin 2 → ℚ) ∉ scalingSpace Ktoy := by
  rw [mem_scalingSpace]; decide +kernel

theorem Ktoy_rank : Ktoy.rank = 1 := by unfold Ktoy; eval_rank
theorem Atoy_rank : Atoy.rank = 1 := by unfold Atoy; eval_rank

-- Rank–nullity: 2 quantities, rank 1, so exactly a 1-dimensional family of scalings.
example : Module.finrank ℚ (scalingSpace Ktoy) = 1 := by
  rw [finrank_scalingSpace, Ktoy_rank]

-- Maximality: the one scaling we wrote down generates all of them.
example : Submodule.span ℚ (Set.range Atoy.row) = scalingSpace Ktoy :=
  maximal_of_rank Atoy Ktoy (by decide +kernel) Atoy_rank (by rw [Ktoy_rank])

-- With no constraints at all (K has no columns of information), every vector is a scaling.
example (a : Fin 3 → ℚ) : a ∈ scalingSpace (0 : Matrix (Fin 3) (Fin 2) ℚ) := by
  simp [mem_scalingSpace]

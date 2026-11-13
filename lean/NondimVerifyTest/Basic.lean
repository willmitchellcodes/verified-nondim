import NondimVerify.Basic

/-! # Unit tests: `monomial`, `scale`, `monomial_scale` -/

open NondimVerify Matrix

/-! ## `monomial` computes what we think it computes -/

example : monomial ![2, 3] ![1, 2] = 18 := by
  simp [monomial, Fin.prod_univ_two]; norm_num

example : monomial ![2, 4] ![1, -1] = 1 / 2 := by
  simp [monomial, Fin.prod_univ_two]; norm_num

example (x : Fin 3 → ℝ) : monomial x 0 = 1 := by simp [monomial]

/-! ## `scale` multiplies each quantity by the right power -/

-- One scaling with exponents (1, -1): the first quantity is multiplied by λ, the second divided.
example (lam x y : ℝ) : scale !![1, -1] ![lam] ![x, y] 0 = x * lam := by
  simp [scale]

example (lam x y : ℝ) : scale !![1, -1] ![lam] ![x, y] 1 = y * lam⁻¹ := by
  simp [scale]

-- Scale factors equal to 1 change nothing.
example (A : Matrix (Fin 2) (Fin 3) ℤ) (x : Fin 3 → ℝ) : scale A (fun _ => 1) x = x := by
  funext i; simp [scale]

/-! ## `monomial_scale`: invariance on small hand-made examples -/

-- Time t and a rate r with scaling (1, -1): the product r * t is invariant.
example (lam : Fin 1 → ℝ) (h : ∀ j, lam j ≠ 0) (x : Fin 2 → ℝ) :
    monomial (scale !![1, -1] lam x) ![1, 1] = monomial x ![1, 1] :=
  monomial_scale _ lam h x _ (by decide +kernel)

-- ...but t alone is not: its exponent vector is not killed by the scaling.
example : (!![1, -1] : Matrix (Fin 1) (Fin 2) ℤ) *ᵥ ![1, 0] ≠ 0 := by decide +kernel

-- And concretely: doubling time units changes t.
example : monomial (scale !![1, -1] ![2] ![3, 5]) ![1, 0] ≠ monomial ![3, 5] ![1, 0] := by
  simp [monomial, scale, Fin.prod_univ_two]

/-! ## `zpow_sum_of_ne_zero` -/

example : (2 : ℝ) ^ (∑ i : Fin 3, (![1, -2, 3] : Fin 3 → ℤ) i) = 4 := by
  rw [zpow_sum_of_ne_zero _ (by norm_num)]
  simp [Fin.prod_univ_three]; norm_num

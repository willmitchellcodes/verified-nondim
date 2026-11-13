import NondimVerify.Criterion

/-! # Unit tests: the constraint criterion as an equivalence -/

open NondimVerify Matrix

namespace NondimVerifyTest.Criterion

/-! ## Clearing denominators -/

example : ∃ z : ℤ, (z : ℚ) = (3 / 4 : ℚ) * 8 := ⟨6, by norm_num⟩

example (q : Fin 3 → ℚ) : ∃ D : ℤ, D ≠ 0 ∧ ∀ i, ∃ z : ℤ, (z : ℚ) = q i * D :=
  exists_common_denominator q

/-! ## Exactly one certificate exists -/

-- Independent columns: a left inverse exists. Here it is written down.
example : ∃ (G : Matrix (Fin 2) (Fin 2) ℤ) (d : ℤ), d ≠ 0 ∧
    G * (!![1, 1; 0, 2] : Matrix (Fin 2) (Fin 2) ℤ) = d • (1 : Matrix (Fin 2) (Fin 2) ℤ) :=
  ⟨!![2, -1; 0, 1], 2, by decide, by decide +kernel⟩

-- Dependent columns: a kernel vector exists.
example : ∃ v : Fin 2 → ℤ, v ≠ 0 ∧ (!![1, 1; 2, 2] : Matrix (Fin 2) (Fin 2) ℤ) *ᵥ v = 0 :=
  ⟨![1, -1], by decide, by decide +kernel⟩

-- The two alternatives exclude each other: a left inverse kills every kernel vector.
example (B : Matrix (Fin 3) (Fin 2) ℤ) (G : Matrix (Fin 2) (Fin 3) ℤ) (d : ℤ) (hd : d ≠ 0)
    (hG : G * B = d • (1 : Matrix (Fin 2) (Fin 2) ℤ)) (v : Fin 2 → ℤ) (hv : B *ᵥ v = 0) : v = 0 := by
  have h : (G * B) *ᵥ v = 0 := by rw [← Matrix.mulVec_mulVec, hv, Matrix.mulVec_zero]
  rw [hG, Matrix.smul_mulVec, Matrix.one_mulVec] at h
  funext i
  have := congrFun h i
  simpa [hd] using this

-- More columns than rows can never be independent: the criterion says no before any search.
example (B : Matrix (Fin 1) (Fin 2) ℤ) : ∃ v : Fin 2 → ℤ, v ≠ 0 ∧ B *ᵥ v = 0 := by
  rcases left_inverse_or_kernel B with ⟨G, d, hd, hG⟩ | h
  · exfalso
    -- a 2×2 identity cannot factor through a 1-dimensional space
    have h00 := congrFun (congrFun hG 0) 0
    have h01 := congrFun (congrFun hG 0) 1
    have h10 := congrFun (congrFun hG 1) 0
    have h11 := congrFun (congrFun hG 1) 1
    simp [Matrix.mul_apply] at h00 h01 h10 h11
    rcases h01 with h | h
    · rw [h] at h00; simp at h00; exact hd h00.symm
    · rcases h10 with h' | h'
      · rw [h'] at h11; simp at h11; exact hd h11.symm
      · rw [h'] at h00; simp at h00; exact hd h00.symm
  · exact h

/-! ## The criterion on a concrete scaling matrix

Two scalings acting on three parameters `a, b, c` with weights `(1,0), (0,1), (1,1)`:
any two of them can be normalized, all three cannot. -/

def A : Matrix (Fin 2) (Fin 3) ℤ := !![1, 0, 1; 0, 1, 1]

-- {a, b}: independent columns, so always normalizable.
example (c : Fin 3 → ℝ) (hc : ∀ i, 0 < c i) :
    ∃ lam : Fin 2 → ℝ, (∀ j, 0 < lam j) ∧ ∀ i, scale A lam c (![0, 1] i) = 1 := by
  refine (normalizable_iff A ![0, 1] (by decide)).mpr (fun v hv => ?_) c hc
  have h0 := congrFun hv 0
  have h1 := congrFun hv 1
  simp [A, Matrix.mulVec, dotProduct, Fin.sum_univ_succ] at h0 h1
  funext i; fin_cases i <;> simp [h0, h1]

-- {a, b, c}: three columns in a 2-row matrix are dependent, so NOT always normalizable.
example :
    ¬ ∀ c : Fin 3 → ℝ, (∀ i, 0 < c i) →
      ∃ lam : Fin 2 → ℝ, (∀ j, 0 < lam j) ∧ ∀ i, scale A lam c (id i) = 1 := by
  rw [normalizable_iff A id Function.injective_id]
  intro h
  have := h ![1, 1, -1] (by decide +kernel)
  exact absurd (congrFun this 0) (by decide)

/-! ## Rank form, and its boundary cases -/

-- Asking for nothing (k = 0): rank 0 = 0, always possible.
example (B : Matrix (Fin 2) (Fin 0) ℤ) : (B.map (Int.castRingHom ℚ)).rank = 0 :=
  (independent_iff_rank B).mp fun _ _ => funext fun i => i.elim0

-- No scalings (r = 0) and one parameter: its column is empty, hence dependent, never normalizable.
example : ¬ ∀ v : Fin 1 → ℤ, (0 : Matrix (Fin 0) (Fin 1) ℤ) *ᵥ v = 0 → v = 0 := by
  intro h
  have := h ![1] (by ext i; exact i.elim0)
  exact absurd (congrFun this 0) (by decide)

example (A : Matrix (Fin 2) (Fin 5) ℤ) (S : Fin 2 → Fin 5) (hS : Function.Injective S) :
    (∀ c : Fin 5 → ℝ, (∀ i, 0 < c i) →
        ∃ lam : Fin 2 → ℝ, (∀ j, 0 < lam j) ∧ ∀ i, scale A lam c (S i) = 1) ↔
      ((A.submatrix id S).map (Int.castRingHom ℚ)).rank = 2 :=
  normalizable_iff_rank A S hS

end NondimVerifyTest.Criterion

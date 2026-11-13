import NondimVerify.SIR

/-! # Unit tests: the SIR proofs, instantiated -/

open NondimVerify.SIR

/-! ## Definitions evaluate correctly -/

example : R0 2 1 3 = 6 := by norm_num [R0]
example : fS 2 3 5 = -30 := by norm_num [fS]
example : fI 2 4 3 5 = 10 := by norm_num [fI]
example : gX 6 (1 / 2) (1 / 3) = -1 := by norm_num [gX]
example : gY 6 (1 / 2) (1 / 3) = 2 / 3 := by norm_num [gY]

/-! ## Right-hand sides agree at a concrete point (β = 2, γ = 4, N = 10, S = 3, I = 5) -/

example : gX (R0 2 4 10) (3 / 10) (5 / 10) = fS 2 3 5 / (4 * 10) :=
  rhs_X (by norm_num) (by norm_num) 3 5

example : gY (R0 2 4 10) (3 / 10) (5 / 10) = fI 2 4 3 5 / (4 * 10) :=
  rhs_Y (by norm_num) (by norm_num) 3 5

/-! ## Equilibria -/

-- The disease-free state (any S, I = 0) is an equilibrium of the dimensional model...
example (β γ S : ℝ) : fS β S 0 = 0 ∧ fI β γ S 0 = 0 := by simp [fS, fI]

-- ...hence, by `equilibrium_iff`, of the dimensionless model too.
example (β γ N S : ℝ) (hγ : γ ≠ 0) (hN : N ≠ 0) :
    gX (R0 β γ N) (S / N) (0 / N) = 0 ∧ gY (R0 β γ N) (S / N) (0 / N) = 0 :=
  (equilibrium_iff hγ hN S 0).mp (by simp [fS, fI])

/-! ## Threshold -/

example : 0 < gY 3 (1 / 2) (1 / 10) := (threshold 3 (1 / 2) (1 / 10) (by norm_num)).mpr (by norm_num)
example : ¬ 0 < gY 3 (1 / 4) (1 / 10) := by
  rw [threshold 3 (1 / 4) (1 / 10) (by norm_num)]; norm_num

-- Fully susceptible population: growth iff R₀ > 1.
example (R₀ Y : ℝ) (hY : 0 < Y) : 0 < gY R₀ 1 Y ↔ 1 < R₀ := by
  simpa using threshold R₀ 1 Y hY

/-! ## Trajectories: the constant disease-free solution maps to a constant solution -/

example (β γ N s : ℝ) (hγ : γ ≠ 0) (hN : N ≠ 0) (τ : ℝ) :
    HasDerivAt (fun _ : ℝ => s / N) 0 τ := by
  have h := (trajectory_forward (β := β) hγ hN (S := fun _ => s) (I := fun _ => 0)
    (fun t => by simpa [fS] using hasDerivAt_const t s)
    (fun t => by simpa [fI] using hasDerivAt_const t (0 : ℝ)) τ).1
  simpa [gX] using h

import NondimVerify.Basic

/-!
# SIR: the rescaling to `R₀` is correct (hand-written proofs)

Ellner & Guckenheimer, Ch. 6: with `X = S/N`, `Y = I/N`, `τ = γ t` the SIR model

    dS/dt = -β S I,          dI/dt = β S I - γ I

becomes the one-parameter model

    dX/dτ = -R₀ X Y,         dY/dτ = R₀ X Y - Y,       R₀ = β N / γ.

The generated certificate `NondimVerify/Cert/SIR.lean` checks the algebra (Check 8).
This file proves what we actually care about:

1. `rhs_X`, `rhs_Y`: the right-hand sides agree pointwise (after the chain-rule factor).
2. `equilibrium_iff`: equilibria correspond.
3. `trajectory_forward`: every solution of the original model gives a solution of the
   rescaled model, and `trajectory_backward`: conversely. So *nothing is lost*.
4. `threshold`: the epidemic grows iff `R₀ X > 1`, the textbook threshold.
-/

namespace NondimVerify.SIR

/-- Dimensional right-hand side for `S`. -/
def fS (β S I : ℝ) : ℝ := -(β * S * I)

/-- Dimensional right-hand side for `I`. -/
def fI (β γ S I : ℝ) : ℝ := β * S * I - γ * I

/-- Dimensionless right-hand side for `X = S / N`. -/
def gX (R₀ X Y : ℝ) : ℝ := -(R₀ * X * Y)

/-- Dimensionless right-hand side for `Y = I / N`. -/
def gY (R₀ X Y : ℝ) : ℝ := R₀ * X * Y - Y

/-- The basic reproductive number `R₀ = β N / γ`. -/
noncomputable def R0 (β γ N : ℝ) : ℝ := β * N / γ

variable {β γ N : ℝ}

/-! ## 1. Right-hand sides agree -/

theorem rhs_X (hγ : γ ≠ 0) (hN : N ≠ 0) (S I : ℝ) :
    gX (R0 β γ N) (S / N) (I / N) = fS β S I / (γ * N) := by
  unfold gX fS R0
  rhs_check

theorem rhs_Y (hγ : γ ≠ 0) (hN : N ≠ 0) (S I : ℝ) :
    gY (R0 β γ N) (S / N) (I / N) = fI β γ S I / (γ * N) := by
  unfold gY fI R0
  rhs_check

/-! ## 2. Equilibria correspond -/

theorem equilibrium_iff (hγ : γ ≠ 0) (hN : N ≠ 0) (S I : ℝ) :
    (fS β S I = 0 ∧ fI β γ S I = 0) ↔
      (gX (R0 β γ N) (S / N) (I / N) = 0 ∧ gY (R0 β γ N) (S / N) (I / N) = 0) := by
  rw [rhs_X hγ hN, rhs_Y hγ hN]
  simp [hγ, hN]

/-! ## 3. Solutions correspond (chain rule) -/

/-- If `(S, I)` solves the dimensional SIR model, then `X(τ) = S(τ/γ)/N`, `Y(τ) = I(τ/γ)/N`
solve the dimensionless model. -/
theorem trajectory_forward (hγ : γ ≠ 0) (hN : N ≠ 0) {S I : ℝ → ℝ}
    (hS : ∀ t, HasDerivAt S (fS β (S t) (I t)) t)
    (hI : ∀ t, HasDerivAt I (fI β γ (S t) (I t)) t) (τ : ℝ) :
    HasDerivAt (fun τ => S (τ / γ) / N) (gX (R0 β γ N) (S (τ / γ) / N) (I (τ / γ) / N)) τ ∧
    HasDerivAt (fun τ => I (τ / γ) / N) (gY (R0 β γ N) (S (τ / γ) / N) (I (τ / γ) / N)) τ := by
  have hτ : HasDerivAt (fun τ : ℝ => τ / γ) (1 / γ) τ := (hasDerivAt_id' τ).div_const γ
  refine ⟨?_, ?_⟩
  · have h : HasDerivAt (fun τ => S (τ / γ) / N) (fS β (S (τ / γ)) (I (τ / γ)) * (1 / γ) / N) τ :=
      (HasDerivAt.comp (x := τ) (hh₂ := hS (τ / γ)) (hh := hτ)).div_const N
    refine h.congr_deriv ?_
    rw [rhs_X hγ hN]
    rhs_check
  · have h : HasDerivAt (fun τ => I (τ / γ) / N)
        (fI β γ (S (τ / γ)) (I (τ / γ)) * (1 / γ) / N) τ :=
      (HasDerivAt.comp (x := τ) (hh₂ := hI (τ / γ)) (hh := hτ)).div_const N
    refine h.congr_deriv ?_
    rw [rhs_Y hγ hN]
    rhs_check

/-- Conversely, a solution `(X, Y)` of the dimensionless model gives the solution
`S(t) = N X(γ t)`, `I(t) = N Y(γ t)` of the dimensional model. -/
theorem trajectory_backward (hγ : γ ≠ 0) (hN : N ≠ 0) {X Y : ℝ → ℝ}
    (hX : ∀ τ, HasDerivAt X (gX (R0 β γ N) (X τ) (Y τ)) τ)
    (hY : ∀ τ, HasDerivAt Y (gY (R0 β γ N) (X τ) (Y τ)) τ) (t : ℝ) :
    HasDerivAt (fun t => N * X (γ * t)) (fS β (N * X (γ * t)) (N * Y (γ * t))) t ∧
    HasDerivAt (fun t => N * Y (γ * t)) (fI β γ (N * X (γ * t)) (N * Y (γ * t))) t := by
  have ht : HasDerivAt (fun t : ℝ => γ * t) γ t := by
    simpa using (hasDerivAt_id' t).const_mul γ
  refine ⟨?_, ?_⟩
  · have h : HasDerivAt (fun t => N * X (γ * t)) (N * (gX (R0 β γ N) (X (γ * t)) (Y (γ * t)) * γ)) t :=
      (HasDerivAt.comp (x := t) (hh₂ := hX (γ * t)) (hh := ht)).const_mul N
    refine h.congr_deriv ?_
    unfold gX fS R0
    rhs_check
  · have h : HasDerivAt (fun t => N * Y (γ * t)) (N * (gY (R0 β γ N) (X (γ * t)) (Y (γ * t)) * γ)) t :=
      (HasDerivAt.comp (x := t) (hh₂ := hY (γ * t)) (hh := ht)).const_mul N
    refine h.congr_deriv ?_
    unfold gY fI R0
    rhs_check

/-! ## 4. The epidemic threshold -/

/-- With some infection present (`Y > 0`), prevalence grows iff `R₀ X > 1`. At the start of an
outbreak `X ≈ 1`, so this is the classical condition `R₀ > 1`. -/
theorem threshold (R₀ X Y : ℝ) (hY : 0 < Y) : 0 < gY R₀ X Y ↔ 1 < R₀ * X := by
  unfold gY
  rw [show R₀ * X * Y - Y = Y * (R₀ * X - 1) by ring, mul_pos_iff_of_pos_left hY, sub_pos]

end NondimVerify.SIR

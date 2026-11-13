import NondimVerify.System
import NondimVerify.BuckinghamPi

/-!
# Reduction to invariant coordinates (the Hubert–Labahn / desr form)

A tool like desr returns, besides the scaling matrix `A`, a unimodular integer matrix
`V = [Vi | Vn]` with inverse `W = [Wu ; Wd]`. The columns of `Vn` are the **invariants**
(the new, dimensionless variables); the columns of `Vi` are auxiliary monomials that the
reduction sets to `1`.

* `eq_reconstruct_of_section`: a positive point at which all auxiliary monomials equal `1` is
  determined by its invariants, through `Wd`.
* `IsSymmetry.reduction`: **the reduction theorem.** Any positive solution whose auxiliary
  monomials are constant in time can be rescaled to a solution of the same system that lies on
  the cross-section, has the same invariants, and is therefore a function of the invariants alone.

The hypotheses on the matrices are integer identities, so a certificate can discharge them
by computation.
-/

namespace NondimVerify

open Matrix

variable {n r k m : ℕ}

/-- The point whose coordinates are the monomials `∏ j, π j ^ Wd j p` of the invariants `π`. -/
noncomputable def reconstruct (Wd : Matrix (Fin m) (Fin n) ℤ) (π : Fin m → ℝ) : Fin n → ℝ :=
  fun p => monomial π fun j => Wd j p

/-- **Reconstruction.** If `Vi * Wu + Vn * Wd = 1` and every auxiliary monomial of the positive
point `y` equals `1`, then `y` is recovered from its invariants alone. -/
theorem eq_reconstruct_of_section (Vi : Matrix (Fin n) (Fin k) ℤ) (Vn : Matrix (Fin n) (Fin m) ℤ)
    (Wu : Matrix (Fin k) (Fin n) ℤ) (Wd : Matrix (Fin m) (Fin n) ℤ)
    (hVW : Vi * Wu + Vn * Wd = 1) (y : Fin n → ℝ) (hy : ∀ i, 0 < y i)
    (haux : ∀ j, monomial y (fun i => Vi i j) = 1) :
    y = reconstruct Wd (piGroups Vn y) := by
  funext p
  have hy0 : ∀ i, y i ≠ 0 := fun i => (hy i).ne'
  have h1 : monomial (fun j => monomial y fun i => Vi i j) (fun j => Wu j p) = 1 := by
    have : (fun j => monomial y fun i => Vi i j) = fun _ => (1 : ℝ) := funext haux
    rw [this]
    simp [monomial]
  have h2 := monomial_monomial Vi y hy0 (fun j => Wu j p)
  have h3 := monomial_monomial Vn y hy0 (fun j => Wd j p)
  have hsum : (Vi *ᵥ fun j => Wu j p) + (Vn *ᵥ fun j => Wd j p) = fun i => if i = p then 1 else 0 := by
    funext i
    have := congrFun (congrFun hVW i) p
    simpa [Matrix.add_apply, Matrix.mul_apply, Matrix.mulVec, dotProduct, Matrix.one_apply] using this
  show y p = monomial (piGroups Vn y) fun j => Wd j p
  unfold piGroups
  rw [h3]
  have := monomial_add y hy0 (Vi *ᵥ fun j => Wu j p) (Vn *ᵥ fun j => Wd j p)
  rw [hsum, monomial_single, ← h2, h1, one_mul] at this
  exact this

/-- **The reduction theorem.** Let `A, τ` be scaling symmetries of `sys` and let `V = [Vi | Vn]`,
`W = [Wu ; Wd]` be as above, with `A * Vn = 0` (the columns of `Vn` are invariants) and
`G * (A * Vi) = d • 1` (the auxiliary monomials can be scaled freely). Then every positive
solution `x` whose auxiliary monomials are constant in time can be rescaled to a solution `y` that

* solves the same system,
* has the same invariants as `x` (at the rescaled time), and
* is a function of its invariants alone: `y s = reconstruct Wd (invariants of y s)`.

So the invariants satisfy a closed system of equations: the reduced system. -/
theorem LaurentSystem.IsSymmetry.reduction {sys : LaurentSystem n} {A : Matrix (Fin r) (Fin n) ℤ}
    {τ : Fin r → ℤ} (h : sys.IsSymmetry A τ)
    (Vi : Matrix (Fin n) (Fin k) ℤ) (Vn : Matrix (Fin n) (Fin m) ℤ)
    (Wu : Matrix (Fin k) (Fin n) ℤ) (Wd : Matrix (Fin m) (Fin n) ℤ)
    (hVW : Vi * Wu + Vn * Wd = 1) (hinv : A * Vn = 0)
    (G : Matrix (Fin k) (Fin r) ℤ) (d : ℤ) (hd : d ≠ 0)
    (hG : G * (A * Vi) = d • (1 : Matrix (Fin k) (Fin k) ℤ))
    {x : ℝ → Fin n → ℝ} (hx : sys.IsSolution x) (hpos : ∀ s i, 0 < x s i)
    (hconst : ∀ s j, monomial (x s) (fun i => Vi i j) = monomial (x 0) (fun i => Vi i j)) :
    ∃ lam : Fin r → ℝ, (∀ j, 0 < lam j) ∧
      sys.IsSolution (fun s => scale A lam (x (s / timeFactor lam τ))) ∧
      (∀ s i, 0 < scale A lam (x (s / timeFactor lam τ)) i) ∧
      (∀ s, piGroups Vn (scale A lam (x (s / timeFactor lam τ)))
        = piGroups Vn (x (s / timeFactor lam τ))) ∧
      ∀ s, scale A lam (x (s / timeFactor lam τ))
        = reconstruct Wd (piGroups Vn (scale A lam (x (s / timeFactor lam τ)))) := by
  obtain ⟨lam, hlam, hsec⟩ := exists_scaling_to_section A Vi G d hd hG (x 0) (hpos 0)
  have hlam0 : ∀ j, lam j ≠ 0 := fun j => (hlam j).ne'
  have hscale_pos : ∀ z : Fin n → ℝ, (∀ i, 0 < z i) → ∀ i, 0 < scale A lam z i := fun z hz i =>
    mul_pos (hz i) (Finset.prod_pos fun j _ => zpow_pos (hlam j) _)
  refine ⟨lam, hlam, h.map_solution lam hlam0 hx, fun s => hscale_pos _ (hpos _),
    fun s => pi_group_invariant A Vn hinv lam hlam0 _, fun s => ?_⟩
  refine eq_reconstruct_of_section Vi Vn Wu Wd hVW _ (hscale_pos _ (hpos _)) fun j => ?_
  -- the auxiliary monomials of the rescaled point equal those of the rescaled starting point
  rw [monomial_scale_eq A lam hlam0, hconst, ← monomial_scale_eq A lam hlam0]
  exact hsec j

/-- **The reduction theorem, for parameters.** The usual situation: the auxiliary monomials
involve only parameters (variables with no equation terms). Parameters are constant along every
solution (`IsSolution.param_const`), so the hypothesis "auxiliary monomials are constant" of
`reduction` holds automatically and the statement is about *every* positive solution. -/
theorem LaurentSystem.IsSymmetry.reduction_of_parameters {sys : LaurentSystem n}
    {A : Matrix (Fin r) (Fin n) ℤ} {τ : Fin r → ℤ} (h : sys.IsSymmetry A τ)
    (Vi : Matrix (Fin n) (Fin k) ℤ) (Vn : Matrix (Fin n) (Fin m) ℤ)
    (Wu : Matrix (Fin k) (Fin n) ℤ) (Wd : Matrix (Fin m) (Fin n) ℤ)
    (hVW : Vi * Wu + Vn * Wd = 1) (hinv : A * Vn = 0)
    (G : Matrix (Fin k) (Fin r) ℤ) (d : ℤ) (hd : d ≠ 0)
    (hG : G * (A * Vi) = d • (1 : Matrix (Fin k) (Fin k) ℤ))
    (haux : sys.OnlyParams Vi)
    {x : ℝ → Fin n → ℝ} (hx : sys.IsSolution x) (hpos : ∀ s i, 0 < x s i) :
    ∃ lam : Fin r → ℝ, (∀ j, 0 < lam j) ∧
      sys.IsSolution (fun s => scale A lam (x (s / timeFactor lam τ))) ∧
      (∀ s i, 0 < scale A lam (x (s / timeFactor lam τ)) i) ∧
      (∀ s, piGroups Vn (scale A lam (x (s / timeFactor lam τ)))
        = piGroups Vn (x (s / timeFactor lam τ))) ∧
      ∀ s, scale A lam (x (s / timeFactor lam τ))
        = reconstruct Wd (piGroups Vn (scale A lam (x (s / timeFactor lam τ)))) :=
  h.reduction Vi Vn Wu Wd hVW hinv G d hd hG hx hpos fun s j =>
    monomial_congr_of_support _ _ _ fun i hi => hx.param_const (haux i j hi) s

/-! ## The reduced equations, stated for the original solution

The statement a nondimensionalization tool actually makes is about its new variables:
"`ν = x · (parameters)` satisfies `dν/dτ = g(ν, κ)` in the new time `τ = T · t`".
The next theorem turns that into one algebraic identity per equation. It does not use the
cross-section at all, so it also covers tools whose invariants are not the cross-section
coordinates. -/

/-- **A new variable along a solution.** Let `ν = x_i · (monomial in the parameters)` be a new
variable, with exponent vector `p = u + e_i`, and let the new time be `τ = T · t`, where `T` is a
monomial in the parameters with exponent vector `w`. If

    (u-monomial) · f_i  =  (w-monomial) · g        at every positive point,

then along every positive solution, `ν` as a function of `τ` has derivative `g`. -/
theorem LaurentSystem.IsSolution.hasDerivAt_newVariable {sys : LaurentSystem n}
    {x : ℝ → Fin n → ℝ} (hx : sys.IsSolution x) (hpos : ∀ s i, 0 < x s i)
    (i : Fin n) (p u w : Fin n → ℤ) (hp : p = u + fun j => if j = i then 1 else 0)
    (hu : sys.ParamMonomial u) (hw : sys.ParamMonomial w) (g : (Fin n → ℝ) → ℝ)
    (hg : ∀ z : Fin n → ℝ, (∀ j, 0 < z j) → monomial z u * sys.rhs i z = monomial z w * g z)
    (τ : ℝ) :
    HasDerivAt (fun τ => monomial (x (τ / monomial (x 0) w)) p)
      (g (x (τ / monomial (x 0) w))) τ := by
  have hTpos : 0 < monomial (x 0) w := monomial_pos _ (hpos 0) _
  have hfun : (fun τ => monomial (x (τ / monomial (x 0) w)) p)
      = fun τ => monomial (x 0) u * x (τ / monomial (x 0) w) i := funext fun τ => by
    rw [hp, monomial_add _ (fun j => (hpos _ j).ne'), monomial_single, hx.paramMonomial_const hu]
  rw [hfun]
  have hτ : HasDerivAt (fun τ : ℝ => τ / monomial (x 0) w) (1 / monomial (x 0) w) τ :=
    (hasDerivAt_id' τ).div_const _
  have h1 : HasDerivAt ((fun s => x s i) ∘ fun τ : ℝ => τ / monomial (x 0) w)
      (sys.rhs i (x (τ / monomial (x 0) w)) * (1 / monomial (x 0) w)) τ :=
    HasDerivAt.comp (x := τ) (hh₂ := hx i (τ / monomial (x 0) w)) (hh := hτ)
  refine (h1.const_mul (monomial (x 0) u)).congr_deriv ?_
  have key := hg (x (τ / monomial (x 0) w)) (hpos _)
  rw [hx.paramMonomial_const hu (τ / monomial (x 0) w),
    hx.paramMonomial_const hw (τ / monomial (x 0) w)] at key
  rw [← mul_assoc, key]
  field_simp

end NondimVerify

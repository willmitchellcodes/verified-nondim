import NondimVerify.Reduction
import NondimVerify.Identifiability

/-!
# Rational right-hand sides

Many biological models are not polynomial: a Holling type II response `a N P / (1 + a h N)`,
Michaelis–Menten kinetics `V s / (K + s)`. This file repeats the general theory for systems
whose right-hand sides are **sums of quotients of polynomials**.

A scaling is a symmetry when, in every quotient, each numerator term and each denominator term
have weights that differ by the weight of `dx_i/dt` (`RatSystem.IsSymmetry`, decided from the
data). In particular numerator and denominator are each homogeneous. No assumption that
denominators are nonzero is needed: Lean's division by zero is zero on both sides.

The definitions and `rhs_scale` are new. Everything after `rhs_scale` has the same statement and
the same proof as for polynomial systems (`System.lean`, `Reduction.lean`); the proofs are
repeated here rather than abstracted, to leave the polynomial theory untouched.
-/

namespace NondimVerify

open Matrix

/-- A quotient of two (Laurent) polynomials, each a list of terms. -/
structure Frac (n : ℕ) where
  num : List (Term n)
  den : List (Term n)

/-- The value of the quotient at a point. -/
noncomputable def Frac.eval {n : ℕ} (f : Frac n) (x : Fin n → ℝ) : ℝ := poly f.num x / poly f.den x

/-- An autonomous system whose right-hand sides are sums of quotients of polynomials.
`terms i` lists the quotients of `dx_i/dt`; a variable with none is a parameter. -/
structure RatSystem (n : ℕ) where
  terms : Fin n → List (Frac n)

namespace RatSystem

variable {n r : ℕ}

/-- The right-hand side of equation `i`. -/
noncomputable def rhs (sys : RatSystem n) (i : Fin n) (x : Fin n → ℝ) : ℝ :=
  ((sys.terms i).map fun f => f.eval x).sum

/-- `x` is a solution: every component has the prescribed derivative at every time. -/
def IsSolution (sys : RatSystem n) (x : ℝ → Fin n → ℝ) : Prop :=
  ∀ i t, HasDerivAt (fun s => x s i) (sys.rhs i (x t)) t

/-- The scalings `A` (with time weights `τ`) are symmetries: in every quotient of equation `i`,
(weight of a numerator term) − (weight of a denominator term) + (weight of time) is the weight
of `x_i`. -/
def IsSymmetry (sys : RatSystem n) (A : Matrix (Fin r) (Fin n) ℤ) (τ : Fin r → ℤ) : Prop :=
  ∀ i, ∀ f ∈ sys.terms i, ∀ a ∈ f.num, ∀ b ∈ f.den, ∀ j,
    (A *ᵥ a.exps) j - (A *ᵥ b.exps) j + τ j = A j i

instance (sys : RatSystem n) (A : Matrix (Fin r) (Fin n) ℤ) (τ : Fin r → ℤ) :
    Decidable (sys.IsSymmetry A τ) := by
  unfold IsSymmetry; infer_instance

/-- Variable `i` is a parameter: it has no equation. -/
def IsParam (sys : RatSystem n) (i : Fin n) : Prop := (sys.terms i).length = 0

instance (sys : RatSystem n) (i : Fin n) : Decidable (sys.IsParam i) := by
  unfold IsParam; infer_instance

/-- Every monomial (column of `V`) involves parameters only. -/
def OnlyParams {k : ℕ} (sys : RatSystem n) (V : Matrix (Fin n) (Fin k) ℤ) : Prop :=
  ∀ i j, V i j ≠ 0 → sys.IsParam i

instance {k : ℕ} (sys : RatSystem n) (V : Matrix (Fin n) (Fin k) ℤ) :
    Decidable (sys.OnlyParams V) :=
  decidable_of_iff (∀ i j, (V i j).natAbs ≠ 0 → sys.IsParam i)
    (by simp only [OnlyParams, ne_eq, Int.natAbs_eq_zero])

/-- The monomial with exponent vector `u` involves only parameters. -/
def ParamMonomial (sys : RatSystem n) (u : Fin n → ℤ) : Prop := ∀ j, u j ≠ 0 → sys.IsParam j

instance (sys : RatSystem n) (u : Fin n → ℤ) : Decidable (sys.ParamMonomial u) :=
  decidable_of_iff (∀ j, (u j).natAbs ≠ 0 → sys.IsParam j)
    (by simp only [ParamMonomial, ne_eq, Int.natAbs_eq_zero])

end RatSystem

/-- A quotient whose numerator and denominator weights differ by `A_i − τ` scales like `dx_i/dt`. -/
lemma Frac.eval_scale {n r : ℕ} (f : Frac n) (A : Matrix (Fin r) (Fin n) ℤ) (τ : Fin r → ℤ)
    (i : Fin n)
    (hf : ∀ a ∈ f.num, ∀ b ∈ f.den, ∀ j, (A *ᵥ a.exps) j - (A *ᵥ b.exps) j + τ j = A j i)
    (lam : Fin r → ℝ) (hlam : ∀ j, lam j ≠ 0) (x : Fin n → ℝ) :
    f.eval (scale A lam x) = (∏ j, lam j ^ (A j i - τ j)) * f.eval x := by
  obtain ⟨num, den⟩ := f
  simp only [Frac.eval] at hf ⊢
  cases num with
  | nil => simp [poly]
  | cons a₀ as =>
    cases den with
    | nil => simp [poly]
    | cons b₀ bs =>
      have h00 := hf a₀ List.mem_cons_self b₀ List.mem_cons_self
      have hp : ∀ a ∈ a₀ :: as, ∀ j, (A *ᵥ a.exps) j = (A *ᵥ a₀.exps) j := fun a ha j => by
        have h1 := hf a ha b₀ List.mem_cons_self j
        have h2 := h00 j
        omega
      have hq : ∀ b ∈ b₀ :: bs, ∀ j, (A *ᵥ b.exps) j = (A *ᵥ b₀.exps) j := fun b hb j => by
        have h1 := hf a₀ List.mem_cons_self b hb j
        have h2 := h00 j
        omega
      rw [poly_scale_of_weight A _ _ hp lam hlam, poly_scale_of_weight A _ _ hq lam hlam]
      have hprod : ∏ j, lam j ^ (A j i - τ j)
          = (∏ j, lam j ^ (A *ᵥ a₀.exps) j) / ∏ j, lam j ^ (A *ᵥ b₀.exps) j := by
        rw [← Finset.prod_div_distrib]
        refine Finset.prod_congr rfl fun j _ => ?_
        rw [← zpow_sub₀ (hlam j)]
        congr 1
        have := h00 j
        omega
      rw [hprod, mul_div_mul_comm]

/-- Reducing one quotient: if the denominator is `m · D'` and `c · N = T · m · N'` with `m ≠ 0`,
then `c · (N / D) = T · (N' / D')`. (No assumption on `D'`.) -/
lemma frac_reduce {c T m N D N' D' : ℝ} (hm : m ≠ 0) (hD : D = m * D') (hN : c * N = T * m * N') :
    c * (N / D) = T * (N' / D') := by
  rw [hD, ← mul_div_assoc, hN, mul_assoc, mul_div_assoc, mul_div_mul_left _ _ hm]

/-- **Parameters are constant.** A variable with no equation terms has derivative zero, so it
keeps its initial value along every solution. (Mean value theorem.) -/
theorem RatSystem.IsSolution.param_const {n : ℕ} {sys : RatSystem n} {x : ℝ → Fin n → ℝ}
    (hx : sys.IsSolution x) {i : Fin n} (hi : sys.IsParam i) (s : ℝ) : x s i = x 0 i := by
  have hnil : sys.terms i = [] := List.eq_nil_of_length_eq_zero hi
  have hd : ∀ t, HasDerivAt (fun s => x s i) 0 t := fun t => by
    have := hx i t
    simpa [RatSystem.rhs, hnil] using this
  exact is_const_of_deriv_eq_zero (fun t => (hd t).differentiableAt) (fun t => (hd t).deriv) s 0

/-- A monomial in the parameters is constant along every solution. -/
theorem RatSystem.IsSolution.paramMonomial_const {n : ℕ} {sys : RatSystem n}
    {x : ℝ → Fin n → ℝ} (hx : sys.IsSolution x) {u : Fin n → ℤ} (hu : sys.ParamMonomial u) (s : ℝ) :
    monomial (x s) u = monomial (x 0) u :=
  monomial_congr_of_support _ _ _ fun j hj => hx.param_const (hu j hj) s

namespace RatSystem.IsSymmetry

variable {n r : ℕ} {sys : RatSystem n} {A : Matrix (Fin r) (Fin n) ℤ} {τ : Fin r → ℤ}

/-- Under a symmetry, the right-hand side of equation `i` scales exactly like `dx_i/dt`. -/
theorem rhs_scale (h : sys.IsSymmetry A τ) (lam : Fin r → ℝ) (hlam : ∀ j, lam j ≠ 0)
    (x : Fin n → ℝ) (i : Fin n) :
    sys.rhs i (scale A lam x) = (∏ j, lam j ^ (A j i - τ j)) * sys.rhs i x := by
  unfold RatSystem.rhs
  have key : ∀ f ∈ sys.terms i,
      f.eval (scale A lam x) = (∏ j, lam j ^ (A j i - τ j)) * f.eval x :=
    fun f hf => f.eval_scale A τ i (h i f hf) lam hlam x
  rw [List.map_congr_left key, List.sum_map_mul_left]

/-- **A scaling symmetry maps solutions to solutions.** If `x` solves the system, so does the
rescaled curve `s ↦ scale A lam (x (s / T))`, where `T` is the factor by which time is scaled. -/
theorem map_solution (h : sys.IsSymmetry A τ) (lam : Fin r → ℝ) (hlam : ∀ j, lam j ≠ 0)
    {x : ℝ → Fin n → ℝ} (hx : sys.IsSolution x) :
    sys.IsSolution fun s => scale A lam (x (s / timeFactor lam τ)) := by
  intro i s
  have hT0 : timeFactor lam τ ≠ 0 := timeFactor_ne_zero hlam τ
  have hτ : HasDerivAt (fun s : ℝ => s / timeFactor lam τ) (1 / timeFactor lam τ) s :=
    (hasDerivAt_id' s).div_const _
  have h1 : HasDerivAt ((fun u => x u i) ∘ fun s : ℝ => s / timeFactor lam τ)
      (sys.rhs i (x (s / timeFactor lam τ)) * (1 / timeFactor lam τ)) s :=
    HasDerivAt.comp (x := s) (hh₂ := hx i (s / timeFactor lam τ)) (hh := hτ)
  have h2 := h1.mul_const (∏ j, lam j ^ A j i)
  refine h2.congr_deriv ?_
  rw [h.rhs_scale lam hlam]
  have hprod : ∏ j, lam j ^ (A j i - τ j) = (∏ j, lam j ^ A j i) / timeFactor lam τ := by
    rw [timeFactor, ← Finset.prod_div_distrib]
    exact Finset.prod_congr rfl fun j _ => zpow_sub₀ (hlam j) _ _
  rw [hprod]
  field_simp

/-- **Nothing is lost.** The rescaled curve is a solution *if and only if* the original is:
rescaling by a symmetry is a one-to-one correspondence between solutions. -/
theorem solution_iff (h : sys.IsSymmetry A τ) (lam : Fin r → ℝ) (hlam : ∀ j, lam j ≠ 0)
    {x : ℝ → Fin n → ℝ} :
    sys.IsSolution (fun s => scale A lam (x (s / timeFactor lam τ))) ↔ sys.IsSolution x := by
  refine ⟨fun hx' => ?_, h.map_solution lam hlam⟩
  have hback := h.map_solution (fun j => (lam j)⁻¹) (fun j => inv_ne_zero (hlam j)) hx'
  have hT0 : timeFactor lam τ ≠ 0 := timeFactor_ne_zero hlam τ
  have hfun : (fun s => scale A (fun j => (lam j)⁻¹)
      (scale A lam (x (s / timeFactor (fun j => (lam j)⁻¹) τ / timeFactor lam τ)))) = x := by
    funext s
    rw [scale_inv_scale A lam hlam, timeFactor_inv]
    congr 1
    field_simp
  rw [← hfun]
  exact hback

end RatSystem.IsSymmetry

/-- **Nondimensionalization, in general.** Let `A, τ` be scaling symmetries of `sys`, and let `S`
be parameters whose columns of `A` are independent (certificate `G, d`). Then every solution in
which those parameters have positive values corresponds, by an explicit rescaling of time and
variables, to a solution of the *same* equations in which all of them equal `1`. -/
theorem RatSystem.IsSymmetry.nondimensionalize {n r k : ℕ} {sys : RatSystem n}
    {A : Matrix (Fin r) (Fin n) ℤ} {τ : Fin r → ℤ} (h : sys.IsSymmetry A τ)
    (S : Fin k → Fin n) (G : Matrix (Fin k) (Fin r) ℤ) (d : ℤ) (hd : d ≠ 0)
    (hG : G * A.submatrix id S = d • (1 : Matrix (Fin k) (Fin k) ℤ))
    {x : ℝ → Fin n → ℝ} (hx : sys.IsSolution x) (c : Fin n → ℝ) (hc : ∀ i, 0 < c (S i))
    (hparam : ∀ s i, x s (S i) = c (S i)) :
    ∃ lam : Fin r → ℝ, (∀ j, 0 < lam j) ∧
      sys.IsSolution (fun s => scale A lam (x (s / timeFactor lam τ))) ∧
      ∀ s i, scale A lam (x (s / timeFactor lam τ)) (S i) = 1 := by
  obtain ⟨lam, hpos, hone⟩ := exists_normalizing_scaling A S G d hd hG c hc
  refine ⟨lam, hpos, h.map_solution lam (fun j => (hpos j).ne') hx, fun s i => ?_⟩
  have := hone i
  unfold scale at this ⊢
  rw [hparam]
  exact this

variable {n r k m : ℕ}

/-- **The reduction theorem.** Let `A, τ` be scaling symmetries of `sys` and let `V = [Vi | Vn]`,
`W = [Wu ; Wd]` be as above, with `A * Vn = 0` (the columns of `Vn` are invariants) and
`G * (A * Vi) = d • 1` (the auxiliary monomials can be scaled freely). Then every positive
solution `x` whose auxiliary monomials are constant in time can be rescaled to a solution `y` that

* solves the same system,
* has the same invariants as `x` (at the rescaled time), and
* is a function of its invariants alone: `y s = reconstruct Wd (invariants of y s)`.

So the invariants satisfy a closed system of equations: the reduced system. -/
theorem RatSystem.IsSymmetry.reduction {sys : RatSystem n} {A : Matrix (Fin r) (Fin n) ℤ}
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
theorem RatSystem.IsSymmetry.reduction_of_parameters {sys : RatSystem n}
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

/-- **A new variable along a solution.** Let `ν = x_i · (monomial in the parameters)` be a new
variable, with exponent vector `p = u + e_i`, and let the new time be `τ = T · t`, where `T` is a
monomial in the parameters with exponent vector `w`. If

    (u-monomial) · f_i  =  (w-monomial) · g        at every positive point,

then along every positive solution, `ν` as a function of `τ` has derivative `g`. -/
theorem RatSystem.IsSolution.hasDerivAt_newVariable {sys : RatSystem n}
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

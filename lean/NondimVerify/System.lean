import NondimVerify.Basic
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Analysis.Calculus.MeanValue

/-!
# Polynomial systems and their scaling symmetries, in general

Everything in this file is about an **arbitrary** system, not a particular model.

* `LaurentSystem n`: an autonomous system `dx_i/dt = Σ coeff · ∏ x_j ^ e_j` in `n` variables
  (integer exponents, so `1/x` is allowed). Parameters are simply variables with no terms:
  their derivative is `0`.
* `IsSymmetry sys A τ`: the rows of `A` (weights of the variables) together with `τ` (weights
  of time) are scaling symmetries of `sys`. For a concrete system this is decidable.
* `IsSymmetry.map_solution`: **a scaling symmetry maps solutions to solutions.**
* `exists_normalizing_scaling` / `not_normalizable_of_kernel_vector`: the **constraint
  criterion**. A left inverse of the chosen columns of `A` gives scale factors that set the
  chosen parameters to `1`; a kernel vector of those columns proves no scale factors can.
* `IsSymmetry.nondimensionalize`: **nondimensionalization of any polynomial system.** Every
  solution corresponds to a solution of the same equations in which the chosen parameters equal `1`.
-/

namespace NondimVerify

open Matrix

/-! ## Systems -/

/-- One term `coeff * ∏ j, x j ^ exps j` of a right-hand side. -/
structure Term (n : ℕ) where
  coeff : ℝ
  exps : Fin n → ℤ

/-- The value of a term at the point `x`. -/
noncomputable def Term.eval {n : ℕ} (t : Term n) (x : Fin n → ℝ) : ℝ :=
  t.coeff * monomial x t.exps

/-- An autonomous system `dx_i/dt = Σ (terms i)`. A variable with no terms is a parameter. -/
structure LaurentSystem (n : ℕ) where
  terms : Fin n → List (Term n)

namespace LaurentSystem

variable {n r : ℕ}

/-- The right-hand side of equation `i` at the point `x`. -/
noncomputable def rhs (sys : LaurentSystem n) (i : Fin n) (x : Fin n → ℝ) : ℝ :=
  ((sys.terms i).map fun t => t.eval x).sum

/-- `x` is a solution: every component has the derivative the system prescribes, at every time. -/
def IsSolution (sys : LaurentSystem n) (x : ℝ → Fin n → ℝ) : Prop :=
  ∀ i t, HasDerivAt (fun s => x s i) (sys.rhs i (x t)) t

/-- The scalings `x_i ↦ (∏ j, lam j ^ A j i) * x_i`, `t ↦ (∏ j, lam j ^ τ j) * t` are symmetries of
`sys`: every term of equation `i` has weight `A j i - τ j` under scaling `j`, which is the weight
of `dx_i/dt`. -/
def IsSymmetry (sys : LaurentSystem n) (A : Matrix (Fin r) (Fin n) ℤ) (τ : Fin r → ℤ) : Prop :=
  ∀ i, ∀ t ∈ sys.terms i, ∀ j, (A *ᵥ t.exps) j + τ j = A j i

instance (sys : LaurentSystem n) (A : Matrix (Fin r) (Fin n) ℤ) (τ : Fin r → ℤ) :
    Decidable (sys.IsSymmetry A τ) := by
  unfold IsSymmetry; infer_instance

/-- Variable `i` is a parameter: it has no equation terms, so its derivative is zero. -/
def IsParam (sys : LaurentSystem n) (i : Fin n) : Prop := (sys.terms i).length = 0

instance (sys : LaurentSystem n) (i : Fin n) : Decidable (sys.IsParam i) := by
  unfold IsParam; infer_instance

/-- The monomials given by the columns of `V` involve only parameters. -/
def OnlyParams {k : ℕ} (sys : LaurentSystem n) (V : Matrix (Fin n) (Fin k) ℤ) : Prop :=
  ∀ i j, V i j ≠ 0 → sys.IsParam i

instance {k : ℕ} (sys : LaurentSystem n) (V : Matrix (Fin n) (Fin k) ℤ) :
    Decidable (sys.OnlyParams V) :=
  decidable_of_iff (∀ i j, (V i j).natAbs ≠ 0 → sys.IsParam i)
    (by simp only [OnlyParams, ne_eq, Int.natAbs_eq_zero])

/-- The monomial with exponent vector `u` involves only parameters. -/
def ParamMonomial (sys : LaurentSystem n) (u : Fin n → ℤ) : Prop := ∀ j, u j ≠ 0 → sys.IsParam j

instance (sys : LaurentSystem n) (u : Fin n → ℤ) : Decidable (sys.ParamMonomial u) :=
  decidable_of_iff (∀ j, (u j).natAbs ≠ 0 → sys.IsParam j)
    (by simp only [ParamMonomial, ne_eq, Int.natAbs_eq_zero])

end LaurentSystem

/-- **Parameters are constant.** A variable with no equation terms has derivative zero, so it
keeps its initial value along every solution. (Mean value theorem.) -/
theorem LaurentSystem.IsSolution.param_const {n : ℕ} {sys : LaurentSystem n} {x : ℝ → Fin n → ℝ}
    (hx : sys.IsSolution x) {i : Fin n} (hi : sys.IsParam i) (s : ℝ) : x s i = x 0 i := by
  have hnil : sys.terms i = [] := List.eq_nil_of_length_eq_zero hi
  have hd : ∀ t, HasDerivAt (fun s => x s i) 0 t := fun t => by
    have := hx i t
    simpa [LaurentSystem.rhs, hnil] using this
  exact is_const_of_deriv_eq_zero (fun t => (hd t).differentiableAt) (fun t => (hd t).deriv) s 0

/-- A monomial in the parameters is constant along every solution. -/
theorem LaurentSystem.IsSolution.paramMonomial_const {n : ℕ} {sys : LaurentSystem n}
    {x : ℝ → Fin n → ℝ} (hx : sys.IsSolution x) {u : Fin n → ℤ} (hu : sys.ParamMonomial u) (s : ℝ) :
    monomial (x s) u = monomial (x 0) u :=
  monomial_congr_of_support _ _ _ fun j hj => hx.param_const (hu j hj) s

/-- The factor by which time is multiplied. -/
noncomputable def timeFactor {r : ℕ} (lam : Fin r → ℝ) (τ : Fin r → ℤ) : ℝ := ∏ j, lam j ^ τ j

lemma timeFactor_ne_zero {r : ℕ} {lam : Fin r → ℝ} (hlam : ∀ j, lam j ≠ 0) (τ : Fin r → ℤ) :
    timeFactor lam τ ≠ 0 :=
  Finset.prod_ne_zero_iff.mpr fun j _ => zpow_ne_zero _ (hlam j)

/-! ## A symmetry maps solutions to solutions -/

namespace LaurentSystem.IsSymmetry

variable {n r : ℕ} {sys : LaurentSystem n} {A : Matrix (Fin r) (Fin n) ℤ} {τ : Fin r → ℤ}

/-- Under a symmetry, the right-hand side of equation `i` scales exactly like `dx_i/dt`. -/
theorem rhs_scale (h : sys.IsSymmetry A τ) (lam : Fin r → ℝ) (hlam : ∀ j, lam j ≠ 0)
    (x : Fin n → ℝ) (i : Fin n) :
    sys.rhs i (scale A lam x) = (∏ j, lam j ^ (A j i - τ j)) * sys.rhs i x := by
  unfold LaurentSystem.rhs
  have key : ∀ t ∈ sys.terms i,
      t.eval (scale A lam x) = (∏ j, lam j ^ (A j i - τ j)) * t.eval x := by
    intro t ht
    unfold Term.eval
    rw [monomial_scale_eq A lam hlam]
    have hw : ∀ j, (A *ᵥ t.exps) j = A j i - τ j := fun j => by
      have := h i t ht j
      omega
    simp_rw [hw]
    ring
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

/-- Scaling by the inverse factors undoes a scaling. -/
lemma _root_.NondimVerify.scale_inv_scale (A : Matrix (Fin r) (Fin n) ℤ) (lam : Fin r → ℝ)
    (hlam : ∀ j, lam j ≠ 0) (x : Fin n → ℝ) :
    scale A (fun j => (lam j)⁻¹) (scale A lam x) = x := by
  funext i
  unfold scale
  rw [mul_assoc, ← Finset.prod_mul_distrib]
  have h1 : ∀ j, lam j ^ A j i * (lam j)⁻¹ ^ A j i = 1 := fun j => by
    rw [← mul_zpow, mul_inv_cancel₀ (hlam j), one_zpow]
  rw [Finset.prod_congr rfl fun j _ => h1 j, Finset.prod_const_one, mul_one]

lemma _root_.NondimVerify.timeFactor_inv (lam : Fin r → ℝ) (τ : Fin r → ℤ) :
    timeFactor (fun j => (lam j)⁻¹) τ = (timeFactor lam τ)⁻¹ := by
  unfold timeFactor
  rw [← Finset.prod_inv_distrib]
  exact Finset.prod_congr rfl fun j _ => inv_zpow _ _

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

end LaurentSystem.IsSymmetry

/-! ## The constraint criterion -/

/-- **Constraint criterion, "yes" direction.** Let `S` list the parameters we want to set to `1`.
If the columns of `A` at `S` have a left inverse up to a nonzero integer factor
(`G * A_S = d • 1`, a certificate of linear independence), then for all positive values of those
parameters there are positive scale factors that bring every one of them to `1`. -/
theorem exists_normalizing_scaling {r n k : ℕ} (A : Matrix (Fin r) (Fin n) ℤ) (S : Fin k → Fin n)
    (G : Matrix (Fin k) (Fin r) ℤ) (d : ℤ) (hd : d ≠ 0)
    (hG : G * A.submatrix id S = d • (1 : Matrix (Fin k) (Fin k) ℤ))
    (c : Fin n → ℝ) (hc : ∀ i, 0 < c (S i)) :
    ∃ lam : Fin r → ℝ, (∀ j, 0 < lam j) ∧ ∀ i, scale A lam c (S i) = 1 := by
  have hd' : (d : ℝ) ≠ 0 := by exact_mod_cast hd
  let μ : Fin r → ℝ := fun j => -(∑ l, (G l j : ℝ) * Real.log (c (S l))) / d
  refine ⟨fun j => Real.exp (μ j), fun j => Real.exp_pos _, fun i => ?_⟩
  have hGA : ∀ l, ∑ j, (G l j : ℝ) * (A j (S i) : ℝ) = if l = i then (d : ℝ) else 0 := by
    intro l
    have h := congrFun (congrFun hG l) i
    simp only [Matrix.mul_apply, Matrix.submatrix_apply, id_eq, Matrix.smul_apply,
      Matrix.one_apply, smul_eq_mul, mul_ite, mul_one, mul_zero] at h
    exact_mod_cast h
  have hμ : ∀ j, μ j * d = -∑ l, (G l j : ℝ) * Real.log (c (S l)) := fun j => by
    simp only [μ]
    field_simp
  have hsum : ∑ j, (A j (S i) : ℝ) * μ j = -Real.log (c (S i)) := by
    apply mul_right_cancel₀ hd'
    calc (∑ j, (A j (S i) : ℝ) * μ j) * d
        = ∑ j, (A j (S i) : ℝ) * (μ j * d) := by
          rw [Finset.sum_mul]
          exact Finset.sum_congr rfl fun j _ => by ring
      _ = -∑ j, ∑ l, (G l j : ℝ) * (A j (S i) : ℝ) * Real.log (c (S l)) := by
          simp only [hμ, mul_neg, Finset.sum_neg_distrib, Finset.mul_sum]
          congr 1
          exact Finset.sum_congr rfl fun j _ => Finset.sum_congr rfl fun l _ => by ring
      _ = -∑ l, (∑ j, (G l j : ℝ) * (A j (S i) : ℝ)) * Real.log (c (S l)) := by
          rw [Finset.sum_comm]
          simp only [Finset.sum_mul]
      _ = -Real.log (c (S i)) * d := by
          simp only [hGA, ite_mul, zero_mul, Finset.sum_ite_eq', Finset.mem_univ, ite_true]
          ring
  show c (S i) * ∏ j, Real.exp (μ j) ^ A j (S i) = 1
  have hprod : ∏ j, Real.exp (μ j) ^ A j (S i) = Real.exp (∑ j, (A j (S i) : ℝ) * μ j) := by
    rw [Real.exp_sum]
    exact Finset.prod_congr rfl fun j _ => exp_zpow _ _
  rw [hprod, hsum, Real.exp_neg, Real.exp_log (hc i)]
  exact mul_inv_cancel₀ (hc i).ne'

/-- **Constraint criterion, "no" direction.** If the columns of `A` at (distinct) parameters `S`
admit a nonzero integer kernel vector `v`, then the monomial `∏ c_{S i} ^ v i` is unchanged by
every scaling, so for suitable parameter values *no* scale factors bring all of `S` to `1`. -/
theorem not_normalizable_of_kernel_vector {r n k : ℕ} (A : Matrix (Fin r) (Fin n) ℤ)
    (S : Fin k → Fin n) (hS : Function.Injective S) (v : Fin k → ℤ) (hv : v ≠ 0)
    (hAv : A.submatrix id S *ᵥ v = 0) :
    ∃ c : Fin n → ℝ, (∀ i, 0 < c i) ∧
      ∀ lam : Fin r → ℝ, (∀ j, lam j ≠ 0) → ¬ ∀ i, scale A lam c (S i) = 1 := by
  obtain ⟨i₀, hi₀⟩ : ∃ i, v i ≠ 0 := by
    by_contra hcon
    exact hv (funext fun i => by simpa using not_exists.mp hcon i)
  refine ⟨fun m => if m = S i₀ then 2 else 1, fun m => by dsimp only; split_ifs <;> norm_num, ?_⟩
  intro lam hlam hall
  set c : Fin n → ℝ := fun m => if m = S i₀ then 2 else 1 with hc
  -- the monomial of the chosen parameters with exponents `v` is invariant
  have hinv := monomial_scale (A.submatrix id S) lam hlam (fun i => c (S i)) v hAv
  have hleft : scale (A.submatrix id S) lam (fun i => c (S i)) = fun _ => 1 :=
    funext fun i => hall i
  rw [hleft] at hinv
  have h1 : monomial (fun _ : Fin k => (1 : ℝ)) v = 1 := by simp [monomial]
  have h2 : monomial (fun i => c (S i)) v = 2 ^ v i₀ := by
    unfold monomial
    rw [Finset.prod_eq_single i₀]
    · simp [hc]
    · intro i _ hne
      have : S i ≠ S i₀ := fun h => hne (hS h)
      simp [hc, this]
    · intro h; exact absurd (Finset.mem_univ _) h
  rw [h1, h2] at hinv
  exact hi₀ ((zpow_eq_one_iff_right₀ (by norm_num) (by norm_num)).mp hinv.symm)

/-- **Moving to a cross-section.** Let the columns of `Vi` be monomials (in a tool like desr:
the auxiliary columns of the Hermite multiplier). If `A * Vi` has a left inverse up to a nonzero
integer, then every positive point can be rescaled so that all those monomials equal `1`.
Setting individual parameters to `1` is the special case where the columns are unit vectors. -/
theorem exists_scaling_to_section {r n k : ℕ} (A : Matrix (Fin r) (Fin n) ℤ)
    (Vi : Matrix (Fin n) (Fin k) ℤ) (G : Matrix (Fin k) (Fin r) ℤ) (d : ℤ) (hd : d ≠ 0)
    (hG : G * (A * Vi) = d • (1 : Matrix (Fin k) (Fin k) ℤ))
    (c : Fin n → ℝ) (hc : ∀ i, 0 < c i) :
    ∃ lam : Fin r → ℝ, (∀ j, 0 < lam j) ∧
      ∀ j, monomial (scale A lam c) (fun i => Vi i j) = 1 := by
  obtain ⟨lam, hpos, hone⟩ := exists_normalizing_scaling (A * Vi) id G d hd
    (by simpa using hG) (fun j => monomial c fun i => Vi i j)
    (fun j => monomial_pos c hc _)
  refine ⟨lam, hpos, fun j => ?_⟩
  rw [monomial_scale_eq A lam (fun l => (hpos l).ne')]
  have := hone j
  unfold scale at this
  rw [mul_comm]
  exact this

/-! ## Nondimensionalization of an arbitrary polynomial system -/

/-- **Nondimensionalization, in general.** Let `A, τ` be scaling symmetries of `sys`, and let `S`
be parameters whose columns of `A` are independent (certificate `G, d`). Then every solution in
which those parameters have positive values corresponds, by an explicit rescaling of time and
variables, to a solution of the *same* equations in which all of them equal `1`. -/
theorem LaurentSystem.IsSymmetry.nondimensionalize {n r k : ℕ} {sys : LaurentSystem n}
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

end NondimVerify

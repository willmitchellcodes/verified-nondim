import NondimVerify.Basic
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.LinearAlgebra.Dual.Lemmas
import Mathlib.LinearAlgebra.Basis.VectorSpace

/-!
# The Buckingham Pi theorem

Setting. There are `n` positive quantities `q` and `k` base units. The **dimension matrix**
`D : Matrix (Fin k) (Fin n) ℤ` says how quantity `i` depends on base unit `j`: rescaling the base
units by positive factors `lam` multiplies `q i` by `∏ j, lam j ^ D j i`, i.e. `q ↦ scale D lam q`.

A column vector `p` with `D *ᵥ p = 0` gives a **dimensionless group** `∏ i, q i ^ p i`
(`pi_group_invariant`). Collect such columns in a matrix `P` with `D * P = 0`.

**Theorem** (`buckingham_pi`). If the columns of `P` span the kernel of `D`, then any quantity `f`
that does not depend on the choice of units depends on `q` only through the dimensionless groups:
two points with the same values of all the groups give the same value of `f`. Equivalently
(`buckingham_pi_factorization`) `f = F ∘ (the groups)` for some function `F`.

The spanning hypothesis can be discharged for concrete integer matrices from a small certificate
(`spans_kernel_of_certificate`), which is what a Hermite multiplier computed by an external tool
provides. The number of independent groups is `n - rank D` (`finrank_dimensionless`).
-/

namespace NondimVerify

open Matrix

variable {k n m : ℕ}

/-- Cast an integer matrix to a real one. -/
abbrev toReal {a b : Type*} (M : Matrix a b ℤ) : Matrix a b ℝ := M.map (Int.castRingHom ℝ)

/-- The dimensionless groups defined by the columns of `P`, evaluated at `q`. -/
noncomputable def piGroups (P : Matrix (Fin n) (Fin m) ℤ) (q : Fin n → ℝ) : Fin m → ℝ :=
  fun j => monomial q fun i => P i j

/-- `f` does not depend on the choice of units. -/
def UnitInvariant {α : Type*} (D : Matrix (Fin k) (Fin n) ℤ) (f : (Fin n → ℝ) → α) : Prop :=
  ∀ (lam : Fin k → ℝ) (q : Fin n → ℝ), (∀ j, 0 < lam j) → (∀ i, 0 < q i) → f (scale D lam q) = f q

/-- Each column of `P` is a dimensionless group: changing units does not change its value. -/
theorem pi_group_invariant (D : Matrix (Fin k) (Fin n) ℤ) (P : Matrix (Fin n) (Fin m) ℤ)
    (hDP : D * P = 0) (lam : Fin k → ℝ) (hlam : ∀ j, lam j ≠ 0) (q : Fin n → ℝ) :
    piGroups P (scale D lam q) = piGroups P q := by
  funext j
  refine monomial_scale D lam hlam q _ ?_
  funext l
  have := congrFun (congrFun hDP l) j
  simpa [Matrix.mul_apply, Matrix.mulVec, dotProduct] using this

lemma log_monomial (q : Fin n → ℝ) (hq : ∀ i, 0 < q i) (p : Fin n → ℤ) :
    Real.log (monomial q p) = ∑ i, (p i : ℝ) * Real.log (q i) := by
  unfold monomial
  rw [Real.log_prod fun i _ => zpow_ne_zero _ (hq i).ne']
  exact Finset.sum_congr rfl fun i _ => Real.log_zpow _ _

/-- Linear algebra behind the theorem: a vector orthogonal to the kernel of `D` is a combination
of the rows of `D`. (Stated with the kernel described by a spanning family `P`.) -/
theorem exists_row_combination (D : Matrix (Fin k) (Fin n) ℝ) (P : Matrix (Fin n) (Fin m) ℝ)
    (hspan : ∀ v : Fin n → ℝ, D *ᵥ v = 0 → ∃ w : Fin m → ℝ, v = P *ᵥ w)
    (y : Fin n → ℝ) (hy : ∀ j, ∑ i, P i j * y i = 0) :
    ∃ μ : Fin k → ℝ, ∀ i, y i = ∑ l, μ l * D l i := by
  have hmem : y ∈ Submodule.span ℝ (Set.range D.row) := by
    by_contra hnot
    obtain ⟨φ, hφy, hφ⟩ := Submodule.exists_dual_map_eq_bot_of_notMem hnot inferInstance
    -- `φ` is the dot product with the vector `v`
    let v : Fin n → ℝ := fun i => φ fun j => if i = j then 1 else 0
    have hφv : ∀ z : Fin n → ℝ, φ z = ∑ i, z i * v i := fun z => by
      rw [LinearMap.pi_apply_eq_sum_univ φ z]
      rfl
    -- `φ` vanishes on the rows of `D`, so `D *ᵥ v = 0`
    have hDv : D *ᵥ v = 0 := by
      funext l
      have hl : φ (D.row l) = 0 := by
        have : φ (D.row l) ∈ (Submodule.span ℝ (Set.range D.row)).map φ :=
          Submodule.mem_map_of_mem (Submodule.subset_span ⟨l, rfl⟩)
        rw [hφ] at this
        simpa using this
      rw [hφv] at hl
      simpa [Matrix.mulVec, dotProduct, Matrix.row] using hl
    obtain ⟨w, hw⟩ := hspan v hDv
    apply hφy
    rw [hφv, hw]
    calc ∑ i, y i * (P *ᵥ w) i = ∑ i, ∑ j, y i * (P i j * w j) := by
          simp [Matrix.mulVec, dotProduct, Finset.mul_sum]
      _ = ∑ j, (∑ i, P i j * y i) * w j := by
          rw [Finset.sum_comm]
          refine Finset.sum_congr rfl fun j _ => ?_
          rw [Finset.sum_mul]
          exact Finset.sum_congr rfl fun i _ => by ring
      _ = 0 := by simp [hy]
  obtain ⟨μ, hμ⟩ := (Submodule.mem_span_range_iff_exists_fun ℝ).mp hmem
  refine ⟨μ, fun i => ?_⟩
  have := congrFun hμ i
  simp only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul, Matrix.row] at this
  exact this.symm

/-- **Orbit separation.** If the columns of `P` span the kernel of `D`, two points with the same
dimensionless groups differ only by a change of units. -/
theorem exists_scaling_of_piGroups_eq (D : Matrix (Fin k) (Fin n) ℤ) (P : Matrix (Fin n) (Fin m) ℤ)
    (hspan : ∀ v : Fin n → ℝ, toReal D *ᵥ v = 0 → ∃ w : Fin m → ℝ, v = toReal P *ᵥ w)
    (q q' : Fin n → ℝ) (hq : ∀ i, 0 < q i) (hq' : ∀ i, 0 < q' i)
    (hpi : piGroups P q = piGroups P q') :
    ∃ lam : Fin k → ℝ, (∀ j, 0 < lam j) ∧ q' = scale D lam q := by
  -- work with logarithms
  let y : Fin n → ℝ := fun i => Real.log (q' i) - Real.log (q i)
  have hy : ∀ j, ∑ i, toReal P i j * y i = 0 := by
    intro j
    have h := congrArg Real.log (congrFun hpi j)
    simp only [piGroups] at h
    rw [log_monomial q hq, log_monomial q' hq'] at h
    have : ∑ i, toReal P i j * y i
        = ∑ i, (P i j : ℝ) * Real.log (q' i) - ∑ i, (P i j : ℝ) * Real.log (q i) := by
      rw [← Finset.sum_sub_distrib]
      exact Finset.sum_congr rfl fun i _ => by simp [y, toReal]; ring
    rw [this, h, sub_self]
  obtain ⟨μ, hμ⟩ := exists_row_combination (toReal D) (toReal P) hspan y hy
  refine ⟨fun l => Real.exp (μ l), fun l => Real.exp_pos _, funext fun i => ?_⟩
  show q' i = q i * ∏ l, Real.exp (μ l) ^ D l i
  have hprod : ∏ l, Real.exp (μ l) ^ D l i = Real.exp (y i) := by
    rw [hμ i, Real.exp_sum]
    refine Finset.prod_congr rfl fun l _ => ?_
    rw [exp_zpow]
    congr 1
    simp [toReal]; ring
  rw [hprod, show y i = Real.log (q' i) - Real.log (q i) from rfl, Real.exp_sub,
    Real.exp_log (hq' i), Real.exp_log (hq i)]
  field_simp [(hq i).ne']

/-- **Buckingham Pi theorem.** A quantity that does not depend on the choice of units depends
only on the dimensionless groups. -/
theorem buckingham_pi {α : Type*} (D : Matrix (Fin k) (Fin n) ℤ) (P : Matrix (Fin n) (Fin m) ℤ)
    (hspan : ∀ v : Fin n → ℝ, toReal D *ᵥ v = 0 → ∃ w : Fin m → ℝ, v = toReal P *ᵥ w)
    (f : (Fin n → ℝ) → α) (hf : UnitInvariant D f)
    (q q' : Fin n → ℝ) (hq : ∀ i, 0 < q i) (hq' : ∀ i, 0 < q' i)
    (hpi : piGroups P q = piGroups P q') : f q = f q' := by
  obtain ⟨lam, hlam, rfl⟩ := exists_scaling_of_piGroups_eq D P hspan q q' hq hq' hpi
  exact (hf lam q hlam hq).symm

/-- **Buckingham Pi theorem, factorized form.** `f = F ∘ (dimensionless groups)` on positive
quantities, for some function `F` of the groups alone. -/
theorem buckingham_pi_factorization {α : Type*} (D : Matrix (Fin k) (Fin n) ℤ)
    (P : Matrix (Fin n) (Fin m) ℤ)
    (hspan : ∀ v : Fin n → ℝ, toReal D *ᵥ v = 0 → ∃ w : Fin m → ℝ, v = toReal P *ᵥ w)
    (f : (Fin n → ℝ) → α) (hf : UnitInvariant D f) :
    ∃ F : (Fin m → ℝ) → α, ∀ q : Fin n → ℝ, (∀ i, 0 < q i) → f q = F (piGroups P q) := by
  classical
  refine ⟨fun π => if h : ∃ q : Fin n → ℝ, (∀ i, 0 < q i) ∧ piGroups P q = π
      then f h.choose else f fun _ => 1, fun q hq => ?_⟩
  have h : ∃ q₀ : Fin n → ℝ, (∀ i, 0 < q₀ i) ∧ piGroups P q₀ = piGroups P q := ⟨q, hq, rfl⟩
  beta_reduce
  rw [dite_eq_left_of_eq_true (eq_true h)]
  exact buckingham_pi D P hspan f hf q h.choose hq h.choose_spec.1 h.choose_spec.2.symm

/-! ## Discharging the spanning hypothesis from a certificate -/

/-- **Certificate for "the columns of `P` span the kernel of `D`".** Suppose integer matrices
satisfy `V₁ * W₁ + P * W₂ = 1` (the pieces of a unimodular matrix and its inverse), `D * P = 0`,
and `L * (D * V₁) = d • 1` with `d ≠ 0` (the other columns are not in the kernel). Then every real
kernel vector of `D` is a combination of the columns of `P`. All three hypotheses are integer
matrix identities, so Lean can check them by computation. -/
theorem spans_kernel_of_certificate {ρ : ℕ} (D : Matrix (Fin k) (Fin n) ℤ)
    (P : Matrix (Fin n) (Fin m) ℤ) (V₁ : Matrix (Fin n) (Fin ρ) ℤ) (W₁ : Matrix (Fin ρ) (Fin n) ℤ)
    (W₂ : Matrix (Fin m) (Fin n) ℤ) (L : Matrix (Fin ρ) (Fin k) ℤ) (d : ℤ) (hd : d ≠ 0)
    (hVW : V₁ * W₁ + P * W₂ = 1) (hDP : D * P = 0) (hL : L * (D * V₁) = d • (1 : Matrix _ _ ℤ)) :
    ∀ v : Fin n → ℝ, toReal D *ᵥ v = 0 → ∃ w : Fin m → ℝ, v = toReal P *ᵥ w := by
  intro v hv
  have hd' : (d : ℝ) ≠ 0 := by exact_mod_cast hd
  -- the three identities, over the reals
  have hVW' : toReal V₁ * toReal W₁ + toReal P * toReal W₂ = 1 := by
    show V₁.map (Int.castRingHom ℝ) * W₁.map (Int.castRingHom ℝ)
      + P.map (Int.castRingHom ℝ) * W₂.map (Int.castRingHom ℝ) = 1
    rw [← Matrix.map_mul, ← Matrix.map_mul, ← Matrix.map_add _ (map_add _), hVW,
      Matrix.map_one _ (map_zero _) (map_one _)]
  have hDP' : toReal D * toReal P = 0 := by
    show D.map (Int.castRingHom ℝ) * P.map (Int.castRingHom ℝ) = 0
    rw [← Matrix.map_mul, hDP, Matrix.map_zero _ (map_zero _)]
  have hL' : toReal L * (toReal D * toReal V₁) = (d : ℝ) • (1 : Matrix _ _ ℝ) := by
    show L.map (Int.castRingHom ℝ) * (D.map (Int.castRingHom ℝ) * V₁.map (Int.castRingHom ℝ))
      = (d : ℝ) • (1 : Matrix _ _ ℝ)
    rw [← Matrix.map_mul, ← Matrix.map_mul, hL]
    ext i j
    simp only [Matrix.map_apply, Matrix.smul_apply, Matrix.one_apply, smul_eq_mul]
    split_ifs <;> simp
  -- split `v` along the decomposition `1 = V₁ W₁ + P W₂`
  have hsplit : v = toReal V₁ *ᵥ (toReal W₁ *ᵥ v) + toReal P *ᵥ (toReal W₂ *ᵥ v) := by
    have := congrArg (· *ᵥ v) hVW'
    simpa [Matrix.add_mulVec, Matrix.mulVec_mulVec] using this.symm
  -- the `V₁` part vanishes
  have hD0 : toReal D *ᵥ (toReal V₁ *ᵥ (toReal W₁ *ᵥ v)) = 0 := by
    have h1 : toReal D *ᵥ v = toReal D *ᵥ (toReal V₁ *ᵥ (toReal W₁ *ᵥ v))
        + toReal D *ᵥ (toReal P *ᵥ (toReal W₂ *ᵥ v)) := by
      conv_lhs => rw [hsplit]
      rw [Matrix.mulVec_add]
    have h2 : toReal D *ᵥ (toReal P *ᵥ (toReal W₂ *ᵥ v)) = 0 := by
      rw [Matrix.mulVec_mulVec, hDP', Matrix.zero_mulVec]
    rw [hv, h2, add_zero] at h1
    exact h1.symm
  have hW1 : toReal W₁ *ᵥ v = 0 := by
    have h3 : (d : ℝ) • (toReal W₁ *ᵥ v) = 0 := by
      have := congrArg (· *ᵥ (toReal W₁ *ᵥ v)) hL'
      simp only [Matrix.smul_mulVec, Matrix.one_mulVec] at this
      rw [← this, ← Matrix.mulVec_mulVec, ← Matrix.mulVec_mulVec, hD0, Matrix.mulVec_zero]
    exact (smul_eq_zero.mp h3).resolve_left hd'
  refine ⟨toReal W₂ *ᵥ v, ?_⟩
  conv_lhs => rw [hsplit]
  rw [hW1, Matrix.mulVec_zero, zero_add]

/-! ## How many dimensionless groups are there? -/

/-- **Counting.** The dimensionless exponent vectors form a space of dimension `n - rank D`:
with `n` quantities and a dimension matrix of rank `ρ` there are exactly `n - ρ` independent
dimensionless groups. -/
theorem finrank_dimensionless (D : Matrix (Fin k) (Fin n) ℚ) :
    Module.finrank ℚ (LinearMap.ker D.mulVecLin) = n - D.rank := by
  have h := LinearMap.finrank_range_add_finrank_ker D.mulVecLin
  rw [Module.finrank_pi, Fintype.card_fin] at h
  have hr : Module.finrank ℚ (LinearMap.range D.mulVecLin) = D.rank := rfl
  omega

end NondimVerify

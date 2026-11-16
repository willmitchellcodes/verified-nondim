import NondimVerify.System

/-!
# Constraints, measured outputs, and what scalings say about identifiability

Three facts about a scaling symmetry, each decided from the model data:

* **Constraints are preserved** (`IsHomogeneous.poly_scale_eq_zero_iff`): if every term of a
  polynomial relation such as `S + I + R - N = 0` has the same weight, the relation holds for
  the rescaled point exactly when it holds for the original one. This is what a "unit link"
  (`N` is measured like `S`) means for the scalings a reduction may use.
* **Outputs are preserved** (`OutputInvariant.poly_scale`): if every term of every measured
  output has weight zero, the data do not change.
* **Such a scaling hides parameters** (`IsSymmetry.not_identifiable`): if a scaling leaves time
  and the outputs unchanged but moves a parameter, then every solution has a twin with the same
  data and a different value of that parameter. No experiment measuring those outputs can tell
  the two apart.

The last statement goes one way only. A parameter that no scaling moves can still be
non-identifiable for another reason; `NondimVerifyTest/Limits.lean` has a counterexample.
-/

namespace NondimVerify

open Matrix

variable {n r : ℕ}

/-- A (Laurent) polynomial given as a list of terms. -/
noncomputable def poly (ts : List (Term n)) (x : Fin n → ℝ) : ℝ := (ts.map fun t => t.eval x).sum

/-- Every term has weight `w` under the scalings `A`. -/
lemma poly_scale_of_weight (A : Matrix (Fin r) (Fin n) ℤ) (ts : List (Term n)) (w : Fin r → ℤ)
    (hw : ∀ t ∈ ts, ∀ j, (A *ᵥ t.exps) j = w j) (lam : Fin r → ℝ) (hlam : ∀ j, lam j ≠ 0)
    (x : Fin n → ℝ) : poly ts (scale A lam x) = (∏ j, lam j ^ w j) * poly ts x := by
  unfold poly
  have key : ∀ t ∈ ts, t.eval (scale A lam x) = (∏ j, lam j ^ w j) * t.eval x := by
    intro t ht
    unfold Term.eval
    rw [monomial_scale_eq A lam hlam]
    simp_rw [hw t ht]
    ring
  rw [List.map_congr_left key, List.sum_map_mul_left]

/-- All terms of the polynomial have the same weight under every scaling. -/
def IsHomogeneous (A : Matrix (Fin r) (Fin n) ℤ) (ts : List (Term n)) : Prop :=
  ∀ t ∈ ts, ∀ t' ∈ ts, ∀ j, (A *ᵥ t.exps) j = (A *ᵥ t'.exps) j

instance (A : Matrix (Fin r) (Fin n) ℤ) (ts : List (Term n)) : Decidable (IsHomogeneous A ts) := by
  unfold IsHomogeneous; infer_instance

/-- **A homogeneous relation is preserved by scaling.** If `p(x) = 0` is a conservation law or
any other polynomial relation whose terms all have the same weight, then the rescaled point
satisfies it exactly when the original point does. -/
theorem IsHomogeneous.poly_scale_eq_zero_iff {A : Matrix (Fin r) (Fin n) ℤ} {ts : List (Term n)}
    (h : IsHomogeneous A ts) (lam : Fin r → ℝ) (hlam : ∀ j, lam j ≠ 0) (x : Fin n → ℝ) :
    poly ts (scale A lam x) = 0 ↔ poly ts x = 0 := by
  cases ts with
  | nil => simp [poly]
  | cons t₀ rest =>
    rw [poly_scale_of_weight A (t₀ :: rest) (A *ᵥ t₀.exps)
      (fun t ht j => h t ht t₀ (List.mem_cons_self) j) lam hlam x]
    have hc : (∏ j, lam j ^ (A *ᵥ t₀.exps) j) ≠ 0 :=
      Finset.prod_ne_zero_iff.mpr fun j _ => zpow_ne_zero _ (hlam j)
    simp [hc]

/-- Every term of every measured output has weight zero under the scalings `A`. -/
def OutputInvariant (A : Matrix (Fin r) (Fin n) ℤ) (outs : List (List (Term n))) : Prop :=
  ∀ o ∈ outs, ∀ t ∈ o, ∀ j, (A *ᵥ t.exps) j = 0

instance (A : Matrix (Fin r) (Fin n) ℤ) (outs : List (List (Term n))) :
    Decidable (OutputInvariant A outs) := by
  unfold OutputInvariant; infer_instance

/-- The measured outputs take the same values at the rescaled point. -/
theorem OutputInvariant.poly_scale {A : Matrix (Fin r) (Fin n) ℤ} {outs : List (List (Term n))}
    (h : OutputInvariant A outs) (lam : Fin r → ℝ) (hlam : ∀ j, lam j ≠ 0) (x : Fin n → ℝ)
    {o : List (Term n)} (ho : o ∈ outs) : poly o (scale A lam x) = poly o x := by
  rw [poly_scale_of_weight A o 0 (fun t ht j => h o ho t ht j) lam hlam x]
  simp

/-- Variable `i` is **identifiable** from the outputs if two solutions that produce the same
data at all times must agree on `i`. (A strong, global notion: all solutions, all times.) -/
def LaurentSystem.Identifiable (sys : LaurentSystem n) (outs : List (List (Term n))) (i : Fin n) :
    Prop :=
  ∀ x x' : ℝ → Fin n → ℝ, sys.IsSolution x → sys.IsSolution x' →
    (∀ t, ∀ o ∈ outs, poly o (x' t) = poly o (x t)) → x' 0 i = x 0 i

/-- **A scaling that leaves time and the data unchanged hides every variable it moves.**
Let `A` be a symmetry that does not rescale time and leaves every output unchanged. If scaling
`j` acts on variable `i`, then every solution with `x_i ≠ 0` has a twin: another solution with
the same outputs at all times, a different value of `x_i`, and the same signs. -/
theorem LaurentSystem.IsSymmetry.not_identifiable {sys : LaurentSystem n}
    {A : Matrix (Fin r) (Fin n) ℤ} (h : sys.IsSymmetry A 0) {outs : List (List (Term n))}
    (hout : OutputInvariant A outs) (i : Fin n) (j : Fin r) (hij : A j i ≠ 0)
    {x : ℝ → Fin n → ℝ} (hx : sys.IsSolution x) (hxi : x 0 i ≠ 0) :
    ∃ x' : ℝ → Fin n → ℝ, sys.IsSolution x' ∧
      (∀ t, ∀ o ∈ outs, poly o (x' t) = poly o (x t)) ∧ x' 0 i ≠ x 0 i ∧
      ∀ t k, 0 < x t k → 0 < x' t k := by
  set lam : Fin r → ℝ := fun j' => if j' = j then 2 else 1 with hlam_def
  have hlam : ∀ j', lam j' ≠ 0 := fun j' => by
    simp only [hlam_def]; split_ifs <;> norm_num
  have hlam_pos : ∀ j', 0 < lam j' := fun j' => by
    simp only [hlam_def]; split_ifs <;> norm_num
  have hT : timeFactor lam (0 : Fin r → ℤ) = 1 := by simp [timeFactor]
  have hsol := h.map_solution lam hlam hx
  simp only [hT, div_one] at hsol
  refine ⟨fun s => scale A lam (x s), hsol, fun t o ho => hout.poly_scale lam hlam (x t) ho, ?_,
    fun t k hk => ?_⟩
  · have hprod : ∏ j', lam j' ^ A j' i = (2 : ℝ) ^ A j i := by
      rw [Finset.prod_eq_single j]
      · simp [hlam_def]
      · intro b _ hb; simp [hlam_def, hb]
      · intro hj; exact absurd (Finset.mem_univ j) hj
    have h2 : (2 : ℝ) ^ A j i ≠ 1 := by
      intro h1
      have := (zpow_eq_one_iff_right₀ (by norm_num : (0 : ℝ) ≤ 2) (by norm_num : (2 : ℝ) ≠ 1)).mp h1
      exact hij this
    show x 0 i * ∏ j', lam j' ^ A j' i ≠ x 0 i
    rw [hprod]
    intro heq
    apply h2
    have := mul_left_cancel₀ hxi (heq.trans (mul_one _).symm)
    exact this
  · exact mul_pos hk (Finset.prod_pos fun j' _ => zpow_pos (hlam_pos j') _)

/-- The same fact as a statement about identifiability: if some solution has `x_i ≠ 0`, then
`i` is not identifiable from the outputs. -/
theorem LaurentSystem.IsSymmetry.not_identifiable' {sys : LaurentSystem n}
    {A : Matrix (Fin r) (Fin n) ℤ} (h : sys.IsSymmetry A 0) {outs : List (List (Term n))}
    (hout : OutputInvariant A outs) (i : Fin n) (j : Fin r) (hij : A j i ≠ 0)
    (hex : ∃ x : ℝ → Fin n → ℝ, sys.IsSolution x ∧ x 0 i ≠ 0) : ¬ sys.Identifiable outs i := by
  obtain ⟨x, hx, hxi⟩ := hex
  obtain ⟨x', hx', hsame, hne, -⟩ := h.not_identifiable hout i j hij hx hxi
  exact fun hid => hne (hid x x' hx hx' hsame)

end NondimVerify

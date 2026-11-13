import NondimVerify.BuckinghamPi

/-! # Unit tests: the Buckingham Pi theorem on the textbook pendulum

Quantities (index order): `0 = T` period, `1 = L` length, `2 = g` gravity, `3 = m` mass.
Base units (rows of `D`): mass, length, time. So `g` has units length / time².
The only dimensionless group is `T² g / L`, and the classical conclusion is that the period
cannot depend on the mass.
-/

open NondimVerify Matrix

namespace NondimVerifyTest.BuckinghamPi

def D : Matrix (Fin 3) (Fin 4) ℤ := !![0, 0, 0, 1; 0, 1, 1, 0; 1, 0, -2, 0]
/-- The single group `T² g / L`. -/
def P : Matrix (Fin 4) (Fin 1) ℤ := !![2; -1; 1; 0]

-- certificate that `P` spans everything dimensionless: `[V₁ | P]` is unimodular, inverse `[W₁ ; W₂]`
def V₁ : Matrix (Fin 4) (Fin 3) ℤ := !![1, 0, 0; 0, 1, 0; 0, 0, 0; 0, 0, 1]
def W₁ : Matrix (Fin 3) (Fin 4) ℤ := !![1, 0, -2, 0; 0, 1, 1, 0; 0, 0, 0, 1]
def W₂ : Matrix (Fin 1) (Fin 4) ℤ := !![0, 0, 1, 0]
def Linv : Matrix (Fin 3) (Fin 3) ℤ := !![0, 0, 1; 0, 1, 0; 1, 0, 0]

theorem spans : ∀ v : Fin 4 → ℝ, toReal D *ᵥ v = 0 → ∃ w : Fin 1 → ℝ, v = toReal P *ᵥ w :=
  spans_kernel_of_certificate D P V₁ W₁ W₂ Linv 1 one_ne_zero
    (by decide +kernel) (by decide +kernel) (by decide +kernel)

/-! ## The group is what we say it is, and it is dimensionless -/

example (T L g m : ℝ) (hL : L ≠ 0) : piGroups P ![T, L, g, m] 0 = T ^ 2 * g / L := by
  simp [piGroups, monomial, P, Fin.prod_univ_succ]
  field_simp

example (lam : Fin 3 → ℝ) (h : ∀ j, lam j ≠ 0) (q : Fin 4 → ℝ) :
    piGroups P (scale D lam q) = piGroups P q :=
  pi_group_invariant D P (by decide +kernel) lam h q

-- `T g` is not dimensionless, and `D * P = 0` detects that.
example : D * (!![1; 0; 1; 0] : Matrix (Fin 4) (Fin 1) ℤ) ≠ 0 := by decide +kernel

/-! ## The theorem -/

-- Any unit-independent quantity takes equal values at two pendulums with equal `T² g / L`.
example {α : Type} (f : (Fin 4 → ℝ) → α) (hf : UnitInvariant D f) (q q' : Fin 4 → ℝ)
    (hq : ∀ i, 0 < q i) (hq' : ∀ i, 0 < q' i) (h : piGroups P q = piGroups P q') : f q = f q' :=
  buckingham_pi D P spans f hf q q' hq hq' h

/-- **The period law cannot involve the mass.** Changing only `m` changes no unit-independent
quantity. -/
theorem mass_is_irrelevant {α : Type} (f : (Fin 4 → ℝ) → α) (hf : UnitInvariant D f)
    (T L g m m' : ℝ) (hT : 0 < T) (hL : 0 < L) (hg : 0 < g) (hm : 0 < m) (hm' : 0 < m') :
    f ![T, L, g, m] = f ![T, L, g, m'] := by
  refine buckingham_pi D P spans f hf _ _ ?_ ?_ ?_
  · intro i; fin_cases i <;> assumption
  · intro i; fin_cases i <;> assumption
  · funext j
    fin_cases j
    simp [piGroups, monomial, P, Fin.prod_univ_succ]

-- Factorized form: `f = F(T² g / L)` for some function `F` of one variable.
example {α : Type} (f : (Fin 4 → ℝ) → α) (hf : UnitInvariant D f) :
    ∃ F : (Fin 1 → ℝ) → α, ∀ q : Fin 4 → ℝ, (∀ i, 0 < q i) → f q = F (piGroups P q) :=
  buckingham_pi_factorization D P spans f hf

/-! ## The count: 4 quantities − rank 3 = 1 group -/

def Dq : Matrix (Fin 3) (Fin 4) ℚ := !![0, 0, 0, 1; 0, 1, 1, 0; 1, 0, -2, 0]
theorem rank_Dq : Dq.rank = 3 := by unfold Dq; eval_rank

example : Module.finrank ℚ (LinearMap.ker Dq.mulVecLin) = 1 := by
  rw [finrank_dimensionless, rank_Dq]

/-! ## Boundary cases -/

-- No units at all (`D` has no rows): everything is dimensionless, and `P = 1` spans.
example (v : Fin 2 → ℝ) (_ : toReal (0 : Matrix (Fin 0) (Fin 2) ℤ) *ᵥ v = 0) :
    ∃ w : Fin 2 → ℝ, v = toReal (1 : Matrix (Fin 2) (Fin 2) ℤ) *ᵥ w :=
  ⟨v, by simp [toReal]⟩

-- A constant function is unit-invariant, whatever the units are.
example (D : Matrix (Fin 2) (Fin 3) ℤ) : UnitInvariant D (fun _ => (7 : ℝ)) := fun _ _ _ _ => rfl

-- A dimensional quantity is not: the length `L` itself changes with the unit of length.
example : ¬ UnitInvariant D (fun q => q 1) := by
  intro h
  have := h ![1, 2, 1] ![1, 1, 1, 1] (by intro j; fin_cases j <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
  simp [scale, D, Fin.prod_univ_succ] at this

end NondimVerifyTest.BuckinghamPi

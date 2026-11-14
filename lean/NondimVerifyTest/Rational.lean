import NondimVerify.Rational
import NondimVerify.Certified

/-! # Unit tests: systems with rational right-hand sides

Running example: a saturating response `dx/dt = a x / (1 + b x)` with variables
`0 = x`, `1 = a`, `2 = b`. -/

open NondimVerify Matrix

namespace NondimVerifyTest.Rational

noncomputable def saturating : RatSystem 3 where
  terms := ![[⟨[⟨1, ![1, 1, 0]⟩], [⟨1, ![0, 0, 0]⟩, ⟨1, ![1, 0, 1]⟩]⟩], [], []]

example (x a b : ℝ) : saturating.rhs 0 ![x, a, b] = a * x / (1 + b * x) := by
  simp [RatSystem.rhs, Frac.eval, poly, Term.eval, monomial, saturating, Fin.prod_univ_succ]
  ring

example : saturating.IsParam 1 ∧ saturating.IsParam 2 ∧ ¬ saturating.IsParam 0 := by decide

/-! ## Symmetries are decided from numerators and denominators -/

/-- Time: `t ↦ λ t`, `a ↦ a / λ`. Amount: `x ↦ λ x`, `b ↦ b / λ`. -/
def A : Matrix (Fin 2) (Fin 3) ℤ := !![0, -1, 0; 1, 0, -1]

theorem symmetry : saturating.IsSymmetry A ![1, 0] := by decide +kernel

-- Scaling `x` without `b` makes the denominator `1 + b x` inhomogeneous: refused.
example : ¬ saturating.IsSymmetry (!![1, 0, 0] : Matrix (Fin 1) (Fin 3) ℤ) ![0] := by decide +kernel
-- Scaling time without `a`: refused.
example : ¬ saturating.IsSymmetry (!![0, 0, 0] : Matrix (Fin 1) (Fin 3) ℤ) ![1] := by decide +kernel

-- A polynomial system is the special case "denominator 1".
example : (⟨![[⟨[⟨-1, ![1, 1]⟩], [⟨1, ![0, 0]⟩]⟩], []]⟩ : RatSystem 2).IsSymmetry
    (!![0, -1] : Matrix (Fin 1) (Fin 2) ℤ) ![1] := by decide +kernel

/-! ## The general theorems hold verbatim -/

example (lam : Fin 2 → ℝ) (h : ∀ j, lam j ≠ 0) (x : Fin 3 → ℝ) :
    saturating.rhs 0 (scale A lam x) = (∏ j, lam j ^ (A j 0 - ![1, 0] j)) * saturating.rhs 0 x :=
  symmetry.rhs_scale lam h x 0

example (lam : Fin 2 → ℝ) (h : ∀ j, lam j ≠ 0) (x : ℝ → Fin 3 → ℝ) :
    saturating.IsSolution (fun s => scale A lam (x (s / timeFactor lam ![1, 0]))) ↔
      saturating.IsSolution x :=
  symmetry.solution_iff lam h

example (x : ℝ → Fin 3 → ℝ) (hx : saturating.IsSolution x) (s : ℝ) : x s 2 = x 0 2 :=
  hx.param_const (by decide) s

-- both parameters can be scaled to 1 along any positive solution
example (x : ℝ → Fin 3 → ℝ) (hx : saturating.IsSolution x) (hpos : ∀ i, 0 < x 0 i) :
    ∃ lam : Fin 2 → ℝ, (∀ j, 0 < lam j) ∧
      saturating.IsSolution (fun s => scale A lam (x (s / timeFactor lam ![1, 0]))) ∧
      ∀ s i, scale A lam (x (s / timeFactor lam ![1, 0])) (![1, 2] i) = 1 :=
  symmetry.nondimensionalize ![1, 2] !![-1, 0; 0, -1] 1 one_ne_zero (by decide +kernel) hx (x 0)
    (fun i => by fin_cases i <;> exact hpos _)
    (fun s i => by fin_cases i <;> exact hx.param_const (by decide) s)

/-! ## Reducing one quotient -/

-- `frac_reduce` with numbers: 6 * (10 / 4) = 3 * (5 / 1), using m = 4.
example : (6 : ℝ) * (10 / 4) = 3 * (5 / 1) :=
  frac_reduce (m := 4) (by norm_num) (by norm_num) (by norm_num)

-- it needs no assumption on the reduced denominator: with D' = 0 both sides are 0
example (c T N' : ℝ) (N : ℝ) (h : c * N = T * 2 * N') : c * (N / (2 * 0)) = T * (N' / 0) :=
  frac_reduce (m := 2) (by norm_num) rfl h

/-! ## Boundary cases -/

-- an empty denominator evaluates to 0 (Lean's `x / 0 = 0`), an empty numerator too
example (x : Fin 2 → ℝ) : (⟨[⟨1, ![1, 0]⟩], []⟩ : Frac 2).eval x = 0 := by simp [Frac.eval, poly]
example (x : Fin 2 → ℝ) : (⟨[], [⟨1, ![1, 0]⟩]⟩ : Frac 2).eval x = 0 := by simp [Frac.eval, poly]

/-! ## Rosenzweig–MacArthur: the generated certificates -/

section Generated
open NondimVerify.Certified

-- Holling type II predation, certified for this package's solver and for desr
example {x : ℝ → Fin 8 → ℝ} (hx : Own.RosenzweigMacArthur.sys.IsSolution x)
    (hpos : ∀ s i, 0 < x s i) (τ : ℝ) :
    HasDerivAt (fun τ => piGroups Own.RosenzweigMacArthur.Vn
        (x (τ / monomial (x 0) Own.RosenzweigMacArthur.w)) 0)
      (Own.RosenzweigMacArthur.red_N (piGroups Own.RosenzweigMacArthur.Vn
        (x (τ / monomial (x 0) Own.RosenzweigMacArthur.w)))) τ :=
  (Own.RosenzweigMacArthur.reduction_correct hx hpos τ).1

example : Desr.RosenzweigMacArthur.sys.IsSymmetry Desr.RosenzweigMacArthur.A
    Desr.RosenzweigMacArthur.tau := Desr.RosenzweigMacArthur.symmetry

-- both tools leave three parameters, and Lean proves no scaling reduction can leave fewer
example : Own.RosenzweigMacArthur.ParamCols.rank = 3 := Own.RosenzweigMacArthur.rank_paramCols
example : Desr.RosenzweigMacArthur.ParamCols.rank = 3 := Desr.RosenzweigMacArthur.rank_paramCols

end Generated

end NondimVerifyTest.Rational

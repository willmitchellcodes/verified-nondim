import NondimVerify.System

/-! # Unit tests: systems as data, symmetries, and the solution correspondence

The running example is exponential decay, `dx/dt = -k x`, with variables `0 = x`, `1 = k`.
It is small enough to check every statement by hand, and it has an explicit solution, so the
general theorems can be watched acting on a concrete curve.
-/

open NondimVerify Matrix

namespace NondimVerifyTest.System

/-- `dx/dt = -k x`; `k` has no equation, so it is a parameter. -/
noncomputable def decay : LaurentSystem 2 where
  terms := ![[⟨-1, ![1, 1]⟩], []]

/-! ## The data means what we think it means -/

example (x k : ℝ) : decay.rhs 0 ![x, k] = -(k * x) := by
  simp [LaurentSystem.rhs, Term.eval, monomial, decay, Fin.prod_univ_succ]; ring

example (z : Fin 2 → ℝ) : decay.rhs 1 z = 0 := by simp [LaurentSystem.rhs, decay]

example : decay.IsParam 1 := by decide
example : ¬ decay.IsParam 0 := by decide

/-! ## Symmetries are decided from the data -/

/-- Changing the unit of time: `t ↦ λ t`, `k ↦ k / λ`. -/
def Atime : Matrix (Fin 1) (Fin 2) ℤ := !![0, -1]
/-- Changing the unit of `x` (the equation is linear in `x`). -/
def Aamount : Matrix (Fin 1) (Fin 2) ℤ := !![1, 0]
/-- Both at once. -/
def Aboth : Matrix (Fin 2) (Fin 2) ℤ := !![0, -1; 1, 0]

theorem time_symmetry : decay.IsSymmetry Atime ![1] := by decide +kernel
theorem amount_symmetry : decay.IsSymmetry Aamount ![0] := by decide +kernel
theorem both_symmetry : decay.IsSymmetry Aboth ![1, 0] := by decide +kernel

-- Wrong weights are rejected: scaling time without scaling `k`, or `k` the wrong way round.
example : ¬ decay.IsSymmetry (!![0, 0] : Matrix (Fin 1) (Fin 2) ℤ) ![1] := by decide +kernel
example : ¬ decay.IsSymmetry (!![0, 1] : Matrix (Fin 1) (Fin 2) ℤ) ![1] := by decide +kernel
example : ¬ decay.IsSymmetry Atime ![0] := by decide +kernel

-- Coefficients do not matter for symmetry, only exponents: `dx/dt = -5 k x` has the same ones.
example : (⟨![[⟨-5, ![1, 1]⟩], []]⟩ : LaurentSystem 2).IsSymmetry Aboth ![1, 0] := by
  decide +kernel

-- With no scalings at all there is nothing to check.
example (sys : LaurentSystem 3) (A : Matrix (Fin 0) (Fin 3) ℤ) (τ : Fin 0 → ℤ) :
    sys.IsSymmetry A τ := fun _ _ _ j => j.elim0

-- A system with no equations (only parameters) is symmetric under every scaling.
example (A : Matrix (Fin 2) (Fin 3) ℤ) (τ : Fin 2 → ℤ) :
    (⟨fun _ => []⟩ : LaurentSystem 3).IsSymmetry A τ := fun _ t ht => by simp at ht

/-! ## The time factor -/

example : timeFactor ![(2 : ℝ)] ![1] = 2 := by simp [timeFactor]
example : timeFactor ![(2 : ℝ), 3] ![1, 0] = 2 := by simp [timeFactor, Fin.prod_univ_succ]
example : timeFactor ![(2 : ℝ)] ![-1] = 1 / 2 := by simp [timeFactor]
example (lam : Fin 0 → ℝ) (τ : Fin 0 → ℤ) : timeFactor lam τ = 1 := by simp [timeFactor]

/-! ## An explicit solution, and what the theorems do to it

Constant-rate growth, `dx/dt = k`, has the solutions `x(t) = x₀ + k t`. -/

/-- `dx/dt = k`. -/
noncomputable def growth : LaurentSystem 2 where
  terms := ![[⟨1, ![0, 1]⟩], []]

/-- `t ↦ λ t`, `k ↦ k / λ`. -/
theorem growth_time_symmetry : growth.IsSymmetry Atime ![1] := by decide +kernel

/-- `x(t) = x₀ + k t` with `k` constant. -/
noncomputable def line (x₀ k : ℝ) : ℝ → Fin 2 → ℝ := fun t => ![x₀ + k * t, k]

theorem line_isSolution (x₀ k : ℝ) : growth.IsSolution (line x₀ k) := by
  intro i t
  fin_cases i
  · have h : HasDerivAt (fun s : ℝ => x₀ + k * s) (k * 1) t :=
      ((hasDerivAt_id' t).const_mul k).const_add x₀
    refine h.congr_deriv ?_
    simp [LaurentSystem.rhs, Term.eval, monomial, growth, line, Fin.prod_univ_succ]
  · simpa [LaurentSystem.rhs, growth, line] using hasDerivAt_const t k

-- `map_solution`: measuring time in a unit `λ` times smaller gives another solution.
example (x₀ k lam : ℝ) (h : lam ≠ 0) :
    growth.IsSolution fun s => scale Atime ![lam] (line x₀ k (s / timeFactor ![lam] ![1])) :=
  growth_time_symmetry.map_solution ![lam] (by simpa using h) (line_isSolution x₀ k)

-- ...and that new solution is the line with rate `k / λ`, exactly as a change of time unit should give.
example (x₀ k lam : ℝ) (h : lam ≠ 0) (s : ℝ) :
    scale Atime ![lam] (line x₀ k (s / timeFactor ![lam] ![1])) = line x₀ (k / lam) s := by
  funext i
  fin_cases i
  · simp [scale, Atime, line, timeFactor]
    field_simp
  · simp [scale, Atime, line]
    field_simp

-- `solution_iff`: nothing is gained or lost by rescaling.
example (lam : Fin 2 → ℝ) (h : ∀ j, lam j ≠ 0) (x : ℝ → Fin 2 → ℝ) :
    decay.IsSolution (fun s => scale Aboth lam (x (s / timeFactor lam ![1, 0]))) ↔ decay.IsSolution x :=
  both_symmetry.solution_iff lam h

-- `param_const`: along *any* solution the parameter `k` never changes.
example (x : ℝ → Fin 2 → ℝ) (hx : decay.IsSolution x) (s : ℝ) : x s 1 = x 0 1 :=
  hx.param_const (by decide) s

/-! ## Normalizing parameters -/

-- `k` can be scaled to 1, whatever positive value it has (certificate: G = (-1), d = 1).
example (c : Fin 2 → ℝ) (hk : 0 < c 1) :
    ∃ lam : Fin 1 → ℝ, (∀ j, 0 < lam j) ∧ ∀ i, scale Atime lam c (![1] i) = 1 :=
  exists_normalizing_scaling Atime ![1] !![-1] 1 one_ne_zero (by decide +kernel) c
    (fun i => by fin_cases i; exact hk)

-- The whole statement at once: every decay solution is, after rescaling time, a solution with k = 1.
example (x : ℝ → Fin 2 → ℝ) (hx : decay.IsSolution x) (hk : 0 < x 0 1) :
    ∃ lam : Fin 1 → ℝ, (∀ j, 0 < lam j) ∧
      decay.IsSolution (fun s => scale Atime lam (x (s / timeFactor lam ![1]))) ∧
      ∀ s i, scale Atime lam (x (s / timeFactor lam ![1])) (![1] i) = 1 :=
  time_symmetry.nondimensionalize ![1] !![-1] 1 one_ne_zero (by decide +kernel) hx (x 0)
    (fun i => by fin_cases i; exact hk)
    (fun s i => by fin_cases i; exact hx.param_const (by decide) s)

-- Asking for nothing is always possible (k = 0 parameters to normalize).
example (c : Fin 2 → ℝ) :
    ∃ lam : Fin 1 → ℝ, (∀ j, 0 < lam j) ∧ ∀ i : Fin 0, scale Atime lam c (Fin.elim0 i) = 1 :=
  exists_normalizing_scaling Atime Fin.elim0 (Matrix.of fun i _ => Fin.elim0 i) 1 one_ne_zero
    (by ext i; exact i.elim0) c (fun i => i.elim0)

-- Two quantities that always scale together cannot both be normalized (kernel vector (1, -1)).
example :
    ∃ c : Fin 2 → ℝ, (∀ i, 0 < c i) ∧
      ∀ lam : Fin 1 → ℝ, (∀ j, lam j ≠ 0) → ¬ ∀ i, scale (!![1, 1] : Matrix (Fin 1) (Fin 2) ℤ) lam c (id i) = 1 :=
  not_normalizable_of_kernel_vector _ id Function.injective_id ![1, -1] (by decide) (by decide +kernel)

end NondimVerifyTest.System

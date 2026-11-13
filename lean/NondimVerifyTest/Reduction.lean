import NondimVerify.Reduction
import NondimVerify.Certified

/-! # Unit and integration tests: reduction to invariants, and the generated certificates

First the general theorem on a system small enough to follow by hand, then the certificates
that `nondim certify` generates from desr's output and from this package's own solver.
-/

open NondimVerify Matrix

namespace NondimVerifyTest.Reduction

/-! ## By hand: logistic growth `dN/dt = r N - (r/K) N²`

Variables `0 = N`, `1 = r`, `2 = K`. Scalings: time (`r ↦ r/λ`), amount (`N, K ↦ λN, λK`).
Auxiliary monomials `r`, `K` (set to 1); the one invariant is `N / K`. -/

noncomputable def logistic : LaurentSystem 3 where
  terms := ![[⟨1, ![1, 1, 0]⟩, ⟨-1, ![2, 1, -1]⟩], [], []]

def A : Matrix (Fin 2) (Fin 3) ℤ := !![0, -1, 0; 1, 0, 1]
def Vi : Matrix (Fin 3) (Fin 2) ℤ := !![0, 0; 1, 0; 0, 1]
def Vn : Matrix (Fin 3) (Fin 1) ℤ := !![1; 0; -1]
def Wu : Matrix (Fin 2) (Fin 3) ℤ := !![0, 1, 0; 1, 0, 1]
def Wd : Matrix (Fin 1) (Fin 3) ℤ := !![1, 0, 0]
def G : Matrix (Fin 2) (Fin 2) ℤ := !![-1, 0; 0, 1]

theorem symmetry : logistic.IsSymmetry A ![1, 0] := by decide +kernel

example (N r K : ℝ) (hK : K ≠ 0) : logistic.rhs 0 ![N, r, K] = r * N * (1 - N / K) := by
  simp [LaurentSystem.rhs, Term.eval, monomial, logistic, Fin.prod_univ_succ]
  field_simp
  ring

-- the invariant is N / K
example (N r K : ℝ) : piGroups Vn ![N, r, K] 0 = N / K := by
  simp [piGroups, monomial, Vn, Fin.prod_univ_succ, div_eq_mul_inv]

-- on the cross-section r = K = 1, the point is (N/K, 1, 1)
example (π : Fin 1 → ℝ) : reconstruct Wd π = ![π 0, 1, 1] := by
  funext p; fin_cases p <;> simp [reconstruct, monomial, Wd]

-- a point with r = K = 1 is recovered from its invariant
example (y : Fin 3 → ℝ) (hy : ∀ i, 0 < y i) (hr : y 1 = 1) (hK : y 2 = 1) :
    y = reconstruct Wd (piGroups Vn y) :=
  eq_reconstruct_of_section Vi Vn Wu Wd (by decide +kernel) y hy (fun j => by
    fin_cases j <;> simp [monomial, Vi, Fin.prod_univ_succ, hr, hK])

/-- The reduction theorem on the logistic model: every positive solution rescales to a solution
that depends on `N / K` alone. -/
theorem logistic_reduction {x : ℝ → Fin 3 → ℝ} (hx : logistic.IsSolution x) (hpos : ∀ s i, 0 < x s i) :
    ∃ lam : Fin 2 → ℝ, (∀ j, 0 < lam j) ∧
      logistic.IsSolution (fun s => scale A lam (x (s / timeFactor lam ![1, 0]))) ∧
      ∀ s, scale A lam (x (s / timeFactor lam ![1, 0]))
        = reconstruct Wd (piGroups Vn (scale A lam (x (s / timeFactor lam ![1, 0])))) := by
  obtain ⟨lam, hlam, hsol, -, -, hsec⟩ :=
    symmetry.reduction_of_parameters Vi Vn Wu Wd (by decide +kernel) (by decide +kernel) G 1
      one_ne_zero (by decide +kernel) (by decide +kernel) hx hpos
  exact ⟨lam, hlam, hsol, hsec⟩

/-- The reduced logistic equation `du/dτ = u (1 - u)` for `u = N / K`, `τ = r t`, from the general
theorem and one algebraic identity. -/
theorem logistic_reduced {x : ℝ → Fin 3 → ℝ} (hx : logistic.IsSolution x) (hpos : ∀ s i, 0 < x s i)
    (τ : ℝ) :
    HasDerivAt (fun τ => piGroups Vn (x (τ / monomial (x 0) ![0, 1, 0])) 0)
      ((fun u : ℝ => u * (1 - u)) (piGroups Vn (x (τ / monomial (x 0) ![0, 1, 0])) 0)) τ :=
  hx.hasDerivAt_newVariable hpos 0 _ ![0, 0, -1] ![0, 1, 0] (by decide +kernel) (by decide +kernel)
    (by decide +kernel) (fun z => (fun u : ℝ => u * (1 - u)) (piGroups Vn z 0))
    (fun z hz => by
      have h2 := (hz 2).ne'
      simp [LaurentSystem.rhs, Term.eval, monomial, logistic, piGroups, Vn, Fin.prod_univ_succ]
      field_simp; ring) τ

-- a factor that involves a state is refused: `N` is not a parameter
example : ¬ logistic.ParamMonomial ![1, 0, 0] := by decide +kernel
example : logistic.ParamMonomial ![0, 1, -1] := by decide +kernel

-- the auxiliary monomials must be parameters: `N` is not one, and the check says so
example : ¬ logistic.OnlyParams (!![1; 0; 0] : Matrix (Fin 3) (Fin 1) ℤ) := by decide +kernel
example : logistic.OnlyParams Vi := by decide +kernel

/-! ## desr's output, certified -/

section Desr
open NondimVerify.Certified

-- desr's reduced SIR system, as Lean proved it equal to the original on the cross-section
example (π : Fin 2 → ℝ) : Desr.SIRNoN.red_I π = π 0 * π 1 - π 0 := by
  simp [Desr.SIRNoN.red_I]; ring
example (π : Fin 2 → ℝ) : Desr.SIRNoN.red_S π = -(π 0 * π 1) := by
  simp [Desr.SIRNoN.red_S]

-- desr's invariants for SIR are `I β / γ` and `S β / γ` (variable order: β, γ, I, S)
example (β γ I S : ℝ) : piGroups Desr.SIRNoN.Vn ![β, γ, I, S] = ![I * β / γ, S * β / γ] := by
  funext j
  fin_cases j <;>
    simp [piGroups, monomial, Desr.SIRNoN.Vn, Fin.prod_univ_succ, div_eq_mul_inv] <;> ring

-- the main statement, as a fact about every positive solution: desr's new variable for S,
-- followed in desr's new time τ = γ t, has the derivative desr's reduced system says
example {x : ℝ → Fin 4 → ℝ} (hx : Desr.SIRNoN.sys.IsSolution x) (hpos : ∀ s i, 0 < x s i) (τ : ℝ) :
    HasDerivAt (fun τ => piGroups Desr.SIRNoN.Vn (x (τ / monomial (x 0) Desr.SIRNoN.w)) 1)
      (Desr.SIRNoN.red_S (piGroups Desr.SIRNoN.Vn (x (τ / monomial (x 0) Desr.SIRNoN.w)))) τ :=
  (Desr.SIRNoN.reduction_correct hx hpos τ).1

-- the new time really is γ t: the factor is the value of γ (variable 1)
example (x : Fin 4 → ℝ) : monomial x Desr.SIRNoN.w = x 1 := by
  simp [monomial, Desr.SIRNoN.w, Fin.prod_univ_succ]

-- and the same solution can be moved onto the cross-section, keeping its invariants
example {x : ℝ → Fin 4 → ℝ} (hx : Desr.SIRNoN.sys.IsSolution x) (hpos : ∀ s i, 0 < x s i) :
    ∃ lam : Fin 2 → ℝ, (∀ j, 0 < lam j) ∧
      Desr.SIRNoN.sys.IsSolution (fun s => scale Desr.SIRNoN.A lam (x (s / timeFactor lam Desr.SIRNoN.tau))) := by
  obtain ⟨lam, hlam, hsol, -⟩ := Desr.SIRNoN.cross_section hx hpos
  exact ⟨lam, hlam, hsol⟩

-- Lotka–Volterra keeps exactly one parameter, `κ = c / a` (variable order a, b, c, d, x, y)
example (a b c d x y : ℝ) : piGroups Desr.LotkaVolterra.Vn ![a, b, c, d, x, y] 0 = c / a := by
  simp [piGroups, monomial, Desr.LotkaVolterra.Vn, Fin.prod_univ_succ, div_eq_mul_inv]; ring

-- desr and this package's solver found the same number of scalings for every shared model
example : Desr.Logistic.Afull.rank = Own.Logistic.Afull.rank := by
  rw [Desr.Logistic.rank_A, Own.Logistic.rank_A]
example : Desr.SIRNoN.Afull.rank = Own.SIRNoN.Afull.rank := by
  rw [Desr.SIRNoN.rank_A, Own.SIRNoN.rank_A]
example : Desr.LotkaVolterra.Afull.rank = Own.LotkaVolterra.Afull.rank := by
  rw [Desr.LotkaVolterra.rank_A, Own.LotkaVolterra.rank_A]
example : Desr.MichaelisMenten.Afull.rank = Own.MichaelisMenten.Afull.rank := by
  rw [Desr.MichaelisMenten.rank_A, Own.MichaelisMenten.rank_A]

-- and each found as many as rank–nullity allows (variables + time − rank K)
example : Desr.LotkaVolterra.Afull.rank = 7 - Desr.LotkaVolterra.Kmat.rank := by
  rw [Desr.LotkaVolterra.rank_A, Desr.LotkaVolterra.rank_K]
example : Desr.MichaelisMenten.Afull.rank = 7 - Desr.MichaelisMenten.Kmat.rank := by
  rw [Desr.MichaelisMenten.rank_A, Desr.MichaelisMenten.rank_K]

-- Buckingham Pi for desr's SIR invariants: anything unit-free depends on γt, Iβ/γ, Sβ/γ only
example (f : (Fin 5 → ℝ) → ℝ) (hf : UnitInvariant Desr.SIRNoN.Dfull f) (q q' : Fin 5 → ℝ)
    (hq : ∀ i, 0 < q i) (hq' : ∀ i, 0 < q' i)
    (h : piGroups Desr.SIRNoN.Pfull q = piGroups Desr.SIRNoN.Pfull q') : f q = f q' :=
  Desr.SIRNoN.invariants_complete f hf q q' hq hq' h

end Desr

end NondimVerifyTest.Reduction

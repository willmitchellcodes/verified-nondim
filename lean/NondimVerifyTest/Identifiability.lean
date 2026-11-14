import NondimVerify.Identifiability
import NondimVerify.Certified

/-! # Unit tests: constraints, outputs, and the one-way identifiability theorem -/

open NondimVerify Matrix

namespace NondimVerifyTest.Identifiability

/-! ## Polynomials and homogeneous relations

The SIR conservation law `S + I + R - N = 0`, in the variable order of the generated
certificate (`S, I, R, β, γ, N`). -/

noncomputable def conservation : List (Term 6) :=
  [⟨1, ![1, 0, 0, 0, 0, 0]⟩, ⟨1, ![0, 1, 0, 0, 0, 0]⟩, ⟨1, ![0, 0, 1, 0, 0, 0]⟩,
   ⟨-1, ![0, 0, 0, 0, 0, 1]⟩]

example (S I R β γ N : ℝ) : poly conservation ![S, I, R, β, γ, N] = S + I + R - N := by
  simp [poly, Term.eval, monomial, conservation, Fin.prod_univ_succ]; ring

-- The scalings the certificate uses give every term of the law the same weight...
theorem conservation_homogeneous : IsHomogeneous Certified.Own.SIR.A conservation := by
  decide +kernel

-- ...so a rescaled state satisfies `S + I + R = N` exactly when the original one does.
example (lam : Fin 2 → ℝ) (h : ∀ j, lam j ≠ 0) (x : Fin 6 → ℝ) :
    poly conservation (scale Certified.Own.SIR.A lam x) = 0 ↔ poly conservation x = 0 :=
  conservation_homogeneous.poly_scale_eq_zero_iff lam h x

/-- Scale `S`, `I`, `R` by `λ` and `β` by `1/λ`, but leave `N` alone. -/
def withoutN : Matrix (Fin 1) (Fin 6) ℤ := !![1, 1, 1, -1, 0, 0]

-- It does not respect the law, and the check says so.
example : ¬ IsHomogeneous withoutN conservation := by decide +kernel

-- Yet it IS a symmetry of the differential equations, because `N` does not occur in them. This
-- is how a "spurious" nondimensionalization arises when a conservation law is ignored.
example : Certified.Own.SIR.sys.IsSymmetry withoutN ![0] := by decide +kernel

-- Concretely: it sends the consistent state (S, I, R, N) = (1, 1, 1, 3) to (2, 2, 2, 3).
example : poly conservation ![1, 1, 1, 1, 1, 3] = 0 ∧
    poly conservation (scale withoutN ![2] ![1, 1, 1, 1, 1, 3]) ≠ 0 := by
  constructor
  · simp [poly, Term.eval, monomial, conservation, Fin.prod_univ_succ]; norm_num
  · simp [poly, Term.eval, monomial, conservation, scale, withoutN, Fin.prod_univ_succ]; norm_num

-- Boundary cases: the empty relation and a one-term relation are always homogeneous.
example (A : Matrix (Fin 2) (Fin 3) ℤ) : IsHomogeneous A [] := fun _ h => by simp at h
example (A : Matrix (Fin 2) (Fin 3) ℤ) (t : Term 3) : IsHomogeneous A [t] := by
  intro a ha b hb j
  simp at ha hb
  rw [ha, hb]

/-! ## A model small enough to follow: growth seen through an unknown gain

`dx/dt = k`, measured `y = c x`. Variables `0 = x`, `1 = k`, `2 = c`. Doubling `x` and `k` and
halving `c` changes nothing an observer of `y` can see. -/

noncomputable def gain : LaurentSystem 3 where
  terms := ![[⟨1, ![0, 1, 0]⟩], [], []]

noncomputable def y : List (Term 3) := [⟨1, ![1, 0, 1]⟩]

def hidden : Matrix (Fin 1) (Fin 3) ℤ := !![1, 1, -1]

example (x k c : ℝ) : poly y ![x, k, c] = c * x := by
  simp [poly, Term.eval, monomial, y, Fin.prod_univ_succ]; ring

theorem hidden_symmetry : gain.IsSymmetry hidden 0 := by decide +kernel
theorem hidden_output : OutputInvariant hidden [y] := by decide +kernel

-- the output really is unchanged at every point
example (lam : Fin 1 → ℝ) (h : ∀ j, lam j ≠ 0) (x : Fin 3 → ℝ) :
    poly y (scale hidden lam x) = poly y x :=
  hidden_output.poly_scale lam h x (by simp)

/-- An explicit solution: `x = 1 + t`, `k = 1`, `c = 1`. -/
theorem a_solution : gain.IsSolution fun t => ![1 + t, 1, 1] := by
  intro i t
  fin_cases i
  · have h : HasDerivAt (fun s : ℝ => 1 + s) 1 t := (hasDerivAt_id' t).const_add 1
    simpa [LaurentSystem.rhs, Term.eval, monomial, gain, Fin.prod_univ_succ] using h
  · simpa [LaurentSystem.rhs, gain] using hasDerivAt_const t (1 : ℝ)
  · simpa [LaurentSystem.rhs, gain] using hasDerivAt_const t (1 : ℝ)

/-- The gain `c` cannot be identified from `y`. -/
theorem gain_not_identifiable : ¬ gain.Identifiable [y] 2 :=
  hidden_symmetry.not_identifiable' hidden_output 2 0 (by decide)
    ⟨_, a_solution, by simp⟩

/-- Neither can the rate `k`. -/
theorem rate_not_identifiable : ¬ gain.Identifiable [y] 1 :=
  hidden_symmetry.not_identifiable' hidden_output 1 0 (by decide)
    ⟨_, a_solution, by simp⟩

-- The twin solution keeps signs, so it is as physical as the original.
example {x : ℝ → Fin 3 → ℝ} (hx : gain.IsSolution x) (h0 : x 0 2 ≠ 0) :
    ∃ x' : ℝ → Fin 3 → ℝ, gain.IsSolution x' ∧ (∀ t k, 0 < x t k → 0 < x' t k) := by
  obtain ⟨x', hx', -, -, hpos⟩ := hidden_symmetry.not_identifiable hidden_output 2 0 (by decide) hx h0
  exact ⟨x', hx', hpos⟩

-- A scaling that changes the output is refused: scaling `x` alone doubles `y`.
example : ¬ OutputInvariant (!![1, 1, 0] : Matrix (Fin 1) (Fin 3) ℤ) [y] := by decide +kernel

/-! ## The generated certificate for SIR observed through `y = ρ I` -/

section Generated
open NondimVerify.Certified

-- β and ρ are flagged...
example {x : ℝ → Fin 5 → ℝ} (hx : Own.SIRReported.sys.IsSolution x) (h0 : x 0 2 ≠ 0) :
    ∃ x' : ℝ → Fin 5 → ℝ, Own.SIRReported.sys.IsSolution x' ∧ x' 0 2 ≠ x 0 2 := by
  obtain ⟨x', hx', -, hne, -⟩ := Own.SIRReported.not_identifiable_beta hx h0
  exact ⟨x', hx', hne⟩

-- ...and γ is not moved by the output-preserving scaling (so this test says nothing about it).
example : Own.SIRReported.B 0 3 = 0 := by decide +kernel

-- the unit links of SIR with N are respected by the reduction's scalings
example : Own.SIR.A * Own.SIR.Links = 0 := Own.SIR.links_respected

end Generated

end NondimVerifyTest.Identifiability

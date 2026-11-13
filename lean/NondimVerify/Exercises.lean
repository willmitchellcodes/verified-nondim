import NondimVerify.Theory

/-!
# Exercises (not part of the default build)

Open this file in VS Code and replace each `sorry`. They complete the story told by
`Theory.lean`, and working through them is a good way to understand *why* the method works.
Check your work with `lake build NondimVerify.Exercises`.
-/

namespace NondimVerify

open Matrix

/-- **Exercise 1 (ranks over ℤ and ℚ agree).** The certificates compute ranks of integer
matrices; `Theory.lean` talks about rational ranks. This bridges the two.
Hint: `ℚ` is the fraction field of `ℤ`; a ℤ-linear dependency is a ℚ-linear one, and a
ℚ-linear dependency becomes a ℤ-linear one after clearing denominators. -/
theorem rank_map_intCast {m n : ℕ} (A : Matrix (Fin m) (Fin n) ℤ) :
    (A.map (Int.cast : ℤ → ℚ)).rank = A.rank := by
  sorry

/-- **Exercise 2 (normalizing parameters: the SAT half of the constraint criterion).**
If the columns of `A` indexed by `S` are independent, we can choose scale factors
`λ_j = exp (mu j)` that send every parameter in `S` to `1`, whatever their positive values `c`.
Hint: take logs; you need `Aₛᵀ mu = -log c`, solvable because `Aₛᵀ` is surjective when `Aₛ`
has full column rank. -/
theorem normalizable_of_rank {r n k : ℕ} (A : Matrix (Fin r) (Fin n) ℤ) (S : Fin k → Fin n)
    (hS : (A.submatrix id S).rank = k) (c : Fin n → ℝ) (hc : ∀ i, 0 < c i) :
    ∃ mu : Fin r → ℝ, ∀ i, c (S i) * Real.exp (∑ j, mu j * (A j (S i) : ℝ)) = 1 := by
  sorry

/-- **Exercise 3 (the UNSAT half).** Conversely, if scale factors exist that normalize the
parameters in `S` for *every* positive `c`, then the columns indexed by `S` are independent.
Hint: a dependency among the columns gives a monomial in the `c (S i)` that no scaling changes;
pick `c` where that monomial is not 1. -/
theorem rank_of_normalizable {r n k : ℕ} (A : Matrix (Fin r) (Fin n) ℤ) (S : Fin k → Fin n)
    (h : ∀ c : Fin n → ℝ, (∀ i, 0 < c i) →
      ∃ mu : Fin r → ℝ, ∀ i, c (S i) * Real.exp (∑ j, mu j * (A j (S i) : ℝ)) = 1) :
    (A.submatrix id S).rank = k := by
  sorry

/-- **Exercise 4 (Lotka–Volterra by hand).** Prove the textbook rescaling
`u = d x / a`, `v = b y / a`, `τ = a t`, `α = c / a` for the predator equation, in the style of
`SIR.lean`. -/
example (a b c d x y : ℝ) (ha : a ≠ 0) (hb : b ≠ 0) :
    (b / a) / a * (-c * y + d * x * y) = (b * y / a) * (d * x / a - c / a) := by
  sorry

end NondimVerify

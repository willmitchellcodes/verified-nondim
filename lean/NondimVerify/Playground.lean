import NondimVerify.Basic

/-!
# Playground

Not part of the build. Open this file in VS Code (with the Lean 4 extension) to experiment:
put your cursor after a `by` to see the goal, and hover over names for documentation.
-/

open NondimVerify

-- Mathlib can compute ranks of concrete integer matrices with a checked certificate.
example : Matrix.rank (R := ℤ) !![1, 0, -1; 0, 1, 1] = 2 := by eval_rank

-- Matrix identities with integer entries are decided by the kernel.
example : (!![1, 2; 3, 4] : Matrix (Fin 2) (Fin 2) ℤ) * !![1, 0; 0, 1] = !![1, 2; 3, 4] := by
  decide +kernel

-- The logistic rescaling u = N/K, tau = r t, done by hand.
example (r K N : ℝ) (hr : r ≠ 0) (hK : K ≠ 0) :
    (1 / K) / r * (r * N * (1 - N / K)) = (N / K) * (1 - N / K) := by
  rhs_check

-- More to try: `NondimVerify/Exercises.lean`.

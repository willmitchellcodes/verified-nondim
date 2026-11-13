import NondimVerify.Basic

/-! # Unit tests: the tactics the generated certificates rely on

Positive tests show each tactic proves true claims of the shapes we generate.
Refutation tests show the *negation* of a wrong claim is provable, so a wrong certificate
cannot slip through. (Rejection of whole corrupted certificates is tested from Python:
`python/tests/test_lean_build.py`.)
-/

open NondimVerify

/-! ## `rhs_check`: identities between rational expressions -/

example (a b : ℝ) : (a + b) ^ 2 = a ^ 2 + 2 * a * b + b ^ 2 := by rhs_check
example (a b : ℝ) (ha : a ≠ 0) (hb : b ≠ 0) : a / b * (b / a) = 1 := by rhs_check
example (a b : ℝ) (ha : 0 < a) (hb : 0 < b) : (1 / a) / b * (a * b) = 1 := by rhs_check
example (x k : ℝ) (hk : 0 < k) (hx : 0 < x) : x / (k + x) = (x / k) / (1 + x / k) := by
  have : k + x ≠ 0 := by positivity
  have : 1 + x / k ≠ 0 := by positivity
  rhs_check

-- The logistic rescaling u = N/K, τ = r t.
example (r K N : ℝ) (hr : 0 < r) (hK : 0 < K) :
    (1 / K) / r * (r * N * (1 - N / K)) = (N / K) * (1 - N / K) := by rhs_check

/-! ## `decide +kernel`: integer matrix identities, and their refutations -/

example : (!![1, 2; 3, 4] : Matrix (Fin 2) (Fin 2) ℤ) * !![1, 0; 0, 1] = !![1, 2; 3, 4] := by
  decide +kernel
example : (!![1, -1] : Matrix (Fin 1) (Fin 2) ℤ) * (!![1; 1] : Matrix (Fin 2) (Fin 1) ℤ) = 0 := by decide +kernel
example : (!![1, -1] : Matrix (Fin 1) (Fin 2) ℤ) * (!![1; 2] : Matrix (Fin 2) (Fin 1) ℤ) ≠ 0 := by decide +kernel
example : (!![2, 1; 1, 1] : Matrix (Fin 2) (Fin 2) ℤ) * !![1, -1; -1, 2] = 1 := by decide +kernel
example : (!![2, 0; 0, 1] : Matrix (Fin 2) (Fin 2) ℤ) * !![1, 0; 0, 1] ≠ 1 := by decide +kernel
example : (!![1, 2, 3; 4, 5, 6] : Matrix (Fin 2) (Fin 3) ℤ).submatrix id ![2, 0] = !![3, 1; 6, 4] := by
  decide +kernel

/-! ## `eval_rank`: ranks of integer matrices, and refutations of wrong ranks -/

example : Matrix.rank (R := ℤ) !![1, 0, -1; 0, 1, 1] = 2 := by eval_rank
example : Matrix.rank (R := ℤ) !![1, 2; 2, 4] = 1 := by eval_rank
example : Matrix.rank (R := ℤ) !![0, 0; 0, 0] = 0 := by eval_rank
example : Matrix.rank (R := ℤ) !![1; 0] = 1 := by eval_rank
example : Matrix.rank (R := ℤ) !![1, 2; 2, 4] ≠ 2 := by
  have h : Matrix.rank (R := ℤ) !![1, 2; 2, 4] = 1 := by eval_rank
  omega
example : ¬ (3 ≤ Matrix.rank (R := ℤ) !![1, 0, -1; 0, 1, 1]) := by
  have h : Matrix.rank (R := ℤ) !![1, 0, -1; 0, 1, 1] = 2 := by eval_rank
  omega

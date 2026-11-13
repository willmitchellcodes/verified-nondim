import NondimVerify.Theory
import NondimVerify.Cert

/-! # Integration tests: generated certificates + general theorems ⇒ concrete guarantees

The certificates prove facts about integer matrices. Here we plug those facts into the
general lemmas to get statements about the actual models.
-/

open NondimVerify Matrix

/-! ## SIR: `R₀ = β N / γ` is invariant under *every* scaling, for all scale factors

Variable order: t, S, I, R, beta, gamma, N. -/

example (lam : Fin 2 → ℝ) (h : ∀ j, lam j ≠ 0) (x : Fin 7 → ℝ) :
    monomial (scale Cert.SIR.Amat lam x) ![0, 0, 0, 0, 1, -1, 1] =
      monomial x ![0, 0, 0, 0, 1, -1, 1] :=
  monomial_scale _ lam h x _ (by decide +kernel)

-- The dimensionless time γ t likewise.
example (lam : Fin 2 → ℝ) (h : ∀ j, lam j ≠ 0) (x : Fin 7 → ℝ) :
    monomial (scale Cert.SIR.Amat lam x) ![1, 0, 0, 0, 0, 1, 0] =
      monomial x ![1, 0, 0, 0, 0, 1, 0] :=
  monomial_scale _ lam h x _ (by decide +kernel)

-- β N is not invariant (it has units 1/time), and neither is β alone.
example : Cert.SIR.Amat *ᵥ ![0, 0, 0, 0, 1, 0, 1] ≠ 0 := by decide +kernel
example : Cert.SIR.Amat *ᵥ ![0, 0, 0, 0, 1, 0, 0] ≠ 0 := by decide +kernel

/-! ## The certificates agree with the textbook counts -/

example : 7 - Cert.SIR.Kmat.rank = 2 := by rw [Cert.SIR.rank_K]
example : 3 - Cert.SIR.Apar.rank = 1 := by rw [Cert.SIR.rank_Apar]                      -- R₀
example : 2 - Cert.Logistic.Apar.rank = 0 := by rw [Cert.Logistic.rank_Apar]
example : 4 - Cert.LotkaVolterra.Apar.rank = 1 := by rw [Cert.LotkaVolterra.rank_Apar]  -- α = c/a
example : 5 - Cert.MichaelisMentenIC.Apar.rank = 3 := by rw [Cert.MichaelisMentenIC.rank_Apar]
example : 6 - Cert.RosenzweigMacArthur.Apar.rank = 3 := by rw [Cert.RosenzweigMacArthur.rank_Apar]
example : 2 - Cert.SpuriousFixed.Apar.rank = 1 := by rw [Cert.SpuriousFixed.rank_Apar]

/-! ## Every certificate found as many scalings as rank–nullity allows -/

example : Cert.SIR.Amat.rank = 7 - Cert.SIR.Kmat.rank := by
  rw [Cert.SIR.rank_A, Cert.SIR.rank_K]
example : Cert.LotkaVolterra.Amat.rank = 7 - Cert.LotkaVolterra.Kmat.rank := by
  rw [Cert.LotkaVolterra.rank_A, Cert.LotkaVolterra.rank_K]
example : Cert.RosenzweigMacArthur.Amat.rank = 9 - Cert.RosenzweigMacArthur.Kmat.rank := by
  rw [Cert.RosenzweigMacArthur.rank_A, Cert.RosenzweigMacArthur.rank_K]

/-! ## Constraint verdicts are usable as facts -/

example : ¬ (3 ≤ Cert.SIR.Acand2.rank) := by have := Cert.SIR.constraint2_unsat; omega
example : 2 ≤ Cert.SIR.Acand1.rank := Cert.SIR.constraint1_enough

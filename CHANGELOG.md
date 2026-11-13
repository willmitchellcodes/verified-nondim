# Changelog

## 0.1.0 — 2026-11-13

First release.

- **Solver** (`nondim`): scaling symmetries of an ODE model from its equations, every maximal
  nondimensionalization, symbolic and numeric checks.
- **Constraints**: "remove at least k", "at most m left", "keep these", "these named groups must
  appear"; each answered SAT or UNSAT with the reason.
- **Identifiability**: parameters that no measurement can separate, found from output-preserving
  scalings; a synthetic-data SIR experiment.
- **Lean 4 checker**: generated certificates for six models; general theorems (invariance of
  monomials, rank–nullity for scalings, maximality); solution correspondence for SIR.
- **Command line**: `nondim tour | list | show | reduce | constrain | identify | experiment | init-lean | certify | all`.
- **Tests**: Python unit tests, Lean unit tests, and bridge tests in which Lean must reject
  corrupted certificates.

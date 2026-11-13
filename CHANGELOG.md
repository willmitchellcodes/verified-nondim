# Changelog

## Unreleased

- **General theorems in Lean** (`docs/THEORY.md`): a model as data (`LaurentSystem`); a scaling
  symmetry maps solutions to solutions, both ways, for every polynomial system; parameters are
  constant; the constraint criterion as an equivalence (`normalizable_iff_rank`); the Buckingham
  Pi theorem in the form "unit-independent ⟹ function of the groups"; reduction to invariants.
- **Certify desr** (`docs/DESR.md`): `nondim desr <model>` and `nondim compare` run
  [desr](https://github.com/ofloveandhate/desr) and check it against this package's solver;
  `nondim certify` writes Lean certificates for desr's answers (`lean/NondimVerify/Certified/`).
  desr is optional and installed from source.
- **Certificates in the general form** for seven models: the reduced equations are proved for
  every positive solution of the original system, not only as an identity of right-hand sides.
- **Tests**: 675 (was 471), including 18 more corrupted certificates Lean must reject, a Lean
  file showing every hypothesis of the general theorems is needed, and a random-model
  comparison of desr with this package's solver.

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

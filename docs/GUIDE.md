# Guide: how verified-nondim is put together

**The question.** Can a computer nondimensionalize an ODE model *and* hand back machine-checked
guarantees: the new variables are unitless, no solutions are lost, no further parameter could
have been removed, and a requested constraint is either met or provably impossible?

**The example to keep in mind** (Ellner & Guckenheimer §6.2):

```
dS/dt = -β S I                 X = S/N, Y = I/N, τ = γt             dX/dτ = -R0 X Y
dI/dt =  β S I - γ I    ─────────────────────────────────────►      dY/dτ =  R0 X Y - Y
3 parameters: β, γ, N                                               1 parameter: R0 = βN/γ
```

## Start here

From a clone of the repository:

```bash
./setup.sh                      # once: Python env, Lean + Mathlib, runs every test
source .venv/bin/activate
nondim tour                     # 2-minute guided walk through the example above
```

Then read, in this order: `docs/BACKGROUND.md` (the math by hand) → `examples/` (four short
scripts) → `reports/sir.md` (what the tool says about SIR) → `docs/DECISIONS.md` (why
everything is built the way it is, with evidence and sources).

## The pipeline

```
 you write            Python: untrusted solver                         Lean: trusted checker
┌──────────┐   ┌─────────────────────────────────────────┐   ┌──────────────────────────────────┐
│ equations│ → │ 1 exponent matrix K      (model.py)     │   │ Cert/<Model>.lean  (generated)   │
│ params   │   │ 2 all scalings A, A·K=0  (scaling.py)   │ → │   A·K = 0, ranks, invertibility, │
│ unit     │   │ 3 choose S, reduce       (scaling.py)   │   │   reduced equations, constraints │
│ links    │   │ 4 constraints: SAT/UNSAT (constraints.py)│  │ Theory.lean  general theorems    │
└──────────┘   │ 5 what data can see  (identifiability.py)│  │ SIR.lean     solutions correspond│
               │ 6 write certificates     (lean_export.py)│  └──────────────────────────────────┘
               └─────────────────────────────────────────┘        `lake build` re-proves it all
```

If the Python code is wrong, `lake build` fails. You only have to trust the small Lean checks
and the inputs you typed.

## The three framings

| | Question | Where | One-line demo |
|---|---|---|---|
| **1. Certificate checking** | Is this reduction correct and minimal? | `scaling.py`, `lean_export.py`, `lean/NondimVerify/` | `nondim show sir` then `lake build` |
| **2. Constraints** | Can I remove ≥ k parameters, keep these, and get these named groups? | `constraints.py` | `nondim constrain sir -k 2 --keep beta` |
| **3. Identifiability** | Which parameters can data determine? | `identifiability.py`, `experiment_sir.py` | `nondim identify sir_reported` |

## Commands

Run with the virtual environment active (`python -m nondim …` works too).

| Command | What it does |
|---|---|
| `nondim tour` | guided walk-through on SIR |
| `nondim list` | table of all built-in models and their reductions |
| `nondim show <model>` | full report: scalings, every choice, checks, constraints |
| `nondim reduce <model> -n gamma N` | reduce, choosing which parameters become 1 |
| `nondim constrain <model> -k 2 --keep beta --want R0=beta*N/gamma` | SAT/UNSAT with reasons |
| `nondim identify <model> -o y=rho*I` | non-identifiable parameters from scalings |
| `nondim experiment` | SIR data-fitting experiment → `reports/identifiability_sir.md` |
| `nondim certify` | regenerate the Lean certificates |
| `nondim all` | everything: `reports/`, certificates, experiment |
| `cd python && python -m pytest -q` | all Python + bridge tests (Lean tests run if Lean is installed) |
| `cd lean && lake build` | Lean re-checks every certificate, proof and Lean unit test |

## What Lean checks for each model (`lean/NondimVerify/Cert/<Model>.lean`)

| Check | Lean statement | Meaning |
|---|---|---|
| 1 | `Amat * Kmat = 0` | every row of A is a symmetry of the equations |
| 2 | `Kmat.rank = …` | the scalings form a space of dimension n − rank K |
| 3 | `Amat.rank = r` | with 2: A contains **all** scalings (`Theory.maximal_of_rank`) |
| 4 | `Apar.rank = ρ` | at most ρ parameters can be removed: the minimum is p − ρ |
| 5 | `AS.rank = k` | the chosen parameters can be set to 1 together |
| 6 | `Amat * Vmat = 0` | every new variable is dimensionless |
| 7 | `Tmat.rank = n` | the change of variables is invertible |
| 8 | `rhs_<state>` | chain rule: the reduced equations are the old ones, rescaled |
| constraints | `constraintN_enough` / `_unsat`, `_want_invariant` / `_want_not_invariant`, `_regroup_*` | each verdict |

Beyond the certificates: `Theory.lean` proves rank–nullity for scalings and maximality in
general; `SIR.lean` proves that solutions and equilibria of SIR and its reduction correspond
in both directions, and the `R0·X > 1` threshold; `Exercises.lean` holds open problems for
you (not part of the build).

## Built-in models

| Model | Parameters → after | Why it's here |
|---|---|---|
| logistic | 2 → 0 | warm-up |
| sir (E&G Ch. 6) | 3 → 1 (R0) | the textbook example; three valid choices |
| sir_reported | — | identifiability: reporting fraction ρ cannot be separated from β |
| lotka_volterra | 4 → 1 | scalings beat Buckingham Pi |
| michaelis_menten(_ic) | 4 → 2, 5 → 3 | non-uniqueness; ε = e0/s0 must survive |
| rosenzweig_macarthur | 6 → 3 | rational right-hand side |
| spurious_* | 2 → 1 / **0** / 1 | failure mode: a forgotten unit link invents a symmetry |
| Arrhenius | rejected | out of scope: `exp(−E/RT)` |

**Add your own:** copy `examples/04_your_own_model.py`. To make it permanent, add a function
to `python/nondim/models.py` and an entry to `python/nondim/catalog.py`.

## Layout

```
README.md  pyproject.toml  LICENSE  CHANGELOG.md  setup.sh
assets/    logo.svg
docs/      GUIDE.md  BACKGROUND.md  DECISIONS.md  TESTING.md  READING.md  RELEASING.md
examples/  01_quickstart  02_constraints  03_identifiability  04_your_own_model
reports/   generated: SUMMARY.md, one report per model, identifiability_sir.md/.png
python/    nondim/ (the package)   tests/ (pytest)
lean/      NondimVerify/ (library)   NondimVerifyTest/ (Lean unit tests)
scripts/   publish_github.sh  publish_pypi.sh  set_repo_url.py
           workflows/  GitHub Actions templates: ci.yml, publish.yml, dependabot.yml
```

## Limits (details in `docs/BACKGROUND.md` §6 and `docs/DECISIONS.md` D15)

* Verified **relative to the equations and unit links you typed**. A wrong unit link gives a
  verified wrong answer (`spurious_*`).
* Correct is not the same as useful: the tool minimizes the parameter *count*; it does not
  know which small parameter matters.
* Only products, quotients and sums of powers. No `exp`, `log`, non-integer Hill exponents, °C.
* Scalings are not all symmetries, so the identifiability test is one-way.
* Proofs are about exact real numbers, not floating-point solvers.

## Troubleshooting

* `lake exe cache get` downloads prebuilt Mathlib (~5 GB). Without it Lean compiles Mathlib
  itself, which takes over an hour.
* `lake build` prints warnings that Mathlib "is designed for use with the module system".
  They are harmless.
* A failing `Cert/*.lean` means Python and Lean disagree, which is the system working.
  Compare the theorem with `nondim show <model>`.

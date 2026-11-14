# The ODEbase pilot

**Question.** The built-in models are textbook examples. What do scaling symmetries look like in
models people actually published?

**Data.** [ODEbase](https://odebase.org) (Lüders, Sturm, Radulescu; *Bioinformatics Advances*,
2022) offers BioModels systems preprocessed for symbolic computation. Its polynomial models are
available as text files in the OscarODEbase.jl repository (MIT licence). The pilot reads those
files. **No model data is stored in this repository**; the audit works on a local clone and
keeps only the statistics.

```bash
nondim audit --fetch              # clone the model files into ~/.cache/verified-nondim/ and run
nondim audit --data DIR           # or point at an existing copy of src/odes
nondim audit --certify 10         # also write Lean certificates for the 10 smallest models
```

The result is `reports/odebase_pilot.md`: a summary and one row per model.

## What the pilot found (run of 2026-11-13)

190 model files. 162 were read; 13 were larger than 30 kB and not attempted; 15 define a species
by a constraint instead of an equation and are reported as unreadable rather than guessed at.

| | |
|---|---|
| models with at least one scaling symmetry | 158 of 162 (98%) |
| parameters that occur in the equations or laws / removable by scaling | 2,970 / 553 (19%) |
| models with conservation laws | 84 |
| models where a scaling of the equations breaks a stated conservation law | 4 (2%) |
| small models also given to desr: agree / disagree | 25 / 0 |
| models with Lean certificates | 10 |
| parameters declared but never used | 443 |

How to read these:

* **Almost every model has scaling symmetries, and they remove about a fifth of the
  parameters.** That is the size of the reduction available before any modelling judgement.
* **443 declared parameters occur nowhere** in the equations or laws (compartment sizes that
  cancel, unused constants). They are dropped before the analysis. A tool that counted them
  would report reductions that mean nothing.
* **The four models with a broken law are one family** (BIOMD0000000226 and 259–261, NF-κB
  models by Radulescu et al.). Their conservation law has numeric coefficients such as 25 and 5.
  The model's parameter list names two compartments (`default`, `c2`) that divide the equations,
  so those numbers most likely encode a ratio of compartment sizes. A scaling of the equations
  that changes the compartment parameters does not preserve a law with the ratio written in as
  a number. This is an observation about how the law is written, not an error in the model. It
  is the situation `docs/THEORY.md` §7 describes: a tool that sees only the differential
  equations would use that scaling.
* **In the other 80 models with laws, respecting the laws removed no scaling.** That is
  expected: a conservation law that follows from the equations is preserved by their symmetries.
* **desr and this package's solver agreed on all 25 models given to both.** Only small models
  without conservation laws were given to desr, because the adapter does not pass laws to it.

## What "certified" means here

Ten of the smallest models have Lean certificates in `lean/NondimVerify/Certified/ODEbase/`
(for example `BIOMD0000000484.lean`). Each proves the same theorems as a built-in model:
symmetry read off the equations, the reduced equations for every positive solution, the
conservation laws respected, completeness of the invariants, the minimal parameter count. The
header of each file names the model and its source.

The other 148 models with symmetries are **not** certified. Their rows are what this package's
Python computed. Of them, 116 more fit the certificate format; the rest need fractional
powers, or have a scaling no parameter absorbs (see the `note` column).

## How the files are read

The model files are Julia source. They are never executed. `nondim/odebase.py` extracts the
species, parameters, equations and constraints with regular expressions and parses each
polynomial with a small arithmetic parser (`+ - * / ^`, parentheses, integers, declared names).
An unknown name or any other syntax is an error. `tests/test_odebase.py` feeds it code-like
strings to confirm they are refused.

Conservation laws become unit links: a relation is preserved by a scaling exactly when all
ratios of its terms are invariant (`IsHomogeneous.poly_scale_eq_zero_iff`).

## Limits of the pilot

1. **One solver.** Apart from the 25 models compared with desr, the numbers are this package's
   alone. The published tool for minimal parameter counts on reaction networks (Hawi &
   Wechselberger 2026) was not run.
2. **Polynomial models only**, and of those, the ones in the OscarODEbase repository (190; the
   ODEbase paper counts 199 polynomial models among 662). The rational ones were not available
   in this form.
3. **Thirteen large models were not attempted** and fifteen were not readable; they are listed
   at the end of the report with the reason.
4. **Lean at scale was not tried.** Certificates use `decide` and `simp` on explicit matrices,
   which is fine for ten variables and would be slow for sixty.
5. **A scaling symmetry is a statement about units, not about usefulness.** That 19% of the
   parameters can be removed does not say the reduced models are the ones their authors would
   choose.

## Why this is in the project

The literature search behind `docs/CONTRIBUTIONS.md` found no published scaling-symmetry or
nondimensionalization statistics over ODEbase. A pilot on 162 models is not that study, but it
shows the pipeline runs on real models, it produced one observation nobody planted (the NF-κB
family), and it is the natural first step if the project is taken further.

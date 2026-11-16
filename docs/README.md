# The documentation, and how to read it

> **In one line.** Which document answers which question, and what the example blocks mean.
>
> **Start with:** `GUIDE.md` if you want to use the tool, `BACKGROUND.md` if you want the mathematics first.

| Document | Read it to find out |
|---|---|
| [GUIDE.md](GUIDE.md) | how the tool is put together, what each command does, what Lean checks |
| [BACKGROUND.md](BACKGROUND.md) | the mathematics, worked by hand on SIR |
| [THEORY.md](THEORY.md) | the general theorems: statement, Lean name, proof idea, example, limits |
| [DESR.md](DESR.md) | how the reference tool's answers are certified, and what testing that found |
| [ODEBASE.md](ODEBASE.md) | what scaling symmetries look like in 162 published models |
| [TESTING.md](TESTING.md) | what is tested and what the tests cannot show |
| [CONTRIBUTIONS.md](CONTRIBUTIONS.md) | what the project adds, on one page, with the evidence |
| [DECISIONS.md](DECISIONS.md) | why each thing is built the way it is, with sources |
| [READING.md](READING.md) | what to read, in order |
| [RELEASING.md](RELEASING.md) | how to publish a new version |

`AGENTS.md` in the repository root is the briefing for AI coding agents and new contributors:
the rules, a map of the code, and how things are tested, documented and released.

The notebook `examples/walkthrough.ipynb` goes through four course models step by step, and
`examples/01_quickstart.py` to `05_certify_desr.py` are short scripts to run and change.

## How to read the examples

Every explanation comes with an example, and every example is checked by the test suite
(`python/tests/test_docs.py`), so what you read is what the code does today. Four kinds of
block appear:

**A command and its output.** The line after `$` is run; the lines under it are printed by the
tool. `...` marks output that was left out.

```console
$ nondim constrain sir -k 3
UNSAT: only 2 independent scaling direction(s) act on ['beta', 'gamma', 'N'], so at most 2 of them can be removed (asked for 3).
```

**Python, followed by what it prints.** The code is executed as shown.

```python
from nondim import models
from nondim.scaling import analyze

print(analyze(models.logistic()).n_scalings, "scaling symmetries")
```

```text
2 scaling symmetries
```

**Lean, quoted from the sources.** Every line occurs in a file under `lean/`, which Lean has
checked. This one says that the scalings used to reduce SIR are symmetries of its equations:

```lean
theorem symmetry : sys.IsSymmetry A tau := by decide +kernel
```

**Shell instructions for you.** Commands to type, with nothing after them on the line, so they
can be pasted into any shell.

```bash
pip install verified-nondim
nondim tour
```

## Words used the same way everywhere

| Term | Meaning |
|---|---|
| scaling symmetry | a change of units that leaves the equations unchanged |
| unit link | a statement that two quantities are measured in the same units, e.g. `S` and `N` |
| invariant, dimensionless group | a product of powers that no scaling changes; the new variables are invariants |
| this package's solver | the Python code here that computes a reduction (as opposed to desr) |
| matrix-level certificate | the first kind of Lean file (`lean/NondimVerify/Cert/`): facts about matrices, per model |
| general-form certificate | the second kind (`lean/NondimVerify/Certified/`): the general theorems applied to a model |
| goal query | a request such as "remove two parameters and keep `beta`", answered possible or impossible |
| one-way test | a test whose "yes" is proved and whose silence proves nothing (the identifiability test) |

## What the documentation does not include

`PROPOSAL_NOTES.md`, if you see it in your copy, is a private file that is not part of the
repository.

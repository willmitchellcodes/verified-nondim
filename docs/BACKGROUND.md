# Background: the math, worked by hand on SIR

The pipeline turns nondimensionalization into integer linear algebra. That is what makes it
automatable, and it is also what makes it checkable.

## 1. Units are scalings

Changing units multiplies each quantity by a constant. Measuring time in days instead of
weeks multiplies `t` by 7 and every rate by 1/7. A model "makes physical sense" if
changing units maps solutions to solutions. So the question becomes: **which simultaneous
rescalings leave the equations unchanged?**

A scaling is an integer vector `a`. Each quantity `x_i` is replaced by `λ^{a_i} x_i`. The
system `dz_i/dt = f_i` is unchanged exactly when every quantity `t·f_i/z_i` is unchanged
(Tanburn et al. Lemma 3.1). For a sum of monomials that means **each monomial is unchanged**.
A monomial with exponent vector `k` picks up the factor `λ^{a·k}`, so the condition is
`a · k = 0` for every monomial. (Lean: `NondimVerify.monomial_scale`.)

## 2. SIR by hand

Quantities `(t, S, I, β, γ, N)`; equations `dS/dt = −βSI`, `dI/dt = βSI − γI`; and `S, I`
are measured in the same units as `N`, so `S/N` and `I/N` must be invariant.

| source | monomial | exponent vector k over (t, S, I, β, γ, N) |
|---|---|---|
| t·f_S/S = −βtI | βtI | (1, 0, 1, 1, 0, 0) |
| t·f_I/I = βtS − γt | βtS | (1, 1, 0, 1, 0, 0) |
|  | γt | (1, 0, 0, 0, 1, 0) |
| unit link | S/N | (0, 1, 0, 0, 0, −1) |
| unit link | I/N | (0, 0, 1, 0, 0, −1) |

Stack these as the columns of the **exponent matrix K** (6 × 5). A scaling is a row
vector `a` with `a K = 0`:

```
a_t + a_I + a_β = 0,   a_t + a_S + a_β = 0,   a_t + a_γ = 0,   a_S = a_N,   a_I = a_N
```

`rank K = 4`, so by **rank–nullity** the solutions form a space of dimension `6 − 4 = 2`.
A basis, written as the rows of the **scaling matrix A**:

| | t | S | I | β | γ | N | meaning |
|---|---|---|---|---|---|---|---|
| row 1 | 1 | 0 | 0 | −1 | −1 | 0 | change time units |
| row 2 | 0 | 1 | 1 | −1 | 0 | 1 | change population units |

The algorithm rediscovered the two physical units from the equations alone. The Python code
finds an integer basis with a unimodular row reduction (`intlinalg.int_row_echelon`, a
Hermite-normal-form computation; Hubert & Labahn 2013).

## 3. How many parameters can go?

Look only at A's parameter columns: β = (−1, −1), γ = (−1, 0), N = (0, 1). Their rank is
**ρ = 2**. Each independent scaling direction can push one parameter to 1, and no more. So

> **#parameters after = #parameters before − ρ = 3 − 2 = 1.**

No scaling can do better, provided A really contains *all* scalings. That holds because the
rows of A are independent and there are `n − rank K` of them (certificate Checks 2–3,
combined by `maximal_of_rank` in `lean/NondimVerify/Theory.lean`).

## 4. Which ones? (non-uniqueness)

Any set S of ρ parameters whose columns of A are independent can be normalized. For SIR every
pair works, giving three valid answers:

| normalize | surviving parameter |
|---|---|
| β, γ | N̂ = βN/γ (R₀ hides in the initial condition) |
| β, N | γ̂ = γ/(βN) = 1/R₀ |
| **γ, N** | **β̂ = βN/γ = R₀** (the textbook form) |

Take the textbook choice. Pick the time factor so that γ → 1 and the population factor so
that N → 1. Then `t̂ = γt`, `Ŝ = S/N`, `Î = I/N`, `β̂ = βN/γ`. Because the equations are
invariant, the reduced system is just the old one with γ = N = 1 and β = R₀:

```
dŜ/dt̂ = −R₀ Ŝ Î,        dÎ/dt̂ = R₀ Ŝ Î − Î.
```

In general, each kept quantity `x` becomes `x̂ = x · ∏_{s∈S} s^{e_s}`, where `e` solves
`A_S e = −A_x` (`scaling.nondimensionalize`).

Sometimes a pair fails. In Michaelis–Menten with initial substrate s₀, the columns for e₀ and
s₀ are dependent (both are concentrations), so you can never set both to 1. Their ratio
ε = e₀/s₀ always survives. That is exactly the small parameter of the quasi-steady-state
approximation.

## 5. Constraints and certificates

> "Eliminate at least k parameters while keeping the set P" is satisfiable **iff**
> rank(A restricted to parameters not in P) ≥ k.

This is a matroid rank question, so a greedy choice is optimal and no SAT/ILP solver is
needed. (This criterion is our synthesis of Hubert–Labahn and Tanburn et al. Stating
precisely what "keep" means and proving the criterion is a contribution of the project.)

* **SAT certificate:** a set S with `rank(A_S) = k` (Lean: `constraintN_sat`).
* **UNSAT certificate:** `rank(A_candidates) < k` (Lean: `constraintN_unsat`).
  SIR examples: "remove 3" is impossible (only 2 scalings exist). "Remove 2 but keep γ and N"
  is impossible (β's column alone has rank 1).

"Keep p" here means p is not normalized. It may still be absorbed into a group: in
Lotka–Volterra the surviving parameter is c/a, not c.

**Named groups.** You can also demand that specific expressions appear as parameters, e.g.
`want={"R0": "beta*N/gamma"}`. That is possible iff each wanted group is a product of powers
of parameters, is dimensionless (`A·w = 0`), and the groups are independent (after Tanburn
et al. Thm 3.8). Failing any of these gives an UNSAT with the reason: `beta*N` has units of
1/time; `e0/(s0 + Km)` is not a product of powers. Try `python examples/02_constraints.py`.

## 6. What the proofs guarantee, and what they cannot

**Guaranteed (relative to the equations and unit links you entered):** the new variables are
dimensionless; the substitution is invertible; the reduced right-hand sides equal the old ones
by the chain rule; for SIR, solutions and equilibria correspond in both directions; the
parameter count is minimal *among scalings*; and constraint verdicts are correct.

**Not guaranteed — the failure modes to study:**

1. **Garbage in, verified garbage out.** Drop a unit link and you get a fake extra symmetry.
   `spurious_substituted` claims 2 → 0 parameters; restoring the link (`spurious_fixed`)
   gives the correct 2 → 1. Lean happily verifies both.
2. **Correct ≠ useful.** Every choice in §4 is correct, but only some are interpretable, and
   only some expose the right small parameter for asymptotics. Segel & Slemrod's
   ε = e₀/(s₀ + K_m) isn't even a monomial.
3. **Scalings aren't all symmetries.** Translations and other Lie symmetries can allow further
   reduction; scaling-only reasoning about identifiability can mislead (Villaverde & Massonis 2021).
4. **Function class.** `exp`, `log`, non-integer Hill exponents and °C fall outside the
   monomial framework (the Arrhenius model is rejected).
5. **Real numbers vs. floating point.** Lean proves facts about exact ℝ-valued solutions;
   `simulate.py` shows numeric agreement to ~1e-9 or better, which is evidence, not proof.
6. **Trusted computing base.** The exporter that writes the Lean statements is trusted. Keep it
   small and read the generated statements.

## 7. Buckingham Pi vs. scaling symmetries

Buckingham Pi uses only the physical units you declare. For Lotka–Volterra with units
{time, individuals} it finds 7 − 2 = 5 groups. The equations actually admit 3 scalings,
because prey and predator counts can be rescaled independently, so there are only 4
invariants and the model reduces 4 → 1 rather than 4 → 2. `run_all.py` prints both.

## 8. The link to data (identifiability)

If a scaling moves parameters but leaves the observed output unchanged, those parameters
cannot be estimated separately from data; only the invariant groups can. Fitting β, γ, N
separately to epidemic data gives a ridge in the likelihood along the scaling direction,
while R₀ is well-determined. This is a natural "robustness with data" experiment, in the
spirit of the course project suggestions.

The tool makes this concrete. Observe only reported cases `y = ρI` with unknown reporting
fraction ρ. The scaling `S, I → S/λ, I/λ; β, ρ → λβ, λρ` changes nothing you can measure, so
β and ρ are not identifiable; γ, R0 = βS(0)/γ, ρI(0) and β/ρ are. `python -m nondim experiment`
fits synthetic data and shows equally good fits whose β differ twentyfold while R0 agrees to
four digits (`reports/identifiability_sir.md`). The test is one-way: a parameter that no
scaling moves may still be non-identifiable for other reasons.

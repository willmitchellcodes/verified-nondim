"""A guided tour of the whole pipeline on the SIR model.  Run: nondim tour"""

from .constraints import solve
from .identifiability import analyze_identifiability
from .model import Model
from .scaling import all_nondimensionalizations, analyze, nondimensionalize, verify_symbolically
from .simulate import compare_trajectories


def tour():
    step = lambda n, s: print(f"\n--- Step {n}: {s} " + "-" * max(0, 60 - len(s)))  # noqa: E731

    step(1, "write the model down")
    sir = Model.from_strings(
        "SIR",
        equations={"S": "-beta*S*I", "I": "beta*S*I - gamma*I"},
        params="beta gamma N",
        same_units=[("S", "N"), ("I", "N")],  # S and I are counted in the same units as N
    )
    print(sir)

    step(2, "ask which rescalings (changes of units) the equations allow")
    an = analyze(sir)
    for line in an.describe_scalings():
        print("  " + line)
    print(f"  => {an.n_scalings} scalings; they can remove {an.param_rank} of the "
          f"{len(sir.params)} parameters, and no scaling can remove more.")

    step(3, "see every way of doing it (the answer is not unique)")
    for nd in all_nondimensionalizations(sir, analysis=an):
        left = [f"{nd.new_expr[p]}" for p in sir.params if p not in nd.normalized]
        print(f"  set {', '.join(map(str, nd.normalized))} to 1  ->  remaining parameter: {left[0]}")

    step(4, "pick the textbook one: gamma and N become 1, leaving R0")
    nd = nondimensionalize(sir, [sir.symbol("gamma"), sir.symbol("N")], analysis=an)
    print(nd.summary())

    step(5, "check it (before Lean re-checks it properly)")
    print("  chain rule, symbolically:", "pass" if all(r == 0 for r in verify_symbolically(nd)) else "FAIL")
    print(f"  simulate both systems:    max relative difference {compare_trajectories(nd):.1e}")

    step(6, "ask for constraints, and get a yes or a provable no")
    print("  remove 2, keep beta        ->", solve(sir, 2, keep=["beta"]))
    print("  remove 3                   ->", solve(sir, 3))
    print("  want R0 = beta*N/gamma     ->", solve(sir, want={"R0": "beta*N/gamma"}))
    print("  want beta*N as a parameter ->", solve(sir, want={"x": "beta*N"}))

    step(7, "what could data tell us? observe only y = rho*I")
    rep = Model.from_strings("SIR_reported", {"S": "-beta*S*I", "I": "beta*S*I - gamma*I"},
                             "beta gamma rho", outputs={"y": "rho*I"})
    print(analyze_identifiability(rep).summary())

    print("\nNext: `nondim init-lean proofs` creates the Lean project that re-proves every claim above:")
    print("      cd proofs && lake exe cache get && lake build")

"""Human-readable reports: one function per pipeline stage, in pipeline order.

    1. analyze        which scalings do the equations allow?
    2. choices        every maximal nondimensionalization (non-uniqueness)
    3. reduce         the chosen one, with symbolic + numeric checks
    4. constraints    SAT / UNSAT verdicts (Framing 2)
    5. identifiability  what the data can see (Framing 3), if the model has outputs
"""

from __future__ import annotations

import sympy as sp

from . import models
from .buckingham import pi_count, pi_groups
from .catalog import CATALOG
from .constraints import solve
from .identifiability import analyze_identifiability
from .scaling import all_nondimensionalizations, analyze, nondimensionalize, verify_symbolically
from .simulate import compare_trajectories


def build(key: str, normalize=None):
    """Run the whole pipeline for a catalog model. Returns (model, analysis, nd, constraint results)."""
    model = models.ALL[key]()
    cfg = CATALOG.get(key, {})
    an = analyze(model)
    norm = normalize if normalize is not None else cfg.get("normalize")
    nd = nondimensionalize(model, [model.symbol(x) for x in norm] if norm else None, analysis=an)
    results = [solve(model, analysis=an, **c) for c in cfg.get("constraints", [])]
    return model, an, nd, results


def model_report(key: str, normalize=None) -> str:
    model, an, nd, results = build(key, normalize)
    cfg = CATALOG.get(key, {})
    V = model.variables
    L = [f"# {model.name}", ""]
    if model.notes:
        L += [model.notes, ""]
    L += ["## The model", "", "```"]
    L += [f"d{z}/d{model.t} = {f}" for z, f in zip(model.states, model.rhs)]
    L += [f"parameters: {', '.join(map(str, model.params))}"]
    if model.extra_invariants:
        L += [f"unit links (must stay invariant): {', '.join(map(str, model.extra_invariants))}"]
    L += ["```", "", "## 1. Scaling symmetries", "",
          f"The exponent matrix K is {an.K.shape[0]}×{an.K.shape[1]} with rank {an.rank_K}, so there are "
          f"{len(V)} − {an.rank_K} = **{an.n_scalings} independent scalings** (rank–nullity):", ""]
    L += ["| # | " + " | ".join(map(str, V)) + " |", "|---|" + "---|" * len(V)]
    for i in range(an.A.shape[0]):
        L.append(f"| {i + 1} | " + " | ".join(str(an.A[i, j]) for j in range(len(V))) + " |")
    L += ["", f"(Row i says: multiply each variable by λ^entry.) On the parameter columns these rows have rank "
          f"**{an.param_rank}**, so the model reduces from **{len(model.params)} to {an.min_params} parameter(s)**, "
          "and no scaling can do better.", ""]
    if "dims" in cfg:
        dims = {model.symbol(k): v for k, v in cfg["dims"].items()}
        L += [f"Buckingham Pi from the declared physical units alone gives {pi_count(dims)} dimensionless groups "
              f"(`{', '.join(map(str, pi_groups(dims)))}`); the scaling analysis gives "
              f"{len(V) - an.n_scalings} invariants.", ""]

    L += ["## 2. Every maximal choice (non-uniqueness)", "", "| normalize to 1 | surviving parameters |", "|---|---|"]
    for alt in all_nondimensionalizations(model, analysis=an):
        kept = ", ".join(f"{alt.new_symbol[p]} = {alt.new_expr[p]}" for p in model.params if p not in alt.normalized)
        L.append(f"| {', '.join(map(str, alt.normalized)) or '—'} | {kept or '(none)'} |")

    res = verify_symbolically(nd)
    err = compare_trajectories(nd)
    L += ["", "## 3. The reduction used", "", "```"]
    L += [f"{nd.new_symbol[x]} = {nd.new_expr[x]}" for x in V if x not in nd.normalized]
    L += [""] + [f"d{nd.new_symbol[z]}/d{nd.new_symbol[model.t]} = {g}" for z, g in zip(model.states, nd.reduced_rhs)]
    L += ["```", "",
          f"* chain-rule check (SymPy): {'pass' if all(r == 0 for r in res) else 'FAIL ' + str(res)}",
          f"* numeric check, original vs. reduced trajectories: max relative error {err:.1e}",
          f"* every new variable dimensionless: {nd.fully_invariant()}", ""]

    if results:
        L += ["## 4. Constraints", "", "| request | verdict | why / how |", "|---|---|---|"]
        for c, r in zip(cfg["constraints"], results):
            req = ", ".join(f"{k}={v}" for k, v in c.items())
            L.append(f"| `{req}` | **{'SAT' if r.satisfiable else 'UNSAT'}** | {r.explanation} |")
        L.append("")
        for r in results:
            if r.regrouping:
                L += ["Regrouped with " + ", ".join(r.want) + ":", "", "```"]
                L += [f"{g} = {e}" for g, e, _ in r.regrouping.groups]
                L += [f"d{nd.new_symbol[z]}/d{nd.new_symbol[model.t]} = {g}"
                      for z, g in zip(model.states, r.regrouping.reduced_rhs)]
                if r.regrouping.reduced_extra_invariants:
                    L += ["unit links become: " + ", ".join(map(str, r.regrouping.reduced_extra_invariants))]
                L += ["```", ""]

    if model.outputs:
        L += ["## 5. Identifiability from the measured outputs", "", "```",
              analyze_identifiability(model).summary(), "```", ""]
    return "\n".join(L)


def summary_table() -> str:
    L = ["| model | parameters | after | scalings | normalize | reduced parameters |", "|---|---|---|---|---|---|"]
    for key in models.ALL:
        model, an, nd, _ = build(key)
        kept = ", ".join(f"{nd.new_expr[p]}" for p in model.params if p not in nd.normalized)
        L.append(f"| {key} | {len(model.params)} | {an.min_params} | {an.n_scalings} | "
                 f"{', '.join(map(str, nd.normalized)) or '—'} | {kept or '(none)'} |")
    return "\n".join(L)

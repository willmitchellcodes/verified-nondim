"""Optional sections of a general-form Lean certificate.

Each function returns Lean source lines for one question a modeller asks after the reduction:

    links_section            are the scalings consistent with the declared unit links?
    count_section            what is the smallest number of parameters any scaling can leave?
    identifiability_section  which parameters can the measured outputs not tell apart?
    goals_section            can a requested reduction be had, and if not, why not?

All of them state facts about the scaling matrix `A` and the model data `sys` that are already
in the certificate, and every "yes" and every "no" is a theorem Lean has to prove.
"""

from __future__ import annotations

import sympy as sp

from .constraints import solve
from .hlform import HLReduction, NotSupported, left_inverse_certificate
from .identifiability import analyze_identifiability
from .intlinalg import rank, right_kernel_basis
from .lean_export import lean_matrix, lean_name, to_lean
from .model import OutOfScopeError, monomial_exponents

UNFOLD = "poly, Term.eval, monomial, Fin.prod_univ_succ"
FINISH = "try (first | ring1 | (field_simp; ring1) | field_simp)"


def _vec(xs) -> str:
    return "![" + ", ".join(str(int(x)) for x in xs) + "]"


def _coeff(c) -> str:
    c = sp.Rational(c)
    if c.q == 1:
        return f"({c.p})" if c.p < 0 else str(c.p)
    return f"({c.p} / {c.q})"


def _mat(name: str, M: sp.Matrix, doc: str, ring: str = "ℤ") -> list[str]:
    r, c = M.shape
    return [f"/-- {doc} -/", f"def {name} : Matrix (Fin {r}) (Fin {c}) {ring} :=\n  {lean_matrix(M)}", ""]


def poly_terms(expr: sp.Expr, variables: list[sp.Symbol]) -> list[tuple[sp.Rational, list[int]]]:
    """`expr` as a list of (coefficient, integer exponent vector) terms, or NotSupported."""
    terms = []
    for term in sp.Add.make_args(sp.expand(expr)):
        if term == 0:
            continue
        coeff, _ = term.as_coeff_Mul()
        try:
            exps = monomial_exponents(term, variables)
        except OutOfScopeError as e:
            raise NotSupported(f"{term} is not a monomial in the model's variables ({e})") from e
        if any(not sp.Rational(x).is_Integer for x in exps):
            raise NotSupported(f"fractional exponent in {term}")
        terms.append((sp.Rational(coeff), [int(x) for x in exps]))
    return terms


def _term_list(terms) -> str:
    return "[" + ", ".join(f"⟨{_coeff(c)}, {_vec(e)}⟩" for c, e in terms) + "]"


def _exponents(red: HLReduction, expr: sp.Expr) -> list[int]:
    """Exponent vector of a monomial over red.variables (time must not occur)."""
    full = monomial_exponents(expr, red.model.variables)
    if full[red.model.index(red.model.t)] != 0:
        raise NotSupported(f"{expr} involves time")
    return [int(full[red.model.index(v)]) for v in red.variables]


# ----------------------------------------------------------------- unit links

def links_section(red: HLReduction) -> list[str]:
    if not red.links:
        return []
    L = sp.Matrix(red.links).T
    return [
        "/-! ## Unit links",
        "",
        "The model declares that some quantities are measured in the same units, for example because",
        "a conservation law or an initial condition adds them. Each link is a ratio that every scaling",
        "used by the reduction must leave unchanged: " + ", ".join(map(str, red.link_exprs)) + ".",
        "-/",
        "",
        *_mat("Links", L, "Exponent vectors of the linked ratios (one per column)."),
        "/-- Every scaling treats both members of every link alike, so no scaling in this reduction",
        "changes one side of a sum such as `S + I + R = N` without the other. -/",
        "theorem links_respected : A * Links = 0 := by decide +kernel",
        "",
    ]


# ----------------------------------------------------------------- minimal parameter count

def count_section(red: HLReduction) -> list[str]:
    params = red.parameters
    p, r, n = len(params), red.r, red.n
    if p == 0 or r == 0:
        return []
    cols = [red.variables.index(q) for q in params]
    AP = red.A[:, cols]
    rho = rank(AP)
    return [
        "/-! ## The smallest possible number of parameters",
        "",
        f"The scalings act on the {p} parameters with rank {rho}. So {rho} parameters can be scaled to 1",
        f"(the reduction above does it) and no {rho + 1} can: at least {p - rho} parameter(s) remain,",
        "whatever nondimensionalization by scaling is chosen.",
        "-/",
        "",
        f"/-- Positions of the parameters: {', '.join(map(str, params))}. -/",
        f"def P : Fin {p} → Fin {n} := {_vec(cols)}",
        "",
        *_mat("ParamCols", AP, "The parameter columns of `A`.", "ℚ"),
        f"theorem paramCols_eq : (A.submatrix id P).map (Int.castRingHom ℚ) = ParamCols := by\n"
        f"  decide +kernel",
        "",
        f"theorem rank_paramCols : ParamCols.rank = {rho} := by unfold ParamCols; eval_rank",
        "",
        f"/-- **No {rho + 1} distinct parameters can all be scaled to 1** (for every positive choice of",
        "their values). Together with the reduction above this fixes the minimal parameter count. -/",
        f"theorem cannot_remove_more (S : Fin {rho + 1} → Fin {p}) (hS : Function.Injective S) :\n"
        f"    ¬ ∀ c : Fin {n} → ℝ, (∀ i, 0 < c i) →\n"
        f"        ∃ lam : Fin {r} → ℝ, (∀ j, 0 < lam j) ∧ ∀ i, scale A lam c (P (S i)) = 1 :=\n"
        f"  not_normalizable_of_rank_lt A P S (Function.Injective.comp (by decide) hS)\n"
        f"    (by rw [paramCols_eq, rank_paramCols]; omega)",
        "",
    ]


# ----------------------------------------------------------------- identifiability

def identifiability_section(red: HLReduction) -> list[str]:
    m = red.model
    if not m.outputs:
        return []
    V, n = red.variables, red.n
    try:
        outs = {name: poly_terms(h, V) for name, h in m.outputs.items()}
    except NotSupported:
        return []
    res = analyze_identifiability(m)
    B = sp.Matrix([[res.B[i, m.index(v)] for v in V] for i in range(res.B.shape[0])]) if res.B.shape[0] else None
    args = " ".join(lean_name(v) for v in V)
    point = "![" + ", ".join(lean_name(v) for v in V) + "]"
    out = [
        "/-! ## What the measured outputs cannot tell apart",
        "",
        "Measured: " + ", ".join(f"{k} = {h}" for k, h in m.outputs.items()) + ".",
        "A scaling that is a symmetry, does not rescale time and leaves every output unchanged produces",
        "a second solution with exactly the same data. Every parameter such a scaling moves is therefore",
        "not identifiable from these outputs. This is a one-way test: a parameter that is not listed",
        "below may still be non-identifiable for a reason that is not a scaling.",
        "-/",
        "",
    ]
    for name, terms in outs.items():
        on = lean_name(sp.Symbol(name))
        out += [
            f"/-- The output `{name} = {m.outputs[name]}` as data. -/",
            f"noncomputable def out_{on} : List (Term {n}) := {_term_list(terms)}",
            "",
            f"theorem out_{on}_eq ({args} : ℝ) : poly out_{on} {point} = {to_lean(m.outputs[name])} := by\n"
            f"  simp [{UNFOLD}, out_{on}]\n  {FINISH}",
            "",
        ]
    out += [
        "/-- All measured outputs. -/",
        f"noncomputable def outputs : List (List (Term {n})) := ["
        + ", ".join(f"out_{lean_name(sp.Symbol(k))}" for k in outs) + "]",
        "",
    ]
    if B is None:
        out += ["-- No scaling symmetry leaves time and all outputs unchanged: this test flags nothing.", ""]
        return out
    b = B.shape[0]
    out += _mat("B", B, "Scalings that leave time and every measured output unchanged (one per row).")
    out += [
        "/-- They are symmetries of the model that do not rescale time. -/",
        "theorem output_scalings_are_symmetries : sys.IsSymmetry B 0 := by decide +kernel",
        "",
        "/-- They leave every measured output unchanged. -/",
        "theorem outputs_unchanged : OutputInvariant B outputs := by decide +kernel",
        "",
    ]
    for v in [*res.nonidentifiable, *res.hidden_scale_states]:
        i = V.index(v)
        j = next(j for j in range(b) if B[j, i] != 0)
        what = "parameter" if v in res.nonidentifiable else "overall scale of the state"
        out += [
            f"/-- **The {what} `{v}` cannot be determined from the outputs.** Every solution with",
            f"`{v} ≠ 0` has a twin: a solution with the same outputs at all times and a different `{v}`. -/",
            f"theorem not_identifiable_{lean_name(v)} {{x : ℝ → Fin {n} → ℝ}} (hx : sys.IsSolution x)\n"
            f"    (h0 : x 0 {i} ≠ 0) :\n"
            f"    ∃ x' : ℝ → Fin {n} → ℝ, sys.IsSolution x' ∧\n"
            f"      (∀ t, ∀ o ∈ outputs, poly o (x' t) = poly o (x t)) ∧ x' 0 {i} ≠ x 0 {i} ∧\n"
            f"      ∀ t k, 0 < x t k → 0 < x' t k :=\n"
            f"  output_scalings_are_symmetries.not_identifiable outputs_unchanged {i} {j} (by decide) hx h0",
            "",
        ]
    if res.identifiable_groups:
        out += ["-- Parameter groups these scalings leave unchanged (candidates for what the data can see): "
                + ", ".join(map(str, res.identifiable_groups)), ""]
    return out


# ----------------------------------------------------------------- goal queries

def _describe(c: dict) -> str:
    parts = []
    if c.get("eliminate_at_least"):
        parts.append(f"remove at least {c['eliminate_at_least']} parameter(s)")
    if c.get("at_most_params") is not None:
        parts.append(f"leave at most {c['at_most_params']} parameter(s)")
    if c.get("keep"):
        parts.append("keep " + ", ".join(map(str, c["keep"])))
    if c.get("want"):
        parts.append("have the groups " + ", ".join(f"{k} = {v}" for k, v in c["want"].items()))
    return "; ".join(parts) or "no requirement"


def goals_section(red: HLReduction, goals: list[dict]) -> list[str]:
    if not goals or red.r == 0:
        return []
    m, V, n, r = red.model, red.variables, red.n, red.r
    out = [
        "/-! ## Goal queries",
        "",
        "Requests a modeller might make of the reduction, each answered with a proof.",
        "\"Possible\" comes with scale factors that do it; \"impossible\" comes with the reason.",
        "-/",
        "",
    ]
    for idx, c in enumerate(goals, 1):
        res = solve(m, **c)
        g = f"goal{idx}"
        out += [f"-- Goal {idx}: {_describe(c)}.", f"-- Answer: {res}", ""]
        vecs = {}
        if res.want_vectors is not None:
            for col, name in enumerate(res.want):
                full = list(res.want_vectors[:, col])
                vecs[name] = [int(full[m.index(v)]) for v in V]
        if res.satisfiable:
            S = [V.index(s) for s in res.witness.normalized]
            k = len(S)
            if k:
                G, d = left_inverse_certificate(red.A[:, S])
                out += [
                    f"/-- Parameters to scale to 1: {', '.join(map(str, res.witness.normalized))}. -/",
                    f"def {g}_S : Fin {k} → Fin {n} := {_vec(S)}",
                    "",
                    *_mat(f"{g}_G", G, f"Left inverse of the selected columns of `A`, up to the factor {d}."),
                    f"/-- **Goal {idx} is possible:** whatever positive values the parameters have, some change",
                    "of units makes the selected ones equal to 1. -/",
                    f"theorem {g}_possible (c : Fin {n} → ℝ) (hc : ∀ i, 0 < c i) :\n"
                    f"    ∃ lam : Fin {r} → ℝ, (∀ j, 0 < lam j) ∧ ∀ i, scale A lam c ({g}_S i) = 1 :=\n"
                    f"  exists_normalizing_scaling A {g}_S {g}_G ({d}) (by decide) (by decide +kernel) c\n"
                    f"    (fun i => hc _)",
                    "",
                ]
            for name, v in vecs.items():
                out += [
                    f"/-- The requested group `{name} = {res.want[name]}` is dimensionless. -/",
                    f"theorem {g}_{lean_name(sp.Symbol(name))}_dimensionless : A *ᵥ {_vec(v)} = 0 := by decide +kernel",
                    "",
                ]
        elif res.reason == "rank":
            cols = [V.index(q) for q in res.candidates]
            pc, k = len(cols), res.eliminate_at_least
            if pc == 0:
                out += ["-- (No parameter is left to remove, so nothing needs proving.)", ""]
                continue
            AP = red.A[:, cols]
            out += [
                f"/-- Parameters that may be removed: {', '.join(map(str, res.candidates))}. -/",
                f"def {g}_P : Fin {pc} → Fin {n} := {_vec(cols)}",
                "",
                *_mat(f"{g}_cols", AP, "Their columns of `A`.", "ℚ"),
                f"theorem {g}_cols_eq : (A.submatrix id {g}_P).map (Int.castRingHom ℚ) = {g}_cols := by\n"
                f"  decide +kernel",
                "",
                f"theorem {g}_rank : {g}_cols.rank = {res.available_rank} := by unfold {g}_cols; eval_rank",
                "",
                f"/-- **Goal {idx} is impossible:** the scalings act on these parameters with rank",
                f"{res.available_rank}, so no {k} of them can all be scaled to 1. -/",
                f"theorem {g}_impossible (S : Fin {k} → Fin {pc}) (hS : Function.Injective S) :\n"
                f"    ¬ ∀ c : Fin {n} → ℝ, (∀ i, 0 < c i) →\n"
                f"        ∃ lam : Fin {r} → ℝ, (∀ j, 0 < lam j) ∧ ∀ i, scale A lam c ({g}_P (S i)) = 1 :=\n"
                f"  not_normalizable_of_rank_lt A {g}_P S (Function.Injective.comp (by decide) hS)\n"
                f"    (by rw [{g}_cols_eq, {g}_rank]; omega)",
                "",
            ]
        elif res.reason == "not_invariant":
            name, v = next((nm, v) for nm, v in vecs.items() if any(x != 0 for x in red.A * sp.Matrix(v)))
            j = next(j for j in range(r) if (red.A * sp.Matrix(v))[j] != 0)
            out += [
                f"/-- **Goal {idx} is impossible:** `{name} = {res.want[name]}` has units. One change of units",
                "changes its value at every positive point, so it cannot be a parameter of a",
                "dimensionless model. -/",
                f"theorem {g}_impossible :\n"
                f"    ∃ lam : Fin {r} → ℝ, (∀ j, 0 < lam j) ∧ ∀ x : Fin {n} → ℝ, (∀ i, 0 < x i) →\n"
                f"      monomial (scale A lam x) {_vec(v)} ≠ monomial x {_vec(v)} :=\n"
                f"  monomial_not_invariant A {_vec(v)} {j} (by decide +kernel)",
                "",
            ]
        elif res.reason == "dependent" and vecs:
            W = sp.Matrix(list(vecs.values())).T
            ker = right_kernel_basis(W)
            if ker.shape[1] == 0:
                out += ["-- (More independent groups were requested than exist; see the count above.)", ""]
                continue
            cvec = [int(x) for x in ker[:, 0]]
            q = W.shape[1]
            out += [
                *_mat(f"{g}_W", W, "Exponent vectors of the requested groups (one per column)."),
                f"/-- **Goal {idx} is impossible:** the requested groups are not independent. The product of",
                f"their powers with exponents `{cvec}` is identically 1. -/",
                f"theorem {g}_impossible : {g}_W *ᵥ {_vec(cvec)} = 0 ∧ ({_vec(cvec)} : Fin {q} → ℤ) ≠ 0 := by\n"
                f"  decide +kernel",
                "",
            ]
        else:
            out += ["-- (Rejected before any linear algebra: no Lean statement is needed.)", ""]
    return out

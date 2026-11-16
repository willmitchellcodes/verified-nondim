"""Certify what desr computes.

desr (https://github.com/ofloveandhate/desr) is the reference implementation of the
Hubert-Labahn algorithm by the authors of "Nondimensionalization is more science than art".
This module runs desr on a model and converts its answer into `HLReduction`, the
solver-independent form that `lean_export2` turns into a Lean certificate. Nothing desr
returns is trusted: every matrix relation is re-checked here with exact arithmetic and then
again by Lean.

desr is not on PyPI. Install it with

    pip install git+https://github.com/ofloveandhate/desr

Scope: desr's "parameter" reduction scheme (the usual one, where the scalings act through the
parameters) on autonomous systems whose right-hand sides are polynomials or quotients of
polynomials, without unit links.
"""

from __future__ import annotations

import sympy as sp

from .hlform import HLReduction, NotSupported, left_inverse_certificate
from .model import Model

INSTALL_HINT = "desr is not installed. Install it with:  pip install git+https://github.com/ofloveandhate/desr"


def desr_available() -> bool:
    try:
        import desr  # noqa: F401
        return True
    except ImportError:
        return False


def desr_version() -> str:
    import desr
    return getattr(desr, "__version__", "unknown")


def to_desr(model: Model):
    """Build desr's ODESystem for `model` (same equations, desr's own symbols)."""
    try:
        from desr import ODESystem
    except ImportError as e:
        raise ImportError(INSTALL_HINT) from e
    if model.extra_invariants:
        raise NotSupported("models with unit links (same_units) are not passed to desr yet")
    used = set().union(*[f.free_symbols for f in model.rhs])
    if model.t in used:
        raise NotSupported("the general theory covers autonomous systems (time must not appear in the equations)")
    unused = [p for p in model.params if p not in used]
    if unused:
        raise NotSupported(f"parameter(s) {', '.join(map(str, unused))} do not appear in the equations, "
                           "so desr never sees them")
    plain = {v: sp.Symbol(v.name) for v in model.variables}
    derivs = {plain[z]: f.xreplace(plain) for z, f in zip(model.states, model.rhs)}
    return ODESystem.from_dict(derivs, indep_var=plain[model.t])


def from_desr(model: Model) -> HLReduction:
    """Run desr on `model` and return its reduction in solver-independent form (checked)."""
    try:
        from desr import ODETranslator
    except ImportError as e:
        raise ImportError(INSTALL_HINT) from e
    system = to_desr(model)
    tr = ODETranslator.from_ode_system(system)
    r = int(tr.r)
    true_rank = sp.Matrix(tr.scaling_matrix).rank() if r else 0
    if true_rank == 0:
        # desr reports one all-zero "scaling" for a model that has none
        raise NotSupported(f"{model.name} has no scaling symmetry: there is nothing to reduce")
    if true_rank < r:
        raise NotSupported(f"desr returned {r} scalings of rank {true_rank} for {model.name}")
    scheme = str(tr.scheme(system))
    if scheme != "parameter":
        raise NotSupported(f"desr chose its '{scheme}' scheme for {model.name}; only the 'parameter' scheme is supported")
    ours = {v.name: v for v in model.variables}
    domain = [ours[str(s)] for s in tr.symbols_domain]  # desr's order: parameters, time, dependents
    t_pos = domain.index(model.t)
    variables = [v for v in domain if v != model.t]
    keep_rows = [i for i in range(len(domain)) if i != t_pos]

    A_full = sp.Matrix(tr.scaling_matrix)
    V = sp.Matrix(tr.herm_mult)
    W = sp.Matrix(tr.inv_herm_mult)
    N = len(domain)
    names = [str(x) for x in tr.invariant_names(system)]  # one per column of V[:, r:]
    red = tr.translate(system)
    red_rhs = {str(k): sp.sympify(v) for k, v in red.derivative_dict.items()}

    # the invariant that plays the role of time: the column of Vn with a 1 in the time row
    time_cols = [j for j in range(r, N) if V[t_pos, j] != 0]
    if len(time_cols) != 1 or V[t_pos, time_cols[0]] != 1 or any(V[t_pos, j] != 0 for j in range(r)):
        raise NotSupported("time does not appear in exactly one invariant; not the parameter scheme's layout")
    tc = time_cols[0]
    inv_cols = [j for j in range(r, N) if j != tc]

    A = A_full[:, keep_rows]
    tau = [int(A_full[j, t_pos]) for j in range(r)]
    Vi = V[keep_rows, :r]
    Vn = V[keep_rows, inv_cols]
    Wu = W[:r, keep_rows]
    Wd = W[inv_cols, keep_rows]
    G, d = left_inverse_certificate(A * Vi)

    symbols = [sp.Symbol(names[j - r], positive=True) for j in inv_cols]
    rename = {sp.Symbol(names[j - r]): symbols[i] for i, j in enumerate(inv_cols)}
    reduced, state_col = {}, {}
    for z in model.states:
        row = variables.index(z)
        mine = [i for i in range(len(inv_cols)) if Vn[row, i] == 1
                and all(Vn[variables.index(o), i] == 0 for o in model.states if o != z)]
        if len(mine) != 1:
            raise NotSupported(f"cannot tell which desr invariant carries the state {z}")
        state_col[z] = mine[0]
        reduced[z] = red_rhs[symbols[mine[0]].name].xreplace(rename)

    time_inv = sp.Mul(*[domain[i] ** V[i, tc] for i in range(N)])
    out = HLReduction(
        model=model, source=f"desr {desr_version()}", variables=variables, A=A, tau=tau,
        Vi=Vi, Vn=Vn, Wu=Wu, Wd=Wd, G=G, d=d, invariant_symbols=symbols, reduced_rhs=reduced,
        time_exponents=[int(V[i, tc]) for i in keep_rows], state_col=state_col,
        time_invariant=time_inv, full_order=domain, Dfull=A_full, Pfull=V[:, r:], V1full=V[:, :r],
        W1full=W[:r, :], W2full=W[r:, :],
    )
    out.check()
    return out


def compare(model: Model) -> dict:
    """Run both solvers on `model` and report whether they agree on what matters."""
    from .scaling import analyze, nondimensionalize
    from .hlform import from_nondim

    an = analyze(model)
    result = {"model": model.name, "parameters": len(model.params), "ours_scalings": an.n_scalings,
              "ours_after": an.min_params, "desr": None, "agree": None, "note": ""}
    try:
        theirs = from_desr(model)
    except (NotSupported, ImportError) as e:
        result["note"] = str(e)
        return result
    result["desr"] = theirs
    result["desr_scalings"] = theirs.r
    result["desr_after"] = len(theirs.reduced_parameters())
    # same lattice of scalings? compare row spaces of [tau | A] over the same column order
    order = [model.t, *model.states, *model.params]
    mine = sp.Matrix([[an.A[j, model.index(v)] for v in order] for j in range(an.A.shape[0])])
    full = theirs.full_scaling_matrix()
    pos = {v: i for i, v in enumerate([model.t, *theirs.variables])}
    theirs_m = sp.Matrix([[full[j, pos[v]] for v in order] for j in range(theirs.r)])
    same_space = mine.rank() == theirs_m.rank() == mine.col_join(theirs_m).rank()
    result["same_scalings"] = bool(same_space)
    result["desr_maximal_by_our_K"] = theirs.is_maximal()
    result["agree"] = bool(same_space and result["desr_after"] == an.min_params)
    try:
        result["ours"] = from_nondim(nondimensionalize(model, analysis=an))
    except NotSupported as e:
        result["note"] = f"own solver not exported in the general form: {e}"
    return result

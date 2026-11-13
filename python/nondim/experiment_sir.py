"""Framing 3 experiment: fitting an SIR model to noisy, partial data.

Setting: we observe reported prevalence y(t) = rho * I(t) with an unknown
reporting fraction rho, and unknown initial conditions. The scaling

    S, I -> S/lambda, I/lambda      beta, rho -> lambda*beta, lambda*rho

leaves the data unchanged, so beta, rho, S(0), I(0) cannot be estimated
separately. The invariant groups can:

    gamma,   R0 = beta*S(0)/gamma,   y0 = rho*I(0),   kappa = beta/rho.

The experiment shows three things on synthetic data:
  1. many random-start fits agree on the groups and disagree on the raw parameters;
  2. the loss is flat along the scaling direction and curved across it;
  3. fitting the *reduced* model stays well-conditioned as data get sparser/noisier.

Run:  python -m nondim experiment        (writes reports/identifiability_sir.md + .png)
"""

from __future__ import annotations

from pathlib import Path

import numpy as np
from scipy.integrate import solve_ivp
from scipy.optimize import least_squares

TRUTH = dict(beta=0.002, gamma=0.4, rho=0.3, S0=990.0, I0=10.0)
RAW = ["beta", "gamma", "rho", "S0", "I0"]
GROUPS = {
    "gamma": lambda p: p["gamma"],
    "R0 = beta*S0/gamma": lambda p: p["beta"] * p["S0"] / p["gamma"],
    "y0 = rho*I0": lambda p: p["rho"] * p["I0"],
    "kappa = beta/rho": lambda p: p["beta"] / p["rho"],
}


def observe(p: dict, ts: np.ndarray) -> np.ndarray:
    """y(t) = rho * I(t) for the dimensional model."""
    f = lambda t, z: [-p["beta"] * z[0] * z[1], p["beta"] * z[0] * z[1] - p["gamma"] * z[1]]  # noqa: E731
    sol = solve_ivp(f, (0, ts[-1]), [p["S0"], p["I0"]], t_eval=ts, rtol=1e-9, atol=1e-11, method="LSODA")
    return p["rho"] * sol.y[1]


def observe_reduced(q: dict, ts: np.ndarray) -> np.ndarray:
    """Same output from the reduced model: u = beta*S, v = rho*I (v is the observable itself)."""
    f = lambda t, z: [-q["kappa"] * z[0] * z[1], z[0] * z[1] - q["gamma"] * z[1]]  # noqa: E731
    sol = solve_ivp(f, (0, ts[-1]), [q["R0"] * q["gamma"], q["y0"]], t_eval=ts, rtol=1e-9, atol=1e-11, method="LSODA")
    return sol.y[1]


def to_reduced(p: dict) -> dict:
    return dict(gamma=p["gamma"], R0=p["beta"] * p["S0"] / p["gamma"], y0=p["rho"] * p["I0"], kappa=p["beta"] / p["rho"])


def scaled(p: dict, lam: float) -> dict:
    """Move along the symmetry: different parameters, identical data."""
    return dict(beta=lam * p["beta"], gamma=p["gamma"], rho=lam * p["rho"], S0=p["S0"] / lam, I0=p["I0"] / lam)


def make_data(ts, noise=0.05, seed=0):
    rng = np.random.default_rng(seed)
    return observe(TRUTH, ts) * np.exp(noise * rng.standard_normal(len(ts)))


def _fit(model, names, start: dict, ts, y, center: dict | None = None, box: float = 100.0):
    """Least squares in log-parameters. Each parameter is confined to a plausible
    range (within a factor `box` of `center`) so flat directions cannot run off to infinity."""
    x0 = np.log([start[n] for n in names])
    c = np.log([(center or start)[n] for n in names])
    lo, hi = c - np.log(box), c + np.log(box)
    x0 = np.clip(x0, lo + 1e-6, hi - 1e-6)

    def resid(x):
        try:
            pred = model(dict(zip(names, np.exp(x))), ts)
        except Exception:
            return np.full(len(ts), 1e3)
        if pred.shape != y.shape or not np.all(np.isfinite(pred)) or np.any(pred <= 0):
            return np.full(len(ts), 1e3)
        return np.log(pred) - np.log(y)

    out = least_squares(resid, x0, bounds=(lo, hi), method="trf", max_nfev=200)
    cond = np.linalg.cond(out.jac)
    return dict(zip(names, np.exp(out.x))), float(np.sum(out.fun**2)), cond


def jacobian_condition(model, point: dict, names, ts, h: float = 1e-4) -> float:
    """Condition number of d log(output) / d log(parameters) at `point` (central differences).
    A huge value means some combination of parameters barely changes the data."""
    cols = []
    for n in names:
        up, dn = dict(point), dict(point)
        up[n], dn[n] = point[n] * np.exp(h), point[n] * np.exp(-h)
        cols.append((np.log(model(up, ts)) - np.log(model(dn, ts))) / (2 * h))
    return float(np.linalg.cond(np.array(cols).T))


def fit_raw(start, ts, y):
    return _fit(observe, RAW, start, ts, y, center=TRUTH)


def fit_reduced(start, ts, y):
    return _fit(observe_reduced, ["gamma", "R0", "y0", "kappa"], start, ts, y)


def multistart(ts, y, n_starts=12, seed=1, spread=0.7):
    """Fit the raw 5-parameter model from many random starts; keep the good fits."""
    rng = np.random.default_rng(seed)
    fits = []
    for _ in range(n_starts):
        lam = np.exp(rng.uniform(-1.5, 1.5))  # start somewhere along (and off) the ridge
        start = {k: v * np.exp(spread * rng.uniform(-1, 1)) for k, v in scaled(TRUTH, lam).items()}
        p, loss, _ = fit_raw(start, ts, y)
        fits.append((p, loss))
    best = min(l for _, l in fits)
    return [p for p, l in fits if l < 1.5 * best + 1e-9]


def fold_spread(values) -> float:
    """max/min across fits: 1.0 means every fit agrees."""
    v = np.asarray(values, dtype=float)
    return float(v.max() / v.min())


def ridge_profile(ts, y, lams):
    loss = lambda p: float(np.sum((np.log(observe(p, ts)) - np.log(y)) ** 2))  # noqa: E731
    along = [loss(scaled(TRUTH, l)) for l in lams]
    across = [loss({**TRUTH, "beta": TRUTH["beta"] * l}) for l in lams]
    return np.array(along), np.array(across)


SCENARIOS = {
    "full data (61 points, 5% noise)": dict(keep=slice(None), noise=0.05),
    "every 4th point": dict(keep=slice(None, None, 4), noise=0.05),
    "first third only (before the peak)": dict(keep=slice(0, 20), noise=0.05),
    "20% noise": dict(keep=slice(None), noise=0.20),
}


def run(out_dir: Path | None = None, n_starts: int = 12, seed: int = 0, make_figure: bool = True) -> dict:
    ts_full = np.linspace(0.5, 30, 61)
    y_full = make_data(ts_full, 0.05, seed)

    fits = multistart(ts_full, y_full, n_starts, seed + 1)
    raw_spread = {k: fold_spread([p[k] for p in fits]) for k in RAW}
    group_spread = {k: fold_spread([g(p) for p in fits]) for k, g in GROUPS.items()}

    lams = np.exp(np.linspace(np.log(0.2), np.log(5), 25))
    along, across = ridge_profile(ts_full, y_full, lams)

    truth_red = to_reduced(TRUTH)
    rows = []
    for name, sc in SCENARIOS.items():
        ts = ts_full[sc["keep"]]
        y = make_data(ts_full, sc["noise"], seed)[sc["keep"]]
        q, _, _ = fit_reduced({k: v * 1.3 for k, v in truth_red.items()}, ts, y)
        cond_raw = jacobian_condition(observe, TRUTH, RAW, ts)
        cond_red = jacobian_condition(observe_reduced, q, list(q), ts)
        rows.append(dict(scenario=name, n=len(ts), R0=q["R0"], R0_err=abs(q["R0"] / truth_red["R0"] - 1),
                         gamma_err=abs(q["gamma"] / truth_red["gamma"] - 1), cond_raw=cond_raw, cond_reduced=cond_red))

    result = dict(n_good_fits=len(fits), raw_spread=raw_spread, group_spread=group_spread,
                  lams=lams, along=along, across=across, scenarios=rows, truth=truth_red, fits=fits)
    if out_dir is not None:
        out_dir = Path(out_dir)
        out_dir.mkdir(parents=True, exist_ok=True)
        if make_figure:
            try:
                _figure(result, ts_full, y_full, out_dir / "identifiability_sir.png")
            except ImportError:  # matplotlib is optional: pip install "verified-nondim[plots]"
                make_figure = False
        result["figure"] = make_figure
        (out_dir / "identifiability_sir.md").write_text(_markdown(result, make_figure))
    return result


def _figure(res, ts, y, path):
    import matplotlib
    matplotlib.use("Agg")
    import matplotlib.pyplot as plt

    fig, ax = plt.subplots(1, 3, figsize=(13, 3.8))
    ax[0].plot(ts, y, "k.", label="noisy data")
    for i, p in enumerate(res["fits"][:6]):
        ax[0].plot(ts, observe(p, ts), lw=1, alpha=0.8, label="fits" if i == 0 else None)
    ax[0].set(title="Different parameters, same curve", xlabel="time", ylabel="reported prevalence y")
    ax[0].legend()
    b = [p["beta"] for p in res["fits"]]
    r = [p["rho"] for p in res["fits"]]
    ax[1].loglog(b, r, "o")
    lam = np.array([0.1, 10])
    ax[1].loglog(TRUTH["beta"] * lam, TRUTH["rho"] * lam, "k--", lw=1, label="scaling direction (rho/beta fixed)")
    ax[1].set(title="Fits spread along the symmetry", xlabel="beta", ylabel="rho")
    ax[1].legend()
    ax[2].loglog(res["lams"], res["across"], label="changing beta alone")
    ax[2].loglog(res["lams"], res["along"], label="along the scaling (data unchanged)")
    ax[2].set(title="Loss: curved vs. flat ridge", xlabel="scale factor lambda", ylabel="sum of squared log-errors")
    ax[2].set_xticks([0.2, 0.5, 1, 2, 5], labels=["0.2", "0.5", "1", "2", "5"])
    ax[2].minorticks_off()
    ax[2].legend(loc="upper center", fontsize=8)
    fig.tight_layout()
    fig.savefig(path, dpi=130)
    plt.close(fig)


def _markdown(res, with_figure=True) -> str:
    L = ["# Identifiability experiment: SIR with unknown reporting fraction", "",
         "Generated by `python -m nondim experiment`. Synthetic data; truth: "
         + ", ".join(f"{k} = {v}" for k, v in TRUTH.items()) + ".", "",
         "Observed: `y = rho * I`. The scaling `S, I -> S/λ, I/λ; beta, rho -> λ·beta, λ·rho` leaves `y` unchanged.", ""]
    if with_figure:
        L += ["![fits, ridge and loss profile](identifiability_sir.png)", ""]
    L += [f"## 1. Random-start fits ({res['n_good_fits']} equally good fits)", "",
          "Fold spread = largest / smallest estimate across fits (1.00 = all fits agree).", "",
          "| raw parameter | fold spread | | invariant group | fold spread |", "|---|---|---|---|---|"]
    raw, grp = list(res["raw_spread"].items()), list(res["group_spread"].items())
    for i in range(max(len(raw), len(grp))):
        a = f"| {raw[i][0]} | {raw[i][1]:.3g} |" if i < len(raw) else "| | |"
        b = f" | {grp[i][0]} | {grp[i][1]:.3f} |" if i < len(grp) else " | | |"
        L.append(a + b)
    L += ["", "The groups are pinned down; the raw parameters moved by the scaling are not.", "",
          "## 2. Loss along and across the symmetry", "",
          f"Along the scaling direction the loss varies by {np.ptp(res['along']):.1e} (flat, up to solver error); "
          f"changing beta alone raises it by up to {res['across'].max() - res['across'].min():.1f}.", "",
          "## 3. Fitting the reduced model under worse data", "",
          f"True R0 = {res['truth']['R0']:.3f}. `cond` is the condition number of the "
          "output-vs-parameter sensitivities, in logs (huge = some direction is undetermined).", "",
          "| data | points | R0 estimate | R0 rel. error | gamma rel. error | cond (raw, 5 params) | cond (reduced, 4 params) |",
          "|---|---|---|---|---|---|---|"]
    for r in res["scenarios"]:
        L.append(f"| {r['scenario']} | {r['n']} | {r['R0']:.3f} | {r['R0_err']:.1%} | {r['gamma_err']:.1%} | "
                 f"{r['cond_raw']:.1e} | {r['cond_reduced']:.1e} |")
    L += ["", "## Reading the results", "",
          "* The raw model is ill-conditioned in every scenario (in exact arithmetic the condition number is infinite), "
          "because one direction is invisible to the data.",
          "* The reduced model is well conditioned, so its estimates degrade gracefully as data get sparser or noisier. "
          "That degradation is *practical* non-identifiability (too little information), which is a different thing "
          "from the *structural* kind caused by the symmetry.",
          "* Raw parameters were confined to within 100x of the truth; without that box they drift without limit.",
          "* Caveat: scaling symmetries are only one source of non-identifiability (Villaverde & Massonis 2021).", ""]
    return "\n".join(L)

"""Command line: `nondim <command>` (or `python -m nondim <command>`). Run `nondim` for the list.

    tour                         a 2-minute guided walk through SIR -> R0
    list                         the built-in models
    show <model>                 full report for one model
    reduce <model> -n gamma N    nondimensionalize, choosing what to normalize
    constrain <model> -k 2 --keep beta --want R0=beta*N/gamma
    identify <model> [-o y=rho*I]
    experiment                   the SIR data-fitting experiment (Framing 3)
    desr <model>                 run desr on a model and cross-check it against this package
    compare                      desr vs. this package on every model -> reports/desr_comparison.md
    init-lean DIR                create the Lean 4 project that checks the certificates
    certify [models...]          write Lean certificates (matrix-level and general form)
    all                          reports + certificates + experiment
    --version
"""

from __future__ import annotations

import argparse
from pathlib import Path

from . import __version__, models
from .catalog import CATALOG, GENERAL
from .constraints import solve
from .identifiability import analyze_identifiability
from .lean_export import write_certificate
from .leanproject import default_lean_dir, default_reports_dir, init_lean, template_files
from .model import OutOfScopeError
from .report import build, model_report, summary_table
from .scaling import analyze, nondimensionalize, verify_symbolically


def _lib_dir(a) -> Path:
    """The `NondimVerify` library folder of the Lean project selected on the command line."""
    project = Path(a.lean_dir) if getattr(a, "lean_dir", None) else default_lean_dir()
    if not (project / "lakefile.toml").exists():
        raise SystemExit(f"no Lean project at {project}. Create one with:  nondim init-lean {project}")
    return project / "NondimVerify"


def _reports_dir(a) -> Path:
    return Path(a.out) if getattr(a, "out", None) else default_reports_dir()


def _model(key):
    if key not in models.ALL:
        raise SystemExit(f"unknown model {key!r}. Try: {', '.join(models.ALL)}")
    return models.ALL[key]()


def cmd_list(_):
    print(summary_table())


def cmd_show(a):
    _model(a.model)
    print(model_report(a.model))


def cmd_reduce(a):
    m = _model(a.model)
    an = analyze(m)
    print(an.summary(), "\n")
    try:
        nd = nondimensionalize(m, [m.symbol(x) for x in a.normalize] if a.normalize else None,
                               keep=[m.symbol(x) for x in a.keep], analysis=an)
    except ValueError as e:
        raise SystemExit(f"cannot do that: {e}")
    print(nd.summary())
    print("  chain-rule check:", "pass" if all(r == 0 for r in verify_symbolically(nd)) else "FAIL")


def cmd_constrain(a):
    m = _model(a.model)
    want = dict(w.split("=", 1) for w in a.want)
    r = solve(m, a.eliminate, at_most_params=a.at_most, keep=a.keep, want=want)
    print(r)
    if r.witness:
        print(r.witness.summary())
    if r.regrouping:
        print("  regrouped parameters:")
        for g, e, _ in r.regrouping.groups:
            print(f"    {g} = {e}")
        for z, g in zip(m.states, r.regrouping.reduced_rhs):
            print(f"    d{r.witness.new_symbol[z]}/d{r.witness.new_symbol[m.t]} = {g}")


def cmd_identify(a):
    m = _model(a.model)
    outputs = dict(o.split("=", 1) for o in a.output) or None
    try:
        print(analyze_identifiability(m, outputs, known=a.known).summary())
    except ValueError as e:
        raise SystemExit(str(e) + "  (e.g.  -o y=rho*I)")


def cmd_experiment(a):
    from .experiment_sir import run
    out = _reports_dir(a)
    res = run(out, n_starts=a.starts)
    print((out / "identifiability_sir.md").read_text())
    print(f"written to {out / 'identifiability_sir.md'} ({res['n_good_fits']} good fits)")
    if not res["figure"]:
        print('figure skipped: install matplotlib (pip install "verified-nondim[plots]") to get the PNG')


def certify(keys=None, lean_dir: Path | None = None, quiet=False) -> list[str]:
    """Write one Lean certificate per catalog model flagged `certify` into the library folder
    `lean_dir` (a project's `NondimVerify/`). Returns the module names."""
    lean_dir = Path(lean_dir) if lean_dir is not None else default_lean_dir() / "NondimVerify"
    keys = keys or [k for k, c in CATALOG.items() if c.get("certify")]
    written = []
    for key in keys:
        model, _, nd, results = build(key)
        mod = "".join(p[:1].upper() + p[1:] for p in model.name.split("_"))
        path = write_certificate(nd, lean_dir / "Cert" / f"{mod}.lean", results, mod)
        written.append(mod)
        if not quiet:
            print(f"  wrote {path.relative_to(lean_dir.parent)}")
    if set(keys) == {k for k, c in CATALOG.items() if c.get("certify")}:
        imports = "\n".join(f"import NondimVerify.Cert.{m}" for m in sorted(written))
        (lean_dir / "Cert.lean").write_text(
            "-- Auto-generated by `python -m nondim certify`: imports every certificate.\n" + imports + "\n")
    return written


def _camel(name: str) -> str:
    return "".join(p[:1].upper() + p[1:] for p in name.split("_"))


def certify_general(lean_dir: Path | None = None, quiet=False, use_desr: bool | None = None) -> dict:
    """Write general-form certificates into `lean_dir/Certified/{Own,Desr}/`.

    "Own" certificates always; "Desr" ones when desr is installed (or `use_desr=True`).
    Returns {"Own": [...], "Desr": [...], "skipped": {(source, model): reason}}.
    """
    from . import lean_export2
    from .desr_bridge import desr_available, from_desr
    from .hlform import NotSupported, from_nondim

    lean_dir = Path(lean_dir) if lean_dir is not None else default_lean_dir() / "NondimVerify"
    use_desr = desr_available() if use_desr is None else use_desr
    done = {"Own": [], "Desr": [], "skipped": {}}
    sources = [("Own", lambda m: from_nondim(nondimensionalize(m)))]
    if use_desr:
        sources.append(("Desr", from_desr))
    for key in GENERAL:
        model = models.ALL[key]()
        for src, make in sources:
            try:
                red = make(model)
            except NotSupported as e:
                done["skipped"][(src, key)] = str(e)
                continue
            name = _camel(model.name)
            path = lean_export2.write_certificate(red, lean_dir / "Certified" / src / f"{name}.lean", f"{src}.{name}")
            done[src].append(name)
            if not quiet:
                print(f"  wrote {path.relative_to(lean_dir.parent)}")
    present = sorted(p.relative_to(lean_dir / "Certified").with_suffix("").as_posix().replace("/", ".")
                     for p in (lean_dir / "Certified").rglob("*.lean"))
    (lean_dir / "Certified.lean").write_text(
        "-- Auto-generated by `nondim certify`: imports every certificate in the general form.\n"
        + "\n".join(f"import NondimVerify.Certified.{m}" for m in present) + "\n")
    if not use_desr and not quiet:
        print("  desr is not installed: the Certified/Desr files were left as they are")
    return done


def cmd_certify(a):
    lib = _lib_dir(a)
    certify(a.models or None, lib)
    if not a.models:
        certify_general(lib)
    print(f"now run:  cd {lib.parent} && lake build")


def cmd_desr(a):
    from .desr_bridge import compare, desr_available, INSTALL_HINT
    if not desr_available():
        raise SystemExit(INSTALL_HINT)
    m = _model(a.model)
    res = compare(m)
    if res["desr"] is None:
        raise SystemExit(f"desr result not usable here: {res['note']}")
    print(res["desr"].summary())
    print(f"\ncross-check against this package: same scalings: {res['same_scalings']};  "
          f"parameters after: desr {res['desr_after']}, ours {res['ours_after']};  "
          f"maximal by our exponent matrix: {res['desr_maximal_by_our_K']}")


def comparison_table() -> str:
    from .desr_bridge import compare
    L = ["| model | parameters | scalings (ours / desr) | parameters after (ours / desr) | same scalings | desr's invariants | note |",
         "|---|---|---|---|---|---|---|"]
    for key in models.ALL:
        r = compare(models.ALL[key]())
        if r["desr"] is None:
            L.append(f"| {key} | {r['parameters']} | {r['ours_scalings']} / — | {r['ours_after']} / — | — | — | {r['note'].split(';')[0]} |")
        else:
            inv = ", ".join(map(str, [r["desr"].time_invariant, *r["desr"].invariant_monomials()]))
            L.append(f"| {key} | {r['parameters']} | {r['ours_scalings']} / {r['desr_scalings']} | "
                     f"{r['ours_after']} / {r['desr_after']} | {'yes' if r['same_scalings'] else '**NO**'} | `{inv}` | |")
    return "\n".join(L)


def cmd_compare(a):
    from .desr_bridge import desr_available, desr_version, INSTALL_HINT
    if not desr_available():
        raise SystemExit(INSTALL_HINT)
    out = _reports_dir(a)
    out.mkdir(parents=True, exist_ok=True)
    text = ("# desr vs. this package\n\nGenerated by `nondim compare` with desr " + desr_version() + ".\n\n"
            "Both tools are run on every built-in model. \"Same scalings\" means the two scaling matrices have "
            "the same row space, i.e. the tools found the same symmetries.\n\n" + comparison_table() + "\n")
    (out / "desr_comparison.md").write_text(text)
    print(text)


def cmd_init_lean(a):
    try:
        dest = init_lean(a.dir, force=a.force)
    except FileExistsError as e:
        raise SystemExit(str(e))
    print(f"created a Lean project with {len(template_files())} files in {dest}")
    print(f"next:  cd {dest} && lake exe cache get && lake build")


def cmd_all(a):
    out, lib = _reports_dir(a), _lib_dir(a)
    out.mkdir(parents=True, exist_ok=True)
    for key in models.ALL:
        (out / f"{key}.md").write_text(model_report(key))
        print(f"  wrote {out.name}/{key}.md")
    (out / "SUMMARY.md").write_text(
        "# Summary of all models\n\nGenerated by `nondim all`. One detailed report per model is "
        "in this folder.\n\n" + summary_table() + "\n")
    certify(lean_dir=lib)
    certify_general(lib)
    from .desr_bridge import desr_available
    if desr_available():
        cmd_compare(a)
    try:
        analyze(models.arrhenius_out_of_scope())
    except OutOfScopeError as e:
        print(f"  out-of-scope demo (Arrhenius) rejected as expected: {e}")
    from .experiment_sir import run
    run(out)
    print(f"  wrote {out.name}/identifiability_sir.md\n")
    print(summary_table())


def cmd_tour(_):
    from .tour import tour
    tour()


def main(argv=None):
    p = argparse.ArgumentParser(prog="nondim", description=__doc__,
                                formatter_class=argparse.RawDescriptionHelpFormatter)
    p.add_argument("--version", action="version", version=f"verified-nondim {__version__}")
    sub = p.add_subparsers(dest="cmd")
    sub.add_parser("tour").set_defaults(f=cmd_tour)
    sub.add_parser("list").set_defaults(f=cmd_list)
    s = sub.add_parser("show"); s.add_argument("model"); s.set_defaults(f=cmd_show)
    s = sub.add_parser("reduce"); s.add_argument("model")
    s.add_argument("-n", "--normalize", nargs="*", default=[]); s.add_argument("--keep", nargs="*", default=[])
    s.set_defaults(f=cmd_reduce)
    s = sub.add_parser("constrain"); s.add_argument("model")
    s.add_argument("-k", "--eliminate", type=int, default=0); s.add_argument("--at-most", type=int)
    s.add_argument("--keep", nargs="*", default=[]); s.add_argument("--want", nargs="*", default=[], metavar="NAME=EXPR")
    s.set_defaults(f=cmd_constrain)
    s = sub.add_parser("identify"); s.add_argument("model")
    s.add_argument("-o", "--output", nargs="*", default=[], metavar="NAME=EXPR"); s.add_argument("--known", nargs="*", default=[])
    s.set_defaults(f=cmd_identify)
    s = sub.add_parser("experiment"); s.add_argument("--starts", type=int, default=12)
    s.add_argument("--out", help="folder for the report (default: ./reports)"); s.set_defaults(f=cmd_experiment)
    s = sub.add_parser("desr"); s.add_argument("model"); s.set_defaults(f=cmd_desr)
    s = sub.add_parser("compare"); s.add_argument("--out"); s.set_defaults(f=cmd_compare)
    s = sub.add_parser("init-lean"); s.add_argument("dir"); s.add_argument("--force", action="store_true")
    s.set_defaults(f=cmd_init_lean)
    s = sub.add_parser("certify"); s.add_argument("models", nargs="*")
    s.add_argument("--lean-dir", help="Lean project folder (default: ./lean)"); s.set_defaults(f=cmd_certify)
    s = sub.add_parser("all"); s.add_argument("--lean-dir"); s.add_argument("--out"); s.set_defaults(f=cmd_all)
    a = p.parse_args(argv)
    if not a.cmd:
        p.print_help()
        return
    a.f(a)

"""A pilot audit of ODEbase: what do scaling symmetries say about real published models?

ODEbase (Lueders, Sturm, Radulescu; Bioinformatics Advances 2022, https://odebase.org) offers
BioModels systems preprocessed for symbolic computation. Its polynomial models are available
as plain text files in the OscarODEbase.jl repository (MIT licence):

    git clone --depth 1 https://github.com/yuvraj-singh-math/OscarODEbase

This module reads those files WITHOUT executing them (they are Julia source; a small
arithmetic parser extracts the polynomials), turns each into a `Model`, and reports

    * how many scaling symmetries the equations have,
    * how many remain once the model's conservation laws are respected,
    * how many parameters a scaling reduction can remove,
    * whether the model is within reach of the Lean certificates.

No model data is stored in this repository: the audit works on a local clone and writes only
the derived statistics (`reports/odebase_pilot.md`).
"""

from __future__ import annotations

import re
import time
from dataclasses import dataclass, field
from pathlib import Path

import sympy as sp

from .model import Model
from .scaling import analyze

REPO = "https://github.com/yuvraj-singh-math/OscarODEbase"


# ----------------------------------------------------------------- a safe arithmetic parser

class ParseError(ValueError):
    pass


_TOKEN = re.compile(r"\s*(?:(\d+)|([A-Za-z_]\w*)|(//|[-+*/^()]))")


def parse_polynomial(text: str, symbols: dict[str, sp.Symbol]) -> sp.Expr:
    """Parse `1*k1*x2 + (-1)*k3*x1^2/k4` into a SymPy expression.

    Grammar: + - * / ^ //, parentheses, integers and the given names. Nothing is evaluated as
    code, and an unknown name is an error.
    """
    tokens, pos = [], 0
    while pos < len(text):
        if text[pos:].strip() == "":
            break
        m = _TOKEN.match(text, pos)
        if not m:
            raise ParseError(f"unexpected character at {pos}: {text[pos:pos + 20]!r}")
        tokens.append(m.group(1) or m.group(2) or m.group(3))
        pos = m.end()
    i = 0

    def peek():
        return tokens[i] if i < len(tokens) else None

    def take(expected=None):
        nonlocal i
        tok = peek()
        if tok is None or (expected is not None and tok != expected):
            raise ParseError(f"expected {expected or 'a token'}, found {tok!r}")
        i += 1
        return tok

    def atom():
        tok = take()
        if tok == "(":
            e = expr()
            take(")")
            return e
        if tok == "-":
            return -factor()
        if tok == "+":
            return factor()
        if tok.isdigit():
            return sp.Integer(tok)
        if tok in symbols:
            return symbols[tok]
        raise ParseError(f"unknown name {tok!r}")

    def factor():
        base = atom()
        if peek() == "^":
            take()
            exponent = atom()
            if not (exponent.is_Integer):
                raise ParseError("only integer powers are allowed")
            return base ** exponent
        return base

    def term():
        e = factor()
        while peek() in ("*", "/", "//"):
            op = take()
            rhs = factor()
            e = e * rhs if op == "*" else e / rhs
        return e

    def expr():
        e = term()
        while peek() in ("+", "-"):
            op = take()
            rhs = term()
            e = e + rhs if op == "+" else e - rhs
        return e

    result = expr()
    if i != len(tokens):
        raise ParseError(f"trailing input: {tokens[i:i + 5]}")
    return result


def _split_top_level(body: str) -> list[str]:
    parts, depth, cur = [], 0, []
    for ch in body:
        if ch in "([":
            depth += 1
        elif ch in ")]":
            depth -= 1
        if ch == "," and depth == 0:
            parts.append("".join(cur))
            cur = []
        else:
            cur.append(ch)
    if "".join(cur).strip():
        parts.append("".join(cur))
    return [p.strip() for p in parts if p.strip()]


def _names(line: str) -> list[str]:
    m = re.search(r",\(([^)]*)\)=", line)
    return [x.strip() for x in m.group(1).split(",") if x.strip()] if m else []


def _field(text: str, name: str) -> str | None:
    m = re.search(rf"^{name}=(.*)$", text, re.M)
    return m.group(1).strip() if m else None


@dataclass
class Entry:
    """One ODEbase model as read from a file."""
    id: str
    description: str
    species: list[str]
    parameters: list[str]
    equations: list[sp.Expr]
    constraints: list[sp.Expr]
    symbols: dict[str, sp.Symbol] = field(repr=False, default_factory=dict)


def parse_entry(text: str) -> Entry:
    def ring_names(name):
        m = re.search(rf"^{name},.*$", text, re.M)
        return _names(m.group(0)) if m else []

    params, species = ring_names("paramsRing"), ring_names("polRing")
    if not species:
        raise ParseError("no species found")
    symbols = {name: sp.Symbol(name, positive=True) for name in [*params, *species]}

    def exprs(name):
        m = re.search(rf"^{name}=\s*\[", text, re.M)
        if not m:
            return []
        depth, end = 1, m.end()
        while depth and end < len(text):  # the list may run over several lines
            depth += {"[": 1, "]": -1}.get(text[end], 0)
            end += 1
        if depth:
            raise ParseError(f"{name}: unbalanced brackets")
        return [parse_polynomial(p, symbols) for p in _split_top_level(text[m.end():end - 1])]

    eqs = exprs("chemSystem")
    if len(eqs) != len(species):
        raise ParseError(f"{len(eqs)} equations for {len(species)} species "
                         "(a species is defined by a constraint, not an equation)")
    ident = (_field(text, "ID") or "").strip('"')
    desc = (_field(text, "desc") or "").strip('"')
    return Entry(ident, desc, species, params, eqs, exprs("constraints"), symbols)


# ----------------------------------------------------------------- from an entry to a Model

def constraint_links(constraint: sp.Expr) -> list[sp.Expr]:
    """Ratios of the terms of a polynomial relation `p = 0`.

    A scaling preserves the relation exactly when every term has the same weight, i.e. when all
    of these ratios are invariant (Lean: `IsHomogeneous.poly_scale_eq_zero_iff`).
    """
    num = sp.fraction(sp.cancel(sp.together(constraint)))[0]
    terms = [t.as_coeff_Mul()[1] for t in sp.Add.make_args(sp.expand(num)) if t != 0]
    return [t / terms[0] for t in terms[1:]] if len(terms) > 1 else []


def to_model(entry: Entry, use_constraints: bool = True) -> Model:
    """A `Model` for the entry. Parameters that occur nowhere are dropped (they carry no
    information and would otherwise count as removable)."""
    t = sp.Symbol("t", positive=True)
    rhs = [sp.expand(sp.cancel(sp.together(e))) for e in entry.equations]
    links = [r for c in entry.constraints for r in constraint_links(c)] if use_constraints else []
    used = set().union(*[e.free_symbols for e in [*rhs, *links]]) if rhs else set()
    states = [entry.symbols[s] for s in entry.species]
    params = [entry.symbols[p] for p in entry.parameters if entry.symbols[p] in used]
    return Model(entry.id or "ODEbase", t, states, params, rhs, extra_invariants=links,
                 notes=entry.description)


# ----------------------------------------------------------------- the audit

@dataclass
class Row:
    id: str
    description: str
    species: int
    parameters: int          # parameters that occur in the equations or constraints
    unused_parameters: int
    conservation_laws: int
    scalings_equations: int  # scaling symmetries of the equations alone
    scalings: int            # ... that also respect the conservation laws
    removable: int           # parameters a scaling reduction can remove
    in_lean_scope: bool      # polynomial, integer powers, every scaling absorbed by parameters
    note: str = ""
    desr: str = ""           # "agrees" / "differs" / "" (not compared)

    @property
    def remaining(self) -> int:
        return self.parameters - self.removable

    @property
    def spurious(self) -> int:
        """Scalings of the equations that break a conservation law."""
        return self.scalings_equations - self.scalings


def audit_entry(entry: Entry, with_desr: bool = False, desr_max_size: int = 12) -> Row:
    """Analyse one entry. With `with_desr`, small models without conservation laws are also
    given to desr and the two answers are compared (same scalings, same parameter count)."""
    from .hlform import NotSupported, from_nondim
    from .scaling import nondimensionalize

    free = to_model(entry, use_constraints=False)
    model = to_model(entry, use_constraints=True)
    an_free, an = analyze(free), analyze(model)
    note, in_scope = "", False
    try:
        from_nondim(nondimensionalize(model, analysis=an))
        in_scope = True
    except NotSupported as e:
        note = str(e)
    except Exception as e:  # anything else is worth seeing in the report
        note = f"{type(e).__name__}: {e}"
    verdict = ""
    if with_desr and in_scope and not entry.constraints and len(model.variables) - 1 <= desr_max_size:
        from .desr_bridge import compare
        try:
            res = compare(model)
            if res["desr"] is not None:
                verdict = "agrees" if res["agree"] and res["desr_maximal_by_our_K"] else "differs"
        except Exception as e:
            verdict = f"desr failed: {type(e).__name__}"
    return Row(entry.id, entry.description, len(entry.species), len(model.params),
               len(entry.parameters) - len(model.params), len(entry.constraints),
               an_free.n_scalings, an.n_scalings, an.param_rank, in_scope, note[:90], verdict)


def audit(directory: Path, max_bytes: int = 30_000, limit: int | None = None, progress=None,
          with_desr: bool = False) -> tuple[list[Row], list[tuple[str, str]]]:
    """Audit every model file in `directory`. Returns (rows, skipped) where skipped lists
    (file name, reason). Files larger than `max_bytes` are skipped to keep the pilot fast."""
    rows, skipped = [], []
    files = sorted(Path(directory).glob("BIOMD*.jl"))[:limit]
    for path in files:
        if path.stat().st_size > max_bytes:
            skipped.append((path.stem, f"larger than {max_bytes // 1000} kB (not attempted in the pilot)"))
            continue
        start = time.time()
        try:
            rows.append(audit_entry(parse_entry(path.read_text()), with_desr=with_desr))
        except ParseError as e:
            skipped.append((path.stem, f"could not be read: {e}"))
        except Exception as e:
            skipped.append((path.stem, f"{type(e).__name__}: {str(e)[:80]}"))
        if progress:
            progress(path.stem, time.time() - start)
    return rows, skipped


def report(rows: list[Row], skipped: list[tuple[str, str]], source: str = REPO) -> str:
    n = len(rows)
    if n == 0:
        return "# ODEbase pilot\n\nNo model could be read.\n"
    with_sym = [r for r in rows if r.scalings > 0]
    reducible = [r for r in rows if r.removable > 0]
    spurious = [r for r in rows if r.spurious > 0]
    in_scope = [r for r in rows if r.in_lean_scope and r.scalings > 0]
    total_p = sum(r.parameters for r in rows)
    total_removed = sum(r.removable for r in rows)
    pct = lambda k: f"{100 * k / n:.0f}%"  # noqa: E731
    L = [
        "# ODEbase pilot: scaling symmetries of published polynomial models",
        "",
        f"Generated by `nondim audit` from {source} (polynomial ODEbase models; ODEbase is by",
        "Lüders, Sturm and Radulescu, built on BioModels). This is a pilot. The numbers are what this",
        "package's solver finds; a second tool (desr) was run only on the small models without",
        "conservation laws, and only a handful of results are checked in Lean (see `docs/ODEBASE.md`).",
        "",
        "## Summary",
        "",
        "| | |",
        "|---|---|",
        f"| models read | {n} |",
        f"| not attempted or unreadable | {len(skipped)} |",
        f"| with at least one scaling symmetry (conservation laws respected) | {len(with_sym)} ({pct(len(with_sym))}) |",
        f"| where scaling can remove at least one parameter | {len(reducible)} ({pct(len(reducible))}) |",
        f"| parameters in total / removable by scaling | {total_p} / {total_removed} ({100 * total_removed / max(total_p, 1):.0f}%) |",
        f"| models with conservation laws | {sum(1 for r in rows if r.conservation_laws)} |",
        f"| models where ignoring the conservation laws adds scalings that break them | {len(spurious)} ({pct(len(spurious))}) |",
        f"| models with a scaling symmetry that fit the general Lean certificate format | {len(in_scope)} |",
        f"| parameters declared but never used (dropped before the analysis) | {sum(r.unused_parameters for r in rows)} |",
        *([f"| small models also given to desr: same scalings and parameter count / different | "
           f"{sum(1 for r in rows if r.desr == 'agrees')} / {sum(1 for r in rows if r.desr == 'differs')} |"]
          if any(r.desr for r in rows) else []),
        "",
        "\"Scalings that break a conservation law\" are the *spurious* symmetries of Tanburn et al.:",
        "a tool that sees only the differential equations would use them and return a reduction that",
        "is inconsistent with, for example, `x1 + x2 = total`.",
        "",
        "## Per model",
        "",
        "| model | species | parameters | conservation laws | scalings (equations only → with laws) | removable | left | Lean format | desr | note |",
        "|---|---|---|---|---|---|---|---|---|---|",
    ]
    for r in rows:
        L.append(f"| {r.id} | {r.species} | {r.parameters} | {r.conservation_laws} | "
                 f"{r.scalings_equations} → {r.scalings} | {r.removable} | {r.remaining} | "
                 f"{'yes' if r.in_lean_scope and r.scalings else ''} | {r.desr} | "
                 f"{r.note if not r.in_lean_scope else ''} |")
    if skipped:
        L += ["", "## Not attempted or unreadable", "", "| model | reason |", "|---|---|"]
        L += [f"| {name} | {why} |" for name, why in skipped]
    return "\n".join(L) + "\n"


def certifiable(rows: list[Row], count: int = 10, max_size: int = 9) -> list[str]:
    """The smallest models that fit the Lean certificate format (ids, deterministic order)."""
    small = sorted((r.species + r.parameters, r.id) for r in rows
                   if r.in_lean_scope and r.scalings > 0 and r.species + r.parameters <= max_size)
    return [ident for _, ident in small[:count]]


def write_certificates(directory: Path, ids: list[str], lean_dir: Path) -> list[Path]:
    """Lean certificates (general form) for the given models, in `lean_dir/Certified/ODEbase/`."""
    from . import lean_export2
    from .hlform import from_nondim
    from .scaling import nondimensionalize

    written = []
    for ident in ids:
        entry = parse_entry((Path(directory) / f"{ident}.jl").read_text())
        model = to_model(entry)
        model.notes = f"{entry.description} (BioModels {ident}, as preprocessed by ODEbase)"
        red = from_nondim(nondimensionalize(model))
        written.append(lean_export2.write_certificate(
            red, Path(lean_dir) / "Certified" / "ODEbase" / f"{ident}.lean", f"ODEbase.{ident}"))
    return written

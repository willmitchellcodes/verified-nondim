"""The documentation is checked like code.

Every Markdown file in the repository root and in `docs/` is read and held to the same rules:

    * a path, command, theorem, function or test it names must exist;
    * a section it points to (`docs/THEORY.md` §4, Limits §11, D25) must exist;
    * an example it shows must be real:
        ```console   lines starting with `$ nondim` are run, the lines under them must be printed
        ```python    is executed (in a scratch directory); a following ```text block must be printed
        ```lean      every line must occur in a file under `lean/`
        ```bash      instructions for the reader: no inline `#` comments (zsh does not accept them)
    * the numbers it quotes (tests, ODEbase results) must agree with each other and with the source;
    * every document opens the same way and is listed in `docs/README.md`.

`docs/README.md` explains these conventions to a reader.
"""
import contextlib
import functools
import io
import os
import re
import shlex
import subprocess
import sys
from pathlib import Path

import pytest

from conftest import LEAN, ROOT
from nondim import cli
from nondim.desr_bridge import desr_available

PRIVATE = {"PROPOSAL_NOTES.md"}                      # personal notes, not part of the repository
DOCS = [ROOT / "README.md", ROOT / "CHANGELOG.md", ROOT / "AGENTS.md",
        *sorted(p for p in (ROOT / "docs").glob("*.md") if p.name not in PRIVATE)]
GUIDES = [p for p in DOCS if p.parent.name == "docs" and p.name != "README.md"]
IDS = [str(p.relative_to(ROOT)) for p in DOCS]


def text_of(path) -> str:
    return path.read_text()


def blocks(text: str, lang: str) -> list[str]:
    return re.findall(rf"^```{lang}\n(.*?)^```", text, flags=re.S | re.M)


SKIPPED_FOLDERS = {".lake", ".venv", ".git", "__pycache__", ".pytest_cache", "dist", "build", "_to_delete",
                   "Scratch"}   # the last one: Lean scratch files are not sources to quote from


@functools.lru_cache(maxsize=None)
def repository_files() -> tuple:
    """Every file of the repository, without walking into Mathlib, the virtual environment or git.
    (Those hold several hundred thousand files; walking them made these tests take minutes.)"""
    found = []
    for folder, subfolders, names in os.walk(ROOT):
        subfolders[:] = [d for d in subfolders if d not in SKIPPED_FOLDERS]
        found += [Path(folder) / name for name in names if not name.startswith("_tmp_")]
    return tuple(found)


def files_under(folder: str, *suffixes: str) -> list:
    top = ROOT / folder
    return [p for p in repository_files() if top in p.parents and (not suffixes or p.suffix in suffixes)]


def prose(text: str) -> str:
    """The document without its fenced blocks."""
    return re.sub(r"^```.*?^```", "", text, flags=re.S | re.M)


@pytest.fixture(scope="module")
def corpus() -> str:
    """All source text: what a name in the documentation may refer to."""
    sources = (files_under("python", ".py") + files_under("lean", ".lean", ".toml") + files_under("scripts")
               + files_under("examples", ".py", ".ipynb") + [ROOT / "pyproject.toml", ROOT / "setup.sh"])
    return "\n".join(p.read_text(errors="ignore") for p in sources)


# ----------------------------------------------------------------- names

ONLY_IN_THE_BUILT_PACKAGE = {"nondim/_lean_template/"}   # created when the wheel is built
FILES_OF_OTHER_PROJECTS = {"UnitsSystem.lean"}            # cited, not ours
def kept_out_of_git() -> list:
    """The plain entries of `.gitignore` (no wildcards): `lean/.lake`, `docs/PROPOSAL_NOTES.md`, ...
    The documentation may name them, but they exist only on a machine that created them,
    never in a fresh clone, which is where the automatic tests run."""
    lines = [line.strip() for line in (ROOT / ".gitignore").read_text().splitlines()]
    return [line.strip("/") for line in lines if line and not line.startswith("#") and "*" not in line]


def is_kept_out_of_git(path: str) -> bool:
    path = path.strip("/")
    return any(path == entry or path.startswith(entry + "/") for entry in kept_out_of_git())


PATH = re.compile(r"`((?:docs|python|lean|examples|reports|scripts|assets|tests|nondim)/[^`\s]+)`")


@pytest.mark.parametrize("doc", DOCS, ids=IDS)
def test_paths_named_in_the_documentation_exist(doc):
    missing = []
    for raw in PATH.findall(text_of(doc)):
        if any(ch in raw for ch in "<>{}*…") or raw in ONLY_IN_THE_BUILT_PACKAGE:
            continue  # a pattern such as Certified/<Model>.lean, not one file
        path = raw.rstrip(".,:;)")
        if is_kept_out_of_git(path):
            continue  # deliberately untracked: present on the owner's machine, absent from a clone
        candidates = [ROOT / path, ROOT / "python" / path]
        if not any(c.exists() for c in candidates):
            missing.append(raw)
    assert not missing, f"{doc.name} names paths that do not exist: {missing}"


def test_untracked_paths_are_recognised_from_gitignore():
    """Regression: these two exist on a developer's machine and not in a fresh clone. The first
    version of the check above passed locally and failed in the automatic tests because of them."""
    assert is_kept_out_of_git("docs/PROPOSAL_NOTES.md")
    assert is_kept_out_of_git("lean/.lake") and is_kept_out_of_git("lean/.lake/packages/mathlib")
    assert not is_kept_out_of_git("docs/GUIDE.md") and not is_kept_out_of_git("lean/NondimVerify")


@pytest.mark.parametrize("doc", DOCS, ids=IDS)
def test_lean_and_python_files_named_alone_exist(doc):
    names = set(re.findall(r"`([A-Za-z_]\w*\.(?:lean|py|ipynb|sh|yml))`", text_of(doc)))
    existing = {p.name for p in repository_files()}
    missing = names - existing - FILES_OF_OTHER_PROJECTS
    assert not missing, f"{doc.name} names files that do not exist: {sorted(missing)}"


SUBCOMMANDS = {"tour", "list", "show", "reduce", "constrain", "identify", "experiment", "desr", "compare",
               "audit", "init-lean", "certify", "all"}


@pytest.mark.parametrize("doc", DOCS, ids=IDS)
def test_commands_named_in_the_documentation_exist(doc):
    shown = re.sub(r"^```text.*?^```", "", text_of(doc), flags=re.S | re.M)  # printed output is not a command
    used = set(re.findall(r"(?:`|\$ |^)nondim ([a-z][a-z\-]*)", shown, flags=re.M))
    assert used <= SUBCOMMANDS, f"{doc.name}: unknown command(s) {sorted(used - SUBCOMMANDS)}"


# identifiers: `snake_case`, `Dotted.names`, `CamelCase` in backticks must occur in the sources
IDENT = re.compile(r"`([A-Za-z_](?:[\w']|<\w+>)*(?:\.[A-Za-z_](?:[\w']|<\w+>)*)*)`")
NOT_CODE = {
    # mathematical notation and words that are set in code font without naming code
    "x_i", "e_j", "A_S", "A_ji", "x_j", "f_i", "dx_i", "nu_z", "c_z", "g_z", "D_k", "N_k",
    "dep_var",  # the name desr gives one of its reduction schemes
}


def _looks_like_a_name(tok: str) -> bool:
    last = tok.split(".")[-1]
    return "_" in last or "." in tok or (last[:1].isupper() and any(c.islower() for c in last) and len(last) > 6)


@pytest.mark.parametrize("doc", DOCS, ids=IDS)
def test_names_in_code_font_exist_in_the_sources(doc, corpus):
    unknown = set()
    for tok in IDENT.findall(prose(text_of(doc))):
        if tok in NOT_CODE or not _looks_like_a_name(tok) or re.search(r"\.(md|lean|py|toml|yml|sh|ipynb|json|png|svg|jl|command)$", tok):
            continue
        pieces = [tok, tok.split(".")[-1]]
        # `goal<k>_possible` stands for goal1_possible, goal2_possible, ...: one of them must exist
        patterns = [re.sub(r"\\?<\w+\\?>", r"\\w+", re.escape(p)) for p in pieces]
        if not any(re.search(rf"(?<![\w']){p}(?![\w'])", corpus) for p in patterns):
            unknown.add(tok)
    assert not unknown, f"{doc.name} uses names that occur nowhere in the code: {sorted(unknown)}"


# ----------------------------------------------------------------- cross-references

def _sections(path, pattern=r"^## (\d+)\.") -> int:
    return max((int(n) for n in re.findall(pattern, path.read_text(), flags=re.M)), default=0)


@pytest.mark.parametrize("doc", DOCS, ids=IDS)
def test_section_references_point_to_sections_that_exist(doc):
    text = text_of(doc)
    theory = _sections(ROOT / "docs" / "THEORY.md")
    limits = _sections(LEAN / "NondimVerifyTest" / "Limits.lean", r"^/-! ## (\d+)\.")
    decisions = {int(n) for n in re.findall(r"^### D(\d+)\.", (ROOT / "docs" / "DECISIONS.md").read_text(), flags=re.M)}
    for n in re.findall(r"THEORY\.md`? §(\d+)", text):
        assert 0 <= int(n) <= theory, f"{doc.name}: THEORY.md §{n} does not exist (there are {theory})"
    for n in re.findall(r"Limits(?:\.lean`?)? §(\d+)", text):
        assert 1 <= int(n) <= limits, f"{doc.name}: Limits §{n} does not exist (there are {limits})"
    if doc.name != "CHANGELOG.md":
        for n in re.findall(r"\bD(\d+)\b", prose(text)):
            assert int(n) in decisions, f"{doc.name}: decision D{n} does not exist"


def test_decisions_are_numbered_without_gaps():
    ds = [int(n) for n in re.findall(r"^### D(\d+)\.", (ROOT / "docs" / "DECISIONS.md").read_text(), flags=re.M)]
    assert ds == list(range(1, len(ds) + 1))


def test_markdown_links_between_documents_resolve():
    for doc in DOCS:
        for target in re.findall(r"\]\((?!https?://|#|mailto:)([^)#]+)(?:#[^)]*)?\)", text_of(doc)):
            assert (doc.parent / target).exists(), f"{doc.name}: broken link {target}"


# ----------------------------------------------------------------- examples are real

def _run_cli(command: str) -> list[str]:
    argv = shlex.split(command)
    assert argv[0] == "nondim", command
    out = io.StringIO()
    with contextlib.redirect_stdout(out):
        try:
            cli.main(argv[1:])
        except SystemExit as e:  # a command may end with a message; that message is its output
            if e.code not in (0, None):
                print(e.code)
    return [line.rstrip() for line in out.getvalue().splitlines()]


def _console_cases():
    cases = []
    for doc in DOCS:
        for block in blocks(text_of(doc), "console"):
            command, expected = None, []
            for line in block.splitlines() + ["$ end"]:
                if line.startswith("$ "):
                    if command:
                        cases.append(pytest.param(doc.name, command, expected, id=f"{doc.name}: {command}"))
                    command, expected = line[2:].strip(), []
                elif line.strip() and line.strip() != "...":
                    expected.append(line.rstrip())
    return cases


@pytest.mark.parametrize("doc, command, expected", _console_cases())
def test_console_examples_show_real_output(doc, command, expected, tmp_path, monkeypatch):
    if re.match(r"nondim (desr|compare)\b", command) and not desr_available():
        pytest.skip("this example needs desr")
    monkeypatch.chdir(tmp_path)
    actual = _run_cli(command)
    assert expected, f"{doc}: the example `{command}` shows no output"
    position = 0
    for line in expected:
        try:
            position = actual.index(line, position) + 1
        except ValueError:
            pytest.fail(f"{doc}: `{command}` does not print this line (or prints it earlier):\n  {line!r}\n"
                        f"actual output:\n  " + "\n  ".join(actual[:60]))


def _with_blocks(lang: str):
    """The documents that contain a block of this kind, as test parameters."""
    return [pytest.param(p, id=str(p.relative_to(ROOT))) for p in DOCS if blocks(text_of(p), lang)]


@pytest.mark.parametrize("doc", _with_blocks("python"))
def test_python_examples_run_and_print_what_is_shown(doc, tmp_path, monkeypatch):
    code = blocks(text_of(doc), "python")
    if any("desr" in block for block in code) and not desr_available():
        pytest.skip("these examples need desr")
    monkeypatch.chdir(tmp_path)
    out, namespace = io.StringIO(), {}
    with contextlib.redirect_stdout(out):
        for block in code:
            exec(block, namespace)
    printed = [line.rstrip() for line in out.getvalue().splitlines()]
    for block in blocks(text_of(doc), "text"):
        for line in block.splitlines():
            if line.strip() and line.strip() != "...":
                assert line.rstrip() in printed, f"{doc.name} shows a line the code does not print: {line!r}"


@pytest.fixture(scope="module")
def lean_lines() -> set[str]:
    lines = set()
    for p in files_under("lean", ".lean"):
        lines.update(line.strip() for line in p.read_text().splitlines())
    return lines


@pytest.mark.parametrize("doc", _with_blocks("lean"))
def test_lean_snippets_are_quoted_from_the_sources(doc, lean_lines):
    for block in blocks(text_of(doc), "lean"):
        for line in block.splitlines():
            if line.strip() and line.strip() != "...":
                assert line.strip() in lean_lines, f"{doc.name} quotes Lean that is in no source file: {line!r}"


@pytest.mark.parametrize("doc", _with_blocks("bash"))
def test_shell_blocks_can_be_pasted_into_zsh(doc):
    """An interactive zsh does not treat `#` as a comment, so a pasted `cmd  # note` fails."""
    for block in blocks(text_of(doc), "bash"):
        for line in block.splitlines():
            assert "#" not in line, f"{doc.name}: comment inside a shell block: {line!r}"


EXPLANATORY = ["GUIDE.md", "BACKGROUND.md", "THEORY.md", "DESR.md", "ODEBASE.md", "TESTING.md"]


@pytest.mark.parametrize("name", EXPLANATORY)
def test_every_explanatory_document_has_checked_examples(name):
    text = text_of(ROOT / "docs" / name)
    checked = sum(len(blocks(text, lang)) for lang in ("console", "python", "lean"))
    assert checked >= 2, f"docs/{name} explains without showing: add a console, python or lean example"


def test_theory_gives_an_example_for_every_result():
    text = text_of(ROOT / "docs" / "THEORY.md")
    sections = re.split(r"^## (\d+)\. ", text, flags=re.M)
    numbered = dict(zip(sections[1::2], sections[2::2]))
    for n in map(str, range(0, 10)):  # the setting and the nine groups of results
        assert "**Example.**" in numbered[n], f"THEORY.md §{n} has no example"
        assert blocks(numbered[n], "lean"), f"THEORY.md §{n}: the example quotes no Lean"


# ----------------------------------------------------------------- numbers

def _number(pattern: str, path) -> int:
    m = re.search(pattern, path.read_text())
    assert m, f"{path.name} no longer states: {pattern}"
    return int(m.group(1).replace(",", ""))


def test_test_counts_agree_across_documents():
    total = _number(r"\*\*(\d+) tests pass\*\*", ROOT / "docs" / "DECISIONS.md")
    assert _number(r"(\d+) tests in total", ROOT / "docs" / "CONTRIBUTIONS.md") == total
    assert _number(r"\*\*Tests\*\*: (\d+)", ROOT / "CHANGELOG.md") == total
    assert _number(r"\*\*(\d+) tests\*\* in three layers", ROOT / "docs" / "TESTING.md") == total


def test_stated_test_count_is_the_real_one():
    if not desr_available():
        pytest.skip("the count includes the desr tests")
    result = subprocess.run([sys.executable, "-m", "pytest", "--collect-only", "-q", "tests"],
                            cwd=ROOT / "python", capture_output=True, text=True, env={**os.environ})
    collected = int(re.search(r"(\d+) tests collected", result.stdout).group(1))
    assert collected == _number(r"\*\*(\d+) tests pass\*\*", ROOT / "docs" / "DECISIONS.md")


def test_odebase_numbers_match_the_report():
    report = ROOT / "reports" / "odebase_pilot.md"
    if not report.exists():
        pytest.skip("no ODEbase report in this checkout")
    r, doc = report.read_text(), text_of(ROOT / "docs" / "ODEBASE.md").replace(",", "")
    read = _number(r"\| models read \| (\d+) \|", report)
    with_sym = _number(r"\| with at least one scaling symmetry[^|]*\| (\d+) ", report)
    total, removable = re.search(r"removable by scaling \| (\d+) / (\d+)", r).groups()
    agree = _number(r"same scalings and parameter count / different \| (\d+) /", report)
    for fact in (f"{with_sym} of {read}", f"{total} / {removable}", f"{agree} / 0"):
        assert fact in doc, f"docs/ODEBASE.md no longer matches the report: expected {fact!r}"
    for other in ("CONTRIBUTIONS.md", "DESR.md"):
        assert str(agree) in text_of(ROOT / "docs" / other)


def test_certificate_counts_match_the_files():
    counts = {d: len(list((LEAN / "NondimVerify" / "Certified" / d).glob("*.lean"))) for d in ("Own", "Desr", "ODEbase")}
    status = text_of(ROOT / "docs" / "DECISIONS.md")
    assert f"{sum(counts.values())}\n  certificates in the general form" in status or \
        f"{sum(counts.values())} certificates in the general form" in status.replace("\n ", "")
    assert f"({counts['Own']} from this package's solver, {counts['Desr']} from desr, {counts['ODEbase']} for" in status.replace("\n  ", " ")


# ----------------------------------------------------------------- one shape for every document

@pytest.mark.parametrize("doc", GUIDES, ids=[p.name for p in GUIDES])
def test_every_document_opens_the_same_way(doc):
    lines = text_of(doc).splitlines()
    assert lines[0].startswith("# "), f"{doc.name}: first line is not a title"
    head = "\n".join(lines[1:8])
    assert "> **In one line.**" in head, f"{doc.name}: no 'In one line' summary under the title"
    assert "**Start with:**" in head, f"{doc.name}: the summary does not say where to start"


def test_agent_instructions_exist_and_are_shared():
    """One file of instructions for coding agents; `CLAUDE.md` only imports it."""
    agents = text_of(ROOT / "AGENTS.md")
    for heading in ("Rules", "Map", "How things are tested", "Limits", "How things are documented", "GitHub and PyPI"):
        assert re.search(rf"^## \d+\. {heading}", agents, flags=re.M), f"AGENTS.md lost its section on: {heading}"
    assert "@AGENTS.md" in text_of(ROOT / "CLAUDE.md")
    assert "AGENTS.md" in text_of(ROOT / "docs" / "README.md")


def test_the_index_lists_every_document():
    index = text_of(ROOT / "docs" / "README.md")
    for doc in GUIDES:
        assert f"({doc.name})" in index, f"docs/README.md does not list {doc.name}"
    assert "```console" in index and "How to read the examples" in index


def test_one_name_for_each_thing():
    """Terms that drifted while the project grew. One spelling each."""
    banned = {
        r"\bown solver\b": "this package's solver", r"\bour solver\b": "this package's solver",
        r"\bgeneral form certificate": "general-form certificate", r"non-dimensional": "nondimensional",
        r"\bnondimensionalis": "nondimensionaliz (US spelling, as in the package name)",
    }
    for doc in DOCS:
        body = "\n".join(line for line in prose(text_of(doc)).splitlines()
                         if not line.startswith(("* **[", "  ")))  # titles of cited works keep their spelling
        for pattern, use in banned.items():
            hit = re.search(pattern, body, flags=re.I)
            assert not hit, f"{doc.name}: write '{use}' instead of '{hit.group(0)}'"

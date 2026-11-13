"""The package as other people will get it: public API, README examples, bundled Lean project, scripts."""
import contextlib
import io
import os
import re
import shutil
import subprocess
import sys

import pytest

import nondim
from conftest import LEAN, ROOT
from nondim import cli, leanproject

README = (ROOT / "README.md").read_text()


# ------------------------------------------------------------ public API

def test_public_api_is_importable_from_the_top_level():
    for name in nondim.__all__:
        assert hasattr(nondim, name), name
    assert {"Model", "analyze", "nondimensionalize", "solve", "analyze_identifiability", "init_lean"} <= set(nondim.__all__)


def test_version_is_single_sourced():
    pyproject = (ROOT / "pyproject.toml").read_text()
    assert 'dynamic = ["version"]' in pyproject and 'path = "python/nondim/__init__.py"' in pyproject
    assert re.fullmatch(r"\d+\.\d+\.\d+", nondim.__version__)
    assert f"## {nondim.__version__} " in (ROOT / "CHANGELOG.md").read_text(), "CHANGELOG has no entry for this version"


def test_parameters_can_be_named_by_string():
    sir = nondim.Model.from_strings("SIR", {"S": "-beta*S*I", "I": "beta*S*I - gamma*I"}, "beta gamma N",
                                    same_units=[("S", "N"), ("I", "N")])
    by_name = nondim.nondimensionalize(sir, ["gamma", "N"], names={"beta": "R0"})
    by_symbol = nondim.nondimensionalize(sir, [sir.symbol("gamma"), sir.symbol("N")])
    assert by_name.normalized == by_symbol.normalized
    assert by_name.new_symbol[sir.symbol("beta")].name == "R0"
    assert nondim.nondimensionalize(sir, keep=["beta"]).normalized == by_symbol.normalized
    with pytest.raises(KeyError):
        nondim.nondimensionalize(sir, ["nope"])


# ------------------------------------------------------------ README stays true

def _blocks(lang):
    return re.findall(rf"```{lang}\n(.*?)```", README, flags=re.S)


def test_readme_python_examples_run_and_print_what_the_readme_shows():
    out = io.StringIO()
    namespace = {}
    with contextlib.redirect_stdout(out):
        for block in _blocks("python"):
            exec(block, namespace)
    printed = [line.rstrip() for line in out.getvalue().splitlines()]
    shown = [line.rstrip() for block in _blocks("text") for line in block.splitlines() if line.strip()]
    assert len(_blocks("python")) >= 3 and len(shown) >= 10
    for line in shown:
        assert line in printed, f"README shows a line the code does not print: {line!r}"


def test_readme_lean_snippet_is_taken_from_the_real_certificate():
    cert = (LEAN / "NondimVerify" / "Cert" / "SIR.lean").read_text()
    lines = [line for block in _blocks("lean") for line in block.splitlines() if line.strip()]
    assert lines
    for line in lines:
        assert line in cert, f"README quotes a theorem that is not in Cert/SIR.lean: {line!r}"


def test_readme_is_short_and_points_to_existing_files():
    assert len(README.splitlines()) <= 110
    for target in re.findall(r"\]\(((?:docs|examples)/[^)]*)\)", README) + re.findall(r'src="(assets/[^"]+)"', README):
        assert (ROOT / target).exists(), target
    assert "pip install verified-nondim" in README


@pytest.mark.parametrize("command", ["tour", "list", "show", "reduce", "constrain", "identify", "experiment",
                                     "init-lean", "certify", "all"])
def test_every_documented_command_exists(command):
    with pytest.raises(SystemExit) as e:
        cli.main([command, "--help"])
    assert e.value.code == 0


def test_logo_is_a_small_valid_svg():
    import xml.etree.ElementTree as ET

    path = ROOT / "assets" / "logo.svg"
    root = ET.parse(path).getroot()
    assert root.tag.endswith("svg") and root.attrib["viewBox"] == "0 0 64 64"
    assert path.stat().st_size < 20_000  # the drawing is ~1 kB; delivery may embed provenance metadata
    tags = [el.tag.rsplit("}", 1)[-1] for el in root.iter()]
    assert tags.count("circle") == 4 and tags.count("path") == 4
    assert not {"script", "image", "foreignObject"} & set(tags)


# ------------------------------------------------------------ bundled Lean project

def test_template_is_the_repository_lean_project():
    assert leanproject.repo_root() == ROOT and leanproject.template_dir() == LEAN
    files = {str(f) for f in leanproject.template_files()}
    assert {"lakefile.toml", "lean-toolchain", "lake-manifest.json", "NondimVerify.lean", "NondimVerifyTest.lean",
            "NondimVerify/Basic.lean", "NondimVerify/Theory.lean", "NondimVerify/SIR.lean",
            "NondimVerify/Cert/SIR.lean", "NondimVerifyTest/Certificates.lean"} <= files
    assert not any(".lake" in f or "Scratch" in f or "_tmp_" in f for f in files)


def test_init_lean_copies_a_complete_project(tmp_path):
    dest = nondim.init_lean(tmp_path / "proofs")
    for rel in leanproject.template_files():
        assert (dest / rel).read_bytes() == (LEAN / rel).read_bytes(), rel
    assert sorted(p.name for p in dest.iterdir()) == sorted(
        ["lakefile.toml", "lean-toolchain", "lake-manifest.json", "NondimVerify.lean", "NondimVerifyTest.lean",
         "NondimVerify", "NondimVerifyTest"])
    with pytest.raises(FileExistsError):
        nondim.init_lean(dest)
    nondim.init_lean(dest, force=True)


def test_cli_init_lean_then_certify_into_it(tmp_path, capsys):
    proj = tmp_path / "proofs"
    cli.main(["init-lean", str(proj)])
    assert "lake exe cache get" in capsys.readouterr().out
    before = (proj / "NondimVerify" / "Cert" / "SIR.lean").read_text()
    cli.main(["certify", "--lean-dir", str(proj)])
    assert (proj / "NondimVerify" / "Cert" / "SIR.lean").read_text() == before, "bundled certificates are current"
    with pytest.raises(SystemExit, match="already contains"):
        cli.main(["init-lean", str(proj)])
    with pytest.raises(SystemExit, match="init-lean"):
        cli.main(["certify", "--lean-dir", str(tmp_path / "missing")])


def test_cli_all_writes_reports_and_certificates_where_told(tmp_path, capsys):
    proj = nondim.init_lean(tmp_path / "proofs")
    cli.main(["all", "--lean-dir", str(proj), "--out", str(tmp_path / "out")])
    capsys.readouterr()
    assert (tmp_path / "out" / "SUMMARY.md").exists() and (tmp_path / "out" / "sir.md").exists()
    assert (tmp_path / "out" / "identifiability_sir.md").exists()


def test_version_flag(capsys):
    with pytest.raises(SystemExit):
        cli.main(["--version"])
    assert f"verified-nondim {nondim.__version__}" in capsys.readouterr().out


# ------------------------------------------------------------ release scripts

def _copy_repo(tmp_path):
    dest = tmp_path / "repo"
    shutil.copytree(ROOT, dest, ignore=shutil.ignore_patterns(".git", ".venv", ".lake", "__pycache__", ".pytest_cache", "dist"))
    return dest


def test_set_repo_url_is_idempotent_and_makes_links_absolute(tmp_path):
    repo = _copy_repo(tmp_path)
    for owner in ("octocat", "someone-else"):
        subprocess.run([sys.executable, "scripts/set_repo_url.py", owner], cwd=repo, check=True, capture_output=True)
        pyproject, readme = (repo / "pyproject.toml").read_text(), (repo / "README.md").read_text()
        assert pyproject.count("[project.urls]\n") == 1
        assert f'Homepage = "https://github.com/{owner}/verified-nondim"' in pyproject
        assert f'src="https://raw.githubusercontent.com/{owner}/verified-nondim/main/assets/logo.svg"' in readme
        assert f"](https://github.com/{owner}/verified-nondim/blob/main/docs/GUIDE.md)" in readme
        assert f"](https://github.com/{owner}/verified-nondim/tree/main/examples/)" in readme
        assert "](docs/" not in readme and "octocat" not in readme.replace(owner, "")
    bad = subprocess.run([sys.executable, "scripts/set_repo_url.py", "not a name"], cwd=repo, capture_output=True, text=True)
    assert bad.returncode != 0


@pytest.mark.skipif(shutil.which("git") is None, reason="git not installed")
def test_publish_github_dry_run_commits_locally_and_pushes_nothing(tmp_path):
    repo = _copy_repo(tmp_path)
    (repo / "docs" / "PROPOSAL_NOTES.md").write_text("private notes")
    (repo / "setup.log").write_text("log")
    env = {**os.environ, "DRY_RUN": "1", "GITHUB_OWNER": "octocat", "GIT_AUTHOR_NAME": "Test User",
           "GIT_AUTHOR_EMAIL": "test@example.com", "GIT_COMMITTER_NAME": "Test User",
           "GIT_COMMITTER_EMAIL": "test@example.com", "GIT_CONFIG_GLOBAL": str(tmp_path / "gitconfig"), "PATH": os.environ["PATH"]}
    (tmp_path / "gitconfig").write_text("[user]\n\tname = Test User\n\temail = test@example.com\n")
    # Hide any `gh` on this machine: the script must never touch a real account in a test.
    fake_bin = tmp_path / "bin"
    fake_bin.mkdir()
    (fake_bin / "gh").write_text("#!/bin/sh\nexit 1\n")
    (fake_bin / "gh").chmod(0o755)
    env["PATH"] = f"{fake_bin}{os.pathsep}{env['PATH']}"
    p = subprocess.run(["bash", "scripts/publish_github.sh"], cwd=repo, env=env, capture_output=True, text=True, input="")
    assert p.returncode == 0, p.stdout + p.stderr
    tracked = subprocess.run(["git", "ls-files"], cwd=repo, capture_output=True, text=True).stdout.split("\n")
    assert "README.md" in tracked and "pyproject.toml" in tracked and "lean/NondimVerify/Basic.lean" in tracked
    assert "assets/logo.svg" in tracked and "scripts/workflows/ci.yml" in tracked
    assert "docs/PROPOSAL_NOTES.md" not in tracked and "setup.log" not in tracked
    assert not any(t.startswith(("lean/.lake", ".venv")) for t in tracked)
    log = subprocess.run(["git", "log", "-1", "--format=%an|%B"], cwd=repo, capture_output=True, text=True).stdout
    assert log.startswith("Test User|verified-nondim")
    assert subprocess.run(["git", "remote"], cwd=repo, capture_output=True, text=True).stdout.strip() == ""
    assert "github.com/new" in p.stdout  # without gh it explains the manual route instead of pushing


@pytest.mark.slow
@pytest.mark.skipif(not all(__import__("importlib").util.find_spec(m) for m in ("build", "twine")),
                    reason="needs `pip install build twine`")
def test_wheel_contains_package_lean_template_and_entry_point(tmp_path):
    import zipfile

    repo = _copy_repo(tmp_path)
    subprocess.run([sys.executable, "-m", "build", "--outdir", str(tmp_path / "dist")], cwd=repo, check=True, capture_output=True)
    check = subprocess.run([sys.executable, "-m", "twine", "check", "--strict", *map(str, (tmp_path / "dist").iterdir())],
                           capture_output=True, text=True)
    assert check.returncode == 0, check.stdout + check.stderr
    wheel = next((tmp_path / "dist").glob("verified_nondim-*.whl"))
    names = set(zipfile.ZipFile(wheel).namelist())
    assert "nondim/cli.py" in names and "nondim/_lean_template/lakefile.toml" in names
    assert "nondim/_lean_template/NondimVerify/Cert/SIR.lean" in names
    assert {f"nondim/_lean_template/{f}" for f in map(str, leanproject.template_files())} <= names
    assert not any(".lake/" in n or "tests/" in n for n in names)
    entry = zipfile.ZipFile(wheel).read(next(n for n in names if n.endswith("entry_points.txt"))).decode()
    assert "nondim = nondim.cli:main" in entry
    meta = zipfile.ZipFile(wheel).read(next(n for n in names if n.endswith("METADATA"))).decode()
    assert "Name: verified-nondim" in meta and "License-Expression: MIT" in meta and "Author: Will Mitchell" in meta
    assert "@" not in meta.split("\n\n")[0], "no email address in the published metadata"
    sdist = next((tmp_path / "dist").glob("verified_nondim-*.tar.gz"))
    import tarfile
    members = tarfile.open(sdist).getnames()
    assert any(m.endswith("lean/NondimVerify/Basic.lean") for m in members) and any(m.endswith("LICENSE") for m in members)
    assert not any("PROPOSAL_NOTES" in m or "/.lake/" in m for m in members)


@pytest.mark.skipif(shutil.which("git") is None, reason="git not installed")
def test_publish_github_dry_run_with_gh_never_creates_a_repository(tmp_path):
    """With a logged-in `gh`, DRY_RUN must print the create/push command and not run it."""
    repo = _copy_repo(tmp_path)
    (tmp_path / "gitconfig").write_text("[user]\n\tname = Test User\n\temail = test@example.com\n")
    fake_bin = tmp_path / "bin"
    fake_bin.mkdir()
    calls = tmp_path / "gh_calls.txt"
    (fake_bin / "gh").write_text(f'#!/bin/sh\necho "$@" >> "{calls}"\nif [ "$1" = api ]; then echo octocat; fi\nexit 0\n')
    (fake_bin / "gh").chmod(0o755)
    env = {**os.environ, "DRY_RUN": "1", "GIT_CONFIG_GLOBAL": str(tmp_path / "gitconfig"),
           "PATH": f"{fake_bin}{os.pathsep}{os.environ['PATH']}"}
    env.pop("GITHUB_OWNER", None)
    p = subprocess.run(["bash", "scripts/publish_github.sh"], cwd=repo, env=env, capture_output=True, text=True, input="")
    assert p.returncode == 0, p.stdout + p.stderr
    assert "[dry-run] gh repo create octocat/verified-nondim --public --source=. --remote=origin" in p.stdout
    made = calls.read_text()
    assert "auth status" in made and "api user" in made and "repo create" not in made
    assert 'Homepage = "https://github.com/octocat/verified-nondim"' in (repo / "pyproject.toml").read_text()


def test_workflow_templates_are_present_and_consistent():
    """The GitHub Actions files live as templates until the owner copies them into .github/."""
    wf = ROOT / "scripts" / "workflows"
    ci, publish = (wf / "ci.yml").read_text(), (wf / "publish.yml").read_text()
    assert (wf / "dependabot.yml").exists()
    assert "\t" not in ci + publish, "YAML must not contain tabs"
    assert 'pytest -q -m "not lean"' in ci and "pytest -q -m lean" in ci
    assert "leanprover/lean-action@v1" in ci and "lake-package-directory: lean" in ci
    assert "id-token: write" in publish and "pypa/gh-action-pypi-publish@release/v1" in publish
    assert "https://pypi.org/p/verified-nondim" in publish and "password:" not in publish
    releasing = (ROOT / "docs" / "RELEASING.md").read_text()
    assert "cp scripts/workflows/ci.yml scripts/workflows/publish.yml .github/workflows/" in releasing
    script = (ROOT / "scripts" / "publish_github.sh").read_text()
    assert "cp scripts/workflows" not in script, "the script must not install workflows on the owner's behalf"

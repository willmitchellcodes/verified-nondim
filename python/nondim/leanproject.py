"""The Lean 4 project that checks the certificates, and how to get a copy of it.

In a source checkout the project lives in `lean/` at the repository root. In a
pip-installed package the same files are bundled as `nondim/_lean_template/`.
`init_lean(dest)` copies them into a folder of your own, ready for

    cd dest && lake exe cache get && lake build
"""

from __future__ import annotations

import shutil
from pathlib import Path

TOP_LEVEL_FILES = ["lakefile.toml", "lean-toolchain", "lake-manifest.json", "NondimVerify.lean", "NondimVerifyTest.lean"]
LIBRARY_DIRS = ["NondimVerify", "NondimVerifyTest"]


def repo_root() -> Path | None:
    """The repository root when running from a source checkout, else None."""
    root = Path(__file__).resolve().parents[2]
    return root if (root / "lean" / "lakefile.toml").exists() and (root / "pyproject.toml").exists() else None


def template_dir() -> Path:
    """Where the Lean project files are: bundled with the package, or the checkout's `lean/`."""
    bundled = Path(__file__).resolve().parent / "_lean_template"
    if (bundled / "lakefile.toml").exists():
        return bundled
    root = repo_root()
    if root is not None:
        return root / "lean"
    raise FileNotFoundError("the Lean project template is missing from this installation of nondim")


def template_files() -> list[Path]:
    """Every file `init_lean` copies, relative to the template directory."""
    src = template_dir()
    files = [Path(f) for f in TOP_LEVEL_FILES if (src / f).exists()]
    for d in LIBRARY_DIRS:
        files += sorted(p.relative_to(src) for p in (src / d).rglob("*.lean") if "Scratch" not in p.parts)
    return files


def init_lean(dest: str | Path, force: bool = False) -> Path:
    """Create a Lean project at `dest` containing the checker library and the built-in certificates."""
    dest, src = Path(dest), template_dir()
    if (dest / "lakefile.toml").exists() and not force:
        raise FileExistsError(f"{dest} already contains a Lean project (pass force=True / --force to overwrite its files)")
    for rel in template_files():
        target = dest / rel
        target.parent.mkdir(parents=True, exist_ok=True)
        shutil.copyfile(src / rel, target)
    return dest


def default_lean_dir() -> Path:
    """The Lean project the CLI writes certificates into unless told otherwise."""
    root = repo_root()
    return root / "lean" if root is not None else Path.cwd() / "lean"


def default_reports_dir() -> Path:
    root = repo_root()
    return root / "reports" if root is not None else Path.cwd() / "reports"

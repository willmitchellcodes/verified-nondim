#!/usr/bin/env python3
"""Fill in the GitHub address once it is known:  python scripts/set_repo_url.py OWNER [REPO]

* adds [project.urls] to pyproject.toml (shown on the PyPI page);
* makes the README's logo and links absolute, so they also work on PyPI.

Safe to run twice: it replaces what it wrote before.
"""
import re
import sys
from pathlib import Path

ROOT = Path(__file__).resolve().parents[1]


def main(owner: str, repo: str = "verified-nondim") -> None:
    if not re.fullmatch(r"[A-Za-z0-9](?:[A-Za-z0-9-]{0,38})", owner):
        raise SystemExit(f"{owner!r} does not look like a GitHub user name")
    base = f"https://github.com/{owner}/{repo}"
    raw = f"https://raw.githubusercontent.com/{owner}/{repo}/main"

    pyproject = ROOT / "pyproject.toml"
    text = pyproject.read_text()
    urls = (f'[project.urls]\nHomepage = "{base}"\nDocumentation = "{base}/blob/main/docs/GUIDE.md"\n'
            f'Issues = "{base}/issues"\nChangelog = "{base}/blob/main/CHANGELOG.md"\n')
    text = re.sub(r"\[project\.urls\]\n(?:[A-Za-z]+ = \".*\"\n)+", "", text)
    marker = "# [project.urls] is added by scripts/set_repo_url.py when the repository is created.\n"
    if marker not in text:
        raise SystemExit("pyproject.toml: marker line for [project.urls] not found")
    pyproject.write_text(text.replace(marker, marker + urls))

    readme = ROOT / "README.md"
    text = readme.read_text()
    text = re.sub(r'src="(?:https://raw\.githubusercontent\.com/[^"]*/)?assets/logo\.svg"', f'src="{raw}/assets/logo.svg"', text)
    text = re.sub(r"\]\((?:https://github\.com/[^)]*/(?:blob|tree)/main/)?(docs/[^)]*|examples/)\)",
                  lambda m: f"]({base}/{'tree' if m[1].endswith('/') else 'blob'}/main/{m[1]})", text)
    readme.write_text(text)
    print(f"set repository address to {base}")


if __name__ == "__main__":
    if len(sys.argv) < 2:
        raise SystemExit(__doc__)
    main(*sys.argv[1:3])

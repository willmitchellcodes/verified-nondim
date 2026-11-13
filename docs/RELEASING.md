# Releasing: GitHub and PyPI

Everything here runs under **your own accounts** from your own Terminal. Nothing is published
until you run a script and confirm.

## Names

| Where | Name |
|---|---|
| PyPI (what people `pip install`) | `verified-nondim` |
| Python import and command | `nondim` |
| GitHub repository | `verified-nondim` |
| Version | `__version__` in `python/nondim/__init__.py` (the single source) |

## 1. Push to GitHub (once)

```bash
DRY_RUN=1 ./scripts/publish_github.sh    # preview: prints the online steps without doing them
./scripts/publish_github.sh              # asks "Type yes" before creating the public repository
```

What the script does, in order:

1. Checks `git` is installed and knows your name and email.
2. Finds your GitHub user name (from the `gh` CLI if you are logged in, otherwise it asks).
3. Writes the repository address into `pyproject.toml` and makes the README's logo and links
   absolute, so they also work on the PyPI page (`scripts/set_repo_url.py`).
4. `git init`, `git add -A`, one commit. Not committed: `.venv`, `lean/.lake`, logs, and
   `docs/PROPOSAL_NOTES.md` (see `.gitignore`).
5. Creates the repository and pushes. Without `gh` it prints the two commands to run after you
   create the repository at https://github.com/new.

Installing and logging in to `gh` (optional but easiest): `brew install gh`, then `gh auth login`.

### Turn on automatic testing (GitHub Actions): a step you do by hand

The workflow files are kept as templates in `scripts/workflows/`. They only take effect once
they sit in `.github/`, and that folder is one the assistant's tools are not allowed to write
to, so this copy is yours to make. Read the three short files first if you like, then:

```bash
mkdir -p .github/workflows
cp scripts/workflows/ci.yml scripts/workflows/publish.yml .github/workflows/
cp scripts/workflows/dependabot.yml .github/
```

Do it before `publish_github.sh` and the files go into the first commit; do it later and
commit and push them like any other change. If GitHub rejects the push because your login may
not change workflows, run `gh auth refresh -s workflow` and push again.

Once pushed, the **Actions** tab runs `ci.yml`: Python tests on two Python versions, then a
Lean build and the bridge tests. The first Lean run downloads Mathlib and takes several
minutes. These workflows have not run anywhere yet, so expect to fix a detail or two on the
first run.

## 2. Publish to PyPI

PyPI is permanent: a version number can never be uploaded twice, and a deleted name cannot be
reused by a different project. Do the dry run and the sandbox first.

### Option A: from your Terminal with an API token

```bash
./scripts/publish_pypi.sh check       # build + validate, uploads nothing
./scripts/publish_pypi.sh testpypi    # upload to the sandbox test.pypi.org
./scripts/publish_pypi.sh pypi        # the real thing; asks "Type yes"
```

You need an account (with two-factor authentication) on https://test.pypi.org and
https://pypi.org, and an API token from *Account settings → API tokens* on each. When `twine`
asks, the user name is `__token__` and the password is the token.

### Option B: no token, publish from a GitHub Release (trusted publishing)

One-time setup on https://pypi.org → *Your account → Publishing → Add a pending publisher*:

| Field | Value |
|---|---|
| PyPI project name | `verified-nondim` |
| Owner | your GitHub user name |
| Repository name | `verified-nondim` |
| Workflow name | `publish.yml` |
| Environment name | `pypi` |

Then each release is:

```bash
# 1. bump __version__ in python/nondim/__init__.py and add a section to CHANGELOG.md
git commit -am "Release 0.1.1" && git push
gh release create v0.1.1 --title "v0.1.1" --notes "See CHANGELOG.md"
```

Publishing the release starts `.github/workflows/publish.yml` (copied from the template as
described above), which builds the package and
uploads it. PyPI trusts that workflow in that repository, so no secret is stored anywhere.

## 3. Check the result

```bash
python3 -m venv /tmp/try && /tmp/try/bin/pip install verified-nondim
/tmp/try/bin/nondim tour
/tmp/try/bin/nondim init-lean /tmp/try/proofs     # then: cd /tmp/try/proofs && lake exe cache get && lake build
```

## What is in the package

* The wheel contains the `nondim` Python package and, inside it, a copy of the Lean project
  (`nondim/_lean_template/`), which is what `nondim init-lean` copies out.
* The source archive adds `docs/`, `examples/`, `reports/`, the tests and these scripts.
* Core dependencies: `sympy`, `numpy`, `scipy`. `matplotlib` is optional
  (`pip install "verified-nondim[plots]"`) and only draws the experiment's figure.

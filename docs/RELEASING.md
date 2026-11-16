# Releasing: GitHub and PyPI

> **In one line.** How to publish a new version to GitHub and PyPI under your own accounts.
>
> **Start with:** "Releasing the next version" if the repository already exists.

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

The first command is a preview: it prints the online steps without doing them. The second asks
"Type yes" before it creates the public repository.

```bash
DRY_RUN=1 ./scripts/publish_github.sh
./scripts/publish_github.sh
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
minutes. The workflow files were written from the documentation of the actions they use and
could not be run before they were handed over, so look at the first run in the **Actions** tab
and expect to fix a detail or two.

## 2. Publish to PyPI

PyPI is permanent: a version number can never be uploaded twice, and a deleted name cannot be
reused by a different project. Do the dry run and the sandbox first.

### Option A: from your Terminal with an API token

`check` builds and validates and uploads nothing; `testpypi` uploads to the sandbox
test.pypi.org; `pypi` is the real thing and asks "Type yes".

```bash
./scripts/publish_pypi.sh check
./scripts/publish_pypi.sh testpypi
./scripts/publish_pypi.sh pypi
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

After that, a release is three steps. Set `__version__` in `python/nondim/__init__.py`, give
the "Unreleased" section of `CHANGELOG.md` the version number, and then (shown for 0.2.0):

```bash
git commit -am "Release 0.2.0" && git push
gh release create v0.2.0 --title "v0.2.0" --notes "See CHANGELOG.md"
```

Publishing the release starts `.github/workflows/publish.yml` (copied from the template as
described above), which builds the package and uploads it. PyPI trusts that workflow in that
repository, so no secret is stored anywhere.

## Releasing the next version

**Where things stand (2026-11-16).** PyPI has `verified-nondim` 0.1.0, built from `main`. The
work since then (general theorems, desr, unit links, identifiability, goal queries, rational
models, the ODEbase pilot) is on the branch `general-theory` and is **not on PyPI**. Its version
string is still 0.1.0, and PyPI never accepts the same version twice, so a release needs a new
number. The changes add features without breaking the 0.1.0 commands, which makes it 0.2.0.

1. Run `./setup.sh` (or `lake build` in `lean/` and `python -m pytest -q` in `python/`) on the
   branch. Everything should pass.
2. Set `__version__ = "0.2.0"` in `python/nondim/__init__.py`. In `CHANGELOG.md`, rename the
   heading "Unreleased" to "0.2.0" with the date.
3. Commit that on the branch, merge into `main` and push:

```bash
git add -A
git commit -m "Release 0.2.0"
git checkout main
git merge general-theory
git push
```

4. Publish, by Option A (`./scripts/publish_pypi.sh check`, then `testpypi`, then `pypi`) or
   by Option B (create the GitHub release `v0.2.0`).
5. Check the result as in the next section; `nondim --version` should print 0.2.0.

The package on PyPI then contains the new Lean files as well, because the Lean project is
bundled as a folder. desr stays optional: it is not on PyPI, and PyPI does not allow a
dependency on a Git address.

### Protecting `main`

GitHub shows "Your main branch isn't protected" on any repository without a rule for its default
branch. It is a recommendation, not an error. For a repository with one maintainer a small
ruleset is enough: in the repository's **Settings**, under **Rules → Rulesets**, choose **New
ruleset → New branch ruleset**, give it a name, add the target **Include default branch**, and
select **Restrict deletions** and **Block force pushes**. A new ruleset starts with the
enforcement status **Disabled**, which does nothing: switch it to **Active** before you click
**Create**. Requiring status checks or pull requests is optional;
only require the CI check once you have seen it pass, or it will block every merge. Requiring
pull requests means you can no longer push to `main` directly, also as the only maintainer,
unless you add yourself to the ruleset's bypass list. GitHub's description of rulesets:
<https://docs.github.com/repositories/configuring-branches-and-merges-in-your-repository/managing-rulesets/about-rulesets>.

## 3. Check the result

```bash
python3 -m venv /tmp/try && /tmp/try/bin/pip install verified-nondim
/tmp/try/bin/nondim --version
/tmp/try/bin/nondim tour
/tmp/try/bin/nondim init-lean /tmp/try/proofs
cd /tmp/try/proofs && lake exe cache get && lake build
```

## What is in the package

* The wheel contains the `nondim` Python package and, inside it, a copy of the Lean project
  (`nondim/_lean_template/`), which is what `nondim init-lean` copies out.
* The source archive adds `docs/`, `examples/`, `reports/`, the tests and these scripts.
* Core dependencies: `sympy`, `numpy`, `scipy`. `matplotlib` is optional
  (`pip install "verified-nondim[plots]"`) and only draws the experiment's figure.

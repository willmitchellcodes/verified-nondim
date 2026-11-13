#!/usr/bin/env bash
# Create the GitHub repository under YOUR account and push this project to it.
#
#   ./scripts/publish_github.sh             # asks before anything becomes public
#   DRY_RUN=1 ./scripts/publish_github.sh   # show what would happen, change nothing online
#
# Uses your own git identity and your own GitHub login (the `gh` CLI if installed,
# otherwise it prints the two commands to run after creating the repository on github.com).
set -euo pipefail
cd "$(dirname "$0")/.."

REPO_NAME="${REPO_NAME:-verified-nondim}"
VISIBILITY="${VISIBILITY:-public}"          # public | private
DRY_RUN="${DRY_RUN:-0}"
DESCRIPTION="Nondimensionalize ODE models automatically, with certificates that Lean 4 checks"

say()  { printf '\n== %s\n' "$*"; }
fail() { printf '\nERROR: %s\n' "$*" >&2; exit 1; }
online() { if [ "$DRY_RUN" = 1 ]; then echo "[dry-run] $*"; else "$@"; fi; }

command -v git >/dev/null || fail "git is not installed. On macOS run: xcode-select --install"
[ -n "$(git config user.name || true)" ] && [ -n "$(git config user.email || true)" ] || fail \
  'git does not know who you are yet. Run these two lines with your details, then re-run this script:
    git config --global user.name  "Your Name"
    git config --global user.email "you@example.com"   (GitHub offers a private noreply address under Settings > Emails)'

say "1/4 Which GitHub account?"
OWNER="${GITHUB_OWNER:-}"
HAVE_GH=0
if command -v gh >/dev/null && gh auth status >/dev/null 2>&1; then
  HAVE_GH=1
  [ -n "$OWNER" ] || OWNER="$(gh api user -q .login)"
elif command -v gh >/dev/null; then
  echo "The gh CLI is installed but not logged in. Run 'gh auth login' and re-run, or continue without it."
fi
if [ -z "$OWNER" ]; then read -r -p "Your GitHub user name: " OWNER; fi
echo "Account: $OWNER    Repository: $OWNER/$REPO_NAME ($VISIBILITY)    Commits as: $(git config user.name) <$(git config user.email)>"

say "2/4 Fill in the repository address (pyproject.toml, README links)"
python3 scripts/set_repo_url.py "$OWNER" "$REPO_NAME"

[ -d .github/workflows ] || echo "Note: automatic testing is not switched on (no .github/workflows). See docs/RELEASING.md to enable it."

say "3/4 Commit"
[ -d .git ] || git init -q -b main
git add -A
echo "Files to publish: $(git ls-files | wc -l | tr -d ' ')   (not published: .venv, lean/.lake, logs, docs/PROPOSAL_NOTES.md)"
if git diff --cached --quiet; then
  echo "Nothing new to commit."
else
  git commit -q -m "verified-nondim 0.1.0: nondimensionalization with Lean-checked certificates" \
    -m "Python solver (scaling symmetries, constraints, identifiability), Lean 4 checker library and generated certificates, tests for both and for the bridge between them." \
    -m "Co-Authored-By: Claude Fable 5.2 <noreply@anthropic.com>
Claude-Session: https://claude.ai/code/session_01JEVmwSyEP8RmMWQ7pQsxF5"
  git log --oneline -1
fi

say "4/4 Push to GitHub"
if git remote get-url origin >/dev/null 2>&1; then
  online git push -u origin main
elif [ "$HAVE_GH" = 1 ]; then
  if [ "$DRY_RUN" != 1 ]; then
    read -r -p "Create the $VISIBILITY repository $OWNER/$REPO_NAME and push? Type yes to continue: " answer
    [ "$answer" = "yes" ] || { echo "Stopped. Nothing was pushed; the commit is saved locally."; exit 0; }
  fi
  online gh repo create "$OWNER/$REPO_NAME" "--$VISIBILITY" --source=. --remote=origin --description "$DESCRIPTION" --push
else
  cat <<MSG
The gh CLI is not available, so finish in the browser:
  1. Open https://github.com/new and create "$REPO_NAME" ($VISIBILITY). Do NOT add a README, license or .gitignore.
  2. Then run:
       git remote add origin https://github.com/$OWNER/$REPO_NAME.git
       git push -u origin main
MSG
  exit 0
fi
[ "$DRY_RUN" = 1 ] || echo "Done: https://github.com/$OWNER/$REPO_NAME   (CI results appear under the Actions tab)"

#!/usr/bin/env bash
# One-time setup on macOS (safe to re-run). Creates the Python environment, downloads
# Lean + prebuilt Mathlib, then runs every check. Output is also saved to setup.log.
set -uo pipefail
cd "$(dirname "$0")"
exec > >(tee setup.log) 2>&1

echo "== 1/5 Python environment (.venv) =="
python3 -m venv .venv && source .venv/bin/activate
pip install --upgrade pip -q
pip install -e ".[dev]" -q || { echo "pip install failed"; exit 1; }   # installs the `nondim` command

echo "== 2/5 Python tests (without Lean) =="
(cd python && python -m pytest -q -m "not lean") || echo "PYTHON TESTS FAILED (see above)"

echo "== 3/5 Lean toolchain + Mathlib cache (first run downloads ~5 GB) =="
export PATH="$HOME/.elan/bin:$PATH"
if ! command -v lake >/dev/null 2>&1; then
  curl -sSfL https://raw.githubusercontent.com/leanprover/elan/master/elan-init.sh | sh -s -- -y --default-toolchain none
fi
(cd lean && lake exe cache get) || { echo "Mathlib cache download failed"; exit 1; }

echo "== 4/5 Lean build: certificates, proofs, Lean unit tests =="
(cd lean && lake build 2>&1 | tee ../lean_build.log; exit "${PIPESTATUS[0]}")
lean_status=$?

echo "== 5/5 Bridge tests: Lean must accept good certificates and reject corrupted ones =="
(cd python && python -m pytest -q -m lean)
bridge_status=$?

echo
if [ "$lean_status" -eq 0 ] && [ "$bridge_status" -eq 0 ]; then
  echo "ALL CHECKS PASSED.  Next:  source .venv/bin/activate && nondim tour"
else
  echo "Something failed: lean build status $lean_status (lean_build.log), bridge tests status $bridge_status."
fi

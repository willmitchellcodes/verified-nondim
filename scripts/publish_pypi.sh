#!/usr/bin/env bash
# Build the package and upload it with YOUR PyPI account.
#
#   ./scripts/publish_pypi.sh check      # build + validate only (default; uploads nothing)
#   ./scripts/publish_pypi.sh testpypi   # upload to test.pypi.org (a sandbox: do this first)
#   ./scripts/publish_pypi.sh pypi       # upload to pypi.org (permanent: a version can never be re-uploaded)
#
# Uploading asks for an API token: user name "__token__", password = the token from
# https://test.pypi.org/manage/account/token/ or https://pypi.org/manage/account/token/ .
# The token-free alternative (a GitHub Release triggers the upload) is in docs/RELEASING.md.
set -euo pipefail
cd "$(dirname "$0")/.."
TARGET="${1:-check}"
PY="python3"; [ -x .venv/bin/python ] && PY=".venv/bin/python"

"$PY" -m pip install -q --upgrade build twine
rm -rf dist
"$PY" -m build
"$PY" -m twine check --strict dist/*
VERSION="$("$PY" -c 'import re,pathlib; print(re.search(r"__version__ = \"(.+?)\"", pathlib.Path("python/nondim/__init__.py").read_text())[1])')"
echo; ls -lh dist; echo

case "$TARGET" in
  check)
    echo "Built and validated verified-nondim $VERSION. Nothing was uploaded." ;;
  testpypi)
    "$PY" -m twine upload --repository testpypi dist/*
    echo "Try it:  pip install --index-url https://test.pypi.org/simple/ --extra-index-url https://pypi.org/simple/ verified-nondim==$VERSION" ;;
  pypi)
    read -r -p "Upload verified-nondim $VERSION to the real PyPI? This cannot be undone. Type yes: " answer
    [ "$answer" = "yes" ] || { echo "Stopped. Nothing was uploaded."; exit 0; }
    "$PY" -m twine upload dist/*
    echo "Published: https://pypi.org/project/verified-nondim/$VERSION/" ;;
  *) echo "usage: $0 [check|testpypi|pypi]"; exit 2 ;;
esac

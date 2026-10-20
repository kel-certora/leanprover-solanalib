#!/usr/bin/env bash
# Textual style checks for Lean source files.
#
# Catches conventions Lean's own linters can't see across files:
#   - copyright header presence with the expected Authors line
#
# Compatible with macOS bash 3.2 (no mapfile / readarray). Exits 0 if clean,
# 1 if any rule trips.

set -u
set -o pipefail

cd "$(dirname "$0")/.."

EXIT=0
RED=$'\033[31m'
RESET=$'\033[0m'

fail() {
  printf '%s%s%s\n' "$RED" "$1" "$RESET" >&2
  EXIT=1
}

check_file() {
  local f=$1
  local header
  header=$(head -n 6 "$f")

  # ---- Copyright header ----
  if ! grep -q '^Copyright (c) [0-9]\{4\} .* All rights reserved\.$' <<<"$header"; then
    fail "$f: missing 'Copyright (c) YYYY <Owner>. All rights reserved.' line"
  fi
  if ! grep -q '^Authors: .* Contributors$' <<<"$header"; then
    fail "$f: header must end with 'Authors: <Project> Contributors' (no personal names)"
  fi
  if ! grep -q '^Released under Apache 2.0 license' <<<"$header"; then
    fail "$f: header missing Apache 2.0 license line"
  fi
}

COUNT=0
while IFS= read -r f; do
  check_file "$f"
  COUNT=$((COUNT + 1))
done < <(
  find Solanalib SolanalibTest -name '*.lean' 2>/dev/null
  [ -f Solanalib.lean ] && echo Solanalib.lean
  [ -f SolanalibTest.lean ] && echo SolanalibTest.lean
)

if [ $EXIT -eq 0 ]; then
  echo "lint-style: $COUNT files OK"
fi
exit $EXIT

#!/usr/bin/env bash
# Self-check gate for the YangMills3D Lean repository.
#
# Gates:
#   1. Source hygiene: no forbidden tokens (sorry/admit/native_decide) and no
#      `axiom` declarations in the repository's own Lean sources.
#   2. Cold rebuild: delete .lake/build (our own artifacts ONLY) and rebuild
#      from scratch with `lake build`; must exit 0.
#   3. Axiom inventory: `lake env lean YangMills3D/SelfCheck.lean` must print
#      at least 40 "depends on axioms" lines, and every such line must list
#      exactly the standard axioms [propext, Classical.choice, Quot.sound]
#      (the subset form [propext, Quot.sound] is also accepted).
#
# A full pass prints the final line: SELF-CHECK: PASS
#
# NOTE: `.lake/packages` is a Windows junction to the prebuilt offline Mathlib
# cache (../hermes-lean/.lake/packages). This script NEVER touches it; the
# only deletion performed is `.lake/build`. Never run `lake update`.

set -euo pipefail

cd "$(dirname "$0")/.."

FAIL=0

# ---------------------------------------------------------------- Gate 1 ----
echo "== GATE 1: source hygiene (forbidden tokens / new axioms) =="

# The repository's own Lean sources only: .lake is excluded because
# .lake/packages is the shared prebuilt Mathlib cache, not part of the
# delivery.
if grep -rnE 'sorry|admit|native_decide' --include='*.lean' --exclude-dir='.lake' .; then
  echo "FAIL GATE 1a: forbidden token (sorry/admit/native_decide) found above."
  FAIL=1
else
  echo "PASS GATE 1a: no 'sorry' / 'admit' / 'native_decide' in any Lean source."
fi

if grep -rnE '^[[:space:]]*axiom ' --include='*.lean' --exclude-dir='.lake' .; then
  echo "FAIL GATE 1b: 'axiom' declaration found above."
  FAIL=1
else
  echo "PASS GATE 1b: no 'axiom' declarations in any Lean source."
fi

# ---------------------------------------------------------------- Gate 2 ----
echo "== GATE 2: cold rebuild (rm -rf .lake/build; lake build) =="

# ONLY our own build artifacts are removed. .lake/packages is a junction to
# the shared prebuilt Mathlib cache and must never be touched.
rm -rf .lake/build

if lake build; then
  echo "PASS GATE 2: cold 'lake build' exited 0."
else
  echo "FAIL GATE 2: cold 'lake build' exited non-zero."
  FAIL=1
fi

# ---------------------------------------------------------------- Gate 3 ----
echo "== GATE 3: axiom inventory (SelfCheck.lean) =="

AXOUT=""
if ! AXOUT="$(lake env lean YangMills3D/SelfCheck.lean 2>&1)"; then
  echo "FAIL GATE 3: 'lake env lean YangMills3D/SelfCheck.lean' exited non-zero."
  FAIL=1
fi

# Extract the bracketed axiom list from every "depends on axioms" info line
# (strip any CR so Windows line endings cannot break exact matching).
AXLINES="$(printf '%s\n' "$AXOUT" | tr -d '\r' \
  | sed -nE 's/.*depends on axioms:?[[:space:]]*(\[[^]]*\]).*/\1/p')"
COUNT="$(printf '%s\n' "$AXLINES" | grep -c . || true)"
BAD="$(printf '%s\n' "$AXLINES" \
  | grep -vxF -e '[propext, Classical.choice, Quot.sound]' -e '[propext, Quot.sound]' \
  || true)"

echo "Axiom lines counted: $COUNT (requirement: >= 40)"

if [ "$COUNT" -ge 40 ]; then
  echo "PASS GATE 3a: axiom line count >= 40."
else
  echo "FAIL GATE 3a: axiom line count $COUNT is below 40."
  FAIL=1
fi

if [ -z "$BAD" ]; then
  echo "PASS GATE 3b: every 'depends on axioms' line is exactly"
  echo "  [propext, Classical.choice, Quot.sound]  or  [propext, Quot.sound]."
else
  echo "FAIL GATE 3b: offending axiom lines:"
  printf '%s\n' "$BAD"
  FAIL=1
fi

# ---------------------------------------------------------------- Verdict ---
if [ "$FAIL" -eq 0 ]; then
  echo "SELF-CHECK: PASS"
else
  echo "SELF-CHECK: FAIL"
  exit 1
fi

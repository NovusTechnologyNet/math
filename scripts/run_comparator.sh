#!/usr/bin/env bash
# Sandboxed verification of this repository, for a Linux machine.
#
#   scripts/run_comparator.sh [comparator.json]
#
# Needs: git, curl, bubblewrap (`bwrap`, with unprivileged user namespaces), and elan
# (https://elan.lean-lang.org). It deletes this project's own build products first, so that
# `lake comparator` builds the challenge and the solution inside its sandbox; the compiled
# Mathlib is fetched from the community cache. Three steps, each printing its exit code:
#   1. lake comparator            statement identical, permitted axioms only, kernel replay
#   2. lake comparator --paranoid the same through every checker bundled with Lean
#   3. lake build                 the whole library
# Never run the comparator with the sandbox disabled: that verdict does not count.
set -u
cd "$(dirname "$0")/.."
export PATH="$HOME/.elan/bin:$PATH"
CONFIG="${1:-comparator.json}"

echo "commit:    $(git rev-parse HEAD)"
echo "toolchain: $(cat lean-toolchain)"
echo "config:    $CONFIG"
lake --version || exit 2
command -v bwrap >/dev/null || { echo "bwrap not found"; exit 2; }

rm -rf .lake/build
lake exe cache get || exit 2

echo "== 1. lake comparator"
( time lake comparator --config "$CONFIG" ) 2>&1 | tail -8
echo "exit code: ${PIPESTATUS[0]}"

echo "== 2. lake comparator --paranoid"
( time lake comparator --paranoid --config "$CONFIG" ) 2>&1 | tail -24
echo "exit code: ${PIPESTATUS[0]}"

echo "== 3. lake build"
( time lake build ) 2>&1 | tail -5
echo "exit code: ${PIPESTATUS[0]}"

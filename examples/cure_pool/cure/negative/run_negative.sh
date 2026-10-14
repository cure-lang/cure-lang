#!/usr/bin/env bash
#
# run_negative.sh -- prove the pool's compile-time guarantees are real.
#
# Each fixture under this directory MUST fail to compile, with a specific
# diagnostic. This script concatenates the pool core with each fixture into an
# isolated temporary directory and runs `cure run` there; a fixture passes when
# the compiler REJECTS it with the expected diagnostic code.
#
# Running from an isolated directory matters: `cure run` inside the project
# would also load `lib/pool_core.cure` and report a duplicate module identity
# before it ever reaches the fixture's own error. The pool core is therefore
# inlined next to each fixture, with no project manifest in scope.
#
# Usage:  ./run_negative.sh [path-to-cure]
# Exit:   0 when every fixture is rejected as expected, 1 otherwise.

set -u

CURE="${1:-cure}"
HERE="$(cd "$(dirname "$0")" && pwd)"
CORE="$HERE/../lib/pool_core.cure"
TMP="$(mktemp -d)"
trap 'rm -rf "$TMP"' EXIT

pass=0
fail=0

check() {
  local name="$1" expected="$2"
  local dir="$TMP/$name"
  mkdir -p "$dir"
  local src="$dir/fixture.cure"
  cat "$CORE" "$HERE/$name.cure" > "$src"

  local out status
  out="$(cd "$dir" && "$CURE" run "$src" 2>&1)"
  status=$?

  if [ "$status" -eq 0 ]; then
    echo "FAIL  $name: compiled successfully (expected $expected)"
    fail=$((fail + 1))
    return
  fi

  if printf '%s' "$out" | grep -q "$expected"; then
    echo "ok    $name: rejected with $expected"
    pass=$((pass + 1))
  else
    echo "FAIL  $name: rejected, but not with $expected"
    printf '%s\n' "$out" | head -6
    fail=$((fail + 1))
  fi
}

echo "cure_pool: negative fixtures (each MUST be rejected)"
echo "----------------------------------------------------"

check checkout_empty "E093"
check double_return  "E117"
check dropped_lease  "E117"

echo "----------------------------------------------------"
echo "$pass passed, $fail failed"

[ "$fail" -eq 0 ]

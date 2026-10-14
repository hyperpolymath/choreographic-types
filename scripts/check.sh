#!/usr/bin/env bash
# SPDX-License-Identifier: MPL-2.0
# The proof gate: core proofs, the echo-additive instance, and the expected
# rejections.  Pattern: residual-evidence-types / epistemic-types.
#
# Siblings are fetched at pinned commits by scripts/fetch-siblings.sh and
# passed as explicit -i paths under --no-libraries, so no library resolution
# happens and nothing outside the pins is ever read.  Every check runs with
# --ignore-interfaces (no stale .agdai can stand in for a proof), --double-check
# (the kernel re-verifies every term) and -W error (a warning is a failure;
# UnsupportedIndexedMatch is silenced because agda-stdlib emits it under
# --without-K and its .agda-lib flags are not read under --no-libraries).
# Ledger E-4.
set -euo pipefail
cd -- "$(dirname -- "${BASH_SOURCE[0]}")/.."
export LC_ALL="${LC_ALL:-C.UTF-8}"

prover="${AGDA:-agda}"
expected_version="${AGDA_VERSION:-2.6.4.3}"
deps="${DEPENDENCIES_DIR:-_build/dependencies}"
ra="${RESOURCE_ALGEBRA_SRC:-$deps/resource-algebra/src}"
et="${EPISTEMIC_TYPES_SRC:-$deps/epistemic-types/src}"
echo_src="${ECHO_TYPES_SRC:-$deps/echo-types/proofs/agda}"
stdlib="${AGDA_STDLIB_SRC:-/usr/share/agda-stdlib/src}"

# require_dir <path> <what> <how to get it>
# Fails the gate with a usable message when an include path is missing.
# Returns success if <path> is a directory; otherwise exits the script with
# status 1. <what> names the missing sources; <how to get it> suggests a remedy.
require_dir() {
  test -d "$1" || { echo "ERROR: $2 not found at $1 ($3)" >&2; exit 1; }
}
require_dir "$ra"       'resource-algebra sources' 'run scripts/fetch-siblings.sh or set RESOURCE_ALGEBRA_SRC'
require_dir "$et"       'epistemic-types sources'  'run scripts/fetch-siblings.sh or set EPISTEMIC_TYPES_SRC'
require_dir "$echo_src" 'echo-types sources'       'run scripts/fetch-siblings.sh or set ECHO_TYPES_SRC'
require_dir "$stdlib"   'agda-stdlib sources'      'install agda-stdlib=2.1-4 or set AGDA_STDLIB_SRC'

version="$("$prover" --version)"
echo "$version"
if [ "$version" != "Agda version $expected_version" ]; then
  echo "ERROR: expected 'Agda version $expected_version' (the Debian pin); set AGDA_VERSION to check with another" >&2
  exit 1
fi

# 0. Trusted base: the only postulates in the repository are the sanctioned
#    interface declarations of the RapidNJ application target, which is not
#    part of the gate (.cicd-hygiene-allow).  Nothing under src/ or tests/
#    may postulate; the target keeps exactly one `postulate` block.
if stray="$(grep -rlw --include='*.agda' postulate src tests)"; then
  echo "ERROR: postulate outside the sanctioned application target:" >&2
  echo "$stray" >&2
  exit 1
fi
blocks="$(grep -cE '^[[:space:]]*postulate\b' applications/rapidnj-two-thread.agda || true)"
if [ "$blocks" != 1 ]; then
  echo "ERROR: applications/rapidnj-two-thread.agda has $blocks postulate blocks, expected exactly 1" >&2
  exit 1
fi
echo 'PASS: trusted base (no postulates under src/ or tests/; one block in the application target)'

flags=(--safe --without-K --no-libraries --ignore-interfaces --double-check
       -W error -W noUnsupportedIndexedMatch
       -i src -i "$ra" -i "$et")

# 1. The keystone development: builtins only, no standard library anywhere.
"$prover" "${flags[@]}" src/Choreographic/All.agda
echo 'PASS: core proofs (Choreographic.All, builtins only)'

# 2. The echo-additive instance: imports echo-types' own Grade.agda, which
#    needs agda-stdlib, so it is a separate root rather than part of All.
"$prover" "${flags[@]}" -i "$echo_src" -i "$stdlib" src/Choreographic/Base/EchoAdditive.agda
echo 'PASS: echo-additive instance (Choreographic.Base.EchoAdditive, echo-types imported)'

# 3. Expected rejections: each fixture must fail AT its `invalid` declaration
#    with a type mismatch, never for a missing import or a parse error.
mkdir -p _build/check-logs
shopt -s nullglob
rejects=(tests/reject/*.agda)
shopt -u nullglob
if (( ${#rejects[@]} == 0 )); then
  echo 'ERROR: no expected-rejection modules found under tests/reject' >&2
  exit 1
fi
for file in "${rejects[@]}"; do
  name="$(basename -- "$file" .agda)"
  log="_build/check-logs/$name.log"
  if "$prover" "${flags[@]}" -i tests/reject "$file" >"$log" 2>&1; then
    cat "$log"
    echo "ERROR: invalid proof accepted: $name" >&2
    exit 1
  fi
  invalid_line="$(grep -nE '^invalid ' "$file" | head -1 | cut -d: -f1)"
  diag_line="$(grep -oE "/$name\.agda:[0-9]+,[0-9]+" "$log" | head -1 | sed -E 's/.*:([0-9]+),.*/\1/')"
  if [ -z "$invalid_line" ] || [ -z "$diag_line" ] || [ "$diag_line" -lt "$invalid_line" ] ||
     ! grep -q 'when checking that' "$log" ||
     grep -Eq 'Not in scope|Failed to find|Unsolved|Parse error' "$log"; then
    cat "$log"
    echo "ERROR: unexpected failure while checking $name" >&2
    exit 1
  fi
  echo "PASS: rejected $name at its invalid declaration"
done
echo "PASS: core proofs, echo-additive instance and all ${#rejects[@]} expected rejections"

#!/usr/bin/env bash
# SPDX-License-Identifier: MPL-2.0
# Certifies which algebra laws K-CUT-LOSS depends on: KCut.agda, and its
# asynchronous counterpart Async.agda, are checked against tests/minimal-laws,
# a Core whose record has ONLY ⊕-idempotence and ⊗-left-unit.  If this
# passes, no other law is used (PROOF-STATUS K-4, Y-2).
# Use the same warning policy as check.sh: warnings fail the gate, except
# UnsupportedIndexedMatch from imported sources under --without-K.
set -euo pipefail
cd -- "$(dirname -- "${BASH_SOURCE[0]}")/.."
export LC_ALL="${LC_ALL:-C.UTF-8}"
prover="${AGDA:-agda}"
ra="${RESOURCE_ALGEBRA_SRC:-_build/dependencies/resource-algebra/src}"
tmp="$(mktemp -d)"; trap 'rm -rf "$tmp"' EXIT
mkdir -p "$tmp/ResourceAlgebra"
cp "$ra/ResourceAlgebra/Prelude.agda" "$tmp/ResourceAlgebra/"
cp tests/minimal-laws/ResourceAlgebra/Core.agda "$tmp/ResourceAlgebra/"
flags=(--safe --without-K --cubical-compatible --no-libraries --ignore-interfaces --double-check
       -W error -W noUnsupportedIndexedMatch -i src -i "$tmp")
"$prover" "${flags[@]}" src/Choreographic/KCut.agda
echo "PASS: K-CUT-LOSS typechecks with only ⊕-idempotence and ⊗-left-unit"
"$prover" "${flags[@]}" src/Choreographic/Async.agda
echo "PASS: asynchronous K-CUT-LOSS typechecks with only ⊕-idempotence and ⊗-left-unit"

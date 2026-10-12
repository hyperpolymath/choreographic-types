#!/usr/bin/env bash
# SPDX-License-Identifier: MPL-2.0
# Fetch the compared sibling at a pinned commit (pattern: residual-evidence-types).
# FILL IN the commit once hyperpolymath/resource-algebra is pushed.
set -euo pipefail
cd -- "$(dirname -- "${BASH_SOURCE[0]}")/.."
RESOURCE_ALGEBRA_COMMIT="${RESOURCE_ALGEBRA_COMMIT:-b2c9f1f6bc7ed7cc83c7573014cdf88d49d2a881}"
EPISTEMIC_TYPES_COMMIT="${EPISTEMIC_TYPES_COMMIT:-495db9c}"   # Warrant/Base/Access as read 2026-10-12
mkdir -p _build/dependencies
if [ ! -d _build/dependencies/epistemic-types ]; then
  git clone --quiet https://github.com/hyperpolymath/epistemic-types.git _build/dependencies/epistemic-types
fi
git -C _build/dependencies/epistemic-types fetch --quiet origin
git -C _build/dependencies/epistemic-types checkout --quiet "$EPISTEMIC_TYPES_COMMIT"
echo "epistemic-types at $(git -C _build/dependencies/epistemic-types rev-parse --short HEAD)"
if [ ! -d _build/dependencies/resource-algebra ]; then
  git clone --quiet https://github.com/hyperpolymath/resource-algebra.git _build/dependencies/resource-algebra
fi
git -C _build/dependencies/resource-algebra fetch --quiet origin
git -C _build/dependencies/resource-algebra checkout --quiet "$RESOURCE_ALGEBRA_COMMIT"
echo "resource-algebra at $(git -C _build/dependencies/resource-algebra rev-parse --short HEAD)"

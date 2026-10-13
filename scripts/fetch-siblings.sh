#!/usr/bin/env bash
# SPDX-License-Identifier: MPL-2.0
# Fetch every sibling the proofs import, each at ONE pinned commit, into
# _build/dependencies/<repo>.  Pattern: residual-evidence-types.
#
# Each pin is a full 40-character commit SHA, fetched directly (no branch,
# no history) and verified after checkout, so an upstream force-push can
# never change what this gate checks.  Override a pin only through its
# environment variable, and only deliberately.
#
#   resource-algebra  the ResourceAlgebra port: Core, Loss (min-plus),
#                     MaxPlus, HWM — same kernel, imported not re-proved
#   epistemic-types   Warrant / SoundWarrant / Access — imported, not copied
#   echo-types        experimental/echo-additive/Grade.agda, the echo-additive
#                     ℕ ∪ {∞} grade; the one sibling that needs agda-stdlib
set -euo pipefail
cd -- "$(dirname -- "${BASH_SOURCE[0]}")/.."

RESOURCE_ALGEBRA_COMMIT="${RESOURCE_ALGEBRA_COMMIT:-b2c9f1f6bc7ed7cc83c7573014cdf88d49d2a881}"
EPISTEMIC_TYPES_COMMIT="${EPISTEMIC_TYPES_COMMIT:-495db9cca003e12066a3cb9c9f2d7afa1a953aec}"
ECHO_TYPES_COMMIT="${ECHO_TYPES_COMMIT:-da140cc26fd174b20d5d7fcfafcb4febd3276ff3}"
DEPENDENCIES_DIR="${DEPENDENCIES_DIR:-_build/dependencies}"

# fetch_pinned <repo> <commit>
# Fetches exactly <commit> of hyperpolymath/<repo> into $DEPENDENCIES_DIR/<repo>
# (reusing a checkout that already holds the commit) and fails unless HEAD
# is then that commit AND the tree is exactly that commit: a reused checkout
# with edited or added source would let the gate read something other than
# the pin.  Agda's own .agdai interface files are the one tolerated residue;
# the gate ignores them (--ignore-interfaces).
fetch_pinned() {
  local repo="$1" commit="$2" dir="$DEPENDENCIES_DIR/$1" head dirty
  if ! [[ "$commit" =~ ^[0-9a-f]{40}$ ]]; then
    echo "ERROR: $repo pin must be a full 40-character commit SHA, got '$commit'" >&2
    exit 1
  fi
  if [ ! -d "$dir/.git" ]; then
    git init --quiet "$dir"
    git -C "$dir" remote add origin "https://github.com/hyperpolymath/$repo.git"
  fi
  if ! git -C "$dir" cat-file -e "$commit^{commit}" 2>/dev/null; then
    git -C "$dir" fetch --quiet --depth 1 origin "$commit"
  fi
  git -C "$dir" checkout --quiet --detach "$commit"
  head="$(git -C "$dir" rev-parse HEAD)"
  if [ "$head" != "$commit" ]; then
    echo "ERROR: $repo pin mismatch: want $commit got $head" >&2
    exit 1
  fi
  dirty="$(git -C "$dir" status --porcelain --untracked-files=all -- . ':(exclude,glob)**/*.agdai')"
  if [ -n "$dirty" ]; then
    echo "ERROR: $repo checkout at $dir is not exactly $commit; remove the directory and re-run:" >&2
    echo "$dirty" >&2
    exit 1
  fi
  echo "$repo at $head"
}

mkdir -p "$DEPENDENCIES_DIR"
fetch_pinned resource-algebra "$RESOURCE_ALGEBRA_COMMIT"
fetch_pinned epistemic-types  "$EPISTEMIC_TYPES_COMMIT"
fetch_pinned echo-types       "$ECHO_TYPES_COMMIT"

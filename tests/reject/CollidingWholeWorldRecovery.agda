{-# OPTIONS --safe --without-K #-}
-- SPDX-License-Identifier: MPL-2.0
-- SPDX-FileCopyrightText: 2026 Jonathan D.A. Jewell
-- Ledger PR-2.
module CollidingWholeWorldRecovery where

open import ResourceAlgebra.Prelude
open import Agda.Builtin.Maybe using (just)
open import EpistemicTypes.PartialRecovery using (PartialRecovery)
open import PartialRecoveryBoundary

-- A constant decoder cannot satisfy the whole-world roundtrip law.
invalid : PartialRecovery Constant.localRetention
PartialRecovery.decode invalid _ _ = just delivered
PartialRecovery.roundtrip invalid w = refl

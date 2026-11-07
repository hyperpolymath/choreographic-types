{-# OPTIONS --safe --without-K #-}
-- SPDX-License-Identifier: MPL-2.0
-- SPDX-FileCopyrightText: 2026 Jonathan D.A. Jewell
-- Ledger PR-2.
module RevealingResidueCollision where

open import ResourceAlgebra.Prelude
open import EpistemicTypes.EchoBridge using (Retention)
open import PartialRecoveryBoundary

-- Equal sender views do not establish equality of a revealing residue.
invalid : Retention.retain Revealing.localRetention delivered ≡
          Retention.retain Revealing.localRetention in-flight
invalid = refl

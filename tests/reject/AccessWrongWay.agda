{-# OPTIONS --safe --without-K #-}
-- SPDX-License-Identifier: MPL-2.0
-- SPDX-FileCopyrightText: 2026 Jonathan D.A. Jewell
-- Ledger T-5.
module AccessWrongWay where
open import ResourceAlgebra.Prelude
open import ResourceAlgebra.Instances.MaxPlus
open import Choreographic.Global     MaxPlus
open import Choreographic.Projection MaxPlus
open import Choreographic.Kripke     MaxPlus
open import Choreographic.Transport  MaxPlus

-- Must fail: party 2 sees nothing of a protocol between 0 and 1, so 2 does
-- NOT see at least what 1 sees.  Access runs one way only; knowledge
-- cannot be transported from a party that sees more to one that sees less.
G : Global
G = msg 0 1 (val 1) (msg 0 1 (val 1) end)

open Frame G
open Over G

invalid : 1 ⊑ 2
invalid w w' _ = refl

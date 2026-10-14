{-# OPTIONS --safe --without-K #-}
-- SPDX-License-Identifier: MPL-2.0
-- SPDX-FileCopyrightText: 2026 Jonathan D.A. Jewell
-- Ledger W-7.
module GlobalGradeKnown where
open import ResourceAlgebra.Prelude
open import ResourceAlgebra.Instances.MaxPlus
open import Choreographic.Global     MaxPlus
open import Choreographic.Projection MaxPlus
open import Choreographic.Kripke     MaxPlus

-- Must fail: party 2 sees nothing of a protocol between 0 and 1, so it
-- cannot know the global grade — only a bound on it (Bound.agda).  The
-- "cannot determine" clause of K-CUT-WARRANT is not decorative.
G : Global
G = msg 0 1 (val 1) (msg 0 1 (val 1) end)

open Frame G

w₁ : World
w₁ = cont-msg stop , λ _ → cont-msg stop

invalid : Knows 2 w₁ (λ w' → grade (G ↾ cut w') ≡ grade (G ↾ cut w₁))
invalid w' _ = refl

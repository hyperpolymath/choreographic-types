{-# OPTIONS --safe --without-K #-}
-- SPDX-License-Identifier: MPL-2.0
-- SPDX-FileCopyrightText: 2026 Jonathan D.A. Jewell
module UnprojectableChoice where
open import ResourceAlgebra.Prelude
open import ResourceAlgebra.Instances.Loss
open import Choreographic.Global     Loss
open import Choreographic.Projection Loss
open import Choreographic.Local      Loss

-- Must fail: party 2 is outside the choice 0 → 1, and the two branches
-- project to different local types for 2 (recv at loss 2 vs recv at loss
-- 1).  Plain merge is refused, and the equality K-CUT-LOSS promises is
-- false here: restricted global grade fin 1 (min of the branches), local
-- grade fin 2 (the left representative).  The Projectable side-condition
-- is load-bearing, not decorative.
G : Global
G = choice 0 1 (fin 0) (msg 1 2 (fin 2) end) (msg 1 2 (fin 1) end)

invalid : grade↾ 2 G ≡ lgrade (proj 2 G)
invalid = refl

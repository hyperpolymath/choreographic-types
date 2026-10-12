{-# OPTIONS --safe --without-K #-}
-- SPDX-License-Identifier: MPL-2.0
-- SPDX-FileCopyrightText: 2026 Jonathan D.A. Jewell
module InconsistentCut where
open import ResourceAlgebra.Prelude
open import ResourceAlgebra.Instances.Loss
open import Choreographic.Global     Loss
open import Choreographic.Projection Loss
open import Choreographic.Local      Loss

-- Must fail: G is projectable for party 2 (both branches identical), but
-- the cut truncates the left branch after two messages and the right after
-- one, so the frontier is inconsistent for 2.  Restricted global grade at
-- the cut is fin 1 (min 2 1); the local timeline cut (left representative)
-- reads fin 2.  The Consistent side-condition is load-bearing.
G : Global
G = choice 0 1 (fin 0) (msg 1 2 (fin 1) (msg 1 2 (fin 1) end))
                       (msg 1 2 (fin 1) (msg 1 2 (fin 1) end))

c : Cut G
c = cont-choice (cont-msg (cont-msg stop)) (cont-msg stop)

invalid : grade↾ 2 (G ↾ c) ≡ lgrade (proj 2 G ↾ₗ cutproj 2 c)
invalid = refl

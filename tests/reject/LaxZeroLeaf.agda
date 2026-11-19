{-# OPTIONS --safe --without-K #-}
-- SPDX-License-Identifier: MPL-2.0
-- SPDX-FileCopyrightText: 2026 Jonathan D.A. Jewell
-- Ledger KM-8.
module LaxZeroLeaf where
open import ResourceAlgebra.Prelude
open import ResourceAlgebra.Core
open import ResourceAlgebra.Instances.HWM     using (HWM)
open import ResourceAlgebra.Instances.MaxPlus using (MaxPlus)
open import ResourceAlgebra.Morphism          using (LaxHom; peak-lax)
open import Agda.Builtin.List                 using (List; []; _∷_)

-- Must fail: the lax bound h (fold xs) ≼ fold (map h xs) does NOT hold for a
-- ⊕-fold over lists, whose empty case is 𝟘.  A LaxHom gives only
-- B.𝟘 ≼ h A.𝟘, the opposite direction: peak-lax sends HWM's 𝟘 (its 𝟙,
-- peak 0) to val 0, while MaxPlus's 𝟘 is bot.  KCutTransport needs no side
-- condition because grade and grade↾ never use 𝟘 as a base case: end and
-- `outside` give 𝟙 and choice is binary, so the lax proof never needs map-𝟘.
-- (In HWM, where 𝟘 ≡ 𝟙, a grade can equal 𝟘; the bound still holds because
-- the step uses map-𝟙, not map-𝟘.)
altFold : (R : ResourceAlgebra) → List (ResourceAlgebra.Grade R) → ResourceAlgebra.Grade R
altFold R []       = ResourceAlgebra.𝟘 R
altFold R (x ∷ xs) = ResourceAlgebra._⊕_ R x (altFold R xs)

invalid : ResourceAlgebra._≼_ MaxPlus (LaxHom.map peak-lax (altFold HWM [])) (altFold MaxPlus [])
invalid = refl

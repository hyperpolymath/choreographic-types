{-# OPTIONS --safe --without-K --cubical-compatible --exact-split --no-sized-types --no-guardedness #-}
-- SPDX-License-Identifier: MPL-2.0
-- SPDX-FileCopyrightText: 2026 Jonathan D.A. Jewell
-- Ledger WC-4, WC-5.
module EmptyDataWarrant where

open import ResourceAlgebra.Prelude
open import ResourceAlgebra.Instances.MaxPlus using (MaxPlus; MaxPlus-ordered)
open import Choreographic.Global MaxPlus
open import Choreographic.Projection MaxPlus
open import Choreographic.Kripke MaxPlus
open import Choreographic.WarrantClaim MaxPlus MaxPlus-ordered
open import EpistemicTypes.Warrant using (Warrant; SoundWarrant)

open Frame end
open Claim end

w : World
w = stop , λ _ → stop

-- Positive control: the supplied evidence token substantiates the claim,
-- and with p-stability it gives party 0 knowledge of the claim at w.
supported : ReceiverLocalSideCondition 0 (λ _ → ⊤) w
supported = receiverLocal ⊤ (λ token → token) tt (λ _ token → token)

substantiated : ⊤
substantiated = data-claim 0 w (λ _ → ⊤) supported

known : Knows 0 w (λ _ → ⊤)
known = data-knowledge 0 w (λ _ → ⊤) supported

-- Every complete warrant uses its side condition's evidence type.
token : (c : KCutWarrantComplete 0 w (λ _ → ⊤))
  → Warrant.Evidence (SoundWarrant.warrant (KCutWarrantComplete.data-warrant-proof c))
token c = ReceiverLocalSideCondition.evidence (KCutWarrantComplete.data-side-condition c)

from-warrant : KCutWarrantComplete 0 w (λ _ → ⊤) → ⊤
from-warrant c = SoundWarrant.sound (KCutWarrantComplete.data-warrant-proof c) (token c)

-- Must fail at the token: an empty Evidence type with a vacuous soundness
-- function and a stability proof is still not a side condition, because
-- the record requires an inhabitant of Evidence.  So no complete warrant
-- for falsehood can be built this way.
invalid : KCutWarrantComplete 0 w (λ _ → ⊥)
invalid = mkComplete 0 w (λ _ → ⊥) (receiverLocal ⊥ (λ ()) tt (λ _ ()))

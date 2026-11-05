{-# OPTIONS --safe --without-K #-}
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

open Frame end
open Claim end

w : World
w = stop , λ _ → stop

-- Positive control: the supplied evidence token substantiates the claim.
supported : ReceiverLocalSideCondition 0 (λ _ → ⊤) w
supported = receiverLocal ⊤ (λ token → token) tt

substantiated : ⊤
substantiated = data-claim 0 w (λ _ → ⊤) supported

-- Must fail: the old two-field side condition admitted an empty Evidence
-- type and vacuous soundness function, advertising a complete warrant for
-- falsehood.  A token is now required before mkComplete can be applied.
invalid : KCutWarrantComplete 0 w (λ _ → ⊥)
invalid = mkComplete 0 w (λ _ → ⊥) (receiverLocal ⊥ (λ ()))

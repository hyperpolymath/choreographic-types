{-# OPTIONS --safe --without-K #-}
-- SPDX-License-Identifier: MPL-2.0
-- SPDX-FileCopyrightText: 2026 Jonathan D.A. Jewell
-- Ledger PR-2.
module PartialRecoveryBoundary where

open import ResourceAlgebra.Prelude
open import ResourceAlgebra.Instances.MaxPlus
open import Agda.Builtin.Maybe using (just)
open import Choreographic.Global MaxPlus
open import Choreographic.Local MaxPlus
open import Choreographic.Async MaxPlus
open import Choreographic.AsyncKnowledge MaxPlus
open import Choreographic.PartialRecovery MaxPlus
open import EpistemicTypes.EchoBridge using (Migration)
open import EpistemicTypes.PartialRecovery using (PartialRecovery)

G : Global
G = msg 0 1 (val 1) end

open AFrame G
module H = Head 0 1 (val 1) end (λ ())
module Constant = RetainedFrame G 0 ⊤ (λ _ → tt)
module Obstruction = Message 0 1 (val 1) end (λ ()) ⊤ (λ _ → tt)
module Revealing = RetainedFrame G 0 AWorld (λ w → w)

delivered in-flight : AWorld
delivered = H.delivered-world stop stop refl (λ _ → stop)
in-flight = H.in-flight-world stop stop refl (λ _ → stop)

same-sender-view : delivered ~[ 0 ] in-flight
same-sender-view = H.only-receiver-sees 0 stop stop refl (λ _ → stop) (λ ())

-- Ledger PR-2.
constant-residue-blocked : PartialRecovery Constant.localRetention → ⊥
constant-residue-blocked = Obstruction.sender-collision-forbids-partial
  stop stop refl (λ _ → stop) refl

-- Rich residue can retain the whole world. This is a pair-only decoder
-- with the source in its explicit residue, not in an image certificate.
-- No SuccessSound claim is made for unreachable visible/residue pairs.
-- Ledger PR-2.
revealing-residue-recovers : PartialRecovery Revealing.localRetention
PartialRecovery.decode revealing-residue-recovers _ w = just w
PartialRecovery.roundtrip revealing-residue-recovers w = refl

-- A query can survive the collision: the sender's view itself is recovered.
-- This Migration has a different target from whole-world PartialRecovery.
-- Ledger PR-2.
view-query-recovers : Migration Constant.localRetention (λ w → aview 0 G (acut w))
Migration.migrate view-query-recovers view _ = view
Migration.adequate view-query-recovers w = refl

{-# OPTIONS --safe --without-K #-}
-- SPDX-License-Identifier: MPL-2.0
-- SPDX-FileCopyrightText: 2026 Jonathan D.A. Jewell
-- Ledger Y-6.
module SenderKnowsReceipt where
open import ResourceAlgebra.Prelude
open import ResourceAlgebra.Instances.MaxPlus
open import Choreographic.Global         MaxPlus
open import Choreographic.Async          MaxPlus
open import Choreographic.AsyncKnowledge MaxPlus

-- Must fail: asynchronously, the sender of a message does not know it was
-- received until something comes back.  Synchronously the same claim is a
-- theorem (Head.sync-sender-knows-receipt in AsyncKnowledge.agda).
G : Global
G = msg 0 1 (val 1) (msg 0 1 (val 1) end)

open AFrame G

delivered : AWorld
delivered = world (dlv-msg stop) (dlv-msg stop) (λ _ → dlv-msg stop)

invalid : AKnows 0 delivered (λ w' → Delivered (acut w'))
invalid w' _ = tt

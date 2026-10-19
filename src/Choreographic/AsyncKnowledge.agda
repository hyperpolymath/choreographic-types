{-# OPTIONS --safe --without-K #-}
-- SPDX-License-Identifier: MPL-2.0
-- SPDX-FileCopyrightText: 2026 Jonathan D.A. Jewell
--
-- Knowledge over asynchronous cuts (ladder increment I3a).
--
-- The frame is Kripke.agda's, with asynchronous worlds: causal cuts that
-- are consistent for every party.  Two worlds are p-indistinguishable when
-- p's view is the same.
--
--   (Y-4) What survives: p knows its own restricted grade, so holds a sound
--         warrant for it, and p knows its own frontier.
--   (Y-5) The receiver of a delivered message knows it was delivered, and
--         so that it was sent.
--   (Y-6) Its sender does not know it was received, at every world where
--         the receiver has done nothing since.  In the synchronous frame
--         the same proposition is a theorem: asynchrony is what separates
--         the two ends of a message.
open import ResourceAlgebra.Core

module Choreographic.AsyncKnowledge (R : ResourceAlgebra) where

open import ResourceAlgebra.Prelude
open import Choreographic.Party
open import Choreographic.Global     R
open import Choreographic.Local      R
open import Choreographic.Projection R
open import Choreographic.Async      R
open import Choreographic.Kripke     R using (module Frame; view)
open import Choreographic.Transport  R using (↾ₗ-injective)
open import EpistemicTypes.Warrant using (mkWarrant; SoundWarrant; soundWarrant)
open ResourceAlgebra R

-- Ledger Y-4.
module AFrame (G : Global) where

  -- An asynchronous world: a causal cut, consistent for every party.
  record AWorld : Set where
    constructor world
    field
      acut       : ACut G
      causal     : Causal acut
      consistent : ∀ p → AConsistent p acut
  open AWorld public

  infix 4 _~[_]_
  _~[_]_ : AWorld → Party → AWorld → Set
  w ~[ p ] w' = aview p G (acut w) ≡ aview p G (acut w')

  -- φ holds at every world with the same view for p, including w.
  AKnows : Party → AWorld → (AWorld → Set) → Set
  AKnows p w φ = ∀ w' → w ~[ p ] w' → φ w'

  aknows-factive : ∀ p w φ → AKnows p w φ → φ w
  aknows-factive p w φ k = k w refl

  -- epistemic-types' interface, as in Kripke.agda: the evidence is
  -- knowledge, and soundness is the reflexivity of the frame.
  -- Ledger Y-4.
  asound-warrant : (p : Party) (w : AWorld) (φ : AWorld → Set) → SoundWarrant Party p (φ w)
  asound-warrant p w φ = soundWarrant (mkWarrant (AKnows p w φ)) (aknows-factive p w φ)

  -- LOSS ⇒ WARRANT survives asynchrony: by akcut-loss, p's restricted grade
  -- is a function of p's view.
  -- Ledger Y-4.
  aknows-own-grade : ∀ p w → AKnows p w (λ w' → grade↾ₐ p G (acut w') ≡ grade↾ₐ p G (acut w))
  aknows-own-grade p w w' e =
    trans (akcut-loss p G (acut w') (causal w') (consistent w' p))
    (trans (cong lgrade (sym e))
           (sym (akcut-loss p G (acut w) (causal w) (consistent w p))))

  -- p knows exactly how far its own timeline has run.
  -- Ledger Y-4.
  aknows-local-cut : ∀ p w → AKnows p w (λ w' → acutproj p (acut w') ≡ acutproj p (acut w))
  aknows-local-cut p w w' e = ↾ₗ-injective (proj p G) (acutproj p (acut w')) (acutproj p (acut w)) (sym e)

----------------------------------------------------------------------
-- The first message of a protocol msg s r g G: delivered, or sent.
Delivered : ∀ {s r g G} → ACut (msg s r g G) → Set
Delivered stop        = ⊥
Delivered (dlv-msg _) = ⊤
Delivered (flt-msg _) = ⊥

Sent : ∀ {s r g G} → ACut (msg s r g G) → Set
Sent stop        = ⊥
Sent (dlv-msg _) = ⊤
Sent (flt-msg _) = ⊤

delivered→sent : ∀ {s r g G} (κ : ACut (msg s r g G)) → Delivered κ → Sent κ
delivered→sent stop        ()
delivered→sent (dlv-msg _) _  = tt
delivered→sent (flt-msg _) ()

-- The same, for a synchronous cut, where the message is one event.
SDelivered : ∀ {s r g G} → Cut (msg s r g G) → Set
SDelivered stop         = ⊥
SDelivered (cont-msg _) = ⊤

-- The first message, s → r, of an arbitrary protocol.
module Head (s r : Party) (g : Grade) (G : Global) (s≢r : s ≢ r) where
  open AFrame (msg s r g G)

  private
    -- The receiver's view tells a delivered message from one not delivered.
    r-dlv≢stop : ∀ {L} (ρ : Role r s r) (k : LCut L) → proj-msg ρ g L ↾ₗ cutproj-msg ρ k ≢ end
    r-dlv≢stop (sender e)     k _  = s≢r (sym e)
    r-dlv≢stop (receiver _ _) k ()
    r-dlv≢stop (outside _ ne) k _  = ne refl

    r-dlv≢flt : ∀ {L} (ρ : Role r s r) (k k' : LCut L)
              → proj-msg ρ g L ↾ₗ cutproj-msg ρ k ≢ proj-msg ρ g L ↾ₗ fltproj-msg ρ k'
    r-dlv≢flt (sender e)     k k' _  = s≢r (sym e)
    r-dlv≢flt (receiver _ _) k k' ()
    r-dlv≢flt (outside _ ne) k k' _  = ne refl

    r-delivered : (κ κ' : ACut (msg s r g G)) → Delivered κ
                → aview r (msg s r g G) κ ≡ aview r (msg s r g G) κ' → Delivered κ'
    r-delivered (dlv-msg c) (dlv-msg c') _ _ = tt
    r-delivered (dlv-msg c) stop         _ e = ⊥-elim (r-dlv≢stop (role r s r) (acutproj r c) e)
    r-delivered (dlv-msg c) (flt-msg c') _ e = ⊥-elim (r-dlv≢flt (role r s r) (acutproj r c) (acutproj r c') e)
    r-delivered stop        _            () _
    r-delivered (flt-msg c) _            () _

  -- Ledger Y-5.
  receiver-knows-delivered : ∀ w → Delivered (acut w) → AKnows r w (λ w' → Delivered (acut w'))
  receiver-knows-delivered w d w' e = r-delivered (acut w) (acut w') d e

  -- Ledger Y-5.
  receiver-knows-sent : ∀ w → Delivered (acut w) → AKnows r w (λ w' → Sent (acut w'))
  receiver-knows-sent w d w' e = delivered→sent (acut w') (receiver-knows-delivered w d w' e)

  --------------------------------------------------------------------
  -- The world where the first message is delivered and its receiver has
  -- done nothing since, and the world where it is still in flight.
  delivered-world in-flight-world : (c : ACut G) → Causal c → Quiet r c → (∀ p → AConsistent p c) → AWorld
  delivered-world c a q k = world (dlv-msg c) (dlv-msg a)   (λ p → dlv-msg (k p))
  in-flight-world c a q k = world (flt-msg c) (flt-msg a q) (λ p → flt-msg (k p))

  -- Every party but the receiver sees the two alike.
  -- Ledger Y-6.
  only-receiver-sees : ∀ p c a q k → p ≢ r → delivered-world c a q k ~[ p ] in-flight-world c a q k
  only-receiver-sees p c a q k ne = cong (proj p (msg s r g G) ↾ₗ_) (sym (flight-invisible p c ne))

  -- So the sender does not know its message was received.
  -- Ledger Y-6.
  sender-cannot-know-receipt : ∀ c a q k → ¬ AKnows s (delivered-world c a q k) (λ w' → Delivered (acut w'))
  sender-cannot-know-receipt c a q k K = K (in-flight-world c a q k) (only-receiver-sees s c a q k s≢r)

  --------------------------------------------------------------------
  -- The synchronous contrast: there the sender does know.
  private
    module S = Frame (msg s r g G)

    s-dlv≢stop : ∀ {L} (ρ : Role s s r) (k : LCut L) → proj-msg ρ g L ↾ₗ cutproj-msg ρ k ≢ end
    s-dlv≢stop (sender _)      k ()
    s-dlv≢stop (receiver ne _) k _  = ne refl
    s-dlv≢stop (outside ne _)  k _  = ne refl

    s-delivered : (c c' : Cut (msg s r g G)) → SDelivered c
                → view s (msg s r g G) c ≡ view s (msg s r g G) c' → SDelivered c'
    s-delivered (cont-msg c) (cont-msg c') _ _ = tt
    s-delivered (cont-msg c) stop          _ e = ⊥-elim (s-dlv≢stop (role s s r) (cutproj s c) e)
    s-delivered stop         _             () _

  -- Ledger Y-6.
  sync-sender-knows-receipt : ∀ w → SDelivered (S.cut w) → S.Knows s w (λ w' → SDelivered (S.cut w'))
  sync-sender-knows-receipt w d w' e = s-delivered (S.cut w) (S.cut w') d e

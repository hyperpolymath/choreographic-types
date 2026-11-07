{-# OPTIONS --safe --without-K #-}
-- SPDX-License-Identifier: MPL-2.0
-- SPDX-FileCopyrightText: 2026 Jonathan D.A. Jewell
-- Ledger PR-1.
-- Whole-world recovery from a local view and an explicitly retained residue.
-- This is stronger than recovery of a query constant on indistinguishable
-- worlds. No conclusion follows from equal local views alone.
open import ResourceAlgebra.Core

module Choreographic.PartialRecovery (R : ResourceAlgebra) where

open import ResourceAlgebra.Prelude
open import Agda.Builtin.Sigma using (_,_)
open import Choreographic.Party
open import Choreographic.Global R
open import Choreographic.Local R
open import Choreographic.Async R
open import Choreographic.AsyncKnowledge R
open import EpistemicTypes.EchoBridge using (Retention)
open import EpistemicTypes.PartialRecovery
  using (PartialRecovery; SuccessSound; retainedPair; partialSeparates)
open ResourceAlgebra R

private
  pair-cong : ∀ {A B : Set} {x x' : A} {y y' : B} →
    x ≡ x' → y ≡ y' → (x , y) ≡ (x' , y')
  pair-cong refl refl = refl

module RetainedFrame (G : Global) (p : Party) (Residue : Set)
                     (residue : AFrame.AWorld G → Residue) where
  open AFrame G

  -- The certificate is deliberately trivial: the obstruction needs only
  -- equality of the actual view and residue functions, never certificate data.
  localRetention : Retention AWorld Local Residue
  Retention.observe localRetention w = aview p G (acut w)
  Retention.retain localRetention = residue
  Retention.Cert localRetention _ _ = ⊤
  Retention.sound localRetention _ = tt

  same-retained-pair : ∀ {w w'} → w ~[ p ] w' → residue w ≡ residue w' →
    retainedPair localRetention w ≡ retainedPair localRetention w'
  same-retained-pair = pair-cong

  -- This uses only PartialRecovery.roundtrip, so requiring SuccessSound
  -- as well cannot avoid the collision obstruction.
  -- Ledger PR-1.
  collision-forbids-partial : ∀ w w' → w ~[ p ] w' → residue w ≡ residue w' →
    w ≢ w' → PartialRecovery localRetention → ⊥
  collision-forbids-partial w w' same-view same-residue distinct rec =
    distinct (partialSeparates rec (same-retained-pair same-view same-residue))

  -- Ledger PR-1.
  collision-forbids-sound-partial : ∀ w w' → w ~[ p ] w' → residue w ≡ residue w' →
    w ≢ w' → (rec : PartialRecovery localRetention) → SuccessSound rec → ⊥
  collision-forbids-sound-partial w w' v r different rec _ =
    collision-forbids-partial w w' v r different rec

module Message (s r : Party) (g : Grade) (G : Global) (s≢r : s ≢ r)
               (Residue : Set)
               (residue : AFrame.AWorld (msg s r g G) → Residue) where
  module H = Head s r g G s≢r
  open AFrame (msg s r g G)
  open RetainedFrame (msg s r g G) s Residue residue

  delivered≢in-flight : ∀ c a q k → H.delivered-world c a q k ≢ H.in-flight-world c a q k
  delivered≢in-flight c a q k same with cong acut same
  ... | ()

  -- Distinct worlds and the same sender view are supplied by AsyncKnowledge.
  -- Equal residue is an additional premise, not a consequence of Y-6.
  -- Ledger PR-1.
  sender-collision-forbids-partial : ∀ c a q k →
    residue (H.delivered-world c a q k) ≡ residue (H.in-flight-world c a q k) →
    PartialRecovery localRetention → ⊥
  sender-collision-forbids-partial c a q k same-residue =
    collision-forbids-partial (H.delivered-world c a q k) (H.in-flight-world c a q k)
      (H.only-receiver-sees s c a q k s≢r) same-residue (delivered≢in-flight c a q k)

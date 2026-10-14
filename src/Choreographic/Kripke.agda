{-# OPTIONS --safe --without-K #-}
-- SPDX-License-Identifier: MPL-2.0
-- SPDX-FileCopyrightText: 2026 Jonathan D.A. Jewell
--
-- A Kripke frame for a choreography, and a model of epistemic-types'
-- Warrant / SoundWarrant interface in it.
--
--   worlds            cuts consistent for every party (global states)
--   standpoint of p   p's local timeline at the cut (the view)
--   accessibility     two worlds are p-indistinguishable when p's view is
--                     the same (the Halpern–Moses relation, by construction)
--   knowledge         truth at every indistinguishable world
--
-- Knowledge in this frame is factive because the frame is reflexive, so
-- every type-determined warrant is a SoundWarrant.  That is the "global
-- soundness of warrants" epistemic-types leaves unformalised, discharged
-- for the warrants the choreography itself determines.  Warrants about
-- data the type does not determine are not in this frame; those are where
-- SoundWarrant must still be assumed at the receiver.
open import ResourceAlgebra.Core

module Choreographic.Kripke (R : ResourceAlgebra) where

open import ResourceAlgebra.Prelude
open import Choreographic.Party
open import Choreographic.Global     R
open import Choreographic.Local      R
open import Choreographic.Projection R
open import Choreographic.KCut       R
open import EpistemicTypes.Warrant using (Warrant; mkWarrant; SoundWarrant; soundWarrant)
open ResourceAlgebra R

-- p's standpoint at a cut: its local timeline up to the projected cut.
view : (p : Party) (G : Global) → Cut G → Local
view p G c = proj p G ↾ₗ cutproj p c

-- Ledger W-1.
module Frame (G : Global) where

  -- A world is a frontier consistent for every party: a global state.
  AllConsistent : Cut G → Set
  AllConsistent c = ∀ p → Consistent p c

  World : Set
  World = Σ (Cut G) AllConsistent

  cut : World → Cut G
  cut = fst

  infix 4 _~[_]_
  _~[_]_ : World → Party → World → Set
  w ~[ p ] w' = view p G (cut w) ≡ view p G (cut w')

  ~-refl : ∀ p w → w ~[ p ] w
  ~-refl _ _ = refl

  ~-sym : ∀ {p w w'} → w ~[ p ] w' → w' ~[ p ] w
  ~-sym = sym

  ~-trans : ∀ {p w w' w''} → w ~[ p ] w' → w' ~[ p ] w'' → w ~[ p ] w''
  ~-trans = trans

  -- Require φ at every world with the same local view for p, including w.
  Knows : Party → World → (World → Set) → Set
  Knows p w φ = ∀ w' → w ~[ p ] w' → φ w'

  -- Extract truth at the current world from knowledge there.
  knows-factive : ∀ p w φ → Knows p w φ → φ w
  knows-factive p w φ k = k w refl

  ----------------------------------------------------------------------
  -- epistemic-types' interface, instantiated.  Evidence tokens are
  -- knowledge in this frame; soundness is reflexivity of the frame.
  -- Define the evidence type as Knows p w φ; no evidence token is supplied.
  warrant : (p : Party) (w : World) (φ : World → Set) → Warrant Party p (φ w)
  warrant p w φ = mkWarrant (Knows p w φ)

  -- Package the warrant with a map from knowledge evidence to truth at w.
  -- The caller must supply an evidence token to obtain a proof of φ w.
  -- Ledger W-2.
  sound-warrant : (p : Party) (w : World) (φ : World → Set) → SoundWarrant Party p (φ w)
  sound-warrant p w φ = soundWarrant (warrant p w φ) (knows-factive p w φ)

  ----------------------------------------------------------------------
  -- LOSS ⇒ WARRANT.  K-CUT-LOSS says p's restricted global grade is a
  -- function of p's view; hence p knows it at every world.
  -- Ledger W-3.
  knows-own-grade : ∀ p w → Knows p w (λ w' → grade↾ p (G ↾ cut w') ≡ grade↾ p (G ↾ cut w))
  knows-own-grade p (c , k) (c' , k') e =
    trans (kcut-loss p G c' (k' p))
    (trans (cong lgrade (sym e))
           (sym (kcut-loss p G c (k p))))

  -- Construct the sound warrant for equality with the grade at w;
  -- knows-own-grade supplies its knowledge evidence separately.
  -- Ledger W-3.
  own-grade-warrant : ∀ p w → SoundWarrant Party p (grade↾ p (G ↾ cut w) ≡ grade↾ p (G ↾ cut w))
  own-grade-warrant p w = sound-warrant p w (λ w' → grade↾ p (G ↾ cut w') ≡ grade↾ p (G ↾ cut w))

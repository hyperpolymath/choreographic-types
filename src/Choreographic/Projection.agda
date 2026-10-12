{-# OPTIONS --safe --without-K #-}
-- SPDX-License-Identifier: MPL-2.0
-- SPDX-FileCopyrightText: 2026 Jonathan D.A. Jewell
--
-- Endpoint projection, projectability (plain merge), and the projection of
-- a global cut to a local cut.  Each case analysis is a small helper over an
-- explicit Role so that the theorems in KCut.agda compose helpers instead of
-- re-doing the analysis under `with`.
open import ResourceAlgebra.Core

module Choreographic.Projection (R : ResourceAlgebra) where

open import ResourceAlgebra.Prelude
open import Choreographic.Party
open import Choreographic.Global R
open import Choreographic.Local  R
open ResourceAlgebra R

----------------------------------------------------------------------
-- Projection.  A non-participant in a choice takes the left branch as
-- representative; `Projectable` below demands the branches agree there
-- (plain merge).  Projection is therefore total and the side-condition is
-- explicit, which is what the theorems need.
-- Prepend a send or receive for a participant; leave an outsider's
-- continuation unchanged.
proj-msg : ∀ {p s r} → Role p s r → Grade → Local → Local
proj-msg {s = s} {r = r} (sender _)     g L = send r g L
proj-msg {s = s} {r = r} (receiver _ _) g L = recv s g L
proj-msg                 (outside _ _)  _ L = L

-- Form a selection or branch for a participant; return the left
-- continuation for an outsider without checking agreement with the right.
proj-choice : ∀ {p s r} → Role p s r → Grade → Local → Local → Local
proj-choice {s = s} {r = r} (sender _)     g L₁ L₂ = select r g L₁ L₂
proj-choice {s = s} {r = r} (receiver _ _) g L₁ L₂ = branch s g L₁ L₂
proj-choice                 (outside _ _)  _ L₁ L₂ = L₁

-- Compute p's endpoint, omitting messages it does not take part in and
-- choosing the left branch of choices it does not take part in.  This
-- computes a local type even when Projectable p G has no witness.
proj : Party → Global → Local
proj p end                   = end
proj p (msg s r g G)         = proj-msg    (role p s r) g (proj p G)
proj p (choice s r g G₁ G₂)  = proj-choice (role p s r) g (proj p G₁) (proj p G₂)

-- What a choice demands of p: nothing if p takes part; agreement of the
-- two projected branches (plain merge) if p does not.
Merge : ∀ (p : Party) {s r} → Role p s r → Global → Global → Set
Merge p (sender _)     G₁ G₂ = ⊤
Merge p (receiver _ _) G₁ G₂ = ⊤
Merge p (outside _ _)  G₁ G₂ = proj p G₁ ≡ proj p G₂

data Projectable (p : Party) : Global → Set where
  end    : Projectable p end
  msg    : ∀ {s r g G} → Projectable p G → Projectable p (msg s r g G)
  choice : ∀ {s r g G₁ G₂}
         → Projectable p G₁ → Projectable p G₂
         → Merge p (role p s r) G₁ G₂
         → Projectable p (choice s r g G₁ G₂)

----------------------------------------------------------------------
-- Projecting a cut: follow the projection node by node.
-- Retain a message cut at a participating endpoint; pass the continuation
-- cut through unchanged for an outsider.
cutproj-msg : ∀ {p s r g L} (ρ : Role p s r) → LCut L → LCut (proj-msg ρ g L)
cutproj-msg (sender _)     c = cont-send c
cutproj-msg (receiver _ _) c = cont-recv c
cutproj-msg (outside _ _)  c = c

-- Retain both branch cuts for a participant; use only the left cut for
-- an outsider, matching proj-choice.
cutproj-choice : ∀ {p s r g L₁ L₂} (ρ : Role p s r)
               → LCut L₁ → LCut L₂ → LCut (proj-choice ρ g L₁ L₂)
cutproj-choice (sender _)     c₁ c₂ = cont-select c₁ c₂
cutproj-choice (receiver _ _) c₁ c₂ = cont-branch c₁ c₂
cutproj-choice (outside _ _)  c₁ c₂ = c₁

-- Map a global frontier to p's endpoint, with stop mapping to stop.
-- No consistency witness is required to compute the projected cut.
cutproj : ∀ {G} (p : Party) → Cut G → LCut (proj p G)
cutproj p stop                                       = stop
cutproj p (cont-msg    {s} {r} {g} {G} c)            = cutproj-msg    (role p s r) (cutproj p c)
cutproj p (cont-choice {s} {r} {g} {G₁} {G₂} c₁ c₂)  = cutproj-choice (role p s r) (cutproj p c₁) (cutproj p c₂)

----------------------------------------------------------------------
-- A cut is consistent for p when, at every choice p does not take part
-- in, the two truncated branches still project identically.  This is the
-- "consistent frontier" of K-CUT made explicit.
data Consistent (p : Party) : ∀ {G} → Cut G → Set where
  stop        : ∀ {G} → Consistent p (stop {G})
  cont-msg    : ∀ {s r g G} {c : Cut G}
              → Consistent p c → Consistent p (cont-msg {s} {r} {g} c)
  cont-choice : ∀ {s r g G₁ G₂} {c₁ : Cut G₁} {c₂ : Cut G₂}
              → Consistent p c₁ → Consistent p c₂
              → Merge p (role p s r) (G₁ ↾ c₁) (G₂ ↾ c₂)
              → Consistent p (cont-choice {s} {r} {g} c₁ c₂)

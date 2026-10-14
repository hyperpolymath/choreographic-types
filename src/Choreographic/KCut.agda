{-# OPTIONS --safe --without-K #-}
-- SPDX-License-Identifier: MPL-2.0
-- SPDX-FileCopyrightText: 2026 Jonathan D.A. Jewell
--
-- K-CUT-LOSS, parametric in the resource algebra.
--
--   kcut-loss : grade↾ p (G ↾ c) ≡ lgrade (proj p G ↾ₗ cutproj p c)
--
-- "The global accumulation over G up to the cut c, restricted to p, equals
-- the grade read on p's local timeline up to the projected cut."  It is
-- assembled from three lemmas, each of which is a result in its own right:
--
--   proj-cut        projection commutes with cutting (syntactic, no
--                   side-conditions, uses no algebra laws at all)
--   grade-proj      restricted global grade = grade of the projection, for
--                   projectable types (uses exactly: ⊗ left unit, and
--                   ⊕ idempotence at merged choices)
--   cut-projectable a consistent cut of any global type is projectable
--
-- Hence the algebra laws K-CUT-LOSS needs are: 𝟙 ⊗ x ≡ x and x ⊕ x ≡ x.
-- Associativity, commutativity, ⊗ right unit, distributivity, order and
-- annihilation are not used.  (Checked: delete them from the record and
-- this module still typechecks; see PROOF-STATUS, K-4.)
open import ResourceAlgebra.Core

module Choreographic.KCut (R : ResourceAlgebra) where

open import ResourceAlgebra.Prelude
open import Choreographic.Party
open import Choreographic.Global     R
open import Choreographic.Local      R
open import Choreographic.Projection R
open ResourceAlgebra R

----------------------------------------------------------------------
-- (A) Projection commutes with cutting.
proj-cut-msg : ∀ {p s r} (ρ : Role p s r) g L (c : LCut L)
             → proj-msg ρ g (L ↾ₗ c) ≡ proj-msg ρ g L ↾ₗ cutproj-msg ρ c
proj-cut-msg (sender _)     g L c = refl
proj-cut-msg (receiver _ _) g L c = refl
proj-cut-msg (outside _ _)  g L c = refl

proj-cut-choice : ∀ {p s r} (ρ : Role p s r) g L₁ L₂ (c₁ : LCut L₁) (c₂ : LCut L₂)
                → proj-choice ρ g (L₁ ↾ₗ c₁) (L₂ ↾ₗ c₂)
                ≡ proj-choice ρ g L₁ L₂ ↾ₗ cutproj-choice ρ c₁ c₂
proj-cut-choice (sender _)     g L₁ L₂ c₁ c₂ = refl
proj-cut-choice (receiver _ _) g L₁ L₂ c₁ c₂ = refl
proj-cut-choice (outside _ _)  g L₁ L₂ c₁ c₂ = refl

-- Ledger K-2.
proj-cut : ∀ p G (c : Cut G) → proj p (G ↾ c) ≡ proj p G ↾ₗ cutproj p c
proj-cut p G stop = refl
proj-cut p (msg s r g G) (cont-msg c) =
  trans (cong (proj-msg (role p s r) g) (proj-cut p G c))
        (proj-cut-msg (role p s r) g (proj p G) (cutproj p c))
proj-cut p (choice s r g G₁ G₂) (cont-choice c₁ c₂) =
  trans (cong₂ (proj-choice (role p s r) g) (proj-cut p G₁ c₁) (proj-cut p G₂ c₂))
        (proj-cut-choice (role p s r) g (proj p G₁) (proj p G₂) (cutproj p c₁) (cutproj p c₂))

----------------------------------------------------------------------
-- (B) The restricted global grade is the grade of the projection.
grade-proj-msg : ∀ {p s r} (ρ : Role p s r) g {x L}
               → x ≡ lgrade L → at ρ g ⊗ x ≡ lgrade (proj-msg ρ g L)
grade-proj-msg (sender _)     g e = cong (g ⊗_) e
grade-proj-msg (receiver _ _) g e = cong (g ⊗_) e
grade-proj-msg (outside _ _)  g {x} e = trans (IsSeqMonoid.unitˡ seq x) e

grade-proj-choice : ∀ {p s r} (ρ : Role p s r) g {x₁ x₂ G₁ G₂}
                  → x₁ ≡ lgrade (proj p G₁) → x₂ ≡ lgrade (proj p G₂)
                  → Merge p ρ G₁ G₂
                  → at ρ g ⊗ (x₁ ⊕ x₂) ≡ lgrade (proj-choice ρ g (proj p G₁) (proj p G₂))
grade-proj-choice (sender _)     g e₁ e₂ _ = cong (g ⊗_) (cong₂ _⊕_ e₁ e₂)
grade-proj-choice (receiver _ _) g e₁ e₂ _ = cong (g ⊗_) (cong₂ _⊕_ e₁ e₂)
grade-proj-choice {p = p} (outside _ _) g {x₁} {x₂} {G₁} {G₂} e₁ e₂ m =
  trans (IsSeqMonoid.unitˡ seq (x₁ ⊕ x₂))
  (trans (cong₂ _⊕_ e₁ e₂)
  (trans (cong (lgrade (proj p G₁) ⊕_) (cong lgrade (sym m)))
         (IsAltMonoid.idem alt (lgrade (proj p G₁)))))

-- Ledger K-3.
grade-proj : ∀ p G → Projectable p G → grade↾ p G ≡ lgrade (proj p G)
grade-proj p end                  end                 = refl
grade-proj p (msg s r g G)        (msg pr)            =
  grade-proj-msg (role p s r) g (grade-proj p G pr)
grade-proj p (choice s r g G₁ G₂) (choice pr₁ pr₂ m)  =
  grade-proj-choice (role p s r) g (grade-proj p G₁ pr₁) (grade-proj p G₂ pr₂) m

----------------------------------------------------------------------
-- (C) A consistent cut yields a projectable global type.
-- Ledger K-5.
cut-projectable : ∀ p G (c : Cut G) → Consistent p c → Projectable p (G ↾ c)
cut-projectable p G                  stop                 stop                   = end
cut-projectable p (msg s r g G)      (cont-msg c)         (cont-msg k)           =
  msg (cut-projectable p G c k)
cut-projectable p (choice s r g G₁ G₂) (cont-choice c₁ c₂) (cont-choice k₁ k₂ m) =
  choice (cut-projectable p G₁ c₁ k₁) (cut-projectable p G₂ c₂ k₂) m

----------------------------------------------------------------------
-- K-CUT-LOSS.
-- Ledger K-1.
kcut-loss : ∀ p G (c : Cut G) → Consistent p c
          → grade↾ p (G ↾ c) ≡ lgrade (proj p G ↾ₗ cutproj p c)
kcut-loss p G c k =
  trans (grade-proj p (G ↾ c) (cut-projectable p G c k))
        (cong lgrade (proj-cut p G c))

-- The uncut special case, for the record: on a projectable type, the
-- restricted global grade is the local grade outright.
kcut-loss-full : ∀ p G → Projectable p G → grade↾ p G ≡ lgrade (proj p G)
kcut-loss-full = grade-proj

{-# OPTIONS --safe --without-K #-}
-- SPDX-License-Identifier: MPL-2.0
-- SPDX-FileCopyrightText: 2026 Jonathan D.A. Jewell
--
-- K-CUT-WARRANT's bound over asynchronous cuts (ladder increment I3a).
--
-- The global grade is the sent-so-far grade `gradeₛ`: the grade of the
-- completion, where everything in flight is delivered.  Both directions of
-- Bound.agda survive.
--
--   every grade ≽ 𝟙  ⇒  grade↾ₐ p G κ ≼ gradeₛ G κ    (HWM; MaxPlus on vals)
--   every grade ≼ 𝟙  ⇒  gradeₛ G κ ≼ grade↾ₐ p G κ    (Loss)
--
-- The case to watch is a receiver that lags behind its messages.  It has
-- paid 𝟙 where the completion pays g, and 𝟙 sits on the same side of every
-- grade as the bound needs: below them in the first case, above them in the
-- second.
open import ResourceAlgebra.Core

module Choreographic.AsyncBound (R : ResourceAlgebra) (ord : IsOrdered R) where

open import ResourceAlgebra.Prelude
open import Choreographic.Party
open import Choreographic.Global         R
open import Choreographic.Async          R
open import Choreographic.AsyncKnowledge R using (module AFrame)
open import Choreographic.Bound          R ord using (Each; msg; choice; each-cut; grade↾-≼; grade-≼↾; ≡-≼)
open ResourceAlgebra R
open IsOrdered ord

----------------------------------------------------------------------
-- What p has paid by κ, against what it pays once κ is completed.
atₐ-≼ : ∀ {p s r} (ρ : Role p s r) {g} → 𝟙 ≼ g → atₐ ρ g ≼ at ρ g
atₐ-≼ (sender _)     {g} _ = ≼-refl g
atₐ-≼ (receiver _ _)     u = u
atₐ-≼ (outside _ _)      _ = ≼-refl 𝟙

≼-atₐ : ∀ {p s r} (ρ : Role p s r) {g} → g ≼ 𝟙 → at ρ g ≼ atₐ ρ g
≼-atₐ (sender _)     {g} _ = ≼-refl g
≼-atₐ (receiver _ _)     u = u
≼-atₐ (outside _ _)      _ = ≼-refl 𝟙

-- Ledger Y-7.
grade↾ₐ-≼ : ∀ p {G} → Each (𝟙 ≼_) G → (κ : ACut G) → grade↾ₐ p G κ ≼ grade↾ p (G ↾ complete κ)
grade↾ₐ-≼ p _                                          stop               = ≼-refl 𝟙
grade↾ₐ-≼ p {msg s r g G}        (msg u e)             (dlv-msg c)        =
  ⊗-mono (≼-refl (at (role p s r) g)) (grade↾ₐ-≼ p e c)
grade↾ₐ-≼ p {msg s r g G}        (msg u e)             (flt-msg c)        =
  ⊗-mono (atₐ-≼ (role p s r) u) (grade↾ₐ-≼ p e c)
grade↾ₐ-≼ p {choice s r g G₁ G₂} (choice u e₁ e₂)     (dlv-choice c₁ c₂) =
  ⊗-mono (≼-refl (at (role p s r) g)) (⊕-mono (grade↾ₐ-≼ p e₁ c₁) (grade↾ₐ-≼ p e₂ c₂))
grade↾ₐ-≼ p {choice s r g G₁ G₂} (choice u e₁ e₂)     (flt-choice c₁ c₂) =
  ⊗-mono (atₐ-≼ (role p s r) u) (⊕-mono (grade↾ₐ-≼ p e₁ c₁) (grade↾ₐ-≼ p e₂ c₂))

-- Ledger Y-7.
≼-grade↾ₐ : ∀ p {G} → Each (_≼ 𝟙) G → (κ : ACut G) → grade↾ p (G ↾ complete κ) ≼ grade↾ₐ p G κ
≼-grade↾ₐ p _                                          stop               = ≼-refl 𝟙
≼-grade↾ₐ p {msg s r g G}        (msg u e)             (dlv-msg c)        =
  ⊗-mono (≼-refl (at (role p s r) g)) (≼-grade↾ₐ p e c)
≼-grade↾ₐ p {msg s r g G}        (msg u e)             (flt-msg c)        =
  ⊗-mono (≼-atₐ (role p s r) u) (≼-grade↾ₐ p e c)
≼-grade↾ₐ p {choice s r g G₁ G₂} (choice u e₁ e₂)     (dlv-choice c₁ c₂) =
  ⊗-mono (≼-refl (at (role p s r) g)) (⊕-mono (≼-grade↾ₐ p e₁ c₁) (≼-grade↾ₐ p e₂ c₂))
≼-grade↾ₐ p {choice s r g G₁ G₂} (choice u e₁ e₂)     (flt-choice c₁ c₂) =
  ⊗-mono (≼-atₐ (role p s r) u) (⊕-mono (≼-grade↾ₐ p e₁ c₁) (≼-grade↾ₐ p e₂ c₂))

----------------------------------------------------------------------
-- The bound against the sent-so-far grade, then known.

-- Ledger Y-7.
grade↾ₐ-≼ₛ : ∀ p {G} → Each (𝟙 ≼_) G → (κ : ACut G) → grade↾ₐ p G κ ≼ gradeₛ G κ
grade↾ₐ-≼ₛ p e κ = ≼-trans (grade↾ₐ-≼ p e κ) (grade↾-≼ p (each-cut e (complete κ)))

-- Ledger Y-7.
gradeₛ-≼↾ₐ : ∀ p {G} → Each (_≼ 𝟙) G → (κ : ACut G) → gradeₛ G κ ≼ grade↾ₐ p G κ
gradeₛ-≼↾ₐ p e κ = ≼-trans (grade-≼↾ p (each-cut e (complete κ))) (≼-grade↾ₐ p e κ)

module _ (G : Global) (p : Party) where
  open AFrame G

  -- Ledger Y-7.
  aknows-lower-bound : Each (𝟙 ≼_) G → ∀ w
                     → AKnows p w (λ w' → grade↾ₐ p G (acut w) ≼ gradeₛ G (acut w'))
  aknows-lower-bound e w w' s =
    ≡-≼ (sym (aknows-own-grade p w w' s)) (grade↾ₐ-≼ₛ p e (acut w'))

  -- Ledger Y-7.
  aknows-upper-bound : Each (_≼ 𝟙) G → ∀ w
                     → AKnows p w (λ w' → gradeₛ G (acut w') ≼ grade↾ₐ p G (acut w))
  aknows-upper-bound e w w' s =
    ≼-trans (gradeₛ-≼↾ₐ p e (acut w')) (≡-≼ (aknows-own-grade p w w' s) (≼-refl _))

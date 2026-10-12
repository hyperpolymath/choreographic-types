{-# OPTIONS --safe --without-K #-}
-- SPDX-License-Identifier: MPL-2.0
-- SPDX-FileCopyrightText: 2026 Jonathan D.A. Jewell
--
-- K-CUT-WARRANT, fragment: the bound.
--
-- The type upper-bounds discoverability but cannot determine it.  Made
-- precise: at every world p considers possible, the global grade is bounded
-- by p's own restricted grade — which p knows (Kripke.knows-own-grade) —
-- and the direction of the bound is set by where the sequence unit 𝟙 sits
-- in the algebra's order:
--
--   every grade in G is ≽ 𝟙   ⇒   grade↾ p G ≼ grade G    (HWM; MaxPlus on vals)
--   every grade in G is ≼ 𝟙   ⇒   grade G ≼ grade↾ p G    (Loss: 𝟙 = fin 0 is top)
--
-- This is the first place the family's order structure is used: ⊗ must be
-- monotone (IsOrdered), and ⊕ monotone (every resource algebra).  K-CUT-LOSS
-- needed neither (PROOF-STATUS K-4).
open import ResourceAlgebra.Core

module Choreographic.Bound (R : ResourceAlgebra) (ord : IsOrdered R) where

open import ResourceAlgebra.Prelude
open import Choreographic.Party
open import Choreographic.Global     R
open import Choreographic.Local      R
open import Choreographic.Projection R
open import Choreographic.Kripke     R
open import EpistemicTypes.Warrant using (SoundWarrant)
open ResourceAlgebra R
open IsOrdered ord

-- A predicate holding of every grade carried by a global type.
data Each (P : Grade → Set) : Global → Set where
  end    : Each P end
  msg    : ∀ {s r g G} → P g → Each P G → Each P (msg s r g G)
  choice : ∀ {s r g G₁ G₂} → P g → Each P G₁ → Each P G₂ → Each P (choice s r g G₁ G₂)

each-of : ∀ {P} → (∀ g → P g) → ∀ G → Each P G
each-of h end                   = end
each-of h (msg s r g G)         = msg (h g) (each-of h G)
each-of h (choice s r g G₁ G₂)  = choice (h g) (each-of h G₁) (each-of h G₂)

each-cut : ∀ {P G} → Each P G → (c : Cut G) → Each P (G ↾ c)
each-cut e               stop                = end
each-cut (msg h e)       (cont-msg c)        = msg h (each-cut e c)
each-cut (choice h e₁ e₂) (cont-choice c₁ c₂) = choice h (each-cut e₁ c₁) (each-cut e₂ c₂)

≡-≼ : ∀ {a b c} → a ≡ b → b ≼ c → a ≼ c
≡-≼ refl q = q

----------------------------------------------------------------------
-- Unit below every grade: the restricted grade is below the global one.
at-≼ : ∀ {p s r} (ρ : Role p s r) {g} → 𝟙 ≼ g → at ρ g ≼ g
at-≼ (sender _)     {g} _ = ≼-refl g
at-≼ (receiver _ _) {g} _ = ≼-refl g
at-≼ (outside _ _)      u = u

grade↾-≼ : ∀ p {G} → Each (𝟙 ≼_) G → grade↾ p G ≼ grade G
grade↾-≼ p end                                        = ≼-refl 𝟙
grade↾-≼ p {msg s r g G}        (msg u e)             =
  ⊗-mono (at-≼ (role p s r) u) (grade↾-≼ p e)
grade↾-≼ p {choice s r g G₁ G₂} (choice u e₁ e₂)      =
  ⊗-mono (at-≼ (role p s r) u) (⊕-mono (grade↾-≼ p e₁) (grade↾-≼ p e₂))

----------------------------------------------------------------------
-- Unit above every grade: the global grade is below the restricted one.
≼-at : ∀ {p s r} (ρ : Role p s r) {g} → g ≼ 𝟙 → g ≼ at ρ g
≼-at (sender _)     {g} _ = ≼-refl g
≼-at (receiver _ _) {g} _ = ≼-refl g
≼-at (outside _ _)      u = u

grade-≼↾ : ∀ p {G} → Each (_≼ 𝟙) G → grade G ≼ grade↾ p G
grade-≼↾ p end                                        = ≼-refl 𝟙
grade-≼↾ p {msg s r g G}        (msg u e)             =
  ⊗-mono (≼-at (role p s r) u) (grade-≼↾ p e)
grade-≼↾ p {choice s r g G₁ G₂} (choice u e₁ e₂)      =
  ⊗-mono (≼-at (role p s r) u) (⊕-mono (grade-≼↾ p e₁) (grade-≼↾ p e₂))

----------------------------------------------------------------------
-- K-CUT-WARRANT (bound form).  At every world p considers possible, the
-- global grade up to the cut is bounded by p's own restricted grade.
module _ (G : Global) (p : Party) where
  open Frame G

  knows-lower-bound : Each (𝟙 ≼_) G → ∀ w
                    → Knows p w (λ w' → grade↾ p (G ↾ cut w) ≼ grade (G ↾ cut w'))
  knows-lower-bound e w w' s =
    ≡-≼ (sym (knows-own-grade p w w' s)) (grade↾-≼ p (each-cut e (cut w')))

  knows-upper-bound : Each (_≼ 𝟙) G → ∀ w
                    → Knows p w (λ w' → grade (G ↾ cut w') ≼ grade↾ p (G ↾ cut w))
  knows-upper-bound e w w' s =
    ≼-trans (grade-≼↾ p (each-cut e (cut w'))) (≡-≼ (knows-own-grade p w w' s) (≼-refl _))

  -- ... and these are sound warrants in epistemic-types' sense.
  lower-bound-warrant : Each (𝟙 ≼_) G → ∀ w
                      → SoundWarrant Party p (grade↾ p (G ↾ cut w) ≼ grade (G ↾ cut w))
  lower-bound-warrant e w = sound-warrant p w (λ w' → grade↾ p (G ↾ cut w) ≼ grade (G ↾ cut w'))

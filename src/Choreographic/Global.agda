{-# OPTIONS --safe --without-K #-}
-- SPDX-License-Identifier: MPL-2.0
-- SPDX-FileCopyrightText: 2026 Jonathan D.A. Jewell
--
-- Graded global types, their grade, the grade "restricted to a party",
-- and cuts (consistent frontiers) with their truncation.
-- Parametric in the resource algebra: nothing below mentions min, max or +.
open import ResourceAlgebra.Core

module Choreographic.Global (R : ResourceAlgebra) where

open import ResourceAlgebra.Prelude
open import Choreographic.Party
open ResourceAlgebra R

-- Binary choice is enough for the keystone; n-ary choice is a fold of it.
data Global : Set where
  end    : Global
  msg    : (s r : Party) → Grade → Global → Global            -- s → r : g . G
  choice : (s r : Party) → Grade → Global → Global → Global   -- s → r chooses

-- Well-formed global types have no self-interactions: an interaction s → r
-- with s ≡ r would project to a send with no matching receive.  The theorems
-- below are stated for all Global (they hold for the degenerate case too, by
-- the projection convention), and applications state WellFormed as a
-- hypothesis when the communicating reading is the point.
data WellFormed : Global → Set where
  end    : WellFormed end
  msg    : ∀ {s r g G} → s ≢ r → WellFormed G → WellFormed (msg s r g G)
  choice : ∀ {s r g G₁ G₂} → s ≢ r → WellFormed G₁ → WellFormed G₂ → WellFormed (choice s r g G₁ G₂)

-- Global accumulation of grades: sequence is ⊗, alternatives are ⊕.
grade : Global → Grade
grade end                 = 𝟙
grade (msg _ _ g G)       = g ⊗ grade G
grade (choice _ _ g G₁ G₂) = g ⊗ (grade G₁ ⊕ grade G₂)

-- The share of an interaction's grade that party p experiences.
at : ∀ {p s r} → Role p s r → Grade → Grade
at (sender _)     g = g
at (receiver _ _) g = g
at (outside _ _)  _ = 𝟙

-- Global accumulation restricted to p: p's interactions count, the rest
-- contribute the sequence unit.  This is the "restricted to p" of K-CUT.
grade↾ : Party → Global → Grade
grade↾ p end                   = 𝟙
grade↾ p (msg s r g G)         = at (role p s r) g ⊗ grade↾ p G
grade↾ p (choice s r g G₁ G₂)  = at (role p s r) g ⊗ (grade↾ p G₁ ⊕ grade↾ p G₂)

----------------------------------------------------------------------
-- Cuts: a frontier through the global type.  `stop` cuts everything below
-- it; `cont-*` keeps the node and continues into each continuation.
data Cut : Global → Set where
  stop        : ∀ {G} → Cut G
  cont-msg    : ∀ {s r g G} → Cut G → Cut (msg s r g G)
  cont-choice : ∀ {s r g G₁ G₂} → Cut G₁ → Cut G₂ → Cut (choice s r g G₁ G₂)

infixl 5 _↾_
-- Truncate at the frontier: stop replaces a subtree with end; continuing
-- retains the interaction and truncates each continuation at its own cut.
_↾_ : (G : Global) → Cut G → Global
G                  ↾ stop               = end
msg s r g G        ↾ cont-msg c         = msg s r g (G ↾ c)
choice s r g G₁ G₂ ↾ cont-choice c₁ c₂  = choice s r g (G₁ ↾ c₁) (G₂ ↾ c₂)

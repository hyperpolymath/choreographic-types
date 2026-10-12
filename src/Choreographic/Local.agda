{-# OPTIONS --safe --without-K #-}
-- SPDX-License-Identifier: MPL-2.0
-- SPDX-FileCopyrightText: 2026 Jonathan D.A. Jewell
--
-- Graded local (endpoint) types, their grade, and local cuts.
open import ResourceAlgebra.Core

module Choreographic.Local (R : ResourceAlgebra) where

open import ResourceAlgebra.Prelude
open import Choreographic.Party
open ResourceAlgebra R

data Local : Set where
  end    : Local
  send   : Party → Grade → Local → Local
  recv   : Party → Grade → Local → Local
  select : Party → Grade → Local → Local → Local
  branch : Party → Grade → Local → Local → Local

-- The endpoint's own timeline, graded: what K-CUT calls "read locally".
lgrade : Local → Grade
lgrade end                 = 𝟙
lgrade (send _ g L)        = g ⊗ lgrade L
lgrade (recv _ g L)        = g ⊗ lgrade L
lgrade (select _ g L₁ L₂)  = g ⊗ (lgrade L₁ ⊕ lgrade L₂)
lgrade (branch _ g L₁ L₂)  = g ⊗ (lgrade L₁ ⊕ lgrade L₂)

data LCut : Local → Set where
  stop        : ∀ {L} → LCut L
  cont-send   : ∀ {q g L} → LCut L → LCut (send q g L)
  cont-recv   : ∀ {q g L} → LCut L → LCut (recv q g L)
  cont-select : ∀ {q g L₁ L₂} → LCut L₁ → LCut L₂ → LCut (select q g L₁ L₂)
  cont-branch : ∀ {q g L₁ L₂} → LCut L₁ → LCut L₂ → LCut (branch q g L₁ L₂)

infixl 5 _↾ₗ_
_↾ₗ_ : (L : Local) → LCut L → Local
L                ↾ₗ stop               = end
send q g L       ↾ₗ cont-send c        = send q g (L ↾ₗ c)
recv q g L       ↾ₗ cont-recv c        = recv q g (L ↾ₗ c)
select q g L₁ L₂ ↾ₗ cont-select c₁ c₂  = select q g (L₁ ↾ₗ c₁) (L₂ ↾ₗ c₂)
branch q g L₁ L₂ ↾ₗ cont-branch c₁ c₂  = branch q g (L₁ ↾ₗ c₁) (L₂ ↾ₗ c₂)

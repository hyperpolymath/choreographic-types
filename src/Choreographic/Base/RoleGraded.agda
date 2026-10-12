{-# OPTIONS --safe --without-K #-}
-- SPDX-License-Identifier: MPL-2.0
-- SPDX-FileCopyrightText: 2026 Jonathan D.A. Jewell
--
-- The "degenerate single-static-edge base case" the choreographic README
-- cites (echo-types characteristic/RoleGraded.agda) re-emerges here:
--
--   its three-grade coarsening order  keep ≤g residue ≤g forget
--   is the CONVERSE of the Loss absorption order ≼ on {fin 0, fin 1, inf}
--   under  keep ↦ fin 0, residue ↦ fin 1, forget ↦ inf.
--
-- The grade type and order are transcribed from echo-types EchoGraded (the
-- repo cannot be imported: it uses the standard library and a different
-- lake); echo-types' own experimental/echo-additive/Grade.agda already
-- carries the same `embed` with `embed-preserves-join`, so this module adds
-- the order correspondence, both directions.
--
-- Why the base case was single-edge: {fin 0, fin 1, inf} is closed under
-- alternatives (min) but NOT under sequence (fin 1 +g fin 1 = fin 2), so
-- RoleGraded could only ever grade one interaction.  The general K-CUT-LOSS
-- in KCut.agda is what sequencing needed.
module Choreographic.Base.RoleGraded where

open import ResourceAlgebra.Prelude
open import ResourceAlgebra.Core
open import ResourceAlgebra.Instances.Loss

data EGrade : Set where
  keep residue forget : EGrade

infix 4 _≤g_
data _≤g_ : EGrade → EGrade → Set where
  keep≤keep       : keep    ≤g keep
  keep≤residue    : keep    ≤g residue
  keep≤forget     : keep    ≤g forget
  residue≤residue : residue ≤g residue
  residue≤forget  : residue ≤g forget
  forget≤forget   : forget  ≤g forget

embed : EGrade → Grade
embed keep    = fin 0
embed residue = fin 1
embed forget  = inf

open ResourceAlgebra Loss using (_≼_)

-- Coarsening in echo is moving DOWN the Loss absorption order.
≤g→≼ : ∀ {a b} → a ≤g b → embed b ≼ embed a
≤g→≼ keep≤keep       = refl
≤g→≼ keep≤residue    = refl
≤g→≼ keep≤forget     = refl
≤g→≼ residue≤residue = refl
≤g→≼ residue≤forget  = refl
≤g→≼ forget≤forget   = refl

-- ... and nothing else is: the embedding reflects the order too.
≼→≤g : ∀ a b → embed b ≼ embed a → a ≤g b
≼→≤g keep    keep    _  = keep≤keep
≼→≤g keep    residue _  = keep≤residue
≼→≤g keep    forget  _  = keep≤forget
≼→≤g residue keep    ()
≼→≤g residue residue _  = residue≤residue
≼→≤g residue forget  _  = residue≤forget
≼→≤g forget  keep    ()
≼→≤g forget  residue ()
≼→≤g forget  forget  _  = forget≤forget

-- Closed under alternatives: the join of two base grades is a base grade.
alt-closed : ∀ a b → Σ EGrade (λ c → embed a ⊓g embed b ≡ embed c)
alt-closed keep    b       = keep , alt-keep b
  where
  alt-keep : ∀ b → fin 0 ⊓g embed b ≡ fin 0
  alt-keep keep    = refl
  alt-keep residue = refl
  alt-keep forget  = refl
alt-closed residue keep    = keep    , refl
alt-closed residue residue = residue , refl
alt-closed residue forget  = residue , refl
alt-closed forget  b       = b       , refl

-- Not closed under sequence: a residue followed by a residue leaves the
-- base lattice.  This is the fact that confined RoleGraded to one edge.
seq-escapes : ∀ c → embed residue +g embed residue ≢ embed c
seq-escapes keep    ()
seq-escapes residue ()
seq-escapes forget  ()

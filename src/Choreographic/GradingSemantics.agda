{-# OPTIONS --safe --without-K #-}
-- SPDX-License-Identifier: MPL-2.0
-- SPDX-FileCopyrightText: 2026 Jonathan D.A. Jewell
--
-- Grading semantics for bounds under interaction.
--
-- This module defines the grading semantics using the algebraic
-- vocabulary of tropical-types (Resource/Algebra/Interface.lean,
-- read-only provenance reference), keeping grade, measure, and index
-- distinct.  It derives one-step bound propagation theorems and the
-- projection theorem from the declared semantics, and records a
-- checked negative result for non-commutative ⊗.
--
-- ====================================================================
-- TROPICAL-TYPES PROOF WITNESSES (read-only, provenance not import)
-- ====================================================================
--
-- tropical-types (Lean 4, main branch 2026-10-27) provides:
--
--   Resource/Algebra/Interface.lean:
--     ResourceSemiring: add (⊞) is commutative and associative with
--       identity zero; mul (⊠) is associative with identity one; zero
--       annihilates; mul distributes over add on both sides.
--       mul is NOT assumed commutative.
--
--   Resource/Algebra/Dioid.lean:
--     canonicalLe: a ⊑ b ⇔ a ⊞ b = b.
--     Proven generically for any idempotent ResourceSemiring:
--       canonicalLe_refl, canonicalLe_trans, canonicalLe_antisymm,
--       canonicalLe_add_le_add_left,
--       canonicalLe_mul_le_mul_left, canonicalLe_mul_le_mul_right.
--     ResourceAlgebra.ofIdempotentAdd: builds the full ordered
--       algebra from any idempotent semiring.
--
-- These Lean proof witnesses establish that the dioid order is a
-- partial order with monotone operations, for any idempotent
-- semiring.  The choreographic-types ResourceAlgebra (Agda) is an
-- independent port of this interface; the Lean proofs are provenance,
-- not an import (bridge obligation M-2 in PROOF-STATUS).
--
-- ====================================================================
-- TERMINOLOGY (grade, measure, index — kept distinct)
-- ====================================================================
--
-- Grade:
--   An element of the resource algebra carrier.  In tropical-types:
--   a "resource grade" — a binder/resource quantity (usage, cost,
--   latency, residue measure).  Here: Grade = ResourceAlgebra.Grade R.
--   A grade is a VALUE in the algebra, not a function or parameter.
--
-- Measure:
--   A function from a syntactic object (Global or Local) to a Grade.
--   Measures ACCUMULATE grades over the interaction structure.
--     grade    : Global → Grade   unrestricted global measure
--     grade↾ p : Global → Grade   restricted global measure (party p)
--     lgrade   : Local  → Grade   local measure
--   The unrestricted measure counts all interactions; the restricted
--   measure counts only those involving the indexed party; the local
--   measure counts all actions in the projected timeline.
--   A measure is a FUNCTION, not a value; it maps syntax to grades.
--
-- Index:
--   A parameter that selects a view or position in the type structure.
--     Party index : p : Party          selects which party's view
--     Cut index   : c : Cut G          selects a frontier
--     Role index  : Role p s r         selects p's role in an interaction
--   An index PARAMETERISES a measure but is not itself a grade or
--   measure.  It does not accumulate.
--
-- Bound:
--   An inequality a ≼ b in the resource algebra's order.  A bound
--   on a measure constrains the accumulated grade.
--
-- ====================================================================
-- ONE-STEP BOUND PROPAGATION (derived from declared semantics)
-- ====================================================================
--
-- When an interaction is prepended to a global type, the bound on the
-- restricted measure transforms predictably:
--
--   If grade↾ p G ≼ x, then:
--     participant: grade↾ p (msg s r g G) ≼ at (role p s r) g ⊗ x
--     outsider:    grade↾ p (msg s r g G) ≼ 𝟙 ⊗ x
--
-- For choices:
--   If grade↾ p G₁ ≼ x₁ and grade↾ p G₂ ≼ x₂, then:
--     grade↾ p (choice s r g G₁ G₂) ≼ at (role p s r) g ⊗ (x₁ ⊕ x₂)
--
-- These are the GRADING SEMANTICS for bounds under interaction.
-- They are derived from ⊗-monotonicity and ⊕-monotonicity (which
-- tropical-types' Dioid.lean proves generically for the canonical
-- order, and which the Agda IsOrdered record carries).
--
-- ====================================================================
-- PROJECTION THEOREM (derived from K-3)
-- ====================================================================
--
-- The restricted measure equals the local measure of the projection:
--   grade↾ p G ≡ lgrade (proj p G)    (for projectable types; K-3)
--
-- Corollary: any bound on the restricted measure transfers to the
-- local measure, and vice versa.  The grading semantics commutes with
-- projection.
--
-- ====================================================================
-- NEGATIVE RESULT (checked, not postulated)
-- ====================================================================
--
-- The HWM instance has disjoint interactions whose unrestricted measure
-- depends on their ORDER, although every restricted measure is unchanged.
--
-- This is a consequence of two existing results:
--   A-1 (swap-grade↾): restricted measure is order-independent for
--       disjoint interactions, regardless of ⊗-commutativity.
--   A-3 (hwm-order-sensitive): unrestricted measure is order-dependent
--       for HWM, because ⊗ does not commute.
--
-- Thus unrestricted order invariance cannot be claimed for all resource
-- algebras.  Commuting grades suffice to preserve the unrestricted measure;
-- noncommuting grades need not change it for every continuation, because a
-- continuation can erase their difference.  The restricted measure is
-- invariant under disjoint reordering without a commutativity assumption.
--
-- This is the precise sense in which "an occupancy reading is not a
-- cost reading" (P-3): the unrestricted HWM measure is order-sensitive
-- (occupancy), while the restricted measure is order-insensitive
-- (cost from one party's perspective).
--
-- No postulates are introduced.  No cross-prover bridge is claimed.
-- The Lean proof witnesses in tropical-types' Dioid.lean are
-- provenance for the algebraic laws; the Agda proofs below are the
-- local verification.
--
-- Ledger GS-1 through GS-4.
open import ResourceAlgebra.Core

module Choreographic.GradingSemantics (R : ResourceAlgebra) (ord : IsOrdered R) where

open import ResourceAlgebra.Prelude
open import Choreographic.Party
open import Choreographic.Global     R
open import Choreographic.Local      R
open import Choreographic.Projection R
open import Choreographic.KCut       R
open import Choreographic.Swap       R
open ResourceAlgebra R
open IsOrdered ord

----------------------------------------------------------------------
-- Measures (named for clarity; these are the existing definitions
-- from Global.agda and Local.agda).
--
-- Grade   = ResourceAlgebra.Grade R       (the carrier; a value)
-- Measure = a function from syntax to Grade
-- Index   = a parameter selecting a view

-- The unrestricted global measure: all interactions count.
unrestricted-measure : Global → Grade
unrestricted-measure = grade

-- The restricted global measure, indexed by party.
restricted-measure : Party → Global → Grade
restricted-measure p = grade↾ p

-- The local measure: all actions in the projected timeline.
local-measure : Local → Grade
local-measure = lgrade

----------------------------------------------------------------------
-- One-step bound propagation: messages (GS-1).
--
-- If the continuation's restricted measure is bounded by x, then
-- prepending a message transforms the bound by ⊗-monotonicity.
-- This uses exactly the monotonicity that tropical-types'
-- Dioid.lean proves generically as canonicalLe_mul_le_mul_left.

-- Ledger GS-1.
bound-step-msg : ∀ {s r g G x} (p : Party)
  → grade↾ p G ≼ x
  → grade↾ p (msg s r g G) ≼ at (role p s r) g ⊗ x
bound-step-msg {s} {r} {g} p b = ⊗-mono (≼-refl (at (role p s r) g)) b

-- For an outsider, at (outside _ _) g = 𝟙, so the bound transforms
-- by 𝟙 ⊗ x.  With ⊗-left-unit (one of the two laws K-CUT-LOSS uses,
-- K-4), the bound is unchanged.
-- Ledger GS-1.
bound-step-msg-outsider : ∀ {s r g G x} (p : Party)
  → p ≢ s → p ≢ r
  → grade↾ p G ≼ x
  → grade↾ p (msg s r g G) ≼ 𝟙 ⊗ x
bound-step-msg-outsider {s} {r} p ps pr b with role p s r
... | sender e     = ⊥-elim (ps e)
... | receiver _ e = ⊥-elim (pr e)
... | outside _ _  = ⊗-mono (≼-refl 𝟙) b

----------------------------------------------------------------------
-- One-step bound propagation: choices (GS-2).
--
-- Uses ⊗-monotonicity and ⊕-monotonicity (every resource algebra).

-- Ledger GS-2.
bound-step-choice : ∀ {s r g G₁ G₂ x₁ x₂} (p : Party)
  → grade↾ p G₁ ≼ x₁ → grade↾ p G₂ ≼ x₂
  → grade↾ p (choice s r g G₁ G₂) ≼ at (role p s r) g ⊗ (x₁ ⊕ x₂)
bound-step-choice {s} {r} {g} p b₁ b₂ =
  ⊗-mono (≼-refl (at (role p s r) g)) (⊕-mono b₁ b₂)

----------------------------------------------------------------------
-- Two-step bound propagation (GS-3).
--
-- Composition of two one-step propagations along a message sequence.

-- Ledger GS-3.
bound-two-step : ∀ {s₁ r₁ g₁ s₂ r₂ g₂ G x} (p : Party)
  → grade↾ p G ≼ x
  → grade↾ p (msg s₁ r₁ g₁ (msg s₂ r₂ g₂ G))
  ≼ at (role p s₁ r₁) g₁ ⊗ (at (role p s₂ r₂) g₂ ⊗ x)
bound-two-step {s₁} {r₁} {g₁} {s₂} {r₂} {g₂} {G} {x} p b =
  bound-step-msg {s = s₁} {r = r₁} {g = g₁} {G = msg s₂ r₂ g₂ G}
    {x = at (role p s₂ r₂) g₂ ⊗ x} p
    (bound-step-msg {s = s₂} {r = r₂} {g = g₂} {G = G} {x = x} p b)

----------------------------------------------------------------------
-- Projection theorem (GS-3).
--
-- The restricted measure equals the local measure of the projection,
-- for projectable types.  This is K-3 (grade-proj) restated in the
-- grading semantics vocabulary: the measure commutes with projection.

-- Ledger GS-3.
projection-theorem : ∀ p G → Projectable p G
  → restricted-measure p G ≡ local-measure (proj p G)
projection-theorem p G pr = grade-proj p G pr

-- Bound transfer through projection: a bound on the restricted
-- measure transfers to the local measure, and vice versa.
≡-≼ : ∀ {a b c} → a ≡ b → b ≼ c → a ≼ c
≡-≼ refl q = q

≼-≡ : ∀ {a b c} → a ≼ b → b ≡ c → a ≼ c
≼-≡ q refl = q

-- Ledger GS-3.
bound-projection-lower : ∀ {p G x} → Projectable p G
  → restricted-measure p G ≼ x
  → local-measure (proj p G) ≼ x
bound-projection-lower {p} {G} pr b =
  ≡-≼ (sym (projection-theorem p G pr)) b

-- Ledger GS-3.
bound-projection-upper : ∀ {p G x} → Projectable p G
  → x ≼ restricted-measure p G
  → x ≼ local-measure (proj p G)
bound-projection-upper {p} {G} pr b =
  ≼-≡ b (projection-theorem p G pr)

----------------------------------------------------------------------
-- Negative result (GS-4): HWM witnesses failure of unrestricted order
-- invariance; this is not a claim about every noncommuting pair and tail.
--
-- Ledger GS-4.
--
-- The scope follows from two existing results in choreographic-types;
-- the concrete checks below include the continuation counterexample:
--
--   A-1 (Swap.swap-grade↾): for disjoint interactions, the
--       RESTRICTED measure is order-independent, regardless of
--       whether ⊗ commutes.  Uses only ⊗-left-unit.
--
--   A-3 (Instances.Diamond.hwm-order-sensitive): for HWM, the
--       UNRESTRICTED measure is order-dependent, because ⊗ does
--       not commute (peak(2 ⊗ 3) = 3, peak(3 ⊗ 2) = 5).
--
-- Together: some disjoint interactions in HWM have order-sensitive
-- unrestricted measures and order-invariant restricted measures.  Thus a
-- generic unrestricted reordering law cannot follow from ResourceAlgebra.
--
-- tropical-types' Interface.lean does NOT assume mul_comm in the
-- base ResourceSemiring; CommResourceSemiring is an optional
-- refinement.  HWM satisfies the base interface and provides the concrete
-- counterexample; the Lean interface itself is not imported here.
--
-- What CAN be proven abstractly (for any R):
--   swap-grade↾ (A-1): restricted measure is order-independent
--     for disjoint interactions
--   swap-grade (A-1): commuting grades suffice for equality of
--     unrestricted measures after swapping adjacent interactions
--
-- What CANNOT be concluded for an arbitrary continuation without an
-- additional right-cancellation hypothesis:
--   "equal unrestricted measures imply commuting grades"
--   This would require cancelling grade G from
--     (a ⊗ b) ⊗ grade G ≡ (b ⊗ a) ⊗ grade G
--   which is not valid in general (HWM absorbs information).
--   IsSeqMonoid already has unitʳ: it handles the special case G = end,
--   but does not cancel an arbitrary grade G.
--
-- The concrete HWM witness (A-3), evaluated below as a global measure,
-- is the checked negative result.
-- No postulates are introduced.  No cross-prover bridge is claimed.
-- The Lean proof witnesses in tropical-types' Dioid.lean are
-- provenance for the algebraic laws; the bridge obligation M-2
-- (no mechanical link between Lean and Agda) is recorded in
-- PROOF-STATUS and not discharged here.

-- What the abstract result gives: if ⊗ commutes for the two grades,
-- the unrestricted measure is order-independent (swap-grade, A-1).
-- Its contrapositive says that if the unrestricted
-- measure is order-dependent, ⊗ does not commute for those grades.
-- The converse fails at the continuation below, despite the same grades.

module HWMReordering where
  import ResourceAlgebra.Instances.HWM as H
  import Choreographic.Instances as Instances
  import Choreographic.Global as GlobalTypes
  module HG = GlobalTypes H.HWM
  open Instances.Diamond using (a; b)

  -- These footprints {0, 1} and {2, 3} are disjoint in both orders.
  ab ba : HG.Global → HG.Global
  ab G = HG.msg 0 1 a (HG.msg 2 3 b G)
  ba G = HG.msg 2 3 b (HG.msg 0 1 a G)

  -- The A-3 pair gives global peaks 3 and 5 when the continuation is end.
  -- Ledger GS-4.
  terminal-order-sensitive :
    H.peak (HG.grade (ab HG.end)) ≢ H.peak (HG.grade (ba HG.end))
  terminal-order-sensitive = Instances.Diamond.hwm-order-sensitive

  -- This continuation reaches peak 10 and retains no live state.
  continuation : HG.Global
  continuation = HG.msg 4 5 (H.hwm 10 0 z≤n) HG.end

  -- Both whole protocols now have peak 13 and drift 3.  Equality of
  -- unrestricted measures therefore does not imply commuting grades.
  -- Ledger GS-4.
  continuation-erases-order :
    HG.grade (ab continuation) ≡ HG.grade (ba continuation)
  continuation-erases-order = H.hwm-≡ refl refl

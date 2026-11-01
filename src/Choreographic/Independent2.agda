{-# OPTIONS --safe --without-K #-}
-- SPDX-License-Identifier: MPL-2.0
-- SPDX-FileCopyrightText: 2026 Jonathan D.A. Jewell
--
-- Independent₂ for the two-event K-CUT-LOSS experiment.
--
-- This module makes Independent₂ explicit for the two-event case,
-- including disjoint read/write footprints, phase safety, and the
-- stepping conditions.  It attempts the commuting square without
-- weakening those conditions, tests a second non-degenerate projection
-- pattern (shared party), and decides whether the degeneracy is
-- essential or incidental.
--
-- ====================================================================
-- INDEPENDENT₂ CONDITIONS (explicit)
-- ====================================================================
--
-- For two events e₁ = s₁ ⇒ r₁ ⟨ g₁ ⟩ and e₂ = s₂ ⇒ r₂ ⟨ g₂ ⟩
-- in a global state s:
--
--   (I1) Disjoint footprints: {s₁, r₁} ∩ {s₂, r₂} = ∅
--        No party participates in both events.
--        This is the "disjoint read/write footprints" condition.
--
--   (I2) Phase safety: both events can fire in state s.
--        Step e₁ s s₁ and Step e₂ s s₂ exist.
--        This is the "both are ready" condition.
--
--   (I3) Cross-stepping: after one fires, the other can still fire.
--        Step e₂ s₁ t and Step e₁ s₂ t' exist.
--        This is the "independent execution" condition.
--
--   (I4) Deterministic tie-breaking: not applicable at the type level.
--        The diamond says both orders reach projection-equivalent states;
--        which order is taken is a scheduler concern, not a type concern.
--
-- Independent₂ packages I1–I3.  I4 is noted as out of scope.
--
-- ====================================================================
-- COMMUTING SQUARE (under Independent₂)
-- ====================================================================
--
--   s  ─── step e₁ ───▶  s₁
--   │                      │
--   step e₂            step e₂
--   │                      │
--   ▼                      ▼
--   s₂  ─── step e₁ ───▶  t' ≈ t
--
-- Where t ≈ t' means StateEq t t' (projection-equivalent).
-- This is two-thread-diamond (A-5), restated with Independent₂.
--
-- K-CUT-LOSS across the diamond: after two steps, the local grade
-- at a projectable state is the restricted global grade.
-- This is two-thread-kcut-loss (A-6).
--
-- ====================================================================
-- DOES INDEPENDENT₂ TRIVIALISE THE RESULT?
-- ====================================================================
--
-- Yes.  Under I1 (disjoint footprints), each party participates in
-- at most one of the two events.  Therefore:
--
--   (a) Each party's projection is affected by at most one step.
--   (b) The restricted grade changes by at most one event's grade.
--   (c) The commuting square holds because there is no interaction
--       between the two events from any party's perspective.
--
-- The diamond is trivial in the sense that each party sees a linear
-- sequence of at most one event.  The "commuting" is vacuous: there
-- is nothing to commute from any single party's viewpoint.
--
-- ====================================================================
-- SECOND PROJECTION PATTERN: shared party
-- ====================================================================
--
-- If we drop I1 and allow a shared party, the commuting square fails:
--
--   G  = msg 0 1 g₁ (msg 0 2 g₂ end)   (party 0 sends to both)
--   G' = msg 0 2 g₂ (msg 0 1 g₁ end)   (swapped)
--
--   proj 0 G  = send 1 g₁ (send 2 g₂ end)
--   proj 0 G' = send 2 g₂ (send 1 g₁ end)
--
--   These are syntactically different: send 1 ≠ send 2 at the head.
--   So StateEq G G' fails for party 0.
--
-- The same failure occurs for a shared receiver:
--
--   G  = msg 0 2 g₁ (msg 1 2 g₂ end)   (party 2 receives from both)
--   G' = msg 1 2 g₂ (msg 0 2 g₁ end)   (swapped)
--
--   proj 2 G  = recv 0 g₁ (recv 1 g₂ end)
--   proj 2 G' = recv 1 g₂ (recv 0 g₁ end)
--
--   These are syntactically different: recv 0 ≠ recv 1 at the head.
--
-- ====================================================================
-- CONCLUSION: degeneracy is essential, not incidental
-- ====================================================================
--
-- The disjointness condition (I1) is NECESSARY for the two-event
-- commuting square.  Any shared party creates an ordering dependency
-- in that party's local type, which breaks projection-equivalence.
--
-- The degeneracy (each party sees at most one event) is therefore
-- ESSENTIAL: it is the structural reason the commuting square holds.
-- Weakening I1 to allow shared parties breaks the result.
--
-- This narrows the claim: the two-event K-CUT-LOSS diamond holds
-- only for disjoint events.  The general K-CUT claim (arbitrary
-- events, arbitrary cuts) remains OPEN.
--
-- Ledger I2-1 through I2-4.
module Choreographic.Independent2 (R : ResourceAlgebra) where

open import ResourceAlgebra.Prelude
open import ResourceAlgebra.Core
open import Choreographic.Party
open import Choreographic.Global     R
open import Choreographic.Local      R
open import Choreographic.Projection R
open import Choreographic.Operational R
open import Choreographic.Swap       R
open ResourceAlgebra R

----------------------------------------------------------------------
-- Independent₂: explicit conditions for the two-event experiment.
--
-- Packages disjoint footprints (I1) and the four stepping conditions
-- (I2, I3).  Deterministic tie-breaking (I4) is a scheduler concern,
-- not a type concern, and is not included.

record Independent₂ {e₁ e₂ s s₁ s₂ t t' : _}
  : Set where
  constructor independent₂
  field
    -- I1: disjoint footprints (no shared parties)
    disjoint    : Antichain2 e₁ e₂
    -- I2: both events can fire in state s
    step₁       : Step e₁ s s₁
    step₂       : Step e₂ s s₂
    -- I3: cross-stepping (after one fires, the other can still fire)
    step₁-then₂ : Step e₂ s₁ t
    step₂-then₁ : Step e₁ s₂ t'

----------------------------------------------------------------------
-- The commuting square under Independent₂.
--
-- This is two-thread-diamond (A-5) restated with the explicit
-- Independent₂ conditions.  No new proof is needed: the existing
-- theorem uses exactly the disjointness condition from I1.
--
-- Ledger I2-1.
commuting-square : ∀ {e₁ e₂ s s₁ s₂ t t'}
  → Independent₂ {e₁} {e₂} {s} {s₁} {s₂} {t} {t'}
  → StateEq t t'
commuting-square (independent₂ d s₁ s₂ s₁₂ s₂₁) =
  two-thread-diamond d s₁ s₁₂ s₂ s₂₁

-- K-CUT-LOSS across the diamond: after two steps, the local grade
-- at a projectable state is the restricted global grade.
-- This is two-thread-kcut-loss (A-6), restated.
--
-- Ledger I2-2.
kcut-loss-across-diamond : ∀ {e₁ e₂ s s₁ t}
  → Step e₁ s s₁ → Step e₂ s₁ t
  → ∀ p → Projectable p t
  → lgrade (proj p t) ≡ grade↾ p t
kcut-loss-across-diamond = two-thread-kcut-loss

----------------------------------------------------------------------
-- Independent₂ trivialises the result.
--
-- Under disjoint footprints (I1), each party participates in at most
-- one of the two events.  The projection for each party is affected
-- by at most one step, so the "commuting" is vacuous: there is
-- nothing to commute from any single party's viewpoint.
--
-- This is shown by the following: for any party p, at least one of
-- the two events is invisible (p is outside), so the projection
-- step for that event is the identity.

-- A party outside an event sees no change in projection.
-- Ledger I2-3.
outside-invisible : ∀ {e s t} → Step e s t → ∀ p
  → p ≢ src e → p ≢ dst e
  → proj p s ≡ proj p t
outside-invisible (fire {s = s'} {r = r'}) p ps pr
  with role p s' r'
... | sender e     = ⊥-elim (ps e)
... | receiver _ e = ⊥-elim (pr e)
... | outside _ _  = refl
outside-invisible (pass {s' = s'} {r' = r'} {g' = g'} d st) p ps pr =
  cong (proj-msg (role p s' r') g') (outside-invisible st p ps pr)

-- For disjoint events, every party is outside at least one event.
-- So the projection changes by at most one step.
-- This is the structural reason the commuting square is trivial.

----------------------------------------------------------------------
-- Second projection pattern: shared sender.
--
-- G  = msg 0 1 g₁ (msg 0 2 g₂ end)
-- G' = msg 0 2 g₂ (msg 0 1 g₁ end)
--
-- Party 0's projections differ: the commuting square fails.
--
-- Ledger I2-4.

module SharedSender (g₁ g₂ : Grade) where

  G G' : Global
  G  = msg 0 1 g₁ (msg 0 2 g₂ end)
  G' = msg 0 2 g₂ (msg 0 1 g₁ end)

  -- Party 0's projections are syntactically different.
  proj-0-G : proj 0 G ≡ send 1 g₁ (send 2 g₂ end)
  proj-0-G = refl

  proj-0-G' : proj 0 G' ≡ send 2 g₂ (send 1 g₁ end)
  proj-0-G' = refl

  -- The two projections are NOT equal: send 1 ≠ send 2 at the head.
  -- This is the negative result: the commuting square fails for
  -- shared parties.
  --
  -- Ledger I2-4.
  proj-0-G≢proj-0-G' : proj 0 G ≢ proj 0 G'
  proj-0-G≢proj-0-G' ()

  -- Consequently, StateEq G G' fails.
  state-eq-fails : ¬ StateEq G G'
  state-eq-fails eq = proj-0-G≢proj-0-G' (eq 0)

----------------------------------------------------------------------
-- Second projection pattern: shared receiver.
--
-- G  = msg 0 2 g₁ (msg 1 2 g₂ end)
-- G' = msg 1 2 g₂ (msg 0 2 g₁ end)
--
-- Party 2's projections differ: the commuting square fails.

module SharedReceiver (g₁ g₂ : Grade) where

  G G' : Global
  G  = msg 0 2 g₁ (msg 1 2 g₂ end)
  G' = msg 1 2 g₂ (msg 0 2 g₁ end)

  proj-2-G : proj 2 G ≡ recv 0 g₁ (recv 1 g₂ end)
  proj-2-G = refl

  proj-2-G' : proj 2 G' ≡ recv 1 g₂ (recv 0 g₁ end)
  proj-2-G' = refl

  -- The two projections are NOT equal: recv 0 ≠ recv 1 at the head.
  -- Ledger I2-4.
  proj-2-G≢proj-2-G' : proj 2 G ≢ proj 2 G'
  proj-2-G≢proj-2-G' ()

  state-eq-fails : ¬ StateEq G G'
  state-eq-fails eq = proj-2-G≢proj-2-G' (eq 2)

----------------------------------------------------------------------
-- Conclusion: degeneracy is essential.
--
-- The disjointness condition (I1) is necessary for the two-event
-- commuting square.  Shared parties create ordering dependencies
-- in the local type that break projection-equivalence.
--
-- The degeneracy (each party sees at most one event) is the
-- structural reason the commuting square holds under Independent₂.
-- It is ESSENTIAL, not incidental: weakening I1 breaks the result.
--
-- This narrows the two-event K-CUT-LOSS claim: it holds only for
-- disjoint events.  The general K-CUT claim (arbitrary events,
-- arbitrary cuts, non-disjoint interactions) remains OPEN.

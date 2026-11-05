{-# OPTIONS --safe --without-K #-}
-- SPDX-License-Identifier: MPL-2.0
-- SPDX-FileCopyrightText: 2026 Jonathan D.A. Jewell
--
-- Independent₂ for the two-event K-CUT-LOSS experiment.
--
-- This module makes Independent₂ explicit for the two-event case,
-- including disjoint read/write footprints, phase safety, and the
-- stepping conditions.  It proves the commuting square under those
-- conditions, derives the corresponding endpoint-grade equalities,
-- and contrasts static swaps of disjoint and shared-party events.
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
-- K-CUT-LOSS across the diamond: at both projectable endpoints, the
-- local grade is the restricted global grade, and the restricted grades
-- agree across the square.  The endpoint equalities use
-- two-thread-kcut-loss (A-6); their agreement uses the diamond (A-5).
--
-- ====================================================================
-- WHAT DISJOINTNESS GUARANTEES
-- ====================================================================
--
-- Under I1 (disjoint footprints), each party participates in
-- at most one of the two events.  Therefore:
--
--   (a) Each party's projection is affected by at most one step.
--   (b) The restricted grade changes by at most one event's grade.
--   (c) The commuting square holds because there is no interaction
--       between the two events from any party's perspective.
--
-- For these two events, each party sees at most one local action.
-- The other event is invisible in both execution orders.  This is the
-- structural reason the two local actions commute, proved below by
-- outside-one and independent-outside-invisible.
--
-- ====================================================================
-- SECOND PROJECTION PATTERN: shared party
-- ====================================================================
--
-- If we allow a shared party, a static swap can change projections:
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
-- SCOPE OF THE RESULT
-- ====================================================================
--
-- Disjointness is a sufficient condition for the commuting-square
-- theorem.  The shared-party examples above show that arbitrary static
-- swaps do not preserve projections.  They are NOT failed operational
-- diamonds: Step cannot fire their nested shared-party event first,
-- because pass requires disjointness.  The nested-not-ready proofs
-- below make that distinction explicit.
--
-- Disjointness is not necessary for every projection-preserving static
-- swap: exchanging two identical shared events changes nothing
-- (SameEvent).  Nor is it required for the underlying target-state
-- K-CUT-LOSS theorem, which holds for any projectable target.  The
-- general K-CUT claim (arbitrary events, arbitrary cuts) remains OPEN.
--
-- Ledger I2-1 through I2-4.
open import ResourceAlgebra.Core

module Choreographic.Independent2 (R : ResourceAlgebra) where

open import ResourceAlgebra.Prelude
open import Choreographic.Party
open import Choreographic.Global     R
open import Choreographic.Local      R
open import Choreographic.Projection R
open import Choreographic.Operational R
open import Choreographic.Swap       R hiding (disjoint)
open ResourceAlgebra R

----------------------------------------------------------------------
-- Independent₂: explicit conditions for the two-event experiment.
--
-- Packages disjoint footprints (I1) and the four stepping conditions
-- (I2, I3).  Deterministic tie-breaking (I4) is a scheduler concern,
-- not a type concern, and is not included.
-- Ledger I2-1.
record Independent₂ {e₁ e₂ : Event} {s s₁ s₂ t t' : Global}
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

-- Both endpoint projection laws and the equalities across the diamond.
-- Ledger I2-2.
record DiamondKCutLoss (p : Party) (t t' : Global) : Set where
  constructor diamond-kcut-loss
  field
    endpoint-projections : proj p t ≡ proj p t'
    target-grade         : lgrade (proj p t) ≡ grade↾ p t
    alternate-grade      : lgrade (proj p t') ≡ grade↾ p t'
    restricted-grades    : grade↾ p t ≡ grade↾ p t'

-- The individual endpoint laws hold for any projectable state; only
-- the agreement between endpoints uses Independent₂ and its diamond.
--
-- Ledger I2-2.
kcut-loss-across-diamond : ∀ {e₁ e₂ s s₁ s₂ t t'}
  → Independent₂ {e₁} {e₂} {s} {s₁} {s₂} {t} {t'}
  → ∀ p → Projectable p t → Projectable p t'
  → DiamondKCutLoss p t t'
kcut-loss-across-diamond {t = t} {t' = t'} d p pr pr' =
  diamond-kcut-loss same left-grade right-grade
    (trans (sym left-grade) (trans (cong lgrade same) right-grade))
  where
  same : proj p t ≡ proj p t'
  same = commuting-square d p

  left-grade : lgrade (proj p t) ≡ grade↾ p t
  left-grade = two-thread-kcut-loss
    (Independent₂.step₁ d) (Independent₂.step₁-then₂ d) p pr

  right-grade : lgrade (proj p t') ≡ grade↾ p t'
  right-grade = two-thread-kcut-loss
    (Independent₂.step₂ d) (Independent₂.step₂-then₁ d) p pr'

----------------------------------------------------------------------
-- Disjointness makes one event invisible at each endpoint.
--
-- Under disjoint footprints (I1), each party participates in at most
-- one of the two events.  The projection for each party is affected
-- by at most one of these two events.
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

-- Explicit outside evidence and the choice of an invisible event.
-- Ledger I2-3.
record OutsideEvent (p : Party) (e : Event) : Set where
  constructor outside-event
  field
    outside-source : p ≢ src e
    outside-target : p ≢ dst e

-- Ledger I2-3.
data OutsideEither (p : Party) (e₁ e₂ : Event) : Set where
  outside-first  : OutsideEvent p e₁ → OutsideEither p e₁ e₂
  outside-second : OutsideEvent p e₂ → OutsideEither p e₁ e₂

-- If p participates in the first event, all four disjointness premises
-- rule out participation in the second; otherwise p is already outside
-- the first event.  No separate outsider assumptions are required.
-- Ledger I2-3.
outside-one : ∀ {e₁ e₂} → Antichain2 e₁ e₂ → ∀ p → OutsideEither p e₁ e₂
outside-one {e₁} {e₂} d p with role p (src e₁) (dst e₁)
... | sender e = outside-second (outside-event
  (λ ps → Disjoint.s≢s' d (trans (sym e) ps))
  (λ pr → Disjoint.s≢r' d (trans (sym e) pr)))
... | receiver _ e = outside-second (outside-event
  (λ ps → Disjoint.r≢s' d (trans (sym e) ps))
  (λ pr → Disjoint.r≢r' d (trans (sym e) pr)))
... | outside ps pr = outside-first (outside-event ps pr)

-- The selected event is invisible both before and after the other event.
-- Ledger I2-3.
data InvisibleEither (p : Party) (s s₁ s₂ t t' : Global) : Set where
  first-invisible  : proj p s ≡ proj p s₁ → proj p s₂ ≡ proj p t'
                  → InvisibleEither p s s₁ s₂ t t'
  second-invisible : proj p s ≡ proj p s₂ → proj p s₁ ≡ proj p t
                  → InvisibleEither p s s₁ s₂ t t'

-- Ledger I2-3.
independent-outside-invisible : ∀ {e₁ e₂ s s₁ s₂ t t'}
  → Independent₂ {e₁} {e₂} {s} {s₁} {s₂} {t} {t'}
  → ∀ p → InvisibleEither p s s₁ s₂ t t'
independent-outside-invisible {e₁} {e₂} d p
  with outside-one {e₁} {e₂} (Independent₂.disjoint d) p
... | outside-first (outside-event ps pr) = first-invisible
  (outside-invisible (Independent₂.step₁ d) p ps pr)
  (outside-invisible (Independent₂.step₂-then₁ d) p ps pr)
... | outside-second (outside-event ps pr) = second-invisible
  (outside-invisible (Independent₂.step₂ d) p ps pr)
  (outside-invisible (Independent₂.step₁-then₂ d) p ps pr)

----------------------------------------------------------------------
-- Second projection pattern: shared sender.
--
-- G  = msg 0 1 g₁ (msg 0 2 g₂ end)
-- G' = msg 0 2 g₂ (msg 0 1 g₁ end)
--
-- Party 0's projections differ under this static swap.
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
  -- This is a counterexample to unrestricted static swap preservation.
  --
  -- Ledger I2-4.
  proj-0-G≢proj-0-G' : proj 0 G ≢ proj 0 G'
  proj-0-G≢proj-0-G' ()

  -- Consequently, StateEq G G' fails.
  -- Ledger I2-4.
  state-eq-fails : ¬ StateEq G G'
  state-eq-fails eq = proj-0-G≢proj-0-G' (eq 0)

  -- The second written event is not initially ready, so these two
  -- written types do not exhibit a failed reachable operational diamond.
  -- Ledger I2-4.
  nested-not-ready : ∀ {t} → ¬ Step (0 ⇒ 2 ⟨ g₂ ⟩) G t
  nested-not-ready (pass d _) = Disjoint.s≢s' d refl

----------------------------------------------------------------------
-- Second projection pattern: shared receiver.
--
-- G  = msg 0 2 g₁ (msg 1 2 g₂ end)
-- G' = msg 1 2 g₂ (msg 0 2 g₁ end)
--
-- Party 2's projections differ under this static swap.
-- Ledger I2-4.
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

  -- Ledger I2-4.
  state-eq-fails : ¬ StateEq G G'
  state-eq-fails eq = proj-2-G≢proj-2-G' (eq 2)

  -- Ledger I2-4.
  nested-not-ready : ∀ {t} → ¬ Step (1 ⇒ 2 ⟨ g₂ ⟩) G t
  nested-not-ready (pass d _) = Disjoint.r≢r' d refl

----------------------------------------------------------------------
-- Disjointness is sufficient, not universally necessary for a static
-- swap to preserve projections: exchanging identical events changes
-- nothing, even though both parties are shared.
-- Ledger I2-4.
module SameEvent (g : Grade) where

  -- Ledger I2-4.
  not-disjoint : ¬ Antichain2 (0 ⇒ 1 ⟨ g ⟩) (0 ⇒ 1 ⟨ g ⟩)
  not-disjoint d = Disjoint.s≢s' d refl

  -- Both sides are the same type after exchanging the two occurrences.
  -- Ledger I2-4.
  swap-preserves : StateEq (msg 0 1 g (msg 0 1 g end))
                          (msg 0 1 g (msg 0 1 g end))
  swap-preserves p = refl

-- Independent₂ supplies a sufficient hypothesis for the operational
-- commuting square.  Dropping its disjointness condition does not yield
-- an unrestricted static swap theorem; the shared-party witnesses above
-- show failures and an exceptional success.  K-CUT-LOSS itself continues
-- to hold at every projectable target without a disjointness assumption.
--
-- Extensions beyond the finite binary-choice plain-merge fragment,
-- including recursion, full merge, and delegation, remain OPEN.

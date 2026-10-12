-- SPDX-License-Identifier: MPL-2.0
--
-- Typed target for the first RapidNJ application.  This file is deliberately
-- standalone and is not imported by the repository build: every declaration
-- below is an open interface or an open conjecture, not a proof.
-- STATUS 2026-10-12: read at the type level in src/Choreographic/Operational.agda.
-- Proved there, at the type level: the diamond (two-thread-diamond) and the
-- cut-loss equality after two steps (two-thread-kcut-loss, with transportLoss
-- taking the state). This file's declarations remain OPEN: the type-level
-- results are their counterparts, not their discharge, until Independent2
-- (RapidNJ's own read/write and phase safety) is supplied.  Shown
-- unsatisfiable as typed: transportLoss : Role → Grade → Grade (no function
-- of the global grade returns a local grade; Instances.NoTransportLoss) and
-- globalGradeRespectsStateEq for occupancy (Instances.GradeNotStateInvariant).
-- Still open, and RapidNJ's rather than the type's: Independent2 and
-- independentToAntichain (read/write and phase safety).
module Applications.RapidNJ.TwoThread where

open import Agda.Builtin.Equality using (_≡_)

postulate
  Role       : Set
  State      : Set
  LocalState : Set
  Event      : Set
  Grade      : Set

  -- Canonical equivalence hides representation-only differences such as
  -- finite-map iteration order.  It is not assumed to be raw equality.
  StateEq : State → State → Set

  -- The two events are a consistent frontier when they are incomparable.
  Antichain2 : Event → Event → Set

  project    : Role → State → LocalState
  step       : Event → State → State
  localStep  : Role → Event → LocalState → LocalState

  globalGrade : State → Grade
  localGrade  : Role → LocalState → Grade
  transportLoss : Role → Grade → Grade

  -- This is intentionally stronger than Antichain2.  It must encode the
  -- implementation's read/write and phase-safety conditions as well as
  -- frontier membership.
  Independent2 : Event → Event → State → Set

  independentToAntichain :
    ∀ {e1 e2 s} → Independent2 e1 e2 s → Antichain2 e1 e2

  -- Algorithmic prerequisite: the two selected reductions form a canonical
  -- state diamond.  This is not itself K-CUT.
  twoThreadDiamond :
    ∀ {e1 e2 s} →
    Independent2 e1 e2 s →
    StateEq (step e2 (step e1 s))
            (step e1 (step e2 s))

  globalGradeRespectsStateEq :
    ∀ {s t} → StateEq s t → globalGrade s ≡ globalGrade t

  -- Smallest non-degenerate K-CUT-LOSS target.  The proof must be supplied
  -- for every endpoint and every witnessed independent two-event frontier.
  twoThreadKCutLoss :
    ∀ {p e1 e2 s} →
    Independent2 e1 e2 s →
    localGrade p
      (localStep p e2 (localStep p e1 (project p s)))
    ≡
    transportLoss p (globalGrade (step e2 (step e1 s)))

-- K-CUT-WARRANT is intentionally absent: its first application theorem has a
-- different conclusion (a bound under SoundWarrant), not this equality.

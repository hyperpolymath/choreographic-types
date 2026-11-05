{-# OPTIONS --safe --without-K #-}
-- SPDX-License-Identifier: MPL-2.0
-- SPDX-FileCopyrightText: 2026 Jonathan D.A. Jewell
--
-- The choreographic analog of echo-types' choreo-grade-commute.
--
-- echo-types' RoleGEcho is a 2D family indexed by Role and Grade:
--
--   RoleGEcho r keep    = RoleEcho r true   (a TYPE that varies with r)
--   RoleGEcho _ residue = ⊤
--   RoleGEcho _ forget  = ⊤
--
-- choreo-grade-commute says role transport (applyRole) and grade
-- degradation (applyGrade) commute on this family.  18 cases, all
-- closing by refl.  The one "non-trivial" case (c⊑s, keep≤keep) has
-- both sides computing to client-to-server e — a non-trivial function
-- between different types (RoleEcho Client true ≠ RoleEcho Server true).
--
-- Here we define the choreographic analog: a 2D family indexed by Party
-- and EGrade.  At keep grade the family carries the restricted grade
-- (grade-indexed version) or the projected local type (local-indexed
-- version); at residue and forget grades it collapses to ⊤, mirroring
-- the echo-types structured-loss pattern.
--
-- RESULT (EP-1, EP-2, EP-3):
--
--   The commuting square holds by refl in every case.  The particular
--   transports defined here preserve the stored value and require
--   grade↾ p G ≡ grade↾ q G (grade version) or proj p G ≡ proj q G
--   (local version) as a hypothesis.
--
--   The two-event examples prove equal restricted grades within each
--   message and equal projections for parties 4 and 5 outside both.
--   They also prove cross-message grade equality when g₁ ≡ g₂ and
--   participant/outsider grade equality when g₁ ≡ 𝟙.  Disjointness alone
--   does not classify all grade transports.  In all these cases the
--   chosen transport preserves the stored value and the square is refl.
--
--   The echo-types square has a non-trivial case because client-to-server
--   is a function between different types.  The choreographic analog has
--   not constructed a corresponding role-specific conversion: proj p G
--   is a VALUE of Local and grade↾ p G is a VALUE of Grade; these
--   transports only re-wrap the same value using an assumed equality.
--   Singleton wrappers also admit maps that return the target's canonical
--   value without preserving the input.  The squares below therefore do
--   not classify every possible map or establish a general role-transport
--   theorem.  They compute by refl in all six echo-grade cases.
--
--   This is recorded as the result.  No postulates are introduced, and
--   no general K-CUT is claimed.
module Choreographic.Base.EchoProjection where

open import ResourceAlgebra.Core
open import ResourceAlgebra.Prelude

import Choreographic.Base.RoleGraded as RG

module EchoProjection (R : ResourceAlgebra) where

  open import Choreographic.Party
  open import Choreographic.Global     R
  open import Choreographic.Local      R
  open import Choreographic.Projection R
  open ResourceAlgebra R

  ----------------------------------------------------------------------
  -- Grade-indexed 2D family.
  --
  -- At keep grade: the restricted grade, wrapped in a singleton.
  -- At residue and forget grades: ⊤ (collapsed, as in echo-types).

  CGEchoGrade : Party → RG.EGrade → Global → Set
  CGEchoGrade p RG.keep G     = Σ Grade (λ g → g ≡ grade↾ p G)
  CGEchoGrade p RG.residue G  = ⊤
  CGEchoGrade p RG.forget G   = ⊤

  -- The canonical witness at keep grade.
  keep-witness : ∀ p G → CGEchoGrade p RG.keep G
  keep-witness p G = grade↾ p G , refl

  ----------------------------------------------------------------------
  -- Grade degradation: collapse along the echo-grade order.
  -- keep → {residue, forget} drops the witness; reflexive steps are
  -- identity; residue → forget drops what is already ⊤.

  degradeGrade : ∀ {p g₁ g₂ G} → g₁ RG.≤g g₂ → CGEchoGrade p g₁ G → CGEchoGrade p g₂ G
  degradeGrade RG.keep≤keep       x = x
  degradeGrade RG.keep≤residue    _ = tt
  degradeGrade RG.keep≤forget     _ = tt
  degradeGrade RG.residue≤residue _ = tt
  degradeGrade RG.residue≤forget  _ = tt
  degradeGrade RG.forget≤forget   _ = tt

  ----------------------------------------------------------------------
  -- Party transport (grade version): map between parties whose
  -- restricted grades agree.  At keep grade this re-wraps the grade
  -- with the new equality proof; at higher grades it is the identity
  -- on ⊤.

  transportGrade : ∀ {p q g G} → grade↾ p G ≡ grade↾ q G
                 → CGEchoGrade p g G → CGEchoGrade q g G
  transportGrade {g = RG.keep}     e (g , p) = g , trans p e
  transportGrade {g = RG.residue}  _ _       = tt
  transportGrade {g = RG.forget}   _ _       = tt

  ----------------------------------------------------------------------
  -- The commuting square (grade version).
  --
  --   CGEchoGrade p g₁ G  ──transportGrade e──▶  CGEchoGrade q g₁ G
  --        │                                            │
  --   degradeGrade gp                             degradeGrade gp
  --        │                                            │
  --        ▼                                            ▼
  --   CGEchoGrade p g₂ G  ──transportGrade e──▶  CGEchoGrade q g₂ G
  --
  -- Closes by refl in every case.  The hypothesis e : grade↾ p G ≡
  -- grade↾ q G is required by this value-preserving transport; once given,
  -- the square commutes trivially because the transport at keep grade
  -- is the identity on the grade value, and at higher grades both
  -- sides are tt.
  --
  -- Ledger EP-1.
  echo-grade-commute : ∀ {p q g₁ g₂ G}
                     → (e : grade↾ p G ≡ grade↾ q G)
                     → (gp : g₁ RG.≤g g₂)
                     → (x : CGEchoGrade p g₁ G)
                     → degradeGrade gp (transportGrade e x)
                     ≡ transportGrade e (degradeGrade gp x)
  echo-grade-commute e RG.keep≤keep       (g , p) = refl
  echo-grade-commute e RG.keep≤residue    _       = refl
  echo-grade-commute e RG.keep≤forget     _       = refl
  echo-grade-commute e RG.residue≤residue _       = refl
  echo-grade-commute e RG.residue≤forget  _       = refl
  echo-grade-commute e RG.forget≤forget   _       = refl

  ----------------------------------------------------------------------
  -- Local-type-indexed 2D family.
  --
  -- At keep grade: the singleton of the projected local type.
  -- At residue and forget grades: ⊤ (collapsed).

  CGEchoLocal : Party → RG.EGrade → Global → Set
  CGEchoLocal p RG.keep G     = Σ Local (λ L → L ≡ proj p G)
  CGEchoLocal p RG.residue G  = ⊤
  CGEchoLocal p RG.forget G   = ⊤

  -- Grade degradation (local version).
  degradeLocal : ∀ {p g₁ g₂ G} → g₁ RG.≤g g₂ → CGEchoLocal p g₁ G → CGEchoLocal p g₂ G
  degradeLocal RG.keep≤keep       x = x
  degradeLocal RG.keep≤residue    _ = tt
  degradeLocal RG.keep≤forget     _ = tt
  degradeLocal RG.residue≤residue _ = tt
  degradeLocal RG.residue≤forget  _ = tt
  degradeLocal RG.forget≤forget   _ = tt

  -- Party transport (local version): requires the projections to agree.
  transportLocal : ∀ {p q g G} → proj p G ≡ proj q G
                 → CGEchoLocal p g G → CGEchoLocal q g G
  transportLocal {g = RG.keep}     e (L , p) = L , trans p e
  transportLocal {g = RG.residue}  _ _       = tt
  transportLocal {g = RG.forget}   _ _       = tt

  -- The commuting square (local version).
  -- Ledger EP-2.
  echo-local-commute : ∀ {p q g₁ g₂ G}
                     → (e : proj p G ≡ proj q G)
                     → (gp : g₁ RG.≤g g₂)
                     → (x : CGEchoLocal p g₁ G)
                     → degradeLocal gp (transportLocal e x)
                     ≡ transportLocal e (degradeLocal gp x)
  echo-local-commute e RG.keep≤keep       (L , p) = refl
  echo-local-commute e RG.keep≤residue    _       = refl
  echo-local-commute e RG.keep≤forget     _       = refl
  echo-local-commute e RG.residue≤residue _       = refl
  echo-local-commute e RG.residue≤forget  _       = refl
  echo-local-commute e RG.forget≤forget   _       = refl

  ----------------------------------------------------------------------
  -- Two-event case: the hypotheses hold and the square trivialises.
  --
  -- G = msg 0 1 g₁ (msg 2 3 g₂ end), with {0, 1} ∩ {2, 3} = ∅.
  --
  -- Grade version:
  --   grade↾ 0 G = g₁ ⊗ (𝟙 ⊗ 𝟙) = grade↾ 1 G   (sender/receiver agree)
  --   grade↾ 2 G = 𝟙 ⊗ (g₂ ⊗ 𝟙) = grade↾ 3 G   (second pair agrees)
  --   grade↾ p G = 𝟙 ⊗ (𝟙 ⊗ 𝟙)                  (outside parties)
  -- If g₁ ≡ g₂, the first and second pairs also agree; if g₁ ≡ 𝟙,
  -- the first pair agrees with outside parties as well.
  --
  -- Local version:
  --   proj 0 G = send 1 g₁ end   ≠   recv 0 g₁ end = proj 1 G
  --   proj 4 G = end = proj 5 G                    (outside parties)
  --
  -- The grade transport exists between sender and receiver of the same
  -- message (identical restricted grades), but it is the identity on
  -- the grade value.  The displayed local transport between parties 4
  -- and 5 preserves end.  These examples do not purport to classify all
  -- pairs with equal restricted grades or projections.

  -- Ledger EP-3.
  module TwoEvent (g₁ g₂ : Grade) where

    G : Global
    G = msg 0 1 g₁ (msg 2 3 g₂ end)

    -- Grade version: sender 0 and receiver 1 have the same restricted
    -- grade.  Both compute to g₁ ⊗ (𝟙 ⊗ 𝟙) by evaluation of role and
    -- at on concrete parties.
    -- Ledger EP-3.
    same-grade-01 : grade↾ 0 G ≡ grade↾ 1 G
    same-grade-01 = refl

    -- The commuting square at this hypothesis, for any echo-grade step.
    -- Ledger EP-3.
    commute-grade-01 : ∀ {g₁' g₂'} → (gp : g₁' RG.≤g g₂')
                   → (x : CGEchoGrade 0 g₁' G)
                   → degradeGrade {p = 1} {G = G} gp
                       (transportGrade {p = 0} {q = 1} {g = g₁'} {G = G} same-grade-01 x)
                   ≡ transportGrade {p = 0} {q = 1} {g = g₂'} {G = G} same-grade-01
                       (degradeGrade {p = 0} {G = G} gp x)
    commute-grade-01 = echo-grade-commute {p = 0} {q = 1} {G = G} same-grade-01

    -- Second pair: sender 2 and receiver 3 also agree.
    -- Ledger EP-3.
    same-grade-23 : grade↾ 2 G ≡ grade↾ 3 G
    same-grade-23 = refl

    -- Participants in different messages can agree when the grades do.
    -- Ledger EP-3.
    same-grade-02 : g₁ ≡ g₂ → grade↾ 0 G ≡ grade↾ 2 G
    same-grade-02 e =
      trans (cong (g₁ ⊗_) (IsSeqMonoid.unitˡ seq 𝟙))
      (trans (cong (_⊗ 𝟙) e)
             (sym (IsSeqMonoid.unitˡ seq (g₂ ⊗ 𝟙))))

    -- A participant can also agree with an outsider when its grade is 𝟙.
    -- Ledger EP-3.
    same-grade-04 : g₁ ≡ 𝟙 → grade↾ 0 G ≡ grade↾ 4 G
    same-grade-04 e = cong (_⊗ (𝟙 ⊗ 𝟙)) e

    -- Local version: the outside parties 4 and 5 have the same projection.
    -- Both compute to end.
    -- Ledger EP-3.
    same-proj-45 : proj 4 G ≡ proj 5 G
    same-proj-45 = refl

    -- The commuting square at this hypothesis.
    -- Ledger EP-3.
    commute-local-45 : ∀ {g₁' g₂'} → (gp : g₁' RG.≤g g₂')
                   → (x : CGEchoLocal 4 g₁' G)
                   → degradeLocal {p = 5} {G = G} gp
                       (transportLocal {p = 4} {q = 5} {g = g₁'} {G = G} same-proj-45 x)
                   ≡ transportLocal {p = 4} {q = 5} {g = g₂'} {G = G} same-proj-45
                       (degradeLocal {p = 4} {G = G} gp x)
    commute-local-45 = echo-local-commute {p = 4} {q = 5} {G = G} same-proj-45

    -- Sender and receiver of the same message do NOT have the same
    -- projection: send ≠ recv.  This equality-based local transport
    -- cannot be instantiated between them.  Constructing a role-specific
    -- conversion analogous to client-to-server is a separate problem;
    -- these commuting squares have not solved it.
    -- Ledger EP-3.
    proj-0≢proj-1 : proj 0 G ≢ proj 1 G
    proj-0≢proj-1 ()

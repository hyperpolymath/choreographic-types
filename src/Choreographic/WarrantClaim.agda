{-# OPTIONS --safe --without-K #-}
-- SPDX-License-Identifier: MPL-2.0
-- SPDX-FileCopyrightText: 2026 Jonathan D.A. Jewell
--
-- K-CUT-WARRANT: precise statement, hypotheses, and side conditions.
--
-- This module states the K-CUT-WARRANT claim as a reviewed theorem
-- statement.  It separates proven components from conditional ones,
-- makes every hypothesis explicit, and documents the gap between
-- type-determined and data-dependent warrants.
--
-- ====================================================================
-- THEOREM STATEMENT (K-CUT-WARRANT, precise)
-- ====================================================================
--
-- For a resource algebra R with order, a global type G, a party p,
-- and a world w (a cut consistent for every party):
--
--   (C1) GRADE EQUALITY WARRANT  [PROVEN]
--        p holds a SoundWarrant for
--          grade↾ p (G ↾ cut w) ≡ grade↾ p (G ↾ cut w)
--        Evidence: Kripke knowledge in the choreographic frame.
--        Soundness: factivity of the frame (reflexivity).
--
--   (C2) GRADE BOUND WARRANT  [PROVEN, with hypothesis]
--        If EveryGrade≽𝟙 G (every interaction grade ≽ 𝟙):
--          p holds a SoundWarrant for
--            grade↾ p (G ↾ cut w) ≼ grade (G ↾ cut w)
--        If EveryGrade≼𝟙 G (every interaction grade ≼ 𝟙):
--          p holds a SoundWarrant for
--            grade (G ↾ cut w) ≼ grade↾ p (G ↾ cut w)
--        Evidence: Kripke knowledge of the bound.
--        Soundness: factivity.
--
--   (C3) DATA WARRANT  [CONDITIONAL]
--        For a data-dependent proposition φ : World → Set:
--          p holds a SoundWarrant for φ w
--        IF AND ONLY IF p provides:
--          Evidence : Set
--          sound    : Evidence → φ w
--        This is the RECEIVER-LOCAL SIDE CONDITION.
--
-- ====================================================================
-- REQUIRED HYPOTHESES
-- ====================================================================
--
--   (H1) R : ResourceAlgebra, ord : IsOrdered R
--        The resource algebra and its order structure.
--
--   (H2) G : Global
--        A well-formed global type (finite, binary choice, plain merge).
--
--   (H3) w : World = Σ (Cut G) (λ c → ∀ q → Consistent q c)
--        A cut consistent for EVERY party (a global state).
--
--   (H4) For C2: Each (𝟙 ≼_) G or Each (_≼ 𝟙) G
--        Every interaction grade is above (or below) the sequence unit.
--        This determines the direction of the bound.
--
--   (H5) For C3: ReceiverLocalSideCondition p φ w
--        The receiver provides Evidence and a soundness proof.
--        NOT type-determined: external assumption.
--
-- ====================================================================
-- RECEIVER-LOCAL SIDE CONDITION
-- ====================================================================
--
-- For data-dependent claims (C3), the receiver r of a message must
-- provide:
--
--   Evidence : Set         — the type of evidence tokens
--   sound    : Evidence → φ w  — proof that evidence entails the claim
--
-- These are NOT derivable from the global type.  The choreographic
-- frame provides the warrant STRUCTURE (Warrant, SoundWarrant from
-- epistemic-types) and the type-determined evidence (Kripke knowledge
-- for grades), but data-dependent evidence and soundness are external.
--
-- In epistemic-types' ProofTransport vocabulary, this corresponds to
-- the receiver holding a CertificateCheck with:
--   check : Payload → Bool
--   sound : (p : Payload) → check p ≡ true → Meaning r artifact claim
-- The checker is an external assumption, not a consequence of the type.
--
-- ====================================================================
-- GAP
-- ====================================================================
--
-- The current interface does not derive Evidence or sound from the
-- global type for data-dependent claims.  The gap is:
--
--   TYPE-DETERMINED: grades, projections, cuts, restricted grades,
--                    bounds.  Evidence is Kripke knowledge; soundness
--                    is frame factivity.  PROVEN (C1, C2).
--
--   NOT TYPE-DETERMINED: payload properties, authenticity, timing
--                        beyond the type, cryptographic evidence.
--                        Evidence and soundness are EXTERNAL.
--                        CONDITIONAL (C3).
--
-- epistemic-types' ProofTransport.agda provides the vocabulary
-- (CertificateCheck, verify, Gap) but does not bridge the gap:
-- the checker must be supplied by the application.
--
-- This is not a deficiency of the formalisation: it is the precise
-- boundary between what a choreographic type can determine and what
-- it cannot.  Warrants about data the type does not determine are
-- outside the frame (Kripke.agda header, W-2 scope).
--
-- Ledger WC-1 through WC-5.
module Choreographic.WarrantClaim (R : ResourceAlgebra) (ord : IsOrdered R) where

open import ResourceAlgebra.Prelude
open import ResourceAlgebra.Core
open import Choreographic.Party
open import Choreographic.Global     R
open import Choreographic.Local      R
open import Choreographic.Projection R
open import Choreographic.KCut       R
open import Choreographic.Kripke     R
open import Choreographic.Bound      R ord
open import Choreographic.Transport  R
open import EpistemicTypes.Warrant using (Warrant; mkWarrant; SoundWarrant; soundWarrant)
open ResourceAlgebra R

----------------------------------------------------------------------
-- The claim, for a fixed global type.

module Claim (G : Global) where

  open Frame G

  ====================================================================
  -- COMPONENT 1: Grade equality warrant.  PROVEN.
  --
  -- At every world w, p holds a SoundWarrant for the (reflexive)
  -- equality of its own restricted grade.  The evidence type is
  -- Kripke knowledge; the soundness proof is factivity.
  --
  -- This is the LOSS ⇒ WARRANT direction: by K-CUT-LOSS, the
  -- restricted grade is a function of p's view, so p knows it at
  -- every world.
  --
  -- Hypotheses: H1–H3 only.  No grade-ordering hypothesis needed.
  --
  -- Ledger WC-1.
  grade-equality-warrant : ∀ p w
    → SoundWarrant Party p (grade↾ p (G ↾ cut w) ≡ grade↾ p (G ↾ cut w))
  grade-equality-warrant p w = own-grade-warrant p w

  -- The evidence token: p knows its own restricted grade.
  -- Ledger WC-1.
  grade-equality-evidence : ∀ p w
    → Knows p w (λ w' → grade↾ p (G ↾ cut w') ≡ grade↾ p (G ↾ cut w))
  grade-equality-evidence p w = knows-own-grade p w

  ====================================================================
  -- COMPONENT 2: Grade bound warrant.  PROVEN, with hypothesis H4.
  --
  -- Lower bound direction: if every grade in G is ≽ 𝟙, then p's
  -- restricted grade is a lower bound on the global grade at every
  -- world p considers possible.
  --
  -- Hypotheses: H1–H3, plus Each (𝟙 ≼_) G.
  --
  -- Ledger WC-2.
  grade-bound-warrant-lower : ∀ p → Each (𝟙 ≼_) G → ∀ w
    → SoundWarrant Party p (grade↾ p (G ↾ cut w) ≼ grade (G ↾ cut w))
  grade-bound-warrant-lower p e w = lower-bound-warrant G p e w

  -- The evidence token: p knows the lower bound.
  -- Ledger WC-2.
  grade-bound-evidence-lower : ∀ p → Each (𝟙 ≼_) G → ∀ w
    → Knows p w (λ w' → grade↾ p (G ↾ cut w) ≼ grade (G ↾ cut w'))
  grade-bound-evidence-lower p e w = knows-lower-bound G p e w

  -- Upper bound direction: if every grade in G is ≼ 𝟙, then the
  -- global grade is below p's restricted grade.
  --
  -- Hypotheses: H1–H3, plus Each (_≼ 𝟙) G.
  --
  -- Ledger WC-3.
  grade-bound-warrant-upper : ∀ p → Each (_≼ 𝟙) G → ∀ w
    → SoundWarrant Party p (grade (G ↾ cut w) ≼ grade↾ p (G ↾ cut w))
  grade-bound-warrant-upper p e w =
    sound-warrant p w (λ w' → grade (G ↾ cut w') ≼ grade↾ p (G ↾ cut w))

  -- The evidence token: p knows the upper bound.
  -- Ledger WC-3.
  grade-bound-evidence-upper : ∀ p → Each (_≼ 𝟙) G → ∀ w
    → Knows p w (λ w' → grade (G ↾ cut w') ≼ grade↾ p (G ↾ cut w))
  grade-bound-evidence-upper p e w = knows-upper-bound G p e w

  ====================================================================
  -- COMPONENT 3: Data warrant.  CONDITIONAL on receiver-local side
  -- condition (H5).
  --
  -- For a data-dependent proposition φ : World → Set, p holds a
  -- SoundWarrant for φ w IF p provides Evidence and a soundness proof.
  --
  -- The receiver-local side condition:
  --   Evidence : Set
  --   sound    : Evidence → φ w
  --
  -- These are NOT type-determined.  The global type provides the
  -- warrant structure but not the evidence or soundness.
  --
  -- Hypotheses: H1–H3, plus H5 (receiver-local side condition).

  -- Ledger WC-4.
  record ReceiverLocalSideCondition
    (p : Party) (φ : World → Set) (w : World) : Set₁ where
    constructor receiverLocal
    field
      Evidence : Set
      sound    : Evidence → φ w

  -- Construct a SoundWarrant from the receiver-local side condition.
  -- This is a packaging step: the receiver's Evidence and soundness
  -- proof are wrapped in epistemic-types' SoundWarrant record.
  --
  -- Ledger WC-4.
  data-warrant : ∀ p w (φ : World → Set)
    → ReceiverLocalSideCondition p φ w
    → SoundWarrant Party p (φ w)
  data-warrant p w φ (receiverLocal E s) =
    soundWarrant (mkWarrant E) s

  ====================================================================
  -- COMPLETE K-CUT-WARRANT: packaging the unconditional components.
  --
  -- A complete K-CUT-WARRANT for party p at world w, with a
  -- data-dependent proposition φ, packages:
  --   (1) the grade equality warrant (proven, no extra hypothesis)
  --   (3) the data warrant (conditional on side condition H5)
  --
  -- Component (2), the grade bound warrant, is stated separately
  -- because it requires a grade-ordering hypothesis (H4) whose
  -- direction depends on the algebra.  The caller constructs it
  -- with grade-bound-warrant-lower or grade-bound-warrant-upper.
  --
  -- Ledger WC-5.
  record KCutWarrantComplete
    (p : Party) (w : World) (φ : World → Set) : Set₁ where
    constructor kcutWarrantComplete
    field
      -- Component 1: grade equality (proven from H1–H3 alone).
      grade-eq-warrant :
        SoundWarrant Party p (grade↾ p (G ↾ cut w) ≡ grade↾ p (G ↾ cut w))

      -- Component 3: data warrant (conditional on H5).
      data-side-condition : ReceiverLocalSideCondition p φ w
      data-warrant-proof  : SoundWarrant Party p (φ w)

  -- Populate a complete K-CUT-WARRANT from the receiver-local side
  -- condition.  The grade equality is proven; the data warrant is
  -- constructed from the side condition.
  --
  -- Ledger WC-5.
  mkComplete : ∀ p w (φ : World → Set)
    → (sc : ReceiverLocalSideCondition p φ w)
    → KCutWarrantComplete p w φ
  mkComplete p w φ sc = kcutWarrantComplete
    (grade-equality-warrant p w)
    sc
    (data-warrant p w φ sc)

----------------------------------------------------------------------
-- What cannot be proven here (the gap, stated precisely).
--
-- For a data-dependent proposition φ, the type system provides:
--   (a) The SoundWarrant record structure (from epistemic-types).
--   (b) A factive Kripke frame (from the choreographic projection).
--   (c) Type-determined warrants for grades (C1, C2 above).
--
-- The type system does NOT provide:
--   (d) Evidence tokens for φ (these depend on the payload).
--   (e) A soundness proof Evidence → φ w (this depends on the
--       application's verification logic).
--
-- In epistemic-types' ProofTransport vocabulary:
--   (f) A CertificateCheck for φ (the checker is application-specific).
--   (g) A Meaning function from artifacts to claims (the semantics
--       of the payload is outside the type).
--
-- Items (d)–(g) are the receiver-local side condition.  They are
-- external assumptions, not consequences of the choreographic type.
-- This is the precise scope of "SoundWarrant at the receiver" from
-- the pre-registration: it applies to data-dependent claims only,
-- not to the grade claims that the type determines.

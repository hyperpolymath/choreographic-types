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
--   (C1) GRADE KNOWLEDGE WARRANT  [PROVEN]
--        p holds a WitnessedWarrant (a SoundWarrant together with an
--        evidence token) for
--          OwnGradeKnown p w
--            = ∀ w' → w ~[ p ] w' → grade↾ p (G ↾ cut w') ≡ grade↾ p (G ↾ cut w)
--        that is, p's restricted grade is the same at every world p
--        cannot tell apart from w.  This is K-CUT-LOSS read as knowledge.
--        Evidence: Kripke knowledge in the choreographic frame.
--        Soundness: factivity of the frame (reflexivity).
--
--   (C2) GRADE BOUND WARRANT  [PROVEN, with hypothesis]
--        If EveryGrade≽𝟙 G (every interaction grade ≽ 𝟙):
--          p holds a WitnessedWarrant for
--            grade↾ p (G ↾ cut w) ≼ grade (G ↾ cut w)
--        If EveryGrade≼𝟙 G (every interaction grade ≼ 𝟙):
--          p holds a WitnessedWarrant for
--            grade (G ↾ cut w) ≼ grade↾ p (G ↾ cut w)
--        Evidence: Kripke knowledge of the bound.
--        Soundness: factivity.
--
--   (C3) DATA WARRANT  [CONDITIONAL]
--        For a data-dependent proposition φ : World → Set:
--          a SoundWarrant indexed by p for φ w can be constructed,
--          and p knows φ at w,
--        IF the application supplies:
--          Evidence : Set
--          sound    : Evidence → φ w
--          evidence : Evidence
--          local    : ∀ {w'} → w ~[ p ] w' → φ w → φ w'
--        This is the RECEIVER-LOCAL SIDE CONDITION.  The last field
--        makes it local to p: φ must not vary between worlds that p
--        cannot tell apart.
--        A SoundWarrant alone does not supply an evidence token.
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
--        Evidence, a soundness proof, a token and a proof that φ is
--        stable along p's indistinguishability are supplied externally.
--        Receiver ownership of the token is also an external assumption.
--
-- ====================================================================
-- RECEIVER-LOCAL SIDE CONDITION
-- ====================================================================
--
-- For data-dependent claims (C3), the application must supply:
--
--   Evidence : Set         — the type of evidence tokens
--   sound    : Evidence → φ w  — proof that evidence entails the claim
--   evidence : Evidence    — an actual token
--   local    : ∀ {w'} → w ~[ p ] w' → φ w → φ w'
--                          — φ does not change across worlds p cannot
--                            tell apart from w
--
-- The `local` field is what ties the condition to p: with it, the token
-- gives p knowledge of φ at w (data-knowledge), not only the truth of
-- φ w.  Receiver ownership of the token itself remains an external
-- assumption: no field records which party holds it.
-- These are NOT derivable from the global type.  The choreographic
-- frame provides the warrant STRUCTURE (Warrant, SoundWarrant from
-- epistemic-types) and the type-determined evidence (Kripke knowledge
-- for grades), but the data-dependent evidence token and soundness are
-- external.  Merely giving an empty Evidence type and a vacuous sound
-- function does not meet the side condition.
--
-- In epistemic-types' ProofTransport vocabulary, a corresponding
-- externally supplied CertificateCheck has:
--   check : Payload → Bool
--   sound : (p : Payload) → check p ≡ true → Meaning r artifact claim
-- The checker is an external assumption, not a consequence of the type.
--
-- ====================================================================
-- GAP
-- ====================================================================
--
-- The current interface does not derive Evidence, evidence, or sound
-- from the global type for data-dependent claims.  The gap is:
--
--   TYPE-DETERMINED: grades, projections, cuts, restricted grades,
--                    bounds.  Evidence is Kripke knowledge; soundness
--                    is frame factivity.  PROVEN (C1, C2).
--
--   NOT TYPE-DETERMINED: payload properties, authenticity, timing
--                        beyond the type, cryptographic evidence.
--                        Evidence, its token, and soundness are EXTERNAL.
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
open import ResourceAlgebra.Core

module Choreographic.WarrantClaim (R : ResourceAlgebra) (ord : IsOrdered R) where

open import ResourceAlgebra.Prelude
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
-- A sound warrant together with an evidence token for it.
--
-- epistemic-types' SoundWarrant stores an evidence type and a soundness
-- map, but no token, so its Evidence may be empty.  Its Epi record
-- stores a token but no soundness map.  A WitnessedWarrant stores both,
-- so `claim` is derived rather than assumed.  The warranted claims in
-- this module are packaged this way.
record WitnessedWarrant (p : Party) (A : Set) : Set₁ where
  constructor witnessed
  field
    warrant  : SoundWarrant Party p A
    evidence : Warrant.Evidence (SoundWarrant.warrant warrant)

  claim : A
  claim = SoundWarrant.sound warrant evidence

----------------------------------------------------------------------
-- The claim, for a fixed global type.

module Claim (G : Global) where

  open Frame G

  -- ====================================================================
  -- COMPONENT 1: Grade knowledge warrant.  PROVEN.
  --
  -- What p is warranted in is not the equality of its grade with
  -- itself but that the grade does not vary over the worlds p cannot
  -- tell apart from w.  This is the LOSS ⇒ WARRANT direction: by
  -- K-CUT-LOSS the restricted grade is a function of p's view.
  --
  -- The warrant is the frame's own: evidence is p's knowledge, at w,
  -- of OwnGradeKnown, and soundness is factivity.  The token holds
  -- because knows-own-grade holds at every world.
  --
  -- Hypotheses: H1–H3 only.  No grade-ordering hypothesis needed.
  --
  -- Ledger WC-1.
  OwnGradeKnown : Party → World → Set
  OwnGradeKnown p w =
    Knows p w (λ w' → grade↾ p (G ↾ cut w') ≡ grade↾ p (G ↾ cut w))

  -- Ledger WC-1.
  grade-knowledge-warrant : ∀ p w → WitnessedWarrant p (OwnGradeKnown p w)
  grade-knowledge-warrant p w =
    witnessed (sound-warrant p w (OwnGradeKnown p)) (λ w' _ → knows-own-grade p w')

  -- The evidence token on its own: p knows its own restricted grade.
  -- Ledger WC-1.
  grade-equality-evidence : ∀ p w → OwnGradeKnown p w
  grade-equality-evidence p w = knows-own-grade p w

  -- Superseded by grade-knowledge-warrant.  This warrants the
  -- tautology `x ≡ x`, which any SoundWarrant can do, and it carries
  -- no token.  Kept so existing callers still type-check.
  -- Ledger WC-1.
  grade-equality-warrant : ∀ p w
    → SoundWarrant Party p (grade↾ p (G ↾ cut w) ≡ grade↾ p (G ↾ cut w))
  grade-equality-warrant p w = own-grade-warrant p w

  -- ====================================================================
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

  -- The bound warrants with their tokens.  The warrant terms above do
  -- not use H4 (sound-warrant exists for any claim); the tokens do, so
  -- these are the forms in which H4 is load-bearing.
  -- Ledger WC-2.
  grade-bound-witnessed-lower : ∀ p → Each (𝟙 ≼_) G → ∀ w
    → WitnessedWarrant p (grade↾ p (G ↾ cut w) ≼ grade (G ↾ cut w))
  grade-bound-witnessed-lower p e w =
    witnessed (grade-bound-warrant-lower p e w) (grade-bound-evidence-lower p e w)

  -- Ledger WC-3.
  grade-bound-witnessed-upper : ∀ p → Each (_≼ 𝟙) G → ∀ w
    → WitnessedWarrant p (grade (G ↾ cut w) ≼ grade↾ p (G ↾ cut w))
  grade-bound-witnessed-upper p e w =
    witnessed (grade-bound-warrant-upper p e w) (grade-bound-evidence-upper p e w)

  -- ====================================================================
  -- COMPONENT 3: Data warrant.  CONDITIONAL on receiver-local side
  -- condition (H5).
  --
  -- For a data-dependent proposition φ : World → Set, a SoundWarrant
  -- indexed by p for φ w can be constructed IF an evidence type, a
  -- soundness proof, and an actual evidence token are supplied.
  --
  -- The receiver-local side condition:
  --   Evidence : Set
  --   sound    : Evidence → φ w
  --   evidence : Evidence
  --   local    : ∀ {w'} → w ~[ p ] w' → φ w → φ w'
  --
  -- These are NOT type-determined.  `local` is where p enters: it says
  -- φ cannot change across worlds p cannot tell apart from w.  A claim
  -- about data p never sees (another party's payload, say) cannot meet
  -- it whenever that data differs between two such worlds.
  -- No field records that p holds the token; that remains an external
  -- assumption.  The global type provides the warrant structure but not
  -- the evidence or soundness.
  --
  -- Hypotheses: H1–H3, plus H5 (receiver-local side condition).

  -- Ledger WC-4.
  record ReceiverLocalSideCondition
    (p : Party) (φ : World → Set) (w : World) : Set₁ where
    constructor receiverLocal
    field
      Evidence : Set
      sound    : Evidence → φ w
      evidence : Evidence
      local    : ∀ {w'} → w ~[ p ] w' → φ w → φ w'

  -- Construct a SoundWarrant from the receiver-local side condition.
  -- This is a packaging step: the supplied Evidence and soundness
  -- proof are wrapped in epistemic-types' SoundWarrant record.  That
  -- imported record does not store the token; the side condition does.
  --
  -- Ledger WC-4.
  data-warrant : ∀ p w (φ : World → Set)
    → ReceiverLocalSideCondition p φ w
    → SoundWarrant Party p (φ w)
  data-warrant p w φ (receiverLocal E s e _) =
    soundWarrant (mkWarrant E) s

  -- Use the supplied token to substantiate the data claim.  This cannot
  -- be obtained from a SoundWarrant whose Evidence type is empty.
  -- Ledger WC-4.
  data-claim : ∀ p w (φ : World → Set)
    → ReceiverLocalSideCondition p φ w
    → φ w
  data-claim p w φ (receiverLocal E s e _) = s e

  -- The token and p-stability together give p knowledge of φ at w.
  -- This is the receiver-local content: data-claim alone gives only the
  -- truth of φ w.
  -- Ledger WC-4.
  data-knowledge : ∀ p w (φ : World → Set)
    → ReceiverLocalSideCondition p φ w
    → Knows p w φ
  data-knowledge p w φ (receiverLocal E s e loc) w' w~w' = loc w~w' (s e)

  -- The data warrant with its token.
  -- Ledger WC-4.
  data-witnessed : ∀ p w (φ : World → Set)
    → ReceiverLocalSideCondition p φ w
    → WitnessedWarrant p (φ w)
  data-witnessed p w φ sc =
    witnessed (data-warrant p w φ sc) (ReceiverLocalSideCondition.evidence sc)

  -- ====================================================================
  -- COMPLETE K-CUT-WARRANT: packaging the grade and conditional data parts.
  --
  -- A complete K-CUT-WARRANT for party p at world w, with a
  -- data-dependent proposition φ, packages:
  --   (1) the grade knowledge warrant, with its token (proven, no
  --       extra hypothesis)
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
      -- Component 1: grade knowledge, with its token (proven from
      -- H1–H3 alone).
      grade-knowledge : WitnessedWarrant p (OwnGradeKnown p w)

      -- Component 3: data warrant and its inhabited side condition (H5).
      data-side-condition : ReceiverLocalSideCondition p φ w

    -- The warrant is determined by the side condition, including its
    -- evidence type and soundness function.
    data-warrant-proof : SoundWarrant Party p (φ w)
    data-warrant-proof = data-warrant p w φ data-side-condition

    -- What the record establishes for p at w.
    -- Ledger WC-5.
    grade-known : OwnGradeKnown p w
    grade-known = WitnessedWarrant.claim grade-knowledge

    -- Ledger WC-5.
    data-known : Knows p w φ
    data-known = data-knowledge p w φ data-side-condition

  -- Populate a complete K-CUT-WARRANT from the receiver-local side
  -- condition.  The grade knowledge is proven; the data warrant is
  -- constructed from the side condition.
  --
  -- Ledger WC-5.
  mkComplete : ∀ p w (φ : World → Set)
    → (sc : ReceiverLocalSideCondition p φ w)
    → KCutWarrantComplete p w φ
  mkComplete p w φ sc = kcutWarrantComplete
    (grade-knowledge-warrant p w)
    sc

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

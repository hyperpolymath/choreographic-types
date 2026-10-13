{-# OPTIONS --safe --without-K #-}
-- SPDX-License-Identifier: MPL-2.0
-- SPDX-FileCopyrightText: 2026 Jonathan D.A. Jewell
--
-- The echo-additive grade ℕ ∪ {∞} of echo-types, IMPORTED (not transcribed)
-- from experimental/echo-additive/Grade.agda at the commit pinned in
-- scripts/fetch-siblings.sh, packaged as a ResourceAlgebra with its dioid,
-- order and annihilation layers, and shown to agree with resource-algebra's
-- transcription `Loss` operation for operation.
--
-- resource-algebra's ledger row L-2 and this repository's B-4 said the two
-- definitions were "textually identical, reviewed by eye".  Here the
-- comparison is a checked theorem: `toLoss` / `fromLoss` are inverse, and
-- `toLoss` carries ⊕, ⊗ and both units across (`toLoss-⊕`, `toLoss-⊗`,
-- `toLoss-𝟘`, `toLoss-𝟙`).  The three-grade base lattice of EchoGraded,
-- which Base/RoleGraded transcribes, is matched against the original
-- constructor by constructor (`transcribe`, `≤g-transcribe`, `≤g-original`,
-- `embed-agrees`).
--
-- This is the only module under src/ that needs the Agda standard library
-- (echo-types is built on it), so it is deliberately NOT imported by
-- Choreographic.All: the keystone development stays builtins-only and
-- checks with no library on the include path.  scripts/check.sh checks this
-- module as its own root with echo-types and agda-stdlib on the path.
module Choreographic.Base.EchoAdditive where

open import ResourceAlgebra.Prelude
  using (Nat; zero; suc; _≡_; refl; trans; cong; cong₂; min)
open import ResourceAlgebra.Core
import ResourceAlgebra.Instances.Loss as L
import Choreographic.Base.RoleGraded as RG
import EchoGraded as Old
import experimental.echo-additive.Grade as E
open import Data.Nat.Base using (_⊓_)

----------------------------------------------------------------------
-- The instance, filled from echo-types' own lemmas

EchoAdditive : ResourceAlgebra
EchoAdditive = record
  { Grade = E.Grade
  ; _⊕_   = E._⊓g_
  ; _⊗_   = E._+g_
  ; 𝟘     = E.inf
  ; 𝟙     = E.fin 0
  ; alt   = record { assoc = E.⊓g-assoc ; comm = E.⊓g-comm
                   ; idem = E.⊓g-idem ; unitˡ = E.⊓g-identityˡ }
  ; seq   = record { assoc = E.+g-assoc ; unitˡ = E.+g-identityˡ
                   ; unitʳ = E.+g-identityʳ }
  }

EchoAdditive-dioid : IsDioid EchoAdditive
EchoAdditive-dioid = record { distribˡ = E.+g-distribˡ-⊓g ; distribʳ = distribʳ }
  where
  -- Right distributivity from echo-types' left law and commutativity of +g.
  distribʳ : ∀ a b c → (a E.⊓g b) E.+g c ≡ (a E.+g c) E.⊓g (b E.+g c)
  distribʳ a b c =
    trans (E.+g-comm (a E.⊓g b) c)
    (trans (E.+g-distribˡ-⊓g c a b)
           (cong₂ E._⊓g_ (E.+g-comm c a) (E.+g-comm c b)))

EchoAdditive-ordered : IsOrdered EchoAdditive
EchoAdditive-ordered = IsDioid.ordered EchoAdditive-dioid

EchoAdditive-annihilating : IsAnnihilating EchoAdditive
EchoAdditive-annihilating = record { annihilˡ = E.+g-absorbˡ ; annihilʳ = E.+g-absorbʳ }

----------------------------------------------------------------------
-- Agreement with resource-algebra's transcription, operation for operation

toLoss : E.Grade → L.Grade
toLoss (E.fin n) = L.fin n
toLoss E.inf     = L.inf

fromLoss : L.Grade → E.Grade
fromLoss (L.fin n) = E.fin n
fromLoss L.inf     = E.inf

toLoss∘fromLoss : ∀ g → toLoss (fromLoss g) ≡ g
toLoss∘fromLoss (L.fin _) = refl
toLoss∘fromLoss L.inf     = refl

fromLoss∘toLoss : ∀ g → fromLoss (toLoss g) ≡ g
fromLoss∘toLoss (E.fin _) = refl
fromLoss∘toLoss E.inf     = refl

-- The standard library's ⊓ and the Prelude's min are the same function,
-- clause for clause.
⊓-min : ∀ m n → m ⊓ n ≡ min m n
⊓-min zero    n       = refl
⊓-min (suc m) zero    = refl
⊓-min (suc m) (suc n) = cong suc (⊓-min m n)

toLoss-𝟘 : toLoss E.inf ≡ L.inf
toLoss-𝟘 = refl

toLoss-𝟙 : toLoss (E.fin 0) ≡ L.fin 0
toLoss-𝟙 = refl

toLoss-⊕ : ∀ a b → toLoss (a E.⊓g b) ≡ toLoss a L.⊓g toLoss b
toLoss-⊕ (E.fin m) (E.fin n) = cong L.fin (⊓-min m n)
toLoss-⊕ (E.fin m) E.inf     = refl
toLoss-⊕ E.inf     b         = refl

toLoss-⊗ : ∀ a b → toLoss (a E.+g b) ≡ toLoss a L.+g toLoss b
toLoss-⊗ (E.fin m) (E.fin n) = refl
toLoss-⊗ (E.fin m) E.inf     = refl
toLoss-⊗ E.inf     b         = refl

----------------------------------------------------------------------
-- The three-grade base lattice: Base/RoleGraded's transcription of
-- EchoGraded, matched against the original constructor by constructor

transcribe : Old.Grade → RG.EGrade
transcribe Old.keep    = RG.keep
transcribe Old.residue = RG.residue
transcribe Old.forget  = RG.forget

-- echo-types' own embedding into ℕ ∪ {∞} (Grade.agda `embed`) and
-- RoleGraded's agree through toLoss.
embed-agrees : ∀ g → toLoss (E.embed g) ≡ RG.embed (transcribe g)
embed-agrees Old.keep    = refl
embed-agrees Old.residue = refl
embed-agrees Old.forget  = refl

-- The coarsening order is transcribed faithfully, in both directions.
≤g-transcribe : ∀ {a b} → a Old.≤g b → transcribe a RG.≤g transcribe b
≤g-transcribe Old.keep≤keep       = RG.keep≤keep
≤g-transcribe Old.keep≤residue    = RG.keep≤residue
≤g-transcribe Old.keep≤forget     = RG.keep≤forget
≤g-transcribe Old.residue≤residue = RG.residue≤residue
≤g-transcribe Old.residue≤forget  = RG.residue≤forget
≤g-transcribe Old.forget≤forget   = RG.forget≤forget

≤g-original : ∀ a b → transcribe a RG.≤g transcribe b → a Old.≤g b
≤g-original Old.keep    Old.keep    _  = Old.keep≤keep
≤g-original Old.keep    Old.residue _  = Old.keep≤residue
≤g-original Old.keep    Old.forget  _  = Old.keep≤forget
≤g-original Old.residue Old.keep    ()
≤g-original Old.residue Old.residue _  = Old.residue≤residue
≤g-original Old.residue Old.forget  _  = Old.residue≤forget
≤g-original Old.forget  Old.keep    ()
≤g-original Old.forget  Old.residue ()
≤g-original Old.forget  Old.forget  _  = Old.forget≤forget

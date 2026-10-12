{-# OPTIONS --safe --without-K #-}
-- SPDX-License-Identifier: MPL-2.0
-- SPDX-FileCopyrightText: 2026 Jonathan D.A. Jewell
--
-- The operational interface of applications/rapidnj-two-thread.agda, read
-- at the type level.  Declaration by declaration:
--
--   Role        = Party                State       = Global (what remains)
--   LocalState  = Local                Event       = an interaction (src, dst, wt)
--   StateEq     = projection-equivalence: every endpoint sees the same type
--   Antichain2  = Disjoint (the two interactions share no party)
--   project     = proj                 step        = the relation Step (below)
--   localStep   = prepend the local event (step-proj says this is forced)
--   globalGrade = grade                localGrade  = lgrade
--
-- `step` is a relation, not a function: on tree-shaped global types a
-- function would need decidable equality on grades to find the event, and
-- the file's own StateEq exists precisely to absorb that.  The diamond is
-- then a theorem (two-thread-diamond), and so is the K-CUT-LOSS target —
-- once `transportLoss : Role → Grade → Grade` is re-typed to take the state,
-- because no function of the global grade alone can return the local grade
-- (Instances.NoTransportLoss).
open import ResourceAlgebra.Core

module Choreographic.Operational (R : ResourceAlgebra) where

open import ResourceAlgebra.Prelude
open import Choreographic.Party
open import Choreographic.Global     R
open import Choreographic.Local      R
open import Choreographic.Projection R
open import Choreographic.KCut       R
open import Choreographic.Swap       R
open import Choreographic.Transport  R using (left)
open ResourceAlgebra R

record Event : Set where
  constructor _⇒_⟨_⟩
  field
    src dst : Party
    wt      : Grade
open Event public

disjoint-sym : ∀ {a b c d} → Disjoint a b c d → Disjoint c d a b
disjoint-sym (disjoint p q r s) = disjoint (λ x → p (sym x)) (λ x → r (sym x)) (λ x → q (sym x)) (λ x → s (sym x))

Antichain2 : Event → Event → Set
Antichain2 e₁ e₂ = Disjoint (src e₁) (dst e₁) (src e₂) (dst e₂)

-- Fire an interaction: at the head, or beneath heads it is independent of.
data Step : Event → Global → Global → Set where
  fire : ∀ {s r g G} → Step (s ⇒ r ⟨ g ⟩) (msg s r g G) G
  pass : ∀ {e s' r' g' G G'} → Disjoint (src e) (dst e) s' r' → Step e G G'
       → Step e (msg s' r' g' G) (msg s' r' g' G')

StateEq : Global → Global → Set
StateEq s t = ∀ p → proj p s ≡ proj p t

----------------------------------------------------------------------
-- A global step is a local step at every endpoint: the state before is
-- the local event prepended to the state after (identity for outsiders).
step-proj : ∀ {e s t} → Step e s t → ∀ p
          → proj p s ≡ proj-msg (role p (src e) (dst e)) (wt e) (proj p t)
step-proj fire       p = refl
step-proj {e} (pass {s' = s'} {r'} {g'} {G} {G'} d st) p =
  trans (cong (proj-msg (role p s' r') g') (step-proj st p))
        (swap-msg (role p s' r') (role p (src e) (dst e)) (disjoint-sym d) g' (wt e) (proj p G'))

-- ... and likewise for the restricted grade.
step-grade↾ : ∀ {e s t} → Step e s t → ∀ p
            → grade↾ p s ≡ at (role p (src e) (dst e)) (wt e) ⊗ grade↾ p t
step-grade↾ fire       p = refl
step-grade↾ {e} (pass {s' = s'} {r'} {g'} {G} {G'} d st) p =
  trans (cong (at (role p s' r') g' ⊗_) (step-grade↾ st p))
        (swap-at (role p s' r') (role p (src e) (dst e)) (disjoint-sym d) g' (wt e) (grade↾ p G'))

-- A local step is injective in the state after it.
proj-msg-inj : ∀ {p s r} (ρ : Role p s r) g {L L'} → proj-msg ρ g L ≡ proj-msg ρ g L' → L ≡ L'
proj-msg-inj (sender _)     g e = cong left e
proj-msg-inj (receiver _ _) g e = cong left e
proj-msg-inj (outside _ _)  g e = e

----------------------------------------------------------------------
-- twoThreadDiamond, as a theorem: given executions of two independent
-- events in both orders from the same state, their final states are
-- projection-equivalent.  Existence of both executions is a premise.
two-thread-diamond : ∀ {e₁ e₂ s s₁ s₂ t t'} → Antichain2 e₁ e₂
                   → Step e₁ s s₁ → Step e₂ s₁ t
                   → Step e₂ s s₂ → Step e₁ s₂ t'
                   → StateEq t t'
two-thread-diamond {e₁} {e₂} {s} {t = t} {t' = t'} d a₁ a₂ b₁ b₂ p =
  proj-msg-inj ρ₂ g₂ (proj-msg-inj ρ₁ g₁ chain)
  where
  ρ₁ = role p (src e₁) (dst e₁)
  ρ₂ = role p (src e₂) (dst e₂)
  g₁ = wt e₁
  g₂ = wt e₂
  chain : proj-msg ρ₁ g₁ (proj-msg ρ₂ g₂ (proj p t)) ≡ proj-msg ρ₁ g₁ (proj-msg ρ₂ g₂ (proj p t'))
  chain =
    trans (cong (proj-msg ρ₁ g₁) (sym (step-proj a₂ p)))
    (trans (sym (step-proj a₁ p))
    (trans (step-proj b₁ p)
    (trans (cong (proj-msg ρ₂ g₂) (step-proj b₂ p))
           (swap-msg ρ₂ ρ₁ (disjoint-sym d) g₂ g₁ (proj p t')))))

-- twoThreadKCutLoss, with transportLoss re-typed to take the state: after
-- any two steps (independent or not), the local grade at a projectable
-- state is the global accumulation restricted to the endpoint.
two-thread-kcut-loss : ∀ {e₁ e₂ s s₁ t} → Step e₁ s s₁ → Step e₂ s₁ t
                     → ∀ p → Projectable p t → lgrade (proj p t) ≡ grade↾ p t
two-thread-kcut-loss _ _ p pr = sym (grade-proj p _ pr)

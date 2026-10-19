{-# OPTIONS --safe --without-K #-}
-- SPDX-License-Identifier: MPL-2.0
-- SPDX-FileCopyrightText: 2026 Jonathan D.A. Jewell
--
-- Asynchronous cuts (ladder increment I3a; pre-registered in
-- docs/pre-registration-addendum-2026-10-19.adoc).
--
-- A cut is still a prefix of the global type's tree, but each message and
-- each selection in it is either delivered or in flight: sent, not yet
-- received.  The receiver of a message in flight does nothing later in the
-- prefix (`Causal`): its timeline is blocked at the pending receive.  The
-- sender pays an interaction's grade when it sends and the receiver when it
-- receives (`grade↾ₐ`).
--
--   embed, complete    synchronous cuts are the cuts with nothing in flight;
--                      completion delivers everything in flight
--   akcut-loss         K-CUT-LOSS for asynchronous cuts, from the same two
--                      laws as K-1: ⊗ left unit and ⊕ idempotence
--   flight-invisible   delivering a message changes only its receiver's
--                      local cut
--
-- Like KCut.agda, this module is also checked against a Core with only those
-- two laws (scripts/minimal-laws.sh).
open import ResourceAlgebra.Core

module Choreographic.Async (R : ResourceAlgebra) where

open import ResourceAlgebra.Prelude
open import Choreographic.Party
open import Choreographic.Global     R
open import Choreographic.Local      R
open import Choreographic.Projection R
open import Choreographic.KCut       R using (proj-cut; grade-proj-msg; proj-cut-msg)
open ResourceAlgebra R

⊥-elim : {A : Set} → ⊥ → A
⊥-elim ()

----------------------------------------------------------------------
-- Asynchronous cuts.  `dlv-*` delivered, `flt-*` in flight.
data ACut : Global → Set where
  stop       : ∀ {G} → ACut G
  dlv-msg    : ∀ {s r g G} → ACut G → ACut (msg s r g G)
  flt-msg    : ∀ {s r g G} → ACut G → ACut (msg s r g G)
  dlv-choice : ∀ {s r g G₁ G₂} → ACut G₁ → ACut G₂ → ACut (choice s r g G₁ G₂)
  flt-choice : ∀ {s r g G₁ G₂} → ACut G₁ → ACut G₂ → ACut (choice s r g G₁ G₂)

-- An interaction in flight, projected: the sender has acted, the receiver's
-- local cut stops before its receive, an outsider's passes through.
fltproj-msg : ∀ {p s r g L} (ρ : Role p s r) → LCut L → LCut (proj-msg ρ g L)
fltproj-msg (sender _)     k = cont-send k
fltproj-msg (receiver _ _) k = stop
fltproj-msg (outside _ _)  k = k

fltproj-choice : ∀ {p s r g L₁ L₂} (ρ : Role p s r)
               → LCut L₁ → LCut L₂ → LCut (proj-choice ρ g L₁ L₂)
fltproj-choice (sender _)     k₁ k₂ = cont-select k₁ k₂
fltproj-choice (receiver _ _) k₁ k₂ = stop
fltproj-choice (outside _ _)  k₁ k₂ = k₁

-- p's local cut at an asynchronous cut; a delivered interaction projects
-- as in the synchronous case.
acutproj : ∀ {G} (p : Party) → ACut G → LCut (proj p G)
acutproj p stop                                = stop
acutproj p (dlv-msg    {s} {r} {g} c)          = cutproj-msg    {g = g} (role p s r) (acutproj p c)
acutproj p (flt-msg    {s} {r} {g} c)          = fltproj-msg    {g = g} (role p s r) (acutproj p c)
acutproj p (dlv-choice {s} {r} {g} c₁ c₂)      = cutproj-choice {g = g} (role p s r) (acutproj p c₁) (acutproj p c₂)
acutproj p (flt-choice {s} {r} {g} c₁ c₂)      = fltproj-choice {g = g} (role p s r) (acutproj p c₁) (acutproj p c₂)

-- p's standpoint at an asynchronous cut.
aview : (p : Party) (G : Global) → ACut G → Local
aview p G κ = proj p G ↾ₗ acutproj p κ

-- p has done nothing in κ.  Read off p's local cut, which at a choice p is
-- outside of shows the left branch only; in a world, plain merge for p
-- (AConsistent) makes the two branches agree, so nothing is missed there.
Quiet : ∀ {G} → Party → ACut G → Set
Quiet p κ = acutproj p κ ≡ stop

-- Causality: the receiver of an interaction in flight does nothing later.
data Causal : ∀ {G} → ACut G → Set where
  stop       : ∀ {G} → Causal (stop {G})
  dlv-msg    : ∀ {s r g G} {c : ACut G} → Causal c → Causal (dlv-msg {s} {r} {g} c)
  flt-msg    : ∀ {s r g G} {c : ACut G} → Causal c → Quiet r c → Causal (flt-msg {s} {r} {g} c)
  dlv-choice : ∀ {s r g G₁ G₂} {c₁ : ACut G₁} {c₂ : ACut G₂}
             → Causal c₁ → Causal c₂ → Causal (dlv-choice {s} {r} {g} c₁ c₂)
  flt-choice : ∀ {s r g G₁ G₂} {c₁ : ACut G₁} {c₂ : ACut G₂}
             → Causal c₁ → Causal c₂ → Quiet r c₁ → Quiet r c₂
             → Causal (flt-choice {s} {r} {g} c₁ c₂)

-- Plain merge on views, at a choice p is outside of.
AMerge : ∀ (p : Party) {s r} → Role p s r → ∀ {G₁ G₂} → ACut G₁ → ACut G₂ → Set
AMerge p (sender _)                c₁ c₂ = ⊤
AMerge p (receiver _ _)            c₁ c₂ = ⊤
AMerge p (outside _ _) {G₁} {G₂}   c₁ c₂ = aview p G₁ c₁ ≡ aview p G₂ c₂

data AConsistent (p : Party) : ∀ {G} → ACut G → Set where
  stop       : ∀ {G} → AConsistent p (stop {G})
  dlv-msg    : ∀ {s r g G} {c : ACut G} → AConsistent p c → AConsistent p (dlv-msg {s} {r} {g} c)
  flt-msg    : ∀ {s r g G} {c : ACut G} → AConsistent p c → AConsistent p (flt-msg {s} {r} {g} c)
  dlv-choice : ∀ {s r g G₁ G₂} {c₁ : ACut G₁} {c₂ : ACut G₂}
             → AConsistent p c₁ → AConsistent p c₂ → AMerge p (role p s r) c₁ c₂
             → AConsistent p (dlv-choice {s} {r} {g} c₁ c₂)
  flt-choice : ∀ {s r g G₁ G₂} {c₁ : ACut G₁} {c₂ : ACut G₂}
             → AConsistent p c₁ → AConsistent p c₂ → AMerge p (role p s r) c₁ c₂
             → AConsistent p (flt-choice {s} {r} {g} c₁ c₂)

----------------------------------------------------------------------
-- Synchronous cuts inside asynchronous ones, and back.
-- A synchronous cut is an asynchronous one with nothing in flight.
embed : ∀ {G} → Cut G → ACut G
embed stop                = stop
embed (cont-msg c)        = dlv-msg (embed c)
embed (cont-choice c₁ c₂) = dlv-choice (embed c₁) (embed c₂)

-- Nothing in flight.
data Settled : ∀ {G} → ACut G → Set where
  stop       : ∀ {G} → Settled (stop {G})
  dlv-msg    : ∀ {s r g G} {c : ACut G} → Settled c → Settled (dlv-msg {s} {r} {g} c)
  dlv-choice : ∀ {s r g G₁ G₂} {c₁ : ACut G₁} {c₂ : ACut G₂}
             → Settled c₁ → Settled c₂ → Settled (dlv-choice {s} {r} {g} c₁ c₂)

-- Deliver everything in flight.
complete : ∀ {G} → ACut G → Cut G
complete stop               = stop
complete (dlv-msg c)        = cont-msg (complete c)
complete (flt-msg c)        = cont-msg (complete c)
complete (dlv-choice c₁ c₂) = cont-choice (complete c₁) (complete c₂)
complete (flt-choice c₁ c₂) = cont-choice (complete c₁) (complete c₂)

----------------------------------------------------------------------
-- Grades.  What p has paid for an interaction in flight: the sender its
-- grade, everyone else nothing yet.
atₐ : ∀ {p s r} → Role p s r → Grade → Grade
atₐ (sender _)     g = g
atₐ (receiver _ _) _ = 𝟙
atₐ (outside _ _)  _ = 𝟙

-- p's restricted grade at an asynchronous cut: the sender pays at send,
-- the receiver at receipt.
grade↾ₐ : Party → (G : Global) → ACut G → Grade
grade↾ₐ p G                    stop               = 𝟙
grade↾ₐ p (msg s r g G)        (dlv-msg c)        = at  (role p s r) g ⊗ grade↾ₐ p G c
grade↾ₐ p (msg s r g G)        (flt-msg c)        = atₐ (role p s r) g ⊗ grade↾ₐ p G c
grade↾ₐ p (choice s r g G₁ G₂) (dlv-choice c₁ c₂) = at  (role p s r) g ⊗ (grade↾ₐ p G₁ c₁ ⊕ grade↾ₐ p G₂ c₂)
grade↾ₐ p (choice s r g G₁ G₂) (flt-choice c₁ c₂) = atₐ (role p s r) g ⊗ (grade↾ₐ p G₁ c₁ ⊕ grade↾ₐ p G₂ c₂)

-- The global grade of everything sent so far: the completion's.  A
-- received-so-far grade would drop messages from the middle of the prefix,
-- which leaves no prefix of the global type; it is not defined.
gradeₛ : (G : Global) → ACut G → Grade
gradeₛ G κ = grade (G ↾ complete κ)

----------------------------------------------------------------------
-- (Y-1) Conservativity.

-- Ledger Y-1.
complete-embed : ∀ {G} (c : Cut G) → complete (embed c) ≡ c
complete-embed stop                                  = refl
complete-embed (cont-msg {s} {r} {g} c)              = cong (cont-msg {s} {r} {g}) (complete-embed c)
complete-embed (cont-choice {s} {r} {g} c₁ c₂)       =
  cong₂ (cont-choice {s} {r} {g}) (complete-embed c₁) (complete-embed c₂)

-- And back: a cut with nothing in flight is an embedded synchronous cut, so
-- embed is a bijection onto the settled cuts.
-- Ledger Y-1.
embed-complete : ∀ {G} {κ : ACut G} → Settled κ → embed (complete κ) ≡ κ
embed-complete stop                                    = refl
embed-complete (dlv-msg {s} {r} {g} c)                 = cong (dlv-msg {s} {r} {g}) (embed-complete c)
embed-complete (dlv-choice {s} {r} {g} c₁ c₂)          =
  cong₂ (dlv-choice {s} {r} {g}) (embed-complete c₁) (embed-complete c₂)

-- Ledger Y-1.
embed-settled : ∀ {G} (c : Cut G) → Settled (embed c)
embed-settled stop                = stop
embed-settled (cont-msg c)        = dlv-msg (embed-settled c)
embed-settled (cont-choice c₁ c₂) = dlv-choice (embed-settled c₁) (embed-settled c₂)

-- Ledger Y-1.
embed-causal : ∀ {G} (c : Cut G) → Causal (embed c)
embed-causal stop                = stop
embed-causal (cont-msg c)        = dlv-msg (embed-causal c)
embed-causal (cont-choice c₁ c₂) = dlv-choice (embed-causal c₁) (embed-causal c₂)

-- Ledger Y-1.
acutproj-embed : ∀ {G} p (c : Cut G) → acutproj p (embed c) ≡ cutproj p c
acutproj-embed p stop                            = refl
acutproj-embed p (cont-msg {s} {r} {g} c)        =
  cong (cutproj-msg {g = g} (role p s r)) (acutproj-embed p c)
acutproj-embed p (cont-choice {s} {r} {g} c₁ c₂) =
  cong₂ (cutproj-choice {g = g} (role p s r)) (acutproj-embed p c₁) (acutproj-embed p c₂)

-- An embedded cut's view is the projection of the truncated type.
aview-embed : ∀ p G (c : Cut G) → aview p G (embed c) ≡ proj p (G ↾ c)
aview-embed p G c = trans (cong (proj p G ↾ₗ_) (acutproj-embed p c)) (sym (proj-cut p G c))

amerge-embed : ∀ {p s r} (ρ : Role p s r) {G₁ G₂} (c₁ : Cut G₁) (c₂ : Cut G₂)
             → Merge p ρ (G₁ ↾ c₁) (G₂ ↾ c₂) → AMerge p ρ (embed c₁) (embed c₂)
amerge-embed         (sender _)     c₁ c₂ m = tt
amerge-embed         (receiver _ _) c₁ c₂ m = tt
amerge-embed {p = p} (outside _ _) {G₁} {G₂} c₁ c₂ m =
  trans (aview-embed p G₁ c₁) (trans m (sym (aview-embed p G₂ c₂)))

-- Ledger Y-1.
embed-consistent : ∀ {p G} (c : Cut G) → Consistent p c → AConsistent p (embed c)
embed-consistent         stop                            stop                  = stop
embed-consistent         (cont-msg c)                    (cont-msg k)          = dlv-msg (embed-consistent c k)
embed-consistent {p = p} (cont-choice {s} {r} c₁ c₂)     (cont-choice k₁ k₂ m) =
  dlv-choice (embed-consistent c₁ k₁) (embed-consistent c₂ k₂) (amerge-embed (role p s r) c₁ c₂ m)

-- Ledger Y-1.
grade↾ₐ-embed : ∀ p G (c : Cut G) → grade↾ₐ p G (embed c) ≡ grade↾ p (G ↾ c)
grade↾ₐ-embed p G                    stop                = refl
grade↾ₐ-embed p (msg s r g G)        (cont-msg c)        =
  cong (at (role p s r) g ⊗_) (grade↾ₐ-embed p G c)
grade↾ₐ-embed p (choice s r g G₁ G₂) (cont-choice c₁ c₂) =
  cong (at (role p s r) g ⊗_) (cong₂ _⊕_ (grade↾ₐ-embed p G₁ c₁) (grade↾ₐ-embed p G₂ c₂))

----------------------------------------------------------------------
-- (Y-2) Asynchronous K-CUT-LOSS.  One helper per node shape, each taking the
-- continuation's equation; the receiver of an interaction in flight is
-- quiet, so its continuation contributes 𝟙.

aloss-dlv-msg : ∀ {p s r} (ρ : Role p s r) g {L} (k : LCut L) {x}
              → x ≡ lgrade (L ↾ₗ k)
              → at ρ g ⊗ x ≡ lgrade (proj-msg ρ g L ↾ₗ cutproj-msg ρ k)
aloss-dlv-msg ρ g {L} k e = trans (grade-proj-msg ρ g e) (cong lgrade (proj-cut-msg ρ g L k))

aloss-flt-msg : ∀ {p s r} (ρ : Role p s r) g {L} (k : LCut L) {x}
              → x ≡ lgrade (L ↾ₗ k) → (p ≡ r → k ≡ stop)
              → atₐ ρ g ⊗ x ≡ lgrade (proj-msg ρ g L ↾ₗ fltproj-msg ρ k)
aloss-flt-msg (sender _)      g     k     e q = cong (g ⊗_) e
aloss-flt-msg (receiver _ pr) g {L} k     e q =
  trans (cong (𝟙 ⊗_) (trans e (cong (λ k' → lgrade (L ↾ₗ k')) (q pr)))) (IsSeqMonoid.unitˡ seq 𝟙)
aloss-flt-msg (outside _ _)   g     k {x} e q = trans (IsSeqMonoid.unitˡ seq x) e

-- Plain merge on views collapses the two branches of an outsider.
merge-views : ∀ {L₁ L₂ x₁ x₂} → x₁ ≡ lgrade L₁ → x₂ ≡ lgrade L₂ → L₁ ≡ L₂ → x₁ ⊕ x₂ ≡ lgrade L₁
merge-views {L₁} e₁ e₂ m =
  trans (cong₂ _⊕_ e₁ (trans e₂ (cong lgrade (sym m)))) (IsAltMonoid.idem alt (lgrade L₁))

aloss-dlv-choice : ∀ {p s r} (ρ : Role p s r) g {G₁ G₂} (c₁ : ACut G₁) (c₂ : ACut G₂) {x₁ x₂}
                 → x₁ ≡ lgrade (aview p G₁ c₁) → x₂ ≡ lgrade (aview p G₂ c₂) → AMerge p ρ c₁ c₂
                 → at ρ g ⊗ (x₁ ⊕ x₂)
                 ≡ lgrade (proj-choice ρ g (proj p G₁) (proj p G₂) ↾ₗ cutproj-choice ρ (acutproj p c₁) (acutproj p c₂))
aloss-dlv-choice (sender _)     g c₁ c₂ e₁ e₂ _ = cong (g ⊗_) (cong₂ _⊕_ e₁ e₂)
aloss-dlv-choice (receiver _ _) g c₁ c₂ e₁ e₂ _ = cong (g ⊗_) (cong₂ _⊕_ e₁ e₂)
aloss-dlv-choice (outside _ _)  g c₁ c₂ {x₁} {x₂} e₁ e₂ m =
  trans (IsSeqMonoid.unitˡ seq (x₁ ⊕ x₂)) (merge-views e₁ e₂ m)

aloss-flt-choice : ∀ {p s r} (ρ : Role p s r) g {G₁ G₂} (c₁ : ACut G₁) (c₂ : ACut G₂) {x₁ x₂}
                 → x₁ ≡ lgrade (aview p G₁ c₁) → x₂ ≡ lgrade (aview p G₂ c₂) → AMerge p ρ c₁ c₂
                 → (p ≡ r → acutproj p c₁ ≡ stop) → (p ≡ r → acutproj p c₂ ≡ stop)
                 → atₐ ρ g ⊗ (x₁ ⊕ x₂)
                 ≡ lgrade (proj-choice ρ g (proj p G₁) (proj p G₂) ↾ₗ fltproj-choice ρ (acutproj p c₁) (acutproj p c₂))
aloss-flt-choice (sender _)      g c₁ c₂ e₁ e₂ _ q₁ q₂ = cong (g ⊗_) (cong₂ _⊕_ e₁ e₂)
aloss-flt-choice {p = p} (receiver _ pr) g {G₁} {G₂} c₁ c₂ e₁ e₂ _ q₁ q₂ =
  trans (cong (𝟙 ⊗_) (cong₂ _⊕_ (quiet-𝟙 G₁ c₁ e₁ (q₁ pr)) (quiet-𝟙 G₂ c₂ e₂ (q₂ pr))))
  (trans (IsSeqMonoid.unitˡ seq (𝟙 ⊕ 𝟙)) (IsAltMonoid.idem alt 𝟙))
  where
  quiet-𝟙 : ∀ G (c : ACut G) {x} → x ≡ lgrade (aview p G c) → acutproj p c ≡ stop → x ≡ 𝟙
  quiet-𝟙 G c e q = trans e (cong (λ k → lgrade (proj p G ↾ₗ k)) q)
aloss-flt-choice (outside _ _)   g c₁ c₂ {x₁} {x₂} e₁ e₂ m q₁ q₂ =
  trans (IsSeqMonoid.unitˡ seq (x₁ ⊕ x₂)) (merge-views e₁ e₂ m)

-- The receiver of an interaction in flight is quiet in what follows.
quiet-at : ∀ {p r G} (c : ACut G) → Quiet r c → p ≡ r → acutproj p c ≡ stop
quiet-at c q e = subst (λ t → acutproj t c ≡ stop) (sym e) q

-- Ledger Y-2.
akcut-loss : ∀ p G (κ : ACut G) → Causal κ → AConsistent p κ
           → grade↾ₐ p G κ ≡ lgrade (aview p G κ)
akcut-loss p G                    stop               _                         _                      = refl
akcut-loss p (msg s r g G)        (dlv-msg c)        (dlv-msg a)               (dlv-msg k)            =
  aloss-dlv-msg (role p s r) g (acutproj p c) (akcut-loss p G c a k)
akcut-loss p (msg s r g G)        (flt-msg c)        (flt-msg a q)             (flt-msg k)            =
  aloss-flt-msg (role p s r) g (acutproj p c) (akcut-loss p G c a k) (quiet-at c q)
akcut-loss p (choice s r g G₁ G₂) (dlv-choice c₁ c₂) (dlv-choice a₁ a₂)       (dlv-choice k₁ k₂ m)   =
  aloss-dlv-choice (role p s r) g c₁ c₂ (akcut-loss p G₁ c₁ a₁ k₁) (akcut-loss p G₂ c₂ a₂ k₂) m
akcut-loss p (choice s r g G₁ G₂) (flt-choice c₁ c₂) (flt-choice a₁ a₂ q₁ q₂) (flt-choice k₁ k₂ m)   =
  aloss-flt-choice (role p s r) g c₁ c₂ (akcut-loss p G₁ c₁ a₁ k₁) (akcut-loss p G₂ c₂ a₂ k₂) m
                   (quiet-at c₁ q₁) (quiet-at c₂ q₂)

----------------------------------------------------------------------
-- (Y-3) Delivering an interaction in flight changes only its receiver's
-- local cut.

invisible-msg : ∀ {p s r g L} (ρ : Role p s r) (k : LCut L) → p ≢ r
              → fltproj-msg {g = g} ρ k ≡ cutproj-msg ρ k
invisible-msg (sender _)     k _  = refl
invisible-msg (receiver _ e) k ne = ⊥-elim (ne e)
invisible-msg (outside _ _)  k _  = refl

invisible-choice : ∀ {p s r g L₁ L₂} (ρ : Role p s r) (k₁ : LCut L₁) (k₂ : LCut L₂) → p ≢ r
                 → fltproj-choice {g = g} ρ k₁ k₂ ≡ cutproj-choice ρ k₁ k₂
invisible-choice (sender _)     k₁ k₂ _  = refl
invisible-choice (receiver _ e) k₁ k₂ ne = ⊥-elim (ne e)
invisible-choice (outside _ _)  k₁ k₂ _  = refl

-- Ledger Y-3.
flight-invisible : ∀ p {s r g G} (c : ACut G) → p ≢ r
                 → acutproj p (flt-msg {s} {r} {g} c) ≡ acutproj p (dlv-msg c)
flight-invisible p {s} {r} c ne = invisible-msg (role p s r) (acutproj p c) ne

-- Ledger Y-3.
flight-invisible-choice : ∀ p {s r g G₁ G₂} (c₁ : ACut G₁) (c₂ : ACut G₂) → p ≢ r
                        → acutproj p (flt-choice {s} {r} {g} c₁ c₂) ≡ acutproj p (dlv-choice c₁ c₂)
flight-invisible-choice p {s} {r} c₁ c₂ ne = invisible-choice (role p s r) (acutproj p c₁) (acutproj p c₂) ne

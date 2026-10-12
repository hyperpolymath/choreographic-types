{-# OPTIONS --safe --without-K #-}
-- SPDX-License-Identifier: MPL-2.0
-- SPDX-FileCopyrightText: 2026 Jonathan D.A. Jewell
--
-- K-CUT-WARRANT, transport component.
--
-- (T1) Party access.  p ⊑ q ("q sees at least what p sees") when every
--      distinction p's view makes, q's makes.  It is a preorder — the
--      Preorder record of epistemic-types, instantiated — and knowledge is
--      monotone along it: this is the `increase` of their AccessibleModality.
-- (T2) The local frontier is known.  Truncation of a local type is
--      injective in the cut, so equal views mean equal projected cuts: at
--      every world p knows exactly how far its own timeline has run, and
--      therefore every fact about its own frontier — receiving is knowing
--      it was received.  In this synchronous fragment the sender knows the
--      same of its sends; asynchrony is where that symmetry breaks.
-- (T3) Why AccessibleModality itself cannot be instantiated: its carrier is
--      E : K → Set → Set, but Kripke knowledge is indexed by worlds,
--      E : K → (World → Set) → (World → Set).  IndexedAccessible below is
--      the same record with that one change; the choreographic frame
--      instantiates it with every law holding by `refl`.
open import ResourceAlgebra.Core

module Choreographic.Transport (R : ResourceAlgebra) where

open import ResourceAlgebra.Prelude
open import Choreographic.Party
open import Choreographic.Global     R
open import Choreographic.Local      R
open import Choreographic.Projection R
open import Choreographic.Kripke     R
open import EpistemicTypes.Access using (Preorder)
open ResourceAlgebra R

----------------------------------------------------------------------
-- (T2a) Truncating a local type is injective in the cut.
-- Injectivity of the local constructors, via projections (matching `refl`
-- on `send q g L ≡ send q g L'` would need K to discharge g ≡ g on an
-- abstract Grade; projections need nothing).
left right : Local → Local
left  end                = end
left  (send _ _ L)       = L
left  (recv _ _ L)       = L
left  (select _ _ L₁ _)  = L₁
left  (branch _ _ L₁ _)  = L₁
right end                = end
right (send _ _ L)       = L
right (recv _ _ L)       = L
right (select _ _ _ L₂)  = L₂
right (branch _ _ _ L₂)  = L₂

send-inj : ∀ {q g L L'} → send q g L ≡ send q g L' → L ≡ L'
send-inj = cong left

recv-inj : ∀ {q g L L'} → recv q g L ≡ recv q g L' → L ≡ L'
recv-inj = cong left

select-inj₁ : ∀ {q g L₁ L₂ L₁' L₂'} → select q g L₁ L₂ ≡ select q g L₁' L₂' → L₁ ≡ L₁'
select-inj₁ = cong left

select-inj₂ : ∀ {q g L₁ L₂ L₁' L₂'} → select q g L₁ L₂ ≡ select q g L₁' L₂' → L₂ ≡ L₂'
select-inj₂ = cong right

branch-inj₁ : ∀ {q g L₁ L₂ L₁' L₂'} → branch q g L₁ L₂ ≡ branch q g L₁' L₂' → L₁ ≡ L₁'
branch-inj₁ = cong left

branch-inj₂ : ∀ {q g L₁ L₂ L₁' L₂'} → branch q g L₁ L₂ ≡ branch q g L₁' L₂' → L₂ ≡ L₂'
branch-inj₂ = cong right

↾ₗ-injective : ∀ L (c c' : LCut L) → L ↾ₗ c ≡ L ↾ₗ c' → c ≡ c'
↾ₗ-injective L                  stop                 stop                   e = refl
↾ₗ-injective (send q g L)       stop                 (cont-send c')         ()
↾ₗ-injective (send q g L)       (cont-send c)        stop                   ()
↾ₗ-injective (send q g L)       (cont-send c)        (cont-send c')         e =
  cong cont-send (↾ₗ-injective L c c' (send-inj e))
↾ₗ-injective (recv q g L)       stop                 (cont-recv c')         ()
↾ₗ-injective (recv q g L)       (cont-recv c)        stop                   ()
↾ₗ-injective (recv q g L)       (cont-recv c)        (cont-recv c')         e =
  cong cont-recv (↾ₗ-injective L c c' (recv-inj e))
↾ₗ-injective (select q g L₁ L₂) stop                 (cont-select c₁' c₂')  ()
↾ₗ-injective (select q g L₁ L₂) (cont-select c₁ c₂)  stop                   ()
↾ₗ-injective (select q g L₁ L₂) (cont-select c₁ c₂)  (cont-select c₁' c₂')  e =
  cong₂ cont-select (↾ₗ-injective L₁ c₁ c₁' (select-inj₁ e)) (↾ₗ-injective L₂ c₂ c₂' (select-inj₂ e))
↾ₗ-injective (branch q g L₁ L₂) stop                 (cont-branch c₁' c₂')  ()
↾ₗ-injective (branch q g L₁ L₂) (cont-branch c₁ c₂)  stop                   ()
↾ₗ-injective (branch q g L₁ L₂) (cont-branch c₁ c₂)  (cont-branch c₁' c₂')  e =
  cong₂ cont-branch (↾ₗ-injective L₁ c₁ c₁' (branch-inj₁ e)) (↾ₗ-injective L₂ c₂ c₂' (branch-inj₂ e))

module Over (G : Global) where
  open Frame G

  ----------------------------------------------------------------------
  -- (T2b) The local frontier is known at every world, and p-accessibility
  -- is exactly sameness of the local frontier.
  knows-local-cut : ∀ p w → Knows p w (λ w' → cutproj p (cut w') ≡ cutproj p (cut w))
  knows-local-cut p w w' e =
    ↾ₗ-injective (proj p G) (cutproj p (cut w')) (cutproj p (cut w)) (sym e)

  -- Any fact about p's own frontier is known: receiving is knowing it was
  -- received (and, synchronously, sending is knowing it was sent).
  knows-local : ∀ p w (P : LCut (proj p G) → Set)
              → P (cutproj p (cut w)) → Knows p w (λ w' → P (cutproj p (cut w')))
  knows-local p w P h w' e = subst P (sym (knows-local-cut p w w' e)) h

  local-cut-determines : ∀ p {w w'} → cutproj p (cut w) ≡ cutproj p (cut w') → w ~[ p ] w'
  local-cut-determines p e = cong (proj p G ↾ₗ_) e

  ----------------------------------------------------------------------
  -- (T1) Party access: q sees at least what p sees.
  infix 4 _⊑_
  _⊑_ : Party → Party → Set
  p ⊑ q = ∀ w w' → w ~[ q ] w' → w ~[ p ] w'

  ⊑-refl : ∀ p → p ⊑ p
  ⊑-refl p w w' a = a

  ⊑-trans : ∀ {p q r} → p ⊑ q → q ⊑ r → p ⊑ r
  ⊑-trans pq qr w w' a = pq w w' (qr w w' a)

  knows-mono : ∀ {p q} w {φ} → p ⊑ q → Knows p w φ → Knows q w φ
  knows-mono w pq k w' a = k w' (pq w w' a)

  -- epistemic-types' Preorder, instantiated on parties.
  party-access : Preorder Party
  party-access = record { _≤κ_ = _⊑_ ; refl≤ = λ {p} → ⊑-refl p ; trans≤ = ⊑-trans }

  ----------------------------------------------------------------------
  -- (T3) AccessibleModality over world-indexed propositions.  Field for
  -- field the epistemic-types record, with E indexed by worlds.
  record IndexedAccessible (K : Set) (W : Set) : Set₁ where
    field
      E        : K → (W → Set) → (W → Set)
      map      : ∀ {κ A B} → (∀ w → A w → B w) → ∀ w → E κ A w → E κ B w
      access   : Preorder K
    open Preorder access public
    field
      increase       : ∀ {κ κ' A} → κ ≤κ κ' → ∀ w → E κ A w → E κ' A w
      increase-refl  : ∀ {κ A} w (x : E κ A w) → increase refl≤ w x ≡ x
      increase-trans : ∀ {κ₀ κ₁ κ₂ A} (p : κ₀ ≤κ κ₁) (q : κ₁ ≤κ κ₂) w (x : E κ₀ A w)
                     → increase q w (increase p w x) ≡ increase (trans≤ p q) w x

  -- Knowledge in the choreographic frame is such a modality, lawfully, by refl.
  knowledge : IndexedAccessible Party World
  knowledge = record
    { E = λ κ φ w → Knows κ w φ
    ; map = λ f w k w' a → f w' (k w' a)
    ; access = party-access
    ; increase = λ pq w k → knows-mono w pq k
    ; increase-refl = λ w x → refl
    ; increase-trans = λ p q w x → refl
    }

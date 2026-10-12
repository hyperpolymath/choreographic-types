{-# OPTIONS --safe --without-K #-}
-- SPDX-License-Identifier: MPL-2.0
-- SPDX-FileCopyrightText: 2026 Jonathan D.A. Jewell
--
-- The two-thread diamond, at the type level.
--
-- applications/rapidnj-two-thread.agda asks, operationally, for a state
-- diamond on two independent events and for K-CUT-LOSS across that
-- frontier.  Here is the type-level counterpart: two interactions between
-- disjoint pairs of parties can be swapped without changing any endpoint's
-- projection or restricted grade.  Only ⊗-left-unit is used.
--
-- The *unrestricted* global grade swaps only if ⊗ commutes — true for Loss
-- and MaxPlus, FALSE for the high-water-mark algebra (Instances.agda,
-- `hwm-order-sensitive`): independent threads have an order-dependent peak
-- occupancy even though every endpoint's view is order-free.  That is the
-- first application-level consequence of "an occupancy bound is not a
-- cost bound".
open import ResourceAlgebra.Core

module Choreographic.Swap (R : ResourceAlgebra) where

open import ResourceAlgebra.Prelude
open import Choreographic.Party
open import Choreographic.Global     R
open import Choreographic.Local      R
open import Choreographic.Projection R
open ResourceAlgebra R

-- {s, r} and {s', r'} share no party.
record Disjoint (s r s' r' : Party) : Set where
  constructor disjoint
  field
    s≢s' : s ≢ s'
    s≢r' : s ≢ r'
    r≢s' : r ≢ s'
    r≢r' : r ≢ r'

⊥-elim : {A : Set} → ⊥ → A
⊥-elim ()

-- A party can take part in at most one of two disjoint interactions, so the
-- two projection steps commute.
swap-msg : ∀ {p s r s' r'} (ρ₁ : Role p s r) (ρ₂ : Role p s' r') → Disjoint s r s' r'
         → ∀ g g' L → proj-msg ρ₁ g (proj-msg ρ₂ g' L) ≡ proj-msg ρ₂ g' (proj-msg ρ₁ g L)
swap-msg (outside _ _)   _                _ g g' L = refl
swap-msg (sender _)      (outside _ _)    _ g g' L = refl
swap-msg (receiver _ _)  (outside _ _)    _ g g' L = refl
swap-msg (sender e)      (sender e')      d g g' L = ⊥-elim (Disjoint.s≢s' d (trans (sym e) e'))
swap-msg (sender e)      (receiver _ e')  d g g' L = ⊥-elim (Disjoint.s≢r' d (trans (sym e) e'))
swap-msg (receiver _ e)  (sender e')      d g g' L = ⊥-elim (Disjoint.r≢s' d (trans (sym e) e'))
swap-msg (receiver _ e)  (receiver _ e')  d g g' L = ⊥-elim (Disjoint.r≢r' d (trans (sym e) e'))

swap-proj : ∀ {s r s' r'} → Disjoint s r s' r' → ∀ p g g' G
          → proj p (msg s r g (msg s' r' g' G)) ≡ proj p (msg s' r' g' (msg s r g G))
swap-proj {s} {r} {s'} {r'} d p g g' G = swap-msg (role p s r) (role p s' r') d g g' (proj p G)

-- ... and so do the restricted grades (⊗-left-unit only).
swap-at : ∀ {p s r s' r'} (ρ₁ : Role p s r) (ρ₂ : Role p s' r') → Disjoint s r s' r'
        → ∀ g g' x → at ρ₁ g ⊗ (at ρ₂ g' ⊗ x) ≡ at ρ₂ g' ⊗ (at ρ₁ g ⊗ x)
swap-at (outside _ _)   ρ₂               _ g g' x =
  trans (IsSeqMonoid.unitˡ seq (at ρ₂ g' ⊗ x)) (cong (at ρ₂ g' ⊗_) (sym (IsSeqMonoid.unitˡ seq x)))
swap-at (sender _)      (outside _ _)    _ g g' x =
  trans (cong (g ⊗_) (IsSeqMonoid.unitˡ seq x)) (sym (IsSeqMonoid.unitˡ seq (g ⊗ x)))
swap-at (receiver _ _)  (outside _ _)    _ g g' x =
  trans (cong (g ⊗_) (IsSeqMonoid.unitˡ seq x)) (sym (IsSeqMonoid.unitˡ seq (g ⊗ x)))
swap-at (sender e)      (sender e')      d g g' x = ⊥-elim (Disjoint.s≢s' d (trans (sym e) e'))
swap-at (sender e)      (receiver _ e')  d g g' x = ⊥-elim (Disjoint.s≢r' d (trans (sym e) e'))
swap-at (receiver _ e)  (sender e')      d g g' x = ⊥-elim (Disjoint.r≢s' d (trans (sym e) e'))
swap-at (receiver _ e)  (receiver _ e')  d g g' x = ⊥-elim (Disjoint.r≢r' d (trans (sym e) e'))

swap-grade↾ : ∀ {s r s' r'} → Disjoint s r s' r' → ∀ p g g' G
            → grade↾ p (msg s r g (msg s' r' g' G)) ≡ grade↾ p (msg s' r' g' (msg s r g G))
swap-grade↾ {s} {r} {s'} {r'} d p g g' G = swap-at (role p s r) (role p s' r') d g g' (grade↾ p G)

-- The global grade swaps exactly when the two grades commute under ⊗.
swap-grade : ∀ {s r s' r'} g g' G → g ⊗ g' ≡ g' ⊗ g
           → grade (msg s r g (msg s' r' g' G)) ≡ grade (msg s' r' g' (msg s r g G))
swap-grade g g' G c =
  trans (sym (IsSeqMonoid.assoc seq g g' (grade G)))
  (trans (cong (_⊗ grade G) c)
         (IsSeqMonoid.assoc seq g' g (grade G)))

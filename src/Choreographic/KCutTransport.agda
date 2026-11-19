{-# OPTIONS --safe --without-K #-}
-- SPDX-License-Identifier: MPL-2.0
-- SPDX-FileCopyrightText: 2026 Jonathan D.A. Jewell
--
-- K-CUT-LOSS transported along morphisms of resource algebras
-- (resource-algebra's Morphism.agda: Hom strict, LaxHom lax).
--
-- A grade map f : A → B maps a choreography graded in A to the same
-- choreography graded in B (gmap), its cuts with it (cmap), and its local
-- types with it (lmap).  The structural part needs nothing of f: mapping
-- commutes with cutting and with projection, and consistency transports.
--
-- Then:
--   strict  h (grade↾ p G) ≡ grade↾ p (gmap G), so K-CUT-LOSS holds in B
--           for the mapped protocol and the mapped A-side grade equals the
--           B-side local grade on the nose (kcut-loss-hom).
--   lax     with IsOrdered B, h (grade↾ p G) ≼ grade↾ p (gmap G), so the
--           mapped A-side grade is bounded by the B-side local grade
--           (kcut-loss-lax).  Uses map-𝟙, map-⊗ (≼), exact map-⊕, ⊕-mono
--           and ⊗-monoˡ only: the ⊗ factor passes through h exactly.
--
-- The 𝟘 gap.  A LaxHom need not preserve 𝟘 (only B.𝟘 ≼ h A.𝟘), so a fold
-- with a 𝟘 leaf would break the lax bound (tests/reject/LaxZeroLeaf).
-- grade and grade↾ never reach 𝟘: end and `outside` contribute 𝟙, and choice
-- is binary.  So no side condition is needed here.
open import ResourceAlgebra.Core

module Choreographic.KCutTransport (A B : ResourceAlgebra) where

open import ResourceAlgebra.Prelude
open import ResourceAlgebra.Morphism using (Hom; LaxHom)
open import Choreographic.Party

private
  module A where
    open ResourceAlgebra A public
    open import Choreographic.Global     A public
    open import Choreographic.Local      A public
    open import Choreographic.Projection A public
    open import Choreographic.KCut       A public
  module B where
    open ResourceAlgebra B public
    open import Choreographic.Global     B public
    open import Choreographic.Local      B public
    open import Choreographic.Projection B public
    open import Choreographic.KCut       B public

----------------------------------------------------------------------
-- (S) Structure: any grade map, no laws.
module Map (f : A.Grade → B.Grade) where

  gmap : A.Global → B.Global
  gmap A.end                  = B.end
  gmap (A.msg s r g G)        = B.msg s r (f g) (gmap G)
  gmap (A.choice s r g G₁ G₂) = B.choice s r (f g) (gmap G₁) (gmap G₂)

  lmap : A.Local → B.Local
  lmap A.end                = B.end
  lmap (A.send q g L)       = B.send q (f g) (lmap L)
  lmap (A.recv q g L)       = B.recv q (f g) (lmap L)
  lmap (A.select q g L₁ L₂) = B.select q (f g) (lmap L₁) (lmap L₂)
  lmap (A.branch q g L₁ L₂) = B.branch q (f g) (lmap L₁) (lmap L₂)

  cmap : ∀ {G} → A.Cut G → B.Cut (gmap G)
  cmap A.stop                = B.stop
  cmap (A.cont-msg c)        = B.cont-msg (cmap c)
  cmap (A.cont-choice c₁ c₂) = B.cont-choice (cmap c₁) (cmap c₂)

  -- Ledger KM-1.
  gmap-cut : ∀ G (c : A.Cut G) → gmap (G A.↾ c) ≡ (gmap G B.↾ cmap c)
  gmap-cut G                      A.stop                = refl
  gmap-cut (A.msg s r g G)        (A.cont-msg c)        = cong (B.msg s r (f g)) (gmap-cut G c)
  gmap-cut (A.choice s r g G₁ G₂) (A.cont-choice c₁ c₂) =
    cong₂ (B.choice s r (f g)) (gmap-cut G₁ c₁) (gmap-cut G₂ c₂)

  proj-msg-map : ∀ {p s r} (ρ : Role p s r) g L
               → B.proj-msg ρ (f g) (lmap L) ≡ lmap (A.proj-msg ρ g L)
  proj-msg-map (sender _)     g L = refl
  proj-msg-map (receiver _ _) g L = refl
  proj-msg-map (outside _ _)  g L = refl

  proj-choice-map : ∀ {p s r} (ρ : Role p s r) g L₁ L₂
                  → B.proj-choice ρ (f g) (lmap L₁) (lmap L₂) ≡ lmap (A.proj-choice ρ g L₁ L₂)
  proj-choice-map (sender _)     g L₁ L₂ = refl
  proj-choice-map (receiver _ _) g L₁ L₂ = refl
  proj-choice-map (outside _ _)  g L₁ L₂ = refl

  -- Ledger KM-1.
  proj-gmap : ∀ p G → B.proj p (gmap G) ≡ lmap (A.proj p G)
  proj-gmap p A.end                  = refl
  proj-gmap p (A.msg s r g G)        =
    trans (cong (B.proj-msg (role p s r) (f g)) (proj-gmap p G))
          (proj-msg-map (role p s r) g (A.proj p G))
  proj-gmap p (A.choice s r g G₁ G₂) =
    trans (cong₂ (B.proj-choice (role p s r) (f g)) (proj-gmap p G₁) (proj-gmap p G₂))
          (proj-choice-map (role p s r) g (A.proj p G₁) (A.proj p G₂))

  merge-map : ∀ p {s r} (ρ : Role p s r) G₁ G₂
            → A.Merge p ρ G₁ G₂ → B.Merge p ρ (gmap G₁) (gmap G₂)
  merge-map p (sender _)     G₁ G₂ m = tt
  merge-map p (receiver _ _) G₁ G₂ m = tt
  merge-map p (outside _ _)  G₁ G₂ m =
    trans (proj-gmap p G₁) (trans (cong lmap m) (sym (proj-gmap p G₂)))

  -- Ledger KM-1.
  consistent-map : ∀ p {G} (c : A.Cut G) → A.Consistent p c → B.Consistent p (cmap c)
  consistent-map p A.stop A.stop = B.stop
  consistent-map p (A.cont-msg c) (A.cont-msg k) = B.cont-msg (consistent-map p c k)
  consistent-map p (A.cont-choice {s} {r} {g} {G₁} {G₂} c₁ c₂) (A.cont-choice k₁ k₂ m) =
    B.cont-choice (consistent-map p c₁ k₁) (consistent-map p c₂ k₂)
      (subst₂′ (B.Merge p (role p s r)) (gmap-cut G₁ c₁) (gmap-cut G₂ c₂)
               (merge-map p (role p s r) (G₁ A.↾ c₁) (G₂ A.↾ c₂) m))
    where
    subst₂′ : ∀ {X : Set} (P : X → X → Set) {a b c d : X} → a ≡ b → c ≡ d → P a c → P b d
    subst₂′ P refl refl x = x

----------------------------------------------------------------------
-- (H) Strict morphisms: equality.
module Strict (h : Hom A B) where
  open Hom h
  open Map map public

  at-map : ∀ {p s r} (ρ : Role p s r) g → map (A.at ρ g) ≡ B.at ρ (map g)
  at-map (sender _)     g = refl
  at-map (receiver _ _) g = refl
  at-map (outside _ _)  g = map-𝟙

  -- Ledger KM-2.
  hom-grade : ∀ G → map (A.grade G) ≡ B.grade (gmap G)
  hom-grade A.end                  = map-𝟙
  hom-grade (A.msg s r g G)        =
    trans (map-⊗ g (A.grade G)) (cong (map g B.⊗_) (hom-grade G))
  hom-grade (A.choice s r g G₁ G₂) =
    trans (map-⊗ g (A.grade G₁ A.⊕ A.grade G₂))
    (cong (map g B.⊗_)
      (trans (map-⊕ (A.grade G₁) (A.grade G₂))
             (cong₂ B._⊕_ (hom-grade G₁) (hom-grade G₂))))

  -- Ledger KM-2.
  hom-grade↾ : ∀ p G → map (A.grade↾ p G) ≡ B.grade↾ p (gmap G)
  hom-grade↾ p A.end                  = map-𝟙
  hom-grade↾ p (A.msg s r g G)        =
    trans (map-⊗ (A.at (role p s r) g) (A.grade↾ p G))
          (cong₂ B._⊗_ (at-map (role p s r) g) (hom-grade↾ p G))
  hom-grade↾ p (A.choice s r g G₁ G₂) =
    trans (map-⊗ (A.at (role p s r) g) (A.grade↾ p G₁ A.⊕ A.grade↾ p G₂))
    (cong₂ B._⊗_ (at-map (role p s r) g)
      (trans (map-⊕ (A.grade↾ p G₁) (A.grade↾ p G₂))
             (cong₂ B._⊕_ (hom-grade↾ p G₁) (hom-grade↾ p G₂))))

  -- Strict transport of K-CUT-LOSS: the A-side restricted grade at the cut,
  -- mapped, is the B-side local grade of the mapped protocol at the mapped
  -- cut.  K-CUT-LOSS is used in B, on the transported consistent cut.
  -- Ledger KM-3.
  kcut-loss-hom : ∀ p G (c : A.Cut G) → A.Consistent p c
                → map (A.grade↾ p (G A.↾ c)) ≡ B.lgrade (B.proj p (gmap G) B.↾ₗ B.cutproj p (cmap c))
  kcut-loss-hom p G c k =
    trans (hom-grade↾ p (G A.↾ c))
    (trans (cong (B.grade↾ p) (gmap-cut G c))
           (B.kcut-loss p (gmap G) (cmap c) (consistent-map p c k)))

  -- The square: K-CUT-LOSS in A, mapped, agrees with K-CUT-LOSS in B.
  -- Ledger KM-3.
  kcut-square : ∀ p G (c : A.Cut G) → A.Consistent p c
              → map (A.lgrade (A.proj p G A.↾ₗ A.cutproj p c))
              ≡ B.lgrade (B.proj p (gmap G) B.↾ₗ B.cutproj p (cmap c))
  kcut-square p G c k =
    trans (cong map (sym (A.kcut-loss p G c k))) (kcut-loss-hom p G c k)

----------------------------------------------------------------------
-- (L) Lax morphisms: a bound, given ⊗ monotone (in its second argument)
-- in the target.
module Lax (h : LaxHom A B) (o : IsOrdered B) where
  open LaxHom h
  open Map map public

  private
    ≡-≼ : ∀ {x y z} → x ≡ y → y B.≼ z → x B.≼ z
    ≡-≼ refl q = q

    ≼-≡ : ∀ {x y z} → x B.≼ y → y ≡ z → x B.≼ z
    ≼-≡ q refl = q

    -- One ⊗ node: the factor passes exactly when its image is known.
    step : ∀ a b {a' y} → map a ≡ a' → map b B.≼ y → map (a A.⊗ b) B.≼ (a' B.⊗ y)
    step a b refl q = B.≼-trans (map-⊗ a b) (IsOrdered.⊗-monoˡ o (map a) q)

    -- One ⊕ node: exact, then monotone.
    alt : ∀ a b {x y} → map a B.≼ x → map b B.≼ y → map (a A.⊕ b) B.≼ (x B.⊕ y)
    alt a b p q = ≡-≼ (map-⊕ a b) (B.⊕-mono p q)

  at-map : ∀ {p s r} (ρ : Role p s r) g → map (A.at ρ g) ≡ B.at ρ (map g)
  at-map (sender _)     g = refl
  at-map (receiver _ _) g = refl
  at-map (outside _ _)  g = map-𝟙

  -- Ledger KM-4.
  lax-grade : ∀ G → map (A.grade G) B.≼ B.grade (gmap G)
  lax-grade A.end                  = ≡-≼ map-𝟙 (B.≼-refl B.𝟙)
  lax-grade (A.msg s r g G)        = step g (A.grade G) refl (lax-grade G)
  lax-grade (A.choice s r g G₁ G₂) =
    step g (A.grade G₁ A.⊕ A.grade G₂) refl
         (alt (A.grade G₁) (A.grade G₂) (lax-grade G₁) (lax-grade G₂))

  -- Ledger KM-4.
  lax-grade↾ : ∀ p G → map (A.grade↾ p G) B.≼ B.grade↾ p (gmap G)
  lax-grade↾ p A.end                  = ≡-≼ map-𝟙 (B.≼-refl B.𝟙)
  lax-grade↾ p (A.msg s r g G)        =
    step (A.at (role p s r) g) (A.grade↾ p G) (at-map (role p s r) g) (lax-grade↾ p G)
  lax-grade↾ p (A.choice s r g G₁ G₂) =
    step (A.at (role p s r) g) (A.grade↾ p G₁ A.⊕ A.grade↾ p G₂) (at-map (role p s r) g)
         (alt (A.grade↾ p G₁) (A.grade↾ p G₂) (lax-grade↾ p G₁) (lax-grade↾ p G₂))

  -- Lax transport of K-CUT-LOSS: the A-side restricted grade at the cut,
  -- mapped, is at most the B-side local grade of the mapped protocol at
  -- the mapped cut.
  -- Ledger KM-5.
  kcut-loss-lax : ∀ p G (c : A.Cut G) → A.Consistent p c
                → map (A.grade↾ p (G A.↾ c)) B.≼ B.lgrade (B.proj p (gmap G) B.↾ₗ B.cutproj p (cmap c))
  kcut-loss-lax p G c k =
    ≼-≡ (lax-grade↾ p (G A.↾ c))
        (trans (cong (B.grade↾ p) (gmap-cut G c))
               (B.kcut-loss p (gmap G) (cmap c) (consistent-map p c k)))

  -- The lax square: K-CUT-LOSS in A, mapped, is bounded by K-CUT-LOSS in B.
  -- Ledger KM-5.
  kcut-square-lax : ∀ p G (c : A.Cut G) → A.Consistent p c
                  → map (A.lgrade (A.proj p G A.↾ₗ A.cutproj p c))
                    B.≼ B.lgrade (B.proj p (gmap G) B.↾ₗ B.cutproj p (cmap c))
  kcut-square-lax p G c k =
    ≡-≼ (cong map (sym (A.kcut-loss p G c k))) (kcut-loss-lax p G c k)

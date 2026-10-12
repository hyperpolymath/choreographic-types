{-# OPTIONS --safe --without-K #-}
-- SPDX-License-Identifier: MPL-2.0
-- A deliberately impoverished Core used ONLY by scripts/minimal-laws.sh to
-- certify which laws K-CUT-LOSS depends on.  Not part of the library.
module ResourceAlgebra.Core where
open import ResourceAlgebra.Prelude
record IsAltMonoid {G : Set} (_⊕_ : G → G → G) (𝟘 : G) : Set where
  field idem : ∀ a → a ⊕ a ≡ a
record IsSeqMonoid {G : Set} (_⊗_ : G → G → G) (𝟙 : G) : Set where
  field unitˡ : ∀ a → 𝟙 ⊗ a ≡ a
record ResourceAlgebra : Set₁ where
  infixl 6 _⊕_
  infixl 7 _⊗_
  field
    Grade : Set
    _⊕_ : Grade → Grade → Grade
    _⊗_ : Grade → Grade → Grade
    𝟘 𝟙 : Grade
    alt : IsAltMonoid _⊕_ 𝟘
    seq : IsSeqMonoid _⊗_ 𝟙

{-# OPTIONS --safe --without-K #-}
-- SPDX-License-Identifier: MPL-2.0
-- SPDX-FileCopyrightText: 2026 Jonathan D.A. Jewell
--
-- Parties (roles) and the three-way role a party plays in an interaction.
-- Every case analysis in the development goes through `role`, so that the
-- projection, the cut projection and the theorems split in the same way.
module Choreographic.Party where

open import ResourceAlgebra.Prelude

Party : Set
Party = Nat

data Dec (A : Set) : Set where
  yes : A → Dec A
  no  : ¬ A → Dec A

suc-inj : ∀ {m n : Nat} → suc m ≡ suc n → m ≡ n
suc-inj refl = refl

infix 4 _≟_
_≟_ : (m n : Party) → Dec (m ≡ n)
zero  ≟ zero  = yes refl
zero  ≟ suc n = no (λ ())
suc m ≟ zero  = no (λ ())
suc m ≟ suc n with m ≟ n
... | yes e  = yes (cong suc e)
... | no  ne = no (λ q → ne (suc-inj q))

-- p's role in an interaction from s to r.
data Role (p s r : Party) : Set where
  sender   : p ≡ s → Role p s r
  receiver : p ≢ s → p ≡ r → Role p s r
  outside  : p ≢ s → p ≢ r → Role p s r

role : ∀ p s r → Role p s r
role p s r with p ≟ s
... | yes e  = sender e
... | no  ne with p ≟ r
...   | yes e   = receiver ne e
...   | no  ne' = outside ne ne'

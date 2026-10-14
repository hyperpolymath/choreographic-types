{-# OPTIONS --safe --without-K #-}
-- SPDX-License-Identifier: MPL-2.0
-- SPDX-FileCopyrightText: 2026 Jonathan D.A. Jewell
--
-- K-CUT-LOSS discharged at the three estate instances, plus one worked
-- protocol graded in each algebra (computed by the typechecker: TESTED).
module Choreographic.Instances where

open import ResourceAlgebra.Prelude
open import ResourceAlgebra.Core
open import ResourceAlgebra.Instances.Loss    using (Loss; fin; inf)
open import ResourceAlgebra.Instances.MaxPlus using (MaxPlus; val; bot; Tropical)
open import ResourceAlgebra.Instances.HWM     using (HWM; hwm)
open import Choreographic.Party

import Choreographic.KCut
module KL = Choreographic.KCut Loss
module KM = Choreographic.KCut MaxPlus
module KH = Choreographic.KCut HWM

-- The three discharges, by name.
-- Ledger K-6.
kcut-loss-Loss    = KL.kcut-loss
-- Ledger K-6.
kcut-loss-MaxPlus = KM.kcut-loss
-- Ledger K-6.
kcut-loss-HWM     = KH.kcut-loss

----------------------------------------------------------------------
-- A worked protocol.  Parties: 0 (client), 1 (broker), 2 (server).
--   0 → 1 : a . 1 → 2 : b . 0 → 2 chooses { 2 → 1 : c . end  |  2 → 1 : c . end }
-- Party 1 is outside the choice; both branches project identically for 1
-- (recv from 2 at grade c), so 1's projection is plain-mergeable.
module Worked (R : ResourceAlgebra) (a b c : ResourceAlgebra.Grade R) where
  open ResourceAlgebra R
  open import Choreographic.Global     R
  open import Choreographic.Local      R
  open import Choreographic.Projection R
  open import Choreographic.KCut       R

  G : Global
  G = msg 0 1 a (msg 1 2 b (choice 0 2 𝟙 (msg 2 1 c end) (msg 2 1 c end)))

  -- Ledger P-4.
  projectable-1 : Projectable 1 G
  projectable-1 = msg (msg (choice (msg end) (msg end) refl))

  -- Cut after the broker has forwarded, before the server answers.
  c₁ : Cut G
  c₁ = cont-msg (cont-msg (cont-choice stop stop))

  -- Ledger P-4.
  consistent-1 : Consistent 1 c₁
  consistent-1 = cont-msg (cont-msg (cont-choice stop stop refl))

  -- The keystone at this cut, for the broker.
  -- Ledger P-4.
  broker-cut : grade↾ 1 (G ↾ c₁) ≡ lgrade (proj 1 G ↾ₗ cutproj 1 c₁)
  broker-cut = kcut-loss 1 G c₁ consistent-1

-- Concrete readings (TESTED by evaluation).  The broker's projection is
-- recv 0 a (send 2 b (recv 2 c end)); at the cut c₁ only a and b remain.
module _ where
  open import Choreographic.Global Loss
  private module W = Worked Loss (fin 1) (fin 2) (fin 5)

  -- Ledger P-1.
  loss-broker : grade↾ 1 W.G ≡ fin 8
  loss-broker = refl

  -- Ledger P-1.
  loss-broker-cut : grade↾ 1 (W.G ↾ W.c₁) ≡ fin 3
  loss-broker-cut = refl

module _ where
  open import Choreographic.Global MaxPlus
  private module W = Worked MaxPlus (val 1) (val 2) (val 5)

  -- Ledger P-2.
  maxplus-broker : grade↾ 1 W.G ≡ val 8
  maxplus-broker = refl

-- Occupancy: peaks 1, 2 and 5 with nothing held between them reach 5, not 8.
module _ where
  open import Choreographic.Global HWM
  open import ResourceAlgebra.Instances.HWM using (peak)
  private module W = Worked HWM (hwm 1 0 z≤n) (hwm 2 0 z≤n) (hwm 5 0 z≤n)

  -- Ledger P-3.
  hwm-broker : peak (grade↾ 1 W.G) ≡ 5
  hwm-broker = refl

  -- Ledger P-3.
  hwm-broker-cut : peak (grade↾ 1 (W.G ↾ W.c₁)) ≡ 2
  hwm-broker-cut = refl

----------------------------------------------------------------------
-- K-CUT-WARRANT (bound form) discharged at the three instances.
import Choreographic.Bound
open import ResourceAlgebra.Instances.Loss    using (Loss-ordered; _⊓g_)
open import ResourceAlgebra.Instances.MaxPlus using (MaxPlus-ordered)
open import ResourceAlgebra.Instances.HWM     using (HWM-ordered)

module BH = Choreographic.Bound HWM     HWM-ordered
module BL = Choreographic.Bound Loss    Loss-ordered
module BM = Choreographic.Bound MaxPlus MaxPlus-ordered

-- HWM: the sequence unit is the least grade, so every type qualifies and
-- the restricted (occupancy) grade is a known lower bound on the global one.
-- Ledger W-6.
kcut-warrant-HWM = λ G p w → BH.knows-lower-bound G p (BH.each-of (ResourceAlgebra.𝟘-least HWM) G) w

-- Loss: the sequence unit fin 0 is the GREATEST grade in the absorption
-- order, so the bound runs the other way: the global loss is below the
-- restricted loss in ≼, i.e. numerically p's view accounts for no more loss
-- than the global total.
loss-unit-greatest : ∀ g → ResourceAlgebra._≼_ Loss g (fin 0)
loss-unit-greatest (fin m) = cong fin (min-zeroʳ m)
loss-unit-greatest inf     = refl

-- Ledger W-6.
kcut-warrant-Loss = λ G p w → BL.knows-upper-bound G p (BL.each-of loss-unit-greatest G) w

-- MaxPlus: val 0 is below every val n, but not below bot (−∞, the absent
-- branch).  The discharge therefore takes bot-freeness of G as a hypothesis.
maxplus-val-least : ∀ n → ResourceAlgebra._≼_ MaxPlus (val 0) (val n)
maxplus-val-least n = refl

-- Ledger W-6.
kcut-warrant-MaxPlus = λ G p (botfree : BM.Each (ResourceAlgebra._≼_ MaxPlus (val 0)) G) w →
  BM.knows-lower-bound G p botfree w

----------------------------------------------------------------------
-- The type cannot determine the global grade: two worlds party 2 cannot
-- tell apart with different global grades.  (TESTED by evaluation.)
-- Ledger W-7.
module Witness where
  open import Choreographic.Global     MaxPlus
  open import Choreographic.Projection MaxPlus
  open import Choreographic.Kripke     MaxPlus

  G : Global
  G = msg 0 1 (val 1) (msg 0 1 (val 1) end)

  open Frame G

  w₁ w₂ : World
  w₁ = cont-msg stop            , λ _ → cont-msg stop
  w₂ = cont-msg (cont-msg stop) , λ _ → cont-msg (cont-msg stop)

  indistinguishable : w₁ ~[ 2 ] w₂
  indistinguishable = refl

  grades-differ : grade (G ↾ cut w₁) ≢ grade (G ↾ cut w₂)
  grades-differ ()

  -- Yet the bound is known at w₁ and covers w₂.
  bound-at-w₂ : ResourceAlgebra._≼_ MaxPlus (grade↾ 2 (G ↾ cut w₁)) (grade (G ↾ cut w₂))
  bound-at-w₂ = kcut-warrant-MaxPlus G 2 botfree w₁ w₂ indistinguishable
    where
    botfree : BM.Each (ResourceAlgebra._≼_ MaxPlus (val 0)) G
    botfree = BM.msg refl (BM.msg refl BM.end)

----------------------------------------------------------------------
open import Choreographic.Swap using ()
-- Transport, on the same witness protocol (0 → 1 twice; 2 silent).
module TransportWitness where
  open import Choreographic.Global     MaxPlus
  open import Choreographic.Local      MaxPlus
  open import Choreographic.Projection MaxPlus
  open import Choreographic.Kripke     MaxPlus
  open import Choreographic.Transport  MaxPlus
  open Witness using (G; w₁; w₂)
  open Frame G
  open Over G

  -- A party that takes no part sees nothing, so every party sees at least
  -- what it sees: it is below everyone in the access preorder.
  end-cut : ∀ (c : LCut end) → end ↾ₗ c ≡ end
  end-cut stop = refl

  -- Ledger T-5.
  silent-⊑ : ∀ q → 2 ⊑ q
  silent-⊑ q w w' _ = trans (end-cut (cutproj 2 (cut w))) (sym (end-cut (cutproj 2 (cut w'))))

  -- Receiving is knowing it was received: at w₂ party 1 knows both messages
  -- have reached it ...
  -- Ledger T-2.
  receiver-knows : Knows 1 w₂ (λ w' → cutproj 1 (cut w') ≡ cont-recv (cont-recv stop))
  receiver-knows = knows-local-cut 1 w₂

  -- ... and, synchronously, the sender knows both were sent.  Asynchrony
  -- (send without receipt) is exactly where this symmetry would break.
  -- Ledger T-2.
  sender-knows : Knows 0 w₂ (λ w' → cutproj 0 (cut w') ≡ cont-send (cont-send stop))
  sender-knows = knows-local-cut 0 w₂

  -- What the silent party inherits by monotonicity is only what it could
  -- already know: knowledge flows UP the preorder, never down.
  -- Ledger T-5.
  inherited : Knows 1 w₂ (λ w' → cutproj 2 (cut w') ≡ cutproj 2 (cut w₂))
  inherited = knows-mono w₂ (silent-⊑ 1) (knows-local-cut 2 w₂)

----------------------------------------------------------------------
-- The two-thread diamond (Swap.agda) at the instances.  Loss and MaxPlus
-- sequence commutatively, so their global grades swap; the high-water
-- mark does not: "allocate 2 and release it, then allocate 3 and hold"
-- peaks at 3, the other order at 5.  Every endpoint's view is the same
-- either way (swap-proj), so the difference is invisible locally.
module Diamond where
  open import ResourceAlgebra.Instances.HWM using (peak; _⊗h_)

  a b : ResourceAlgebra.Grade HWM
  a = hwm 2 0 z≤n           -- allocate 2, release it
  b = hwm 3 3 (s≤s (s≤s (s≤s z≤n)))   -- allocate 3, hold it

  -- Ledger A-3.
  hwm-order-sensitive : peak (a ⊗h b) ≢ peak (b ⊗h a)
  hwm-order-sensitive ()

  -- Ledger A-2.
  loss-commutes : ∀ g g' → ResourceAlgebra._⊗_ Loss g g' ≡ ResourceAlgebra._⊗_ Loss g' g
  loss-commutes (fin m) (fin n) = cong fin (+-comm m n)
  loss-commutes (fin _) inf     = refl
  loss-commutes inf     (fin _) = refl
  loss-commutes inf     inf     = refl

  -- Ledger A-2.
  maxplus-commutes : ∀ g g' → ResourceAlgebra._⊗_ MaxPlus g g' ≡ ResourceAlgebra._⊗_ MaxPlus g' g
  maxplus-commutes (val m) (val n) = cong val (+-comm m n)
  maxplus-commutes (val _) bot     = refl
  maxplus-commutes bot     (val _) = refl
  maxplus-commutes bot     bot     = refl

----------------------------------------------------------------------
-- Two declarations of applications/rapidnj-two-thread.agda that cannot be
-- discharged as typed, shown unsatisfiable rather than reshaped.
-- Ledger A-7.
module NoTransportLoss where
  open import Choreographic.Global     MaxPlus
  open import Choreographic.Local      MaxPlus
  open import Choreographic.Projection MaxPlus

  -- `transportLoss : Role → Grade → Grade` presumes the local grade is a
  -- function of the global grade.  Two states with global grade val 1 give
  -- party 0 local grades val 1 and val 0.
  s t : Global
  s = msg 0 1 (val 1) end
  t = msg 2 3 (val 1) end

  same-global : grade s ≡ grade t
  same-global = refl

  no-such-function : ¬ (Σ (Tropical → Tropical) (λ f → ∀ u → lgrade (proj 0 u) ≡ f (grade u)))
  no-such-function (f , h) = absurd (trans (h s) (sym (h t)))
    where
    absurd : lgrade (proj 0 s) ≡ lgrade (proj 0 t) → ⊥
    absurd ()

-- Ledger A-8.
module GradeNotStateInvariant where
  open import Choreographic.Global      HWM
  open import Choreographic.Projection  HWM
  open import Choreographic.Operational HWM
  open import Choreographic.Swap        HWM using (swap-proj; disjoint)
  open import ResourceAlgebra.Instances.HWM using (peak)
  open Diamond using (a; b)

  -- `globalGradeRespectsStateEq` fails for occupancy: these two states are
  -- projection-equivalent (independent interactions swapped), yet their
  -- global peaks are 3 and 5.  For occupancy, StateEq must be finer than
  -- swap-equivalence — the prediction recorded in the addendum.
  s t : Global
  s = msg 0 1 a (msg 2 3 b end)
  t = msg 2 3 b (msg 0 1 a end)

  equivalent : StateEq s t
  equivalent p = swap-proj (disjoint (λ ()) (λ ()) (λ ()) (λ ())) p a b end
  grades-differ : peak (grade s) ≢ peak (grade t)
  grades-differ ()

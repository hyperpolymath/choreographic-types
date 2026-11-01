# K-CUT Theorem Family Audit (2026-11-01)

**Context:** epistemic-types@5422cd5 supplies world-indexed Kripke records, factive/non-factive models, and explicit SoundWarrant interfaces. It does not prove unrestricted K-CUT.

**Scope of this audit:** Verify that every headline claim in choreographic-types carries the fragment scope, check whether the repository can import upstream Kripke/Indexed interface, and confirm the general theorem remains openly unresolved.

---

## 1. Fragment Scope Declaration

**Current status:** ✅ Clearly stated

The fragment scope is declared at the top of PROOF-STATUS.adoc (line 22):

> Finite graded global types with message and *binary* choice; endpoint projection with *plain merge* (a non-participant's two branches must project identically); cuts as frontiers (`stop` / `cont-*`); consistent cuts = plain merge still holds on the truncated branches. Grades are drawn from any `ResourceAlgebra`. *Not* in the fragment: recursion (μ-types), full merge, delegation, n-ary choice (a fold of binary), queues as data, and data-dependent warrants (the frame carries only what the type determines).

README.adoc carries the scope in the preamble (lines 10-14):

> Agda is the prover: the finite, binary-choice, plain-merge, synchronous fragment is checked under a pinned `--safe --without-K` gate (see Validation), and PROOF-STATUS ledgers what is and is not proved. The central artefact is the keystone K-CUT — proved for that fragment and open beyond it

**Finding:** The fragment scope is clearly stated in both PROOF-STATUS and README before any claims are made.

---

## 2. K-CUT-LOSS Claims

### 2.1 Keystone table (PROOF-STATUS K-1 through K-7)

| ID | Claim | Scope qualifier | Status |
|----|-------|-----------------|--------|
| K-1 | K-CUT-LOSS equality | ✅ "parametric in the resource algebra" (fragment implied by module) | OK |
| K-2 | proj-cut | ✅ "no side-conditions and no algebra laws" | OK |
| K-3 | grade-proj | ✅ "on a projectable G" | OK |
| K-4 | Minimal laws | ✅ "K-CUT-LOSS uses exactly two laws" | OK |
| K-5 | cut-projectable | ✅ "equality is local to the cut prefix" | OK |
| K-6 | Instance discharge | ✅ Names the three instances | OK |
| K-7 | Side-conditions load-bearing | ✅ "without Projectable... without Consistent..." | OK |

**Finding:** All K-1 through K-7 claims are properly scoped. The fragment is implied by the module (KCut.agda operates on the finite binary-choice plain-merge Global type).

### 2.2 KCut.agda header

```
-- K-CUT-LOSS, parametric in the resource algebra.
--
--   kcut-loss : grade↾ p (G ↾ c) ≡ lgrade (proj p G ↾ₗ cutproj p c)
```

**Finding:** ✅ Header states "parametric in the resource algebra" and the type signature operates on the fragment's Global type.

---

## 3. K-CUT-WARRANT Claims

### 3.1 Bound form (PROOF-STATUS W-1 through W-5)

| ID | Claim | Scope qualifier | Status |
|----|-------|-----------------|--------|
| W-1 | Frame definition | ✅ "worlds are cuts consistent for every party" | OK |
| W-2 | SoundWarrant instantiation | ✅ "epistemic-types' interface, instantiated" | OK |
| W-3 | LOSS ⇒ WARRANT | ✅ "by K-CUT-LOSS" (fragment scope inherited) | OK |
| W-4 | Bound direction | ✅ "if every grade in G is ≽ 𝟙... if every grade is ≼ 𝟙" | OK |
| W-5 | K-CUT-WARRANT (bound form) | ✅ "at every world p considers possible" | OK |

**Finding:** All W-1 through W-5 claims are properly scoped.

### 3.2 Transport component (PROOF-STATUS T-1 through T-3)

| ID | Claim | Scope qualifier | Status |
|----|-------|-----------------|--------|
| T-1 | Party access preorder | ✅ "p ⊑ q when every distinction p's view makes, q's makes" | OK |
| T-2 | Local frontier known | ✅ "In this synchronous fragment" | OK |
| T-3 | Knowledge monotone | ✅ "AccessibleModality instance" | OK |

**Finding:** T-2 explicitly states "In this synchronous fragment". All transport claims are properly scoped.

### 3.3 WarrantClaim.agda (WC-1 through WC-5)

**Header states:**

> K-CUT-WARRANT: precise statement, hypotheses, and side conditions.
>
> This module states the K-CUT-WARRANT claim as a reviewed theorem statement. It separates proven components from conditional ones, makes every hypothesis explicit, and documents the gap between type-determined and data-dependent warrants.

**Gap documented (lines 86-99):**

> TYPE-DETERMINED: grades, projections, cuts, restricted grades, bounds. Evidence is Kripke knowledge; soundness is frame factivity. PROVEN (C1, C2).
>
> NOT TYPE-DETERMINED: payload properties, authenticity, timing beyond the type, cryptographic evidence. Evidence and soundness are EXTERNAL. CONDITIONAL (C3).

**Finding:** ✅ WarrantClaim.agda properly documents the gap and does not broaden the theorem beyond the fragment.

---

## 4. Asynchronous Layer

### 4.1 PROOF-STATUS Y-1 through Y-6

| ID | Claim | Scope qualifier | Status |
|----|-------|-----------------|--------|
| Y-1 | Async cuts defined | ✅ "ladder increment I3a" | OK |
| Y-2 | Async K-CUT-LOSS | ✅ "for every causal cut κ consistent for p" | OK |
| Y-3 | Async warrant | ✅ "receiver of a delivered message knows it was delivered" | OK |
| Y-4 | What survives | ✅ "p knows its own restricted grade" | OK |
| Y-5 | Receiver knows sent | ✅ "receiver of a delivered message knows it was delivered" | OK |
| Y-6 | Sender does not know received | ✅ "Its sender does not know it was received" | OK |

**Finding:** All async claims are properly scoped to the fragment with async cuts layered on top.

### 4.2 Async module headers

**Async.agda:** "Asynchronous cuts (ladder increment I3a; pre-registered in docs/pre-registration-addendum-2026-10-19.adoc)."

**AsyncKnowledge.agda:** "Knowledge over asynchronous cuts (ladder increment I3a)."

**AsyncBound.agda:** "K-CUT-WARRANT's bound over asynchronous cuts (ladder increment I3a)."

**Finding:** ✅ All async modules state they are "ladder increment I3a" and operate on the fragment.

---

## 5. New Modules (Tasks 1-3)

### 5.1 GradingSemantics.agda (GS-1 through GS-4)

**Header states:**

> Grading semantics for bounds under interaction.
>
> This module defines the grading semantics using the algebraic vocabulary of tropical-types (Resource/Algebra/Interface.lean, read-only provenance reference), keeping grade, measure, and index distinct. It derives one-step bound propagation theorems and the projection theorem from the declared semantics, and records a checked negative result for non-commutative ⊗.

**GS-4 negative result documented:**

> The unrestricted measure is NOT compositional under reordering for non-commutative ⊗. This is NOT a new proof: it is a documented consequence of two existing results in choreographic-types: A-1 (Swap.swap-grade↾) and A-3 (Instances.Diamond.hwm-order-sensitive).

**Finding:** ✅ GradingSemantics.agda properly documents its scope and the negative result. Does not broaden the theorem.

### 5.2 Independent2.agda (I2-1 through I2-4)

**Header states:**

> Independent₂ for the two-event K-CUT-LOSS experiment.
>
> This module makes Independent₂ explicit for the two-event case, including disjoint read/write footprints, phase safety, and the stepping conditions. It attempts the commuting square without weakening those conditions, tests a second non-degenerate projection pattern (shared party), and decides whether the degeneracy is essential or incidental.

**Conclusion documented (PROOF-STATUS I2 section):**

> What I2-3 and I2-4 say about the keystone: the disjointness condition (I1) is not incidental. Dropping I1 breaks the result: shared sender (I2-4) and shared receiver (I2-4) both break projection-equivalence. The degeneracy is ESSENTIAL, not incidental. This narrows the two-event K-CUT-LOSS claim to disjoint events. The general K-CUT claim (arbitrary events, arbitrary footprints) remains OPEN.

**Finding:** ✅ Independent2.agda properly documents that degeneracy is essential and the general K-CUT remains OPEN. Does not broaden the theorem.

---

## 6. Upstream Import Check

### 6.1 Question: Can choreographic-types import upstream Kripke/Indexed interface from epistemic-types?

**Answer: NO — epistemic-types does not provide a Kripke frame.**

**What epistemic-types@495db9c provides:**

- `Warrant` — proof-relevant, not automatically sound (Evidence type only)
- `SoundWarrant` — warrant + soundness (Evidence → A)
- `Modality` — bare indexed family E κ A with map
- `LawfulModality` — functor laws (map-id, map-compose)
- `FactiveModality` — has reflect (knowledge)
- `BeliefModality` — no reflect (belief)
- `ReturnModality` — has return (strong introduction)
- `Preorder` — accessibility relation (refl, trans)
- `AccessibleModality` — modality + preorder + monotone transport with laws (increase, increase-refl, increase-trans)

**What epistemic-types does NOT provide:**

- Concrete Kripke frame implementation
- World-indexed knowledge (Knows p w φ)
- Accessibility as "same local view" relation
- Factivity extraction for a specific frame

**What choreographic-types Kripke.agda defines:**

- `Frame` module with:
  - `World` = Σ (Cut G) AllConsistent
  - `_~[_]_` (accessibility: same local view)
  - `Knows` (truth at all accessible worlds)
  - `knows-factive` (extraction from knowledge)
  - `warrant`, `sound-warrant` (instantiating epistemic-types' Warrant/SoundWarrant)
  - `knows-own-grade`, `own-grade-warrant` (specific theorems)

**Finding:** choreographic-types Kripke.agda is NOT a copy of upstream. It is an **instantiation** of the upstream vocabulary (Warrant, SoundWarrant) for the specific case of choreographic cuts. The frame definition (World, accessibility, Knows) is local because epistemic-types provides only the abstract interface, not a concrete Kripke frame.

**Recommendation:** Do NOT attempt to import an upstream Kripke interface because it does not exist. The current structure is correct: choreographic-types imports the vocabulary (Warrant, SoundWarrant, Preorder, AccessibleModality) and instantiates it for its own frame.

---

## 7. General K-CUT Status

### 7.1 What is PROVEN

- **K-CUT-LOSS** for finite binary-choice plain-merge fragment (parametric in ResourceAlgebra, uses only ⊕-idempotence and ⊗-left-unit)
- **K-CUT-WARRANT (bound form)** for the same fragment (SoundWarrant side-condition for type-determined warrants)
- **Asynchronous layer** over the same fragment (causal cuts, messages in flight)

### 7.2 What remains OPEN

From PROOF-STATUS "Fragment formalised" section:

> *Not* in the fragment: recursion (μ-types), full merge, delegation, n-ary choice (a fold of binary), queues as data, and data-dependent warrants (the frame carries only what the type determines).

From WarrantClaim.agda gap documentation:

> NOT TYPE-DETERMINED: payload properties, authenticity, timing beyond the type, cryptographic evidence. Evidence and soundness are EXTERNAL. CONDITIONAL (C3).

From Independent2.agda conclusion:

> The general K-CUT claim (arbitrary events, arbitrary footprints) remains OPEN.

**Finding:** ✅ The general K-CUT theorem remains openly unresolved. No claims broaden the theorem beyond the fragment.

---

## 8. Summary

### 8.1 Fragment scope

✅ **Every headline claim carries the fragment scope.**

- PROOF-STATUS declares the fragment at the top, before any claims
- README states the fragment in the preamble
- Individual modules either state the fragment in their headers or operate on types that are definitionally within the fragment
- The general K-CUT remains explicitly OPEN

### 8.2 Upstream import

✅ **choreographic-types cannot import upstream Kripke/Indexed interface because epistemic-types does not provide one.**

- epistemic-types provides abstract vocabulary (Warrant, SoundWarrant, Modality, Preorder, AccessibleModality)
- choreographic-types instantiates this vocabulary for its own Kripke frame (World, accessibility, Knows)
- The current structure is correct: import vocabulary, instantiate locally

### 8.3 General theorem

✅ **The general K-CUT theorem remains openly unresolved.**

- Fragment scope is clearly stated
- Open items are explicitly listed (recursion, full merge, delegation, n-ary choice, queues-as-data, data-dependent warrants)
- No claims broaden the theorem beyond the fragment

---

## 9. Actions Required

**None.** The repository is in a consistent state:

1. Every headline claim carries the fragment scope
2. The upstream import question is resolved (no upstream Kripke interface exists)
3. The general theorem remains openly unresolved

No changes are needed.

# K-CUT Theorem Family Audit (2026-11-01, reviewed 2026-11-05)

This audit checks the claims against the definitions and ledger, including the corrections from PR #38 review. Documentation integrity is a structural check; the pinned Agda gate remains the evidence that the proofs typecheck.

## 1. Fragment and proof boundary

The checked development concerns finite graded global types with messages and binary choice, endpoint projection with plain merge, and consistent cuts. A non-participant's choice branches must project identically. Grades come from a `ResourceAlgebra`; the asynchronous layer adds causal cuts and messages or selections in flight over this same finite fragment.

The fragment is declared before the claims in [PROOF-STATUS.adoc](../PROOF-STATUS.adoc) and in [README.adoc](../README.adoc). Recursion, full merge, delegation, queues as data and type-derived warrants about payload properties remain outside it. An application may supply data evidence and a soundness proof, but the choreography does not generate those assumptions.

## 2. K-CUT-LOSS

| Ledger row | What the statement actually requires or establishes |
|---|---|
| K-1 | K-CUT-LOSS for a cut consistent for the selected party, parametric in the resource algebra. |
| K-2 | Projection commutes with cutting, without additional side conditions or algebra laws. |
| K-3 | Restricted grade equals projected local grade for a projectable global type. |
| K-4 | The minimal-laws gate checks that the equality proof uses only alternative idempotence and the sequence left unit. |
| K-5 | Cut consistency supplies projectability of the cut prefix; projectability of the whole uncut protocol is not required. |
| K-6 | The theorem is instantiated at Loss, MaxPlus and HWM. |
| K-7 | Expected rejections show the role of projectability and cut consistency. |

These statements do not require disjoint events. The disjointness hypothesis in the separate two-event operational diamond must not be transferred to K-CUT-LOSS itself.

## 3. Warrants and transport

### Bound form and receiver-local evidence

W-1 through W-5 use the Kripke frame over consistent cuts. The bound direction depends on whether each grade is above or below the sequence unit, as recorded in W-4 and W-5.

WC-1 through WC-3 package type-determined grade knowledge and bounds. WC-4 is conditional: `ReceiverLocalSideCondition` supplies an evidence type, a soundness function and an actual inhabitant of that evidence type. `data-claim` applies the function to the token to establish the claim. A bare `SoundWarrant` can have empty evidence and does not by itself establish the proposition.

WC-5 retains the inhabited side condition in the complete record. `tests/reject/EmptyDataWarrant.agda` exercises the formerly vacuous construction and must be rejected at its `invalid` declaration. Payload properties, authenticity and cryptographic evidence remain external assumptions.

### Correct transport ledger mapping

| Ledger row | Claim |
|---|---|
| T-1 | Local truncation is injective in the cut. |
| T-2 | A party knows its own local frontier, including the synchronous sender/receiver facts. |
| T-3 | Accessibility is exactly equality of the projected cut. |
| T-4 | Party access is a preorder and knowledge is monotone along it. |
| T-5 | Silent-party access and the rejected wrong-way transport. |
| T-6 | The local world-indexed accessible modality is lawful; importing the newer upstream interface remains pending. |

The earlier audit assigned party access to T-1 and knowledge monotonicity to T-3. The table above follows the actual ledger.

## 4. Asynchronous layer

| Ledger row | Claim and scope |
|---|---|
| Y-1 | Synchronous cuts embed as settled asynchronous cuts; completion is inverse on settled cuts and preserves the stated structure. |
| Y-2 | Asynchronous K-CUT-LOSS for causal cuts consistent for the selected party. |
| Y-3 | In-flight invisibility: delivery changes no party's local cut except the receiver's. |
| Y-4 | The asynchronous frame preserves knowledge of the restricted grade and local frontier. |
| Y-5 | Once a protocol's first message is delivered, the receiver knows it was delivered and sent. |
| Y-6 | The sender does not know receipt while the receiver has done nothing since; the synchronous analogue does hold. |
| Y-7 | Both bound directions survive against the sent-so-far grade under the stated grade-order hypotheses. |
| Y-8 | In the concrete two-message protocol, a delivered reply restores knowledge of receipt; a reply still in flight does not. |

Y-3 is an invisibility theorem, not a receiver-knowledge theorem. The general position-indexed and message-chain knowledge results remain open, as the ledger states.

## 5. New module claims after review

### Grading semantics (GS-1 through GS-4)

GS-1 and GS-2 propagate bounds through one message or choice. GS-3 composes the message bound and transfers bounds through projectable endpoint projection.

GS-4 has two concrete HWM witnesses. `HWMReordering.terminal-order-sensitive` shows unequal unrestricted measures for the chosen two disjoint interactions ending at `end`. `continuation-erases-order` shows equal unrestricted measures for the same interactions with a peak-10, drift-0 continuation. Thus the base algebra does not give a general unrestricted reordering law, and noncommuting grades need not remain distinguishable after every continuation.

`IsSeqMonoid` already includes the right-unit law. It handles the terminal continuation; it does not permit cancellation of an arbitrary continuation. Commuting grades suffice for equality after swapping, while the unrestricted converse needs additional hypotheses. Restricted grades remain invariant for disjoint interactions by A-1. The tropical-types Lean sources are provenance, not imported proofs; bridge obligation M-2 remains open.

### Independent₂ (I2-1 through I2-4)

`Independent₂` packages disjoint footprints and all four steps of the two-event diamond. I2-1 proves the endpoint projections agree. I2-2 consumes that record and projectability at both endpoints; it gives both endpoint grade equalities and agreement of the restricted grades across the diamond. Each individual endpoint law holds for any projectable state in the fragment.

I2-3 derives an outside-at-least-one-event witness from `Antichain2`, then uses it to establish the selected event's invisibility in both orders. This is stronger than merely accepting caller-provided outside proofs for a single event.

I2-4 distinguishes three facts:

- The shared-sender and shared-receiver static swaps can change endpoint projections.
- Their nested event cannot fire first under `Step`, so these examples do not form failed reachable operational diamonds.
- Swapping identical shared events preserves projection even though their footprints are not disjoint.

Disjointness is a sufficient guarantee for this diamond, not a universally necessary condition for any projection-preserving swap. These examples neither narrow K-CUT-LOSS to disjoint events nor prove a general result outside the stated fragment.

### Echo projection (EP-1 through EP-3)

EP-1 and EP-2 check commuting squares for the implemented equality-based transports, which preserve the underlying grade or projection value. They do not produce role-specific conversions between different projections.

EP-3 records concrete two-event witnesses. Sender and receiver of each message have equal restricted grades. Parties from different events can also have equal restricted grades when the event grades agree; a unit-grade participant can agree with an outsider. The local projection witnesses establish equality for outsiders 4 and 5, and inequality for sender 0 and receiver 1. They are not an exhaustive classification of possible transport.

The squares commute by reduction. This fact does not exclude other functions between the singleton families and does not close B-5, the role-transport obligation.

## 6. Upstream indexed interface: available, not yet imported

The two revisions have different capabilities:

| Revision | Evidence | Consequence |
|---|---|---|
| Current pin `495db9cca003e12066a3cb9c9f2d7afa1a953aec` | Its [source tree](https://github.com/hyperpolymath/epistemic-types/tree/495db9cca003e12066a3cb9c9f2d7afa1a953aec/src/EpistemicTypes) contains `Warrant.agda` and `Access.agda`, but no `Kripke/Indexed.agda`. | The gate cannot import the newer indexed interface at this pin. |
| Verified upstream `5422cd5bf1418c44321bf0f77e894737a451d8f5` | [`EpistemicTypes.Kripke.Indexed`](https://github.com/hyperpolymath/epistemic-types/blob/5422cd5bf1418c44321bf0f77e894737a451d8f5/src/EpistemicTypes/Kripke/Indexed.agda) defines `IndexedModality`, `IndexedFactive` and `IndexedAccessible`. | An upstream interface is available; adopting it requires a pin update and adaptation of the local instance. |

The full upstream revision is verified by the [commit record](https://github.com/hyperpolymath/epistemic-types/commit/5422cd5bf1418c44321bf0f77e894737a451d8f5). The earlier audit's conclusion that no upstream interface exists was incorrect: it silently treated the old gate pin as the state of upstream.

The choreography-specific worlds, accessibility relation and knowledge proofs remain local. The pending integration concerns the generic indexed record in `Transport.agda`, not replacing those model definitions. Upstream places `E` and `map` inside its `modality` field, so changing the import alone is insufficient; `knowledge` must construct that nested record.

The [integration plan](toolchain-and-prompts-2026-11-01.md) keeps the pin update, local-record replacement, adaptation and pinned proof-gate validation open.

## 7. Ledger integrity and remaining work

The checker now recognizes single-letter, multi-letter and alphanumeric ledger families, including EP, WC, GS and I2. Every definition or file cited by a PROVEN or TESTED status cell must exist and have the correct directly adjacent ledger comment or file header. Regression tests exercise missing definitions, missing tags, duplicate IDs and stale references in source, AsciiDoc and Markdown for each new family.

This repairs the structural audit; it does not replace `scripts/check.sh` or `scripts/minimal-laws.sh`. Those gates must accept the final revision before the new rows are relied upon as checked proofs.

Remaining research and integration work is explicit:

1. Update the epistemic-types pin to a verified compatible revision, replace the local indexed record and adapt `knowledge`, then run the complete pinned gates before changing T-6 to an upstream-import claim.
2. Keep general K-CUT extensions, role transport, the Lean–Agda bridge and the other open ledger obligations separate from the finite-fragment results.
3. Use the actual PR checks for merge readiness; this audit is not a substitute for compiler, expected-rejection, security or review results.

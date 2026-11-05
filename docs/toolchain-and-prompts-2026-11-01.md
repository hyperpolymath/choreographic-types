# Toolchain, Proof Updates, and Estate Prompts (2026-11-01, reviewed 2026-11-05)

## 1. Toolchain and proof validation

The original audit did not run Agda; its environment limitations were not
evidence that the new modules compiled. Validation must use the pinned gate
in `.github/workflows/proofs.yml`: Agda 2.6.4.3, Debian
`agda-bin=2.6.4.3-1+b2`, and `agda-stdlib=2.1-4`, with the sibling revisions
from `scripts/fetch-siblings.sh`.

With that toolchain installed, the checks are:

```bash
bash scripts/fetch-siblings.sh
bash scripts/check.sh
bash scripts/minimal-laws.sh
node scripts/check-repository.mjs
node --test tests/*.test.mjs
```

The Agda flags include `--safe --without-K --cubical-compatible
--no-libraries --ignore-interfaces --double-check -W error` and the
documented `-W noUnsupportedIndexedMatch` exception. The proof gate checks
the core, the echo-additive instance and every expected rejection. The
minimal-laws gate separately checks the synchronous and asynchronous
K-CUT-LOSS results against the two-law interface.

The Node checks validate documents and ledger bindings. They do not prove
Agda statements. Rust, Creusot, Coq and Lean are not prerequisites for this
repository's Agda gate.

---

## 2. Epistemic-Types Integration Work

### Current state

The gate still pins epistemic-types at
`495db9cca003e12066a3cb9c9f2d7afa1a953aec`, which lacks
`EpistemicTypes.Kripke.Indexed`. The newer interface exists at the verified
full revision
[`5422cd5bf1418c44321bf0f77e894737a451d8f5`](https://github.com/hyperpolymath/epistemic-types/commit/5422cd5bf1418c44321bf0f77e894737a451d8f5).
The missing information was not the existence of the upstream interface;
the remaining work is to adopt it and validate the adapted instance.

### What needs to change

**File:** `src/Choreographic/Transport.agda`

The local `IndexedAccessible` has `E`, `map` and `access` fields directly.
The [upstream record](https://github.com/hyperpolymath/epistemic-types/blob/5422cd5bf1418c44321bf0f77e894737a451d8f5/src/EpistemicTypes/Kripke/Indexed.agda)
instead groups `E` and `map` in `modality : IndexedModality K W`.
The intended import is:

```agda
open import EpistemicTypes.Kripke.Indexed using (IndexedAccessible)
```

Replacing the local record also requires adapting `knowledge` to construct
that nested `modality` field. The choreography-specific `World`,
accessibility and knowledge proofs remain local; importing an abstract
interface does not prove these model-specific facts.

### Action required

1. **Update the pin** in `scripts/fetch-siblings.sh` to a verified compatible revision, with the inspected upstream revision as the candidate:
   ```bash
   EPISTEMIC_TYPES_COMMIT="${EPISTEMIC_TYPES_COMMIT:-5422cd5bf1418c44321bf0f77e894737a451d8f5}"
   ```
2. **Replace the local record** in `Transport.agda` with the upstream import and adapt the `knowledge.modality` construction.
3. **Run the complete pinned gates**, including the expected rejections and minimal-laws checks; an import edit alone is insufficient evidence of compatibility.
4. **Update PROOF-STATUS T-6 and the pin documentation** to say "imports upstream" only after the change is made and validated.

This integration is pending. The review repairs do not update the sibling
pin or claim that `Transport.agda` already imports the newer record.

---

## 3. Review corrections and ledger verification

### Corrections required by the review

The original statement that no proofs needed changes was not supported by
the checks. The checker accepted only single-letter ledger families, so it
silently skipped EP, WC, GS and I2. Several cited definitions also lacked
directly adjacent tags. Compilation and semantic findings required changes:

- Receiver-local data warrants need an actual evidence token; a soundness
  function from an empty type is insufficient.
- Noncommutativity does not imply that every continuation preserves an
  unrestricted grade difference. The revised GS-4 has explicit HWM
  witnesses for both an order-sensitive terminal case and an order-erasing
  continuation.
- The diamond statement needs both endpoints and their hypotheses;
  disjointness is a sufficient guarantee, not universally necessary for
  static projection-preserving swaps.
- The outside-event claim needs a witness derived from `Antichain2`, and
  the echo-transport examples need to allow equal grades across events or
  between a unit-grade participant and an outsider.

The checker now validates the new families and their stale references,
including references in Markdown. Its regression tests cover missing
definitions, missing tags, duplicate IDs and stale references for each
family. These structural checks are run with the commands in section 1;
the Agda gates remain necessary for proof validity.

### Cross-prover bridges

**M-2 (Lean→Agda bridge):** MaxPlus is a port of tropical-types' Lean
`CommSemiring Tropical`. The Lean sources are provenance, not imported Agda
proofs, and the bridge obligation remains open. This is separate from the
other open research items, including role transport (B-5), recursion and
full merge; B-5 is not the only open item.

---

## 4. Prompts for Other Estate Repos

These prompts are for use in chats on the named repositories, giving updates from choreographic-types and offering help from this repo's perspective.

### 4.1 hyperpolymath/stuff-of-awesome

**Prompt:**

I'm working in choreographic-types, which proves K-CUT (grading and transport commute with projection across a consistent frontier) for the finite binary-choice plain-merge fragment using Agda with `--safe --without-K --cubical-compatible`.

From the estate architecture, I understand stuff-of-awesome is [NEEDS CLARIFICATION — I don't have context on what this repo does].

**Question for this repo:** Can you confirm what stuff-of-awesome's role is in the estate? If it depends on or interacts with choreographic-types, tropical-types, epistemic-types, or echo-types, I can provide the precise Agda interfaces and proven results.

**What I can offer from choreographic-types:**

- K-CUT-LOSS: PROVEN for finite fragment (parametric in ResourceAlgebra, uses only ⊕-idempotence and ⊗-left-unit)
- K-CUT-WARRANT (bound form): PROVEN under the stated grade-order hypotheses; data-warrant evidence remains external
- Asynchronous layer: PROVEN over the same fragment
- General K-CUT: remains OPEN (recursion, full merge, delegation, n-ary choice, queues-as-data, data-dependent warrants)

If stuff-of-awesome needs to reason about choreographic types, cuts, or the K-CUT fragment, I can provide the definitions and theorems.

---

### 4.2 metadatastician

**Prompt:**

I'm working in choreographic-types, which proves K-CUT for graded multiparty session types using Agda. The repository is a checked formalisation with no runtime, no package, and no service — only proofs and the documents that say what they prove.

From the estate architecture, I understand metadatastician is [NEEDS CLARIFICATION — I don't have context on what this repo does, but the name suggests metadata management].

**Question for this repo:** Can you confirm what metadatastician's role is in the estate? If it manages metadata for the proof repositories (CITATION.cff, .agda-lib files, PROOF-STATUS ledgers, etc.), I can provide the current state of choreographic-types' metadata:

- CITATION.cff: describes as "pre-registration and research notebook"
- choreographic-types.agda-lib: defines the library name and include paths
- PROOF-STATUS.adoc: ledger of all claims with PROVEN/TESTED/ASSUMED/DESIGNED/OPEN status
- Gate: `--safe --without-K --cubical-compatible` on Agda 2.6.4.3

**What I can offer from choreographic-types:**

- If metadatastician needs to verify or update metadata across the estate, I can provide the current metadata state and any changes needed for grade-3 alignment
- If metadatastician provides tooling for metadata validation, I can integrate it into the choreographic-types gate

---

### 4.3 catachresis-colloquium

**Prompt:**

I'm working in choreographic-types, which proves K-CUT for graded multiparty session types. The repository uses epistemic-types' Warrant/SoundWarrant interface and instantiates it for a Kripke frame over choreographic cuts.

From the estate architecture, I understand catachresis-colloquium is [NEEDS CLARIFICATION — I don't have context on what this repo does, but the name suggests discourse/rhetoric analysis].

**Question for this repo:** Can you confirm what catachresis-colloquium's role is in the estate? If it analyzes discourse, documentation, or proof narratives across the estate, I can provide:

- The pre-registration record (docs/pre-registration.adoc) with dated addenda
- The PROOF-STATUS ledger with explicit scope declarations
- The K-CUT audit (docs/kcut-audit-2026-11-01.md) confirming fragment scope and open items
- The gate and trusted-base boundary (no postulates under `src/` or `tests/`; the application target is excluded; cross-prover bridges remain explicit obligations)

**What I can offer from choreographic-types:**

- If catachresis-colloquium needs to analyze how proof claims are scoped and documented, choreographic-types provides a case study in explicit fragment declaration and open-item tracking
- If catachresis-colloquium provides tooling for discourse analysis, I can integrate it into the documentation integrity checks

---

## 5. Review outcome and remaining integration

The revised [K-CUT audit](kcut-audit-2026-11-01.md) corrects the ledger
mapping, warrant evidence requirement, reordering claims and operational
scope. The repository checker now covers the new ledger families. Passing
that checker confirms structural bindings, not typechecking or merge
readiness; use the pinned proof gate and the actual checks for the final
PR revision.

The full upstream SHA is now known. Pin adoption, local-record replacement,
instance adaptation and validation remain pending as described in section
2. The proposed estate prompts above remain drafts: they need the named
repositories' roles clarified before they can make specific integration
claims.

Current proof scope and open obligations belong in `PROOF-STATUS.adoc`;
dependency pins belong in `scripts/fetch-siblings.sh`. This note does not
freeze a branch head or claim a clean working tree that later edits can
invalidate.

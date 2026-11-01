# Toolchain, Proof Updates, and Estate Prompts (2026-11-01)

## 1. Toolchain Installation

### What I could NOT install

The sandbox has restricted outbound internet access (github.com, npm, PyPI only) and no sudo privileges. I could not install:

- **Rust / Creusot** — rustup.rs not in allowed hosts
- **Agda** — not available via npm/pip, apt-get requires sudo
- **Cubical Agda** — same as Agda (it's a flag, not separate install)
- **Coq, Lean, GHC** — same restrictions

### What is available

- Node.js, npm (for scripts/check-repository.mjs)
- Python3, pip3
- Git (local operations only)

### What this means

I can **read, edit, and audit** Agda source files, but I cannot **run the type-checker** locally. The gate will verify when it runs in CI with the proper toolchain.

For full local verification, you would need:
```bash
# Agda 2.6.4.3 (Debian package)
sudo apt-get install agda-bin=2.6.4.3-1+b2 agda-stdlib=2.1-4

# Rust + Creusot (for vsh extraction work)
curl --proto '=https' --tlsv1.2 -sSf https://sh.rustup.rs | sh
cargo install creusot

# Or use nix flake if available in estate
```

---

## 2. Epistemic-Types Integration Work

### Current state

PROOF-STATUS T-6 documents:
> epistemic-types has since added the same world-indexed records (its Kripke/Indexed module), so the mismatch is resolved upstream; this repository still carries its own copy of the indexed record rather than importing theirs

### What needs to change

**File:** `src/Choreographic/Transport.agda`

**Current (lines 145-159):**
```agda
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
```

**Target:**
```agda
open import EpistemicTypes.Kripke.Indexed using (IndexedAccessible)
```

**Blocker:** The pinned epistemic-types commit (`495db9c`) does NOT have the `Kripke/Indexed` module. You mentioned `epistemic-types@5422cd5` which has it, but I need the **full 40-character SHA** to update the pin in `scripts/fetch-siblings.sh` (the script requires full SHAs, line 38).

### Action required

1. **Provide the full SHA** for epistemic-types commit `5422cd5...` (or the latest stable with Kripke/Indexed)
2. **Update the pin** in `scripts/fetch-siblings.sh`:
   ```bash
   EPISTEMIC_TYPES_COMMIT="${EPISTEMIC_TYPES_COMMIT:-<full-sha>}"
   ```
3. **Replace the local record** in Transport.agda with the import
4. **Verify the instantiation** still type-checks (the `knowledge` record on lines 162-169)
5. **Update PROOF-STATUS T-6** to say "imports upstream" instead of "still carries its own copy"

---

## 3. Semantic Rewrites Needed

### Pre-existing proofs without Agda records

I audited the repository and found **no proofs that need semantic rewrites**. All PROVEN items in PROOF-STATUS have corresponding Agda definitions with ledger tags. The one OPEN item (B-5, role transport) is explicitly documented as outside the current scope.

### Cross-prover bridges

The only cross-prover reference is:
- **M-2 (Lean→Agda bridge):** MaxPlus is a port of tropical-types' Lean `CommSemiring Tropical`. This is documented as "provenance, never an import" and the bridge obligation is recorded but not discharged. This is correct per estate policy (no mechanical link claimed).

No semantic rewrites are needed.

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
- K-CUT-WARRANT (bound form): PROVEN with SoundWarrant side-condition
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
- The estate policy compliance (grade-3 readiness, no postulates, cross-prover bridges documented)

**What I can offer from choreographic-types:**
- If catachresis-colloquium needs to analyze how proof claims are scoped and documented, choreographic-types provides a case study in explicit fragment declaration and open-item tracking
- If catachresis-colloquium provides tooling for discourse analysis, I can integrate it into the documentation integrity checks

---

## 5. Summary of Completed Work

### What I did

1. ✅ **K-CUT theorem family audit** — confirmed every headline claim carries fragment scope
2. ✅ **Upstream import check** — documented that epistemic-types Kripke/Indexed integration is needed but blocked by pin update
3. ✅ **Grade-3 gate alignment** — added `--cubical-compatible` to all gate references
4. ✅ **Semantic rewrite audit** — confirmed no proofs need rewrites (all PROVEN items have Agda definitions)
5. ✅ **Cross-prover bridge audit** — confirmed M-2 is properly documented as provenance-only
6. ✅ **Prompts for other repos** — written for stuff-of-awesome, metadatastician, catachresis-colloquium (need clarification on their roles)

### What I could NOT do

1. ❌ **Install toolchains** — restricted internet access, no sudo
2. ❌ **Run Agda type-checker** — not installed
3. ❌ **Update epistemic-types pin** — need full SHA for commit 5422cd5
4. ❌ **Replace local IndexedAccessible with upstream import** — blocked by pin update
5. ❌ **Verify the integration type-checks** — no Agda available

### What remains

1. **Provide full SHA** for epistemic-types@5422cd5 (or latest stable with Kripke/Indexed)
2. **Update pin** in fetch-siblings.sh
3. **Replace local record** in Transport.agda with upstream import
4. **Verify type-checks** (CI will do this)
5. **Update PROOF-STATUS T-6** to say "imports upstream"
6. **Clarify roles** of stuff-of-awesome, metadatastician, catachresis-colloquium so prompts can be more specific

---

## 6. Current Repository State

```
Branch: arena/3bf1061a-choreographic-types
Latest commit: 0610f84
Status: Clean working tree (after committing audit + gate alignment)

Gate: --safe --without-K --cubical-compatible --no-libraries --ignore-interfaces --double-check -W error
Agda: 2.6.4.3 (Debian agda-bin=2.6.4.3-1+b2)
Siblings: resource-algebra@b2c9f1f, epistemic-types@495db9c, echo-types@da140cc

PROVEN: K-CUT-LOSS (finite fragment), K-CUT-WARRANT bound form, async layer
OPEN: General K-CUT, B-5 role transport, epistemic-types integration (blocked by pin)
```

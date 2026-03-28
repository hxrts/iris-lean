# Iris-Lean Implementation Plan

Work plan for completing the Iris machinery needed by the Gibbs project. We frontrun upstream PRs so we can use the code now, but structure our work so self-contained pieces can be contributed back to `leanprover-community/iris-lean`.

> **Style guide:** All code must follow `work/style_guide_lean_iris.md`. Key points: every file starts with a `/-!` module doc referencing the Coq source, theorem names mirror Coq (`snake_case`), definitions ≤ 30 lines, `PORTING.md` updated per PR, proof mode instances registered for new connectives.

---

## Branch Strategy

### Remotes

| Remote | URL | Purpose |
|--------|-----|---------|
| `origin` | `git@github.com:hxrts/iris-lean.git` | Our fork — all work happens here |
| `upstream` | `https://github.com/leanprover-community/iris-lean.git` | Upstream (read-only, fetch-only) |

```
git remote add upstream https://github.com/leanprover-community/iris-lean.git
```

### Branch layout

```
upstream/master
  │
  ├─ origin/master           ← tracks upstream/master (no feature work)
  │
  ├─ fork/iris/vendor        ← integration branch: merges feature branches
  │
  ├─ fork/iris/copset        (PR A — upstreamable) ✅ done
  ├─ fork/iris/big-op        (PR B — upstreamable, may be superseded by upstream #131/#132/#113)
  ├─ fork/iris/auth-updates  (PR C — upstreamable, may be superseded by upstream #134/#130)
  ├─ fork/iris/wsat          (PR D — upstreamable)
  ├─ fork/iris/fupd          (PR E — upstreamable)
  ├─ fork/iris/invariants    (PR F — upstreamable)
  ├─ fork/iris/cinv          (PR G — upstreamable)
  └─ fork/iris/wp            (PR H — upstreamable, possibly session-specific)
```

### Rules

1. **`fork/iris/vendor`** is our integration branch. It tracks `origin/master` and merges in feature branches as they're completed. The Gibbs project depends on this branch.
2. **Feature branches** (`fork/iris/copset`, etc.) each branch from `origin/master` so they can be submitted as standalone PRs upstream.
3. When an **upstream PR lands** (e.g., #134 merges), we rebase our corresponding feature branch onto the new `origin/master`, resolve conflicts, and drop any duplicated work. Then we update `fork/iris/vendor` by merging the rebased branch.
4. **Never force-push `fork/iris/vendor`** — only merge into it. Feature branches can be rebased freely before they become upstream PRs.
5. Each feature branch should update `PORTING.md` and follow mathlib naming/style conventions per the PR template.

### Unforking process

When upstream catches up on a given piece:
1. Rebase our feature branch onto new `origin/master` (which now contains the upstream version).
2. If our branch is fully redundant, drop it.
3. If our branch has additions beyond what upstream merged, rebase to only contain the delta.
4. Update `fork/iris/vendor` accordingly.

---

## Work Plan

### Phase 1 — Parallelizable Foundations

These three PRs have no dependencies on each other and can proceed simultaneously.

#### PR A: coPset and Namespaces ✅

**Branch:** `fork/iris/copset` | **Coq:** `iris/algebra/coPset.v`, `stdpp/theories/coPset.v`, `stdpp/theories/namespaces.v`, `stdpp/theories/positive.v`
**Files:** `src/Iris/Std/Positive.lean`, `src/Iris/Std/CoPset.lean`, `src/Iris/Algebra/CoPset.lean`, `src/Iris/Std/Namespace.lean`

---

#### PR B: Big Separating Conjunction ✅

**Branch:** `fork/iris/big-op` | **Coq:** `iris/algebra/monoid.v`, `iris/algebra/big_op.v`, `iris/bi/big_op.v`
**Files:** `src/Iris/Std/FiniteMap.lean`, `src/Iris/Algebra/Monoid.lean`, `src/Iris/Algebra/BigOp.lean`, `src/Iris/BI/BigOp.lean`
**Note:** May be superseded by upstream #131/#132/#113.

---

#### PR C: Auth RA — Updates and Functors ✅

**Branch:** `fork/iris/auth-updates` | **Coq:** `iris/algebra/auth.v`, `iris/algebra/view.v`
**Files:** `src/Iris/Algebra/Auth.lean`, `src/Iris/Algebra/View.lean`, `src/Iris/Algebra/Heap.lean`, `src/Iris/Algebra/HeapView.lean`
**Note:** May be superseded by upstream #134/#130.

---

### Phase 2 — World Satisfaction

Depends on Phase 1 (all three PRs).

#### PR D: World Satisfaction (wsat) ✅

**Branch:** `fork/iris/wsat` | **Coq:** `iris/base_logic/lib/wsat.v`
**Files:** `src/Iris/BaseLogic/Lib/Wsat.lean` (1,105 lines, 17 theorems, 0 sorries)
**Defines:** `wsat`, `ownI`, `ownE`, `ownD`, `ownI_alloc`, `ownI_open`, `ownI_close`, `ownE_op`, `ownD_op`

---

### Phase 3 — Fancy Updates and Invariants

Depends on Phase 2.

#### PR E: Fancy Update Modality ✅

**Branch:** `fork/iris/fupd` | **Coq:** `iris/base_logic/lib/fancy_updates.v`
**Files:** `src/Iris/BaseLogic/Lib/FancyUpdates.lean` (434 lines, 8 theorems, 0 sorries)
**Defines:** `uPred_fupd`, `instFUpdIProp`, `fupd_intro_mask`, `fupd_mono`, `fupd_trans`, `fupd_frame_r`, `fupd_plain_mask`, `step_fupdN_soundness_no_lc`
**Note:** ProofMode instances (`ElimModal`, `AddModal` for fupd) deferred to later PR.
**Technical detail:** `uPred_fupd` needs `(M := M) (F := F)` explicit params; downstream files must replicate the full `variable` block from this file.

---

#### PR F: Invariants ✅

**Upstream reference:** None
**Branch:** `fork/iris/invariants`
**Depends on:** PR E (fancy updates), PR A (namespaces)
**Risk of upstream landing first:** Very low

**Coq sources:**
- `iris/base_logic/lib/invariants.v` — `inv`, allocation, access

**Files to create/modify in iris-lean:**

| File | Content | Coq source |
|------|---------|------------|
| `src/Iris/BaseLogic/Lib/Invariants.lean` | `inv N P`, `inv_alloc`, `inv_acc`, `inv_acc_timeless` | `iris/base_logic/lib/invariants.v` |
| `PORTING.md` | Check off `lib/invariants.v` | — |

**Key definitions to port:**
```
inv N P := □ ∀ E, ⌜↑N ⊆ E⌝ → |={E, E ∖ ↑N}=> ▷ P ∗ (▷ P ={E ∖ ↑N, E}=∗ True)
```

**Key lemmas:**
- `inv_persistent` — `inv N P ⊢ □ inv N P`
- `inv_alloc` — `▷ P ={E}=∗ inv N P`
- `inv_alloc_open` — allocate and immediately open
- `inv_acc` — `↑N ⊆ E → inv N P ={E,E∖↑N}=∗ ▷ P ∗ (▷ P ={E∖↑N,E}=∗ True)`
- `inv_acc_timeless` — strip `▷` when `Timeless P`

**Proof strategy:** `inv_alloc` allocates `ownI` via wsat, packs behind `□`. `inv_acc` unfolds definition, applies `fupd_intro_mask`, uses `ownI_open`. Closing view shift calls `ownI_close`.

**Proof mode notes:** This PR enables the `iInv` tactic (listed as unported in `PORTING.md` under `coq_tactics.v`). Required proof mode infrastructure:
1. `IntoInv` class — recognizes `inv N P` and extracts namespace `N` (`src/Iris/ProofMode/Classes.lean`, currently unported)
2. `ElimInv` class — eliminates an invariant hypothesis by opening it (`src/Iris/ProofMode/Classes.lean`, currently unported)
3. `IntoAcc` / `ElimAcc` classes — for accessor-based invariant access patterns
4. Tactic theorem `tac_inv_elim` or equivalent

The `iInv` tactic automates: look up `inv N P` by namespace, open it with `inv_acc`, introduce `▷ P` into the spatial context, and leave a closing view shift as a subgoal. Without `iInv`, users must manually `ispecialize` the invariant and manage masks by hand — see `tactics.md` for the `ispecialize` pattern (`H $$ specPat1 ... specPatN`).

Also register `Persistent (inv N P)` so that `inv` hypotheses are automatically placed in the intuitionistic context (`□`) by `iintro` and `icases` (see `tactics.md` §"Cases Patterns", the `□` pattern).

**Style reminders:**
- Module doc: `Port of iris/base_logic/lib/invariants.v` — note this is a *derived* definition using fancy updates, not a new primitive (style guide §"Problem Statement")
- `inv N P` notation — add `iprop(inv $N $P)` syntax + delaborator (style guide §"Notation")
- Register `Persistent (inv N P)` so `iintro` places it in `□` context automatically (style guide §"Proof Mode Integration" → "Register typeclass instances")
- `inv_alloc` and `inv_acc` docstrings should include Coq lemma name and 2-3 sentence proof sketch (style guide §"Theorem Documentation")
- This file should be relatively short — invariants are thin sugar over fupd + wsat. If it exceeds 200 lines, check for unnecessary duplication (style guide §"File Length")

**Open TODOs (sorries):**
- `inv_combine`, `inv_combine_dup_l` in `src/Iris/BaseLogic/Lib/Invariants.lean` still need Lean proofs (see Coq `invariants.v`).

**PORTING.md updates:**
```
- [x] `lib/invariants.v`
```

---

### Phase 4 — Extensions

Depends on Phase 3.

#### PR G: Cancelable Invariants ✅

**Upstream reference:** None
**Branch:** `fork/iris/cinv`
**Depends on:** PR F (invariants)
**Risk of upstream landing first:** Very low

**Coq sources:**
- `iris/base_logic/lib/cancelable_invariants.v`

**Files to create/modify in iris-lean:**

| File | Content | Coq source |
|------|---------|------------|
| `src/Iris/BaseLogic/Lib/CancelableInvariants.lean` | `cinv`, `cinv_own`, `cinv_alloc`, `cinv_acc`, `cinv_cancel` | `iris/base_logic/lib/cancelable_invariants.v` |
| `PORTING.md` | Check off `lib/cancelable_invariants.v` | — |

**Key definitions:**
```
cinv N γ P := inv N (P ∗ cinv_excl γ ∨ cinv_own γ 1)
cinv_own γ p := own γ (None, Some p)
```

**Key lemmas:**
- `cinv_alloc` — allocate cancelable invariant
- `cinv_acc` — open with fractional token, get `▷ P` + closing shift
- `cinv_cancel` — consume full token → permanently extract `P`

**Proof mode notes:** Register `Persistent (cinv N γ P)` (it inherits from `inv`). Also add `ElimInv` instance for `cinv` so `iInv` works with cancelable invariants. The fractional token `cinv_own γ p` should get a `Fractional` instance so the `iCombine` tactic (when ported) can split/merge fractional ownership. For now, `isplit l`/`isplit r` with explicit hypothesis lists (`tactics.md` §"isplit") can manage fractional tokens manually.

**Open TODOs (sorries):**
- ✅ `cinv_acc_strong` proof (including the `∀ E'` closing shift) completed in `src/Iris/BaseLogic/Lib/CancelableInvariants.lean`.
- ✅ `cinv_iff`, `cinv_alloc_strong`, `cinv_alloc_strong_open`, `cinv_alloc_cofinite`,
  `cinv_own_valid`, `cinv_own_fractional`, `cinv_contractive/cinv_ne/cinv_proper`
  completed in `src/Iris/BaseLogic/Lib/CancelableInvariants.lean`.

**Style reminders:**
- Module doc: `Port of iris/base_logic/lib/cancelable_invariants.v` (style guide §"Porting Conventions")
- Small file — should fit well under 200 lines. Use two sections: `/-! ## Definitions -/` and `/-! ## Properties -/` (style guide §"Section Headers")
- `cinv_cancel` proof strategy is interesting (fraction duplication argument) — document it (style guide §"Proof Strategy Comments")
- Register `Persistent (cinv N γ P)` and `ElimInv` instance (style guide §"Proof Mode Integration")

**PORTING.md updates:**
```
- [x] `lib/cancelable_invariants.v`
```

---

#### PR H: Weakest Preconditions (Session-Specific) ✅

**Upstream reference:** PRs [#135](https://github.com/leanprover-community/iris-lean/pull/135) (wp examples), [#93](https://github.com/leanprover-community/iris-lean/pull/93) (heaplang)
**Branch:** `fork/iris/wp`
**Depends on:** PR E (fancy updates)
**Risk of upstream landing first:** Low (upstream hasn't decided on program logic design)

**Coq sources:**
- `iris/program_logic/weakestpre.v` — wp fixpoint, rules
- `iris/program_logic/language.v` — language interface
- `iris/program_logic/ectx_language.v` — evaluation context languages

**Files to create/modify in iris-lean:**

| File | Content | Coq source |
|------|---------|------------|
| `src/Iris/ProgramLogic/Language.lean` | `Language` typeclass (expressions, values, reduction) | `iris/program_logic/language.v` |
| `src/Iris/ProgramLogic/WeakestPre.lean` | `wp` fixpoint, `wp_value_fupd`, `wp_strong_mono`, `wp_bind`, `wp_frame_l`, `wp_fupd` | `iris/program_logic/weakestpre.v` |
| `PORTING.md` | Check off `weakestpre.v`, `language.v` items | — |

**Key definitions:**
```
wp_pre E e Φ :=
  match to_val e with
  | Some v => |={E}=> Φ v
  | None => ∀ σ ns κ κs nt,
      state_interp σ ns (κ ++ κs) nt ={E,∅}=∗
        ⌜reducible e σ⌝ ∗
        ∀ e2 σ2 efs, ⌜prim_step e σ κ e2 σ2 efs⌝ -∗ ...
  end
```

**Strategy note:** This PR has two possible scopes:
1. **Generic language interface** — port `language.v` + `weakestpre.v` faithfully. More work but upstreamable.
2. **Session-type-specific wp** — define wp directly for our Effects process language. Less upstreamable but immediately useful.

Recommend option 1 for upstreamability, instantiated with our session-type language in the Gibbs project (not in iris-lean).

**Proof mode notes:** The weakest precondition needs proof mode integration to be usable in practice:
1. `ElimModal` instances for `wp` + `fupd` interaction — allows `iMod` inside wp proofs (`class_instances_updates.v`)
2. `wp` notation in `iprop(...)` quotations — `WP e @ E {{ Φ }}` syntax via `proofmode.md` §2 custom notation pattern
3. The `wp_bind` rule maps to a tactic pattern: apply `wp_bind` then `iapply` the expression-level rule (see `tactics.md` §"iapply")
4. The existing `src/Iris/BI/Notation.lean` already defines some wp notation scaffolding — check `bi/weakestpre.v` in iris-lean for what exists

The `iLöb` tactic (`PORTING.md` — currently unported) becomes critical here: wp proofs for recursive programs need Löb induction. The Löb induction *definition* is already ported (`derived_laws_later.v` — "Löb induction definition" checked off), but the tactic and its `BILöb` class instances are not. Consider porting `iLöb` as part of this PR or as a companion PR.

**Style reminders:**
- `Language.lean` is a typeclass definition — keep it compact, one clear docstring, list the required fields (style guide §"Compact Definitions")
- `WeakestPre.lean` module doc should explain the fixpoint is well-founded because recursion is under `▷` (style guide §"Problem Statement")
- The `wp_pre` fixpoint may be the longest single definition — if it exceeds 30 lines, factor the value and non-value cases into separate helpers (style guide §"Code Block Size Limits")
- `WP e @ E {{ Φ }}` notation: add full `syntax` / `macro_rules` / `delab_rule` chain (style guide §"Notation")
- Two files, two directories: `src/Iris/ProgramLogic/Language.lean` and `src/Iris/ProgramLogic/WeakestPre.lean` (style guide §"Directory Structure")
- If porting `iLöb` tactic: follow the `elab` + `refine tac_*` pattern documented in `proofmode.md` and the style guide §"Proof Mode Integration" → "Add tactic theorems"

**PORTING.md updates:**
```
- [x] `weakestpre.v`
- [x] `language.v`
```

---

## Dependency Graph

```
Phase 1 (parallel):
  PR A: coPset ─────────────────┐
  PR B: big-op ─────────────────┤
  PR C: auth-updates ───────────┤
                                │
Phase 2:                        ▼
  PR D: wsat ───────────────────┤
                                │
Phase 3:                        ▼
  PR E: fupd ───────────────────┤
                  │             │
                  ▼             ▼
  PR F: invariants          PR H: wp
                  │
Phase 4:          ▼
  PR G: cinv
```

---

## Upstream Contribution Plan

### PRs we can submit upstream (self-contained, clean)

| Our PR | Upstream target | Likelihood of acceptance | Notes |
|--------|----------------|--------------------------|-------|
| PR A (coPset) | `leanprover-community/iris-lean` | High | Fills a clear gap, #78 is stale. Coordinate with Remyjck. |
| PR D (wsat) | `leanprover-community/iris-lean` | High | No competing PR, universally needed. |
| PR E (fupd) | `leanprover-community/iris-lean` | High | Same — no competing PR. |
| PR F (invariants) | `leanprover-community/iris-lean` | High | Same. |
| PR G (cinv) | `leanprover-community/iris-lean` | Medium-high | Less commonly needed but clean. |
| PR H (wp/language) | `leanprover-community/iris-lean` | Medium | Upstream hasn't decided on program logic design (#135 is exploratory). |

### PRs likely to be superseded by upstream

| Our PR | Competing upstream | Action when upstream lands |
|--------|-------------------|---------------------------|
| PR B (big-op) | #131, #132, #113 | Drop our branch, rebase `fork/iris/vendor` onto new master. |
| PR C (auth) | #134, #130 | Drop our branch if #134+#130 cover everything. |

### Coordination with maintainers

Before starting PRs D–H, post on the [iris-lean Zulip channel](https://leanprover.zulipchat.com/#narrow/stream/490604-iris-lean) to:
1. Signal intent to port wsat/fupd/invariants.
2. Ask about any in-progress work not reflected in open PRs.
3. Confirm the directory structure (`src/Iris/BaseLogic/Lib/`) matches maintainer expectations.

---

## Proof Mode Integration Summary

The iris-lean proof mode (documented in `proofmode.md` and `tactics.md`) is a tactic framework built on the `BIBase`/`BI` typeclasses with an `EnvsEntails` embedding that manages intuitionistic (`□`) and spatial (`∗`) hypothesis contexts. Our ported definitions need to integrate with this system at three levels:

### Level 1: Notation (`proofmode.md` §2)

All new connectives must be usable inside `iprop(...)` quotations. This requires:
- `syntax` declarations in the `term` category
- `macro_rules` mapping `iprop(...)` forms to Lean expressions
- `delab_rule` entries for readable tactic state display

**Applies to:** `ownI`/`ownE`/`ownD` (PR D), fancy update `|={E1,E2}=> P` (PR E), `inv N P` (PR F), `cinv N γ P` (PR G), `WP e @ E {{ Φ }}` (PR H), big sep `[∗ map]`/`[∗ list]` (PR B)

Existing notation infrastructure is in `src/Iris/BI/Notation.lean`. The FUpd notation `|={E1,E2}=> P` is already partially defined in `src/Iris/BI/Updates.lean` (the `FUpd` class exists).

### Level 2: Typeclass instances (`proofmode.md` §3)

Each new connective needs instances of the relevant proof mode classes (defined in `src/Iris/ProofMode/Classes.lean`) so the tactics can deconstruct/introduce them automatically. Key unported classes and their tactic dependencies:

| Class | Tactic | Coq source | Needed by PR |
|-------|--------|------------|-------------|
| `ElimModal` | `iMod` | `class_instances_updates.v` | E (fupd), H (wp) |
| `AddModal` | `iModIntro` | `class_instances_updates.v` | E (fupd) |
| `IsExcept0` | `iMod` (except-0 stripping) | `derived_laws_later.v` | E (fupd) |
| `IntoInv` | `iInv` | `class_instances.v` | F (inv), G (cinv) |
| `ElimInv` | `iInv` | `class_instances.v` | F (inv), G (cinv) |
| `IntoAcc` / `ElimAcc` | `iInv` (accessor pattern) | `class_instances.v` | F (inv) |
| `Persistent` | `iintro □` pattern | `class_instances.v` | F (inv), G (cinv) |
| `MaybeIntoLaterN` | `iNext` | `class_instances_later.v` | E (fupd), H (wp) |
| `FromModal` | `iModIntro` | `class_instances.v` | E (fupd) |

### Level 3: Tactic theorems and tactics (`proofmode.md` §"Tactics")

The tactic theorems in `src/Iris/ProofMode/Tactics/` justify proof mode context manipulations. New tactics needed:

| Tactic | Status | Depends on | Source |
|--------|--------|------------|--------|
| `iMod` | Not ported | `ElimModal`, `AddModal` | `coq_tactics.v` / `ltac_tactics.v` |
| `iModIntro` | Not ported | `FromModal` | `coq_tactics.v` / `ltac_tactics.v` |
| `iInv` | Not ported | `IntoInv`, `ElimInv` | `coq_tactics.v` / `ltac_tactics.v` |
| `iLöb` | Not ported | `BILöb` class (Löb def ported) | `coq_tactics.v` / `ltac_tactics.v` |
| `iNext` | Not ported | `MaybeIntoLaterN` | `coq_tactics.v` / `ltac_tactics.v` |

These tactics follow the implementation pattern documented in `proofmode.md` §"Tactics": an `elab` function in `TacticM` that parses syntax, finds hypothesis indices via `findHypothesis?`, and applies a tactic theorem via `refine` inside `evalTactic`. The tactic theorems are formulated as implications between `EnvsEntails` embeddings with typeclass constraints (see the `tac_wand_intro` example in `proofmode.md`).

**Recommendation:** PRs E and F should include the minimum proof mode instances (`ElimModal` for fupd, `Persistent` + `IntoInv` for inv) even if the full `iMod`/`iInv` tactic implementations are deferred. This way, users can at least use `iapply` with the relevant lemmas and `iintro` with `□` patterns for persistent propositions. The tactic implementations themselves can follow as a separate PR.

---

## Checklist per PR

Each PR must satisfy the upstream [PR template](https://github.com/leanprover-community/iris-lean/blob/master/PULL_REQUEST_TEMPLATE.md) **and** the full self-review checklist in `work/style_guide_lean_iris.md` §"Self-Review Checklist":

**Upstream requirements:**
- [ ] Code follows mathlib [naming](https://leanprover-community.github.io/contribute/naming.html) and [code style](https://leanprover-community.github.io/contribute/style.html) conventions
- [ ] `PORTING.md` updated with checked-off items
- [ ] Author name added to `authors` section of modified files
- [ ] Builds against `origin/master` (or the appropriate base)
- [ ] No axioms introduced (axiom-free is a project goal)

**Excluded files** — do NOT include these in any PR branch (they are local to our fork):
- `work/` — planning documents
- `.gitignore` — our local additions
- `iris-coq/` — Coq reference checkout
- `flake.nix` / `flake.lock` — our Nix setup
- `.claude/` / `CLAUDE.md` — AI tooling config

**Style guide requirements** (from `work/style_guide_lean_iris.md`):
- [ ] Every file has `/-!` module doc referencing Coq source file
- [ ] Section headers (`/-! ## -/`) break up content
- [ ] Every definition/theorem ≤ 30 lines; helpers extracted for longer proofs
- [ ] Related definitions grouped with whitespace between groups
- [ ] Theorems have docstrings with Coq lemma name references
- [ ] Proof mode typeclass instances registered for new connectives
- [ ] `iprop(...)` notation working with `syntax` + `macro_rules` + `delab_rule`
- [ ] Import discipline respected (Std ← Algebra ← BI ← BaseLogic ← ProgramLogic)
- [ ] Files under 500 lines
- [ ] `sorry` usage (if any) has `-- TODO:` comment and is tracked in this document




#######################################################################




# Iris Lean Port — Phase 2: Program Logic Layer

Follow-on to `iris.md` Tasks 1–8. Faithful port of Coq Iris program logic modules into iris-lean. All PRs target `leanprover-community/iris-lean`.

## Relationship to other documents

- **Phase 1 (above)** PRs A–H: base logic + algebra (auth RA, coPset, wsat, fupd, invariants, cinv, wp fixpoint, big ops)
- **Phase 2 (this section)** PRs I–O: program logic layer (language interface, WP rules, lifting, adequacy, ghost map/var, saved prop, gen_heap)
- **`iris_3.md`**: downstream session-type VM built on top of Phase 1 + Phase 2

## What iris.md leaves unported

PRs A–H cover the base logic and algebra layers. The program logic layer (`iris/program_logic/`) and several `base_logic/lib/` modules remain:

| Coq module | Purpose | Phase 1 coverage |
|---|---|---|
| `iris/program_logic/language.v` | Abstract language interface | Not covered |
| `iris/program_logic/ectx_language.v` | Evaluation context languages | Not covered |
| `iris/program_logic/weakestpre.v` | WP rules (beyond fixpoint definition) | PR H defines fixpoint only |
| `iris/program_logic/lifting.v` | Lifting lemmas (prim_step → WP) | Not covered |
| `iris/program_logic/adequacy.v` | Adequacy theorem | Not covered |
| `iris/program_logic/ectx_lifting.v` | Ectx-specific lifting lemmas | Not covered |
| `iris/program_logic/total_weakestpre.v` | Total WP (termination) | Not covered |
| `iris/base_logic/lib/ghost_map.v` | Ghost map (auth + gmap_view wrapper) | Not covered |
| `iris/base_logic/lib/ghost_var.v` | Ghost variable | Not covered |
| `iris/base_logic/lib/saved_prop.v` | Saved propositions | Not covered |
| `iris/base_logic/lib/gen_heap.v` | Generalized heap | Not covered |

## Open PRs on iris-lean

| PR | Title | Author | Updated | Relevant PR |
|---|---|---|---|---|
| [#134](https://github.com/leanprover-community/iris-lean/pull/134) | Auth CMRA | ahuoguo | 2026-01-27 | Prereq (PR C) |
| [#130](https://github.com/leanprover-community/iris-lean/pull/130) | Heap/HeapView functors | screenl | 2026-01-28 | Prereq for #134 |
| [#78](https://github.com/leanprover-community/iris-lean/pull/78) | coPsets and namespaces | Remyjck | 2025-07-25 | Prereq (PR A) |
| [#131](https://github.com/leanprover-community/iris-lean/pull/131) | FiniteMap interface | lzy0505 | 2026-01-29 | Prereq for #132/#113 |
| [#132](https://github.com/leanprover-community/iris-lean/pull/132) | `algebra/monoid.v` + `algebra/big_op.v` | lzy0505 | 2026-01-26 | Prereq (PR B) |
| [#113](https://github.com/leanprover-community/iris-lean/pull/113) | Big ops (BI layer) | lzy0505 | 2026-01-26 | Prereq (PR B) |
| [#135](https://github.com/leanprover-community/iris-lean/pull/135) | WP examples | markusdemedeiros | 2026-01-30 | PR J, PR K |
| [#93](https://github.com/leanprover-community/iris-lean/pull/93) | Initial heaplang | Shreyas4991 | 2026-01-22 | PR I |
| [#141](https://github.com/leanprover-community/iris-lean/pull/141) | `imodintro` / `imod` tactics | MackieLoeffel | 2026-01-30 | Proof mode infra |
| [#138](https://github.com/leanprover-community/iris-lean/pull/138) | Derived later laws | MackieLoeffel | open | PR M (saved prop) |
| [#74](https://github.com/leanprover-community/iris-lean/pull/74) | `irevert` tactic | oliversoeser | 2026-01-22 | Proof mode infra |
| [#137](https://github.com/leanprover-community/iris-lean/pull/137) | csum CMRA | ahuoguo | 2026-01-28 | Not directly needed |
| [#11](https://github.com/leanprover-community/iris-lean/pull/11) | Alternative CMRA definition | markusdemedeiros | 2026-01-22 | May affect RA approach |

---

## PRs

#### PR I: Language Interface

**Branch:** `fork/iris/language`
**Depends on:** None
**Coq sources:** `iris/program_logic/language.v`, `iris/program_logic/ectx_language.v`

**Files to create/modify:**

| File | Content | Coq source |
|------|---------|------------|
| `src/Iris/ProgramLogic/Language.lean` | `Language`, `LanguageMixin`, `reducible`, `irreducible` | `language.v` |
| `src/Iris/ProgramLogic/EctxLanguage.lean` | `EctxLanguage`, `EctxLanguageMixin`, build `Language` from `EctxLanguage` | `ectx_language.v` |

**Key definitions:** `Language` typeclass (`expr`, `val`, `state`, `of_val`, `to_val`, `prim_step`), `EctxLanguage` (`ectx`, `fill`, `decomp` + compositionality).

**Relevant upstream PRs:** [#93](https://github.com/leanprover-community/iris-lean/pull/93) (heaplang), [#135](https://github.com/leanprover-community/iris-lean/pull/135) (WP examples)

---

#### PR J: WP Rules and Lifting

**Branch:** `fork/iris/wp-rules`
**Depends on:** PR H (wp fixpoint), PR I (language)
**Coq sources:** `iris/program_logic/weakestpre.v` (rules), `iris/program_logic/lifting.v`, `iris/program_logic/ectx_lifting.v`

**Files to create/modify:**

| File | Content | Coq source |
|------|---------|------------|
| `src/Iris/ProgramLogic/WeakestPre.lean` | `wp_unfold`, `wp_value`, `wp_strong_mono`, `wp_bind`, `wp_frame_l/r`, `wp_step_fupd`, `wp_fupd` | `weakestpre.v` |
| `src/Iris/ProgramLogic/Lifting.lean` | `wp_lift_step`, `wp_lift_pure_step_no_fork`, `wp_lift_atomic_step` | `lifting.v` |
| `src/Iris/ProgramLogic/EctxLifting.lean` | `wp_ectx_bind` | `ectx_lifting.v` |

**Relevant upstream PRs:** [#135](https://github.com/leanprover-community/iris-lean/pull/135)

---

#### PR K: Adequacy

**Branch:** `fork/iris/adequacy`
**Depends on:** PR J (WP rules), PR E (fupd soundness)
**Coq sources:** `iris/program_logic/adequacy.v`

**Files to create/modify:**

| File | Content | Coq source |
|------|---------|------------|
| `src/Iris/ProgramLogic/Adequacy.lean` | `wp_adequacy`, `wp_strong_adequacy`, `wp_invariance` | `adequacy.v` |

**Blocked / TODO (2026-02-02):**
- `wp_adequacy`, `wp_invariance` in `src/Iris/ProgramLogic/Adequacy.lean` still require a
  polymorphic `fupd`/`wp` (Coq-style `∀ W`) to apply soundness. The current Lean `wp` is
  fixed to `IrisGS.wsatGS`, so the adequacy extraction cannot use `fupd_soundness_no_lc`.
  Needs either (1) refactor `wp`/`fupd` to be world-polymorphic in adequacy proofs, or
  (2) add a soundness lemma specialized to a fixed `W` with a matching `wsat_alloc`.
**Tasks (2026-02-03):**
- [x] Make adequacy world-polymorphic: eliminate hidden `W` in `step_fupdN`/helpers and
  thread `W` explicitly (or via `∀ W`) through `wp_strong_adequacy`, `wp_adequacy`,
  and `wp_invariance` so `fupd_soundness_no_lc` applies.
- [x] Split `src/Iris/ProgramLogic/Adequacy.lean` into ≤500-line submodules under
  `src/Iris/ProgramLogic/Adequacy/`, each with module docs and ≤30-line blocks.
- [x] Refactor remaining adequacy lemmas to satisfy the ≤30-line block rule (extract
  helpers for `wptp_preservation`, `adq_wp_step`, `wptp_step_len_true`, etc.).
- [x] Update `PORTING.md` to include `iris/program_logic/adequacy.v` once complete.

**Tasks (2026-02-04):**
- [x] Factor out `wptp_body_at_fn` in `ThreadPool` and unfold helpers to avoid
  definitional mismatches with local `match` expressions.
- [x] Refactor `WptpHelpersA` split/append lemmas to use `wptp_body_at_fn` plus
  a shift helper so `big_sepL_app` aligns with the offset form.
- [x] Run `nix develop -c lake build Iris.ProgramLogic.Adequacy.WptpHelpersA`.
- [x] Add `PROP := IProp GF` to `BIBase.«exists»` in `wp_progress_fupd_elim` and
  the `Hwp` binder of `wp_progress` to fix missing `BIBase` instances.
- [x] Resolve `step_fupdN_soundness_later` world mismatch by using
  `step_fupdN_plain` + `laterN` soundness instead of fixed-`W` soundness.
- [x] Fix `wp_progress_soundness_pure`/`wp_progress_soundness` world mismatch
  by rewiring to the new `step_fupdN_soundness` shape.
- [x] Run `nix develop -c lake build` and re-scan adequacy files for long blocks
  (build passes; long-block violations remain — see below).
**Tasks (2026-02-04, PR K path A):**
- [x] Port Coq-style step-fupd: make adequacy `step_fupdN` use the BI
  `|={Eo}[Ei]▷=>` chain and update `step_fupdN_mono`/`step_fupdN_frame_r` and
  `step_fupdN_succ_finish` to match the new definition.
- [x] Add `BIFUpdate` instance for `uPred_fupd` in
  `src/Iris/BaseLogic/Lib/FancyUpdates.lean` (includes `mask_frame_r'` helper).
- [x] Add `BIFUpdatePlainly` instance for `uPred_fupd` in
  `src/Iris/BaseLogic/Lib/FancyUpdates.lean` (`fupd_plainly_keep_l`,
  `fupd_plainly_later`, `fupd_plainly_sForall_2`).
- [x] Add `step_fupdN_plain` using the `BIFUpdatePlainly` instance and rewire
  adequacy to use it.
- [x] Rework `step_fupdN_soundness_*` in
  `src/Iris/ProgramLogic/Adequacy/FUpd.lean` to use `step_fupdN_plain` and
  eliminate the world mismatch.
- [x] Update adequacy soundness (`wp_progress_soundness_pure`,
  `wp_strong_adequacy_finish`) to the new `step_fupdN_soundness` shape and
  provide any required `Plain` instances (pure/derived).
- [x] Fix build failures in `src/Iris/ProgramLogic/Adequacy/FUpd.lean`,
  `StrongAdequacy.lean`, `WptpHelpersC.lean`, `SimplifiedAdequacy.lean`,
  `Invariance.lean`: resolved `(W := W)` annotations, `fupd_elim` abstract
  vs concrete mismatch, `iintro` proof mode `AsEmpValid` patterns,
  `wp_adequacy_inv` section-variable capture, and outside-section theorem
  variable scoping.
- [x] All adequacy files build cleanly with no `sorry`s.

---

#### PR L: Ghost Map + Generalized Heap ✅

**Branch:** `fork/iris/ghost-state`
**Depends on:** PR C (auth RA), PR D (wsat/own)
**Coq sources:** `iris/base_logic/lib/ghost_map.v`, `iris/base_logic/lib/gen_heap.v`

**Files to create/modify:**

| File | Content | Coq source |
|------|---------|------------|
| `src/Iris/BaseLogic/Lib/GhostMap.lean` | `ghost_map_auth`, `ghost_map_elem`, `ghost_map_alloc`, `ghost_map_lookup`, `ghost_map_insert`, `ghost_map_update`, `ghost_map_delete`, `ghost_map_elem_persist` | `ghost_map.v` |
| `src/Iris/BaseLogic/Lib/GenHeap.lean` | `gen_heap_interp`, `pointsto` (`l ↦{dq} v`), `gen_heap_alloc`, `gen_heap_update`, `gen_heap_valid` | `gen_heap.v` |

**Relevant upstream PRs:** [#134](https://github.com/leanprover-community/iris-lean/pull/134) (auth), [#130](https://github.com/leanprover-community/iris-lean/pull/130) (functors)

**Completion notes:**
- Both files build with 0 sorries.
- GhostMap.lean (~608 lines): full ghost map library built on `HeapView` CMRA
  and `iOwn`. Includes auth/elem definitions, validity, agreement, persistence,
  lookup, insert, delete, update, and allocation (`ghost_map_alloc_empty`).
- GenHeap.lean (~175 lines): thin wrapper over GhostMap with `GenHeapGS`
  typeclass providing a singleton ghost name. All theorems are one-liner
  delegations.
- Meta-data infrastructure (`meta_token`, `meta`, `reservation_map`) omitted —
  requires unported `reservation_map` RA and namespace indirection.
- Timeless instances omitted — requires unported `ownM_timeless` infrastructure.
- `gen_heap_init` omitted (not in PR L scope; requires existential typeclass
  binding patterns).

---

#### PR M: Ghost State Primitives (Saved Prop + Ghost Var) ✅

**Branch:** `fork/iris/ghost-primitives`
**Depends on:** None (agreement RA, excl RA, frac RA, later modality already ported)
**Coq sources:** `iris/base_logic/lib/saved_prop.v`, `iris/base_logic/lib/ghost_var.v`

**Files to create/modify:**

| File | Content | Coq source |
|------|---------|------------|
| `src/Iris/BaseLogic/Lib/SavedProp.lean` | `saved_prop_own`, `saved_prop_alloc`, `saved_prop_agree` | `saved_prop.v` |
| `src/Iris/BaseLogic/Lib/GhostVar.lean` | `ghost_var_alloc`, `ghost_var_agree`, `ghost_var_update` | `ghost_var.v` |

**Relevant upstream PRs:** [#138](https://github.com/leanprover-community/iris-lean/pull/138) (derived later laws)

**Completion notes:**
- `GhostVar.lean`: Fully implemented (0 sorry). All theorems proved: `ghost_var_persistent`,
  `ghost_var_alloc`, `ghost_var_valid_2`, `ghost_var_agree`, `ghost_var_update`,
  `ghost_var_update_2`, `ghost_var_persist`. Key techniques: `CoreId.of_pcore_eq_some rfl`
  for product pair persistence, explicit `Exclusive` construction for pairs propagating
  first-component exclusivity, `CMRA.discrete_valid` for Agree agreement extraction.
- `SavedProp.lean`: Partially implemented (2 sorry). All theorems proved except agreement:
  `saved_anything_persistent`, `saved_anything_alloc`, `saved_anything_valid`,
  `saved_anything_persist`, `saved_anything_update`, `saved_prop_persistent`,
  `saved_prop_alloc`, `saved_prop_persist`, `saved_prop_update`.
  Agreement theorems (`saved_anything_agree`, `saved_prop_agree`) blocked on internal
  equality (`≡` as BI connective) and `Later` OFE wrapper, both not yet ported.

---

## Dependency Graph

```
PRs A–H (prerequisite — Phase 1)
    │
    ├── PR I: language interface (no deps)
    │       │
    │       v
    │   PR J: WP rules + lifting ◄── PR H
    │       │
    │       v
    │   PR K: adequacy ◄── PR E
    │
    ├── PR L: ghost_map + gen_heap ◄── PR C, PR D
    │
    └── PR M: saved_prop + ghost_var (independent)
```

**Critical path:** PRs A–H → I → J → K

**Independent:** L, M can land in any order.

## Branch Strategy

| PR | Branch | Depends on |
|---|---|---|
| I | `fork/iris/language` | — |
| J | `fork/iris/wp-rules` | I, H |
| K | `fork/iris/adequacy` | J |
| L | `fork/iris/ghost-state` | C, D |
| M | `fork/iris/ghost-primitives` | — |

**Coordination with existing PRs:**
- If [#93](https://github.com/leanprover-community/iris-lean/pull/93) (heaplang) already factors out a `Language` class, PR I may reduce to review/cleanup.
- If [#135](https://github.com/leanprover-community/iris-lean/pull/135) (WP examples) contains WP rules, PR J can build on it.
- [#141](https://github.com/leanprover-community/iris-lean/pull/141) (imodintro) and [#74](https://github.com/leanprover-community/iris-lean/pull/74) (irevert) provide proof mode tactics useful for J/K.

/-
Copyright (c) 2026 Sam Hart. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sam Hart
-/
import Iris.Instances.IProp.Instance

/-! # Saved Propositions

Reference: `iris/base_logic/lib/saved_prop.v`

A mechanism for storing propositions (and predicates) in ghost state using
the `dfrac_agree` CMRA composed with a contractive OFE functor `F`.

The file follows a "generic then specialize" pattern:
- **Generic layer** (`saved_anything_own`): parameterized by an arbitrary
  contractive OFE functor `G`.
- **Saved propositions** (`saved_prop_own`): specialization where the
  carrier is `DFrac F × Agree (IProp GF)`. In Coq, this uses
  `dfrac_agreeR (laterO (iPropO Σ))` with `Next P`; the `Later` wrapper
  at the OFE level ensures contractivity. Agreement is up to `▷`.

## Main Definitions

- `saved_anything_own` — generic ghost ownership with a contractive functor
- `saved_prop_own` — saved proposition ownership

## Main Results

- `saved_anything_alloc`, `saved_anything_agree`, `saved_anything_persist`,
  `saved_anything_update` — generic allocation, agreement, persistence, update
- `saved_prop_alloc`, `saved_prop_agree` — saved proposition versions

## Simplifications

- The `Later` OFE wrapper on the carrier is omitted in the stub because
  `Later (A : Type u) : Type (u+1)` bumps the universe, which is
  incompatible with `constOF`. The proper implementation should use a
  non-constant functor (e.g., `ProdOF (constOF (DFrac F)) (AgreeOF (LaterOF idOF))`).
- `Fractional` / `AsFractional` instances, `CombineSepGives` / `CombineSepAs`
  proof mode instances, and `Timeless` instances are omitted.
- Saved predicates (`saved_pred_own`) are omitted — they require discrete
  function space infrastructure (`A -d> ...`) not yet ported.
- Agreement theorems (`saved_anything_agree`, `saved_prop_agree`) require
  internal equality (`≡` as a BI connective) which is not yet ported.
  These are left as `sorry`.
-/

namespace Iris.BaseLogic

open Iris Iris.Algebra Iris.Std Iris.BI COFE

variable {GF : BundledGFunctors} {F : Type _} [UFraction F]

/-! ## Helpers -/

/-- `toAgree x` is always valid (singleton list). -/
private theorem toAgree_valid' {X : Type _} [OFE X] (x : X) :
    CMRA.Valid (toAgree x) :=
  fun _ => trivial

/-! ## Generic: Saved Anything -/

variable {G : OFunctorPre} [OFunctor G] [OFunctorContractive G]

-- NOTE: In Coq, `savedAnythingG Σ F` bundles an `inG` instance for
-- `dfrac_agreeR (oFunctor_apply F (iPropO Σ))` plus contractivity of `F`.
-- Here we use `ElemG` with the constant functor wrapping the product CMRA.

/-- The carrier type for saved-anything ghost state, applied at `IProp GF`.

    Coq: `dfrac_agreeR (oFunctor_apply F (iPropO Σ))` -/
abbrev SavedAnythingR (GF : BundledGFunctors) (F : Type _) [UFraction F]
    (G : OFunctorPre) [OFunctor G] :=
  DFrac F × Agree (G (IProp GF) (IProp GF))

/-- Constant functor for the saved-anything ghost state. -/
abbrev SavedAnythingF (GF : BundledGFunctors) (F : Type _) [UFraction F]
    (G : OFunctorPre) [OFunctor G] : OFunctorPre :=
  constOF (SavedAnythingR GF F G)

variable [ElemG GF (SavedAnythingF GF F G)]

/-- Generic saved-anything ownership: ghost name `γ` holds element `x`
    from functor application `G (IProp GF) (IProp GF)` with fraction `dq`.

    Coq: `saved_anything_own` -/
noncomputable def saved_anything_own
    (γ : GName) (dq : DFrac F) (x : G (IProp GF) (IProp GF)) :
    IProp GF :=
  iOwn (GF := GF) (F := SavedAnythingF GF F G) γ (dq, toAgree x)

/-! ### Saved Anything Instances -/

-- Timeless instance omitted: requires `ownM_timeless` infrastructure.
-- Fractional / AsFractional instances omitted: not yet ported.

/-- `saved_anything_own` with discarded fraction is persistent.

    Coq: `saved_anything_discarded_persistent` -/
instance saved_anything_persistent (γ : GName)
    (x : G (IProp GF) (IProp GF)) :
    Persistent (saved_anything_own (GF := GF) (F := F) (G := G)
      γ .discard x) where
  persistent := by
    haveI : CMRA.CoreId (DFrac.discard (F := F), toAgree x) :=
      CMRA.CoreId.of_pcore_eq_some
        (x := (DFrac.discard (F := F), toAgree x)) rfl
    simp only [saved_anything_own]
    exact persistently_intro

/-! ### Saved Anything Allocation -/

/-- Allocate a saved-anything ghost name.

    Coq: `saved_anything_alloc` -/
theorem saved_anything_alloc (dq : DFrac F) (hdq : DFrac.valid dq)
    (x : G (IProp GF) (IProp GF)) :
    ⊢ BUpd.bupd (BIBase.«exists» fun γ =>
      saved_anything_own (GF := GF) (F := F) (G := G) γ dq x) := by
  simp only [saved_anything_own]
  exact iOwn_alloc _ ⟨hdq, toAgree_valid' x⟩

/-! ### Saved Anything Validity and Agreement -/

/-- A saved-anything carries a valid fraction.

    Coq: `saved_anything_valid` -/
theorem saved_anything_valid (γ : GName) (dq : DFrac F)
    (x : G (IProp GF) (IProp GF)) :
    saved_anything_own (GF := GF) (F := F) (G := G) γ dq x
      ⊢ BIBase.pure (DFrac.valid dq) := by
  simp only [saved_anything_own]
  refine (iOwn_cmraValid (GF := GF)
    (F := SavedAnythingF GF F G) (γ := γ)).trans ?_
  refine (UPred.cmraValid_elim _).trans ?_
  exact BI.pure_mono And.left

/-- Two saved-anything at the same name agree on value (up to OFE
    equivalence).

    Coq: `saved_anything_agree`

    TODO: Requires internal equality (`≡` as BI connective) and the
    `Later` OFE wrapper. The Coq conclusion is `▷ (x ≡ y)` using
    internal equality; the stub uses `pure (x ≡ y)` which is too strong
    without discreteness. -/
theorem saved_anything_agree (γ : GName) (dq1 dq2 : DFrac F)
    (x y : G (IProp GF) (IProp GF)) :
    BIBase.sep
      (saved_anything_own (GF := GF) (F := F) (G := G) γ dq1 x)
      (saved_anything_own (GF := GF) (F := F) (G := G) γ dq2 y)
      ⊢ BIBase.pure (x ≡ y) := by
  sorry

/-! ### Saved Anything Update and Persistence -/

/-- Make a saved-anything read-only (persistent).

    Coq: `saved_anything_persist` -/
theorem saved_anything_persist (γ : GName) (dq : DFrac F)
    (x : G (IProp GF) (IProp GF)) :
    saved_anything_own (GF := GF) (F := F) (G := G) γ dq x
      ⊢ BUpd.bupd (saved_anything_own (GF := GF) (F := F) (G := G)
          γ .discard x) := by
  simp only [saved_anything_own]
  exact iOwn_update (GF := GF) (F := SavedAnythingF GF F G) (γ := γ)
    (Update.prod (dq, toAgree x)
      DFrac.DFrac.update_discard Update.id)

/-- Update a saved-anything with full ownership.

    Coq: `saved_anything_update` -/
theorem saved_anything_update (γ : GName)
    (x y : G (IProp GF) (IProp GF)) :
    saved_anything_own (GF := GF) (F := F) (G := G)
        γ (DFrac.own 1) x
      ⊢ BUpd.bupd (saved_anything_own (GF := GF) (F := F) (G := G)
          γ (DFrac.own 1) y) := by
  simp only [saved_anything_own]
  haveI : CMRA.Exclusive (DFrac.own (1 : F), toAgree x) :=
    ⟨fun y hv => CMRA.exclusive0_l (x := DFrac.own (1 : F)) y.1 hv.1⟩
  exact iOwn_update (GF := GF) (F := SavedAnythingF GF F G) (γ := γ)
    (Update.exclusive ⟨DFrac.valid_own_one, toAgree_valid' y⟩)

/-! ## Saved Propositions -/

-- Coq uses `F := laterOF idOF`, i.e., `LaterOF` applied to identity.
-- The carrier is `dfrac_agreeR (laterO (iPropO Σ))`.
--
-- In the Lean port, `Later (A : Type u) : Type (u+1)` bumps the
-- universe, so `DFrac F × Agree (Later (IProp GF)) : Type 1` is
-- incompatible with `constOF (B : Type)`. The stub uses
-- `DFrac F × Agree (IProp GF)` as carrier instead. The proper
-- implementation should use a non-constant functor like
-- `ProdOF (constOF (DFrac F)) (AgreeOF (LaterOF idOF))`.

/-- Carrier for saved propositions.

    Coq: `dfrac_agreeR (laterO (iPropO Σ))` -/
abbrev SavedPropR (GF : BundledGFunctors) (F : Type _) [UFraction F] :=
  DFrac F × Agree (IProp GF)

/-- Constant functor for saved proposition ghost state. -/
abbrev SavedPropF (GF : BundledGFunctors) (F : Type _)
    [UFraction F] : OFunctorPre :=
  constOF (SavedPropR GF F)

variable [ElemG GF (SavedPropF GF F)]

/-- Saved proposition ownership: `saved_prop_own γ dq P` asserts that
    ghost name `γ` stores proposition `P` with fraction `dq`.

    Coq: `saved_prop_own` -/
noncomputable def saved_prop_own (γ : GName) (dq : DFrac F)
    (P : IProp GF) : IProp GF :=
  iOwn (GF := GF) (F := SavedPropF GF F) γ (dq, toAgree P)

/-! ### Saved Proposition Instances -/

/-- `saved_prop_own` with discarded fraction is persistent.

    Coq: `saved_prop_discarded_persistent` -/
instance saved_prop_persistent (γ : GName) (P : IProp GF) :
    Persistent (saved_prop_own (GF := GF) (F := F) γ .discard P) where
  persistent := by
    haveI : CMRA.CoreId (DFrac.discard (F := F), toAgree P) :=
      CMRA.CoreId.of_pcore_eq_some
        (x := (DFrac.discard (F := F), toAgree P)) rfl
    simp only [saved_prop_own]
    exact persistently_intro

/-! ### Saved Proposition Allocation -/

/-- Allocate a saved proposition.

    Coq: `saved_prop_alloc` -/
theorem saved_prop_alloc (dq : DFrac F) (hdq : DFrac.valid dq)
    (P : IProp GF) :
    ⊢ BUpd.bupd (BIBase.«exists» fun γ =>
      saved_prop_own (GF := GF) (F := F) γ dq P) := by
  simp only [saved_prop_own]
  exact iOwn_alloc _ ⟨hdq, toAgree_valid' P⟩

/-! ### Saved Proposition Agreement -/

/-- Two saved propositions at the same name agree up to `▷`.

    Coq: `saved_prop_agree`

    TODO: Requires internal equality (`≡` as BI connective) and the
    `Later` OFE wrapper. The Coq conclusion is `▷ (P ≡ Q)` using
    internal equality; the stub uses `▷ (pure (P = Q))` which requires
    Leibniz equality. -/
theorem saved_prop_agree (γ : GName) (dq1 dq2 : DFrac F)
    (P Q : IProp GF) :
    BIBase.sep
      (saved_prop_own (GF := GF) (F := F) γ dq1 P)
      (saved_prop_own (GF := GF) (F := F) γ dq2 Q)
      ⊢ BIBase.later (BIBase.pure (P = Q)) := by
  sorry

/-! ### Saved Proposition Update and Persistence -/

/-- Make a saved proposition read-only.

    Coq: `saved_prop_persist` -/
theorem saved_prop_persist (γ : GName) (dq : DFrac F) (P : IProp GF) :
    saved_prop_own (GF := GF) (F := F) γ dq P
      ⊢ BUpd.bupd
          (saved_prop_own (GF := GF) (F := F) γ .discard P) := by
  simp only [saved_prop_own]
  exact iOwn_update (GF := GF) (F := SavedPropF GF F) (γ := γ)
    (Update.prod (dq, toAgree P)
      DFrac.DFrac.update_discard Update.id)

/-- Update a saved proposition with full ownership.

    Coq: `saved_prop_update` -/
theorem saved_prop_update (γ : GName) (P Q : IProp GF) :
    saved_prop_own (GF := GF) (F := F) γ (DFrac.own 1) P
      ⊢ BUpd.bupd
          (saved_prop_own (GF := GF) (F := F) γ (DFrac.own 1) Q) := by
  simp only [saved_prop_own]
  haveI : CMRA.Exclusive (DFrac.own (1 : F), toAgree P) :=
    ⟨fun y hv => CMRA.exclusive0_l (x := DFrac.own (1 : F)) y.1 hv.1⟩
  exact iOwn_update (GF := GF) (F := SavedPropF GF F) (γ := γ)
    (Update.exclusive ⟨DFrac.valid_own_one, toAgree_valid' Q⟩)

end Iris.BaseLogic

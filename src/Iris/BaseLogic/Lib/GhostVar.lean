/-
Copyright (c) 2026 Sam Hart. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sam Hart
-/
import Iris.Instances.IProp.Instance

/-! # Ghost Variables

Reference: `iris/base_logic/lib/ghost_var.v`

A simple ghost variable mechanism: `ghost_var γ q a` asserts ownership of a
ghost variable at name `γ` holding value `a : A` with fraction `q`. Full
ownership (`q = 1`) permits updating to any new value; fractional ownership
provides agreement.

## Main Definitions

- `GhostVarR` — carrier CMRA: `DFrac F × Agree A`
- `GhostVarF` — constant OFunctor wrapping the carrier
- `ghost_var` — ghost variable predicate `ghost_var γ dq a`

## Main Results

- `ghost_var_alloc` — allocate a fresh ghost variable
- `ghost_var_valid`, `ghost_var_agree` — validity and agreement
- `ghost_var_update` — update with full ownership
- `ghost_var_update_2` — update with complementary fractions

## Simplifications

`Fractional` / `AsFractional` instances, `CombineSepGives` / `CombineSepAs`
proof mode instances, and `Timeless` instances are omitted — the required
typeclass infrastructure has not been ported from Coq yet.
-/

namespace Iris.BaseLogic

open Iris Iris.Algebra Iris.Std Iris.BI COFE

variable {GF : BundledGFunctors} {F : Type _} [UFraction F]
variable {A : Type _} [OFE A] [OFE.Discrete A] [OFE.Leibniz A]

/-! ## Carrier CMRA -/

/-- Carrier CMRA for ghost variables: a product of discardable fractions
    and the agreement RA over `A`.

    Coq: `dfrac_agreeR (leibnizO A)` -/
abbrev GhostVarR (F : Type _) (A : Type _) [UFraction F] [OFE A] :=
  DFrac F × Agree A

/-- Constant functor for the ghost variable ghost state. -/
abbrev GhostVarF (F : Type _) (A : Type _) [UFraction F] [OFE A] :
    OFunctorPre :=
  COFE.constOF (GhostVarR F A)

variable [ElemG GF (GhostVarF F A)]

/-! ## Helpers -/

/-- `toAgree a` is always valid (singleton list). -/
private theorem toAgree_valid (a : A) : CMRA.Valid (toAgree a) :=
  fun _ => trivial

/-- Validity at step 0 of two composed dfrac-agree pairs gives valid
    combined fraction and equal values. -/
private theorem dfrac_agree_op_valid0 {dq1 dq2 : DFrac F}
    {a1 a2 : A} :
    CMRA.ValidN 0 ((dq1, toAgree a1) • (dq2, toAgree a2)) →
    DFrac.valid (DFrac.op dq1 dq2) ∧ a1 = a2 := by
  intro ⟨hdq, hagr⟩
  exact ⟨hdq,
    (toAgree_op_valid_iff_eq (α := A)).mp (CMRA.discrete_valid hagr)⟩

/-! ## Definition -/

/-- Ghost variable predicate: `ghost_var γ dq a` asserts fractional
    ownership of ghost name `γ` holding value `a`.

    Coq: `ghost_var` -/
noncomputable def ghost_var (γ : GName) (dq : DFrac F) (a : A) :
    IProp GF :=
  iOwn (GF := GF) (F := GhostVarF F A) γ (dq, toAgree a)

/-! ## Instances -/

-- Timeless instance omitted: requires `ownM_timeless` infrastructure.
-- Fractional / AsFractional instances omitted: not yet ported.

/-- `ghost_var` with discarded fraction is persistent.

    Coq: `ghost_var_persistent` (via `dfrac_agree`) -/
instance ghost_var_persistent (γ : GName) (a : A) :
    Persistent (ghost_var (GF := GF) (F := F) γ .discard a) where
  persistent := by
    haveI : CMRA.CoreId (DFrac.discard (F := F), toAgree a) :=
      CMRA.CoreId.of_pcore_eq_some (x := (DFrac.discard (F := F), toAgree a))
        rfl
    simp only [ghost_var]
    exact persistently_intro

/-! ## Allocation -/

/-- Allocate a fresh ghost variable with full ownership.

    Coq: `ghost_var_alloc` -/
theorem ghost_var_alloc (a : A) :
    ⊢ BUpd.bupd (BIBase.«exists» fun γ =>
      ghost_var (GF := GF) (F := F) γ (DFrac.own 1) a) := by
  simp only [ghost_var]
  exact iOwn_alloc _ ⟨DFrac.valid_own_one, toAgree_valid a⟩

/-! ## Validity and Agreement -/

/-- Two ghost variables at the same name have valid combined fraction
    and equal values.

    Coq: `ghost_var_valid_2` -/
theorem ghost_var_valid_2 (γ : GName) (dq1 dq2 : DFrac F)
    (a1 a2 : A) :
    BIBase.sep
      (ghost_var (GF := GF) γ dq1 a1)
      (ghost_var (GF := GF) γ dq2 a2)
      ⊢ BIBase.pure (DFrac.valid (DFrac.op dq1 dq2) ∧ a1 = a2) := by
  simp only [ghost_var]
  refine (iOwn_cmraValid_op (GF := GF)
    (F := GhostVarF F A) (γ := γ)).trans ?_
  refine (UPred.cmraValid_elim _).trans ?_
  exact BI.pure_mono dfrac_agree_op_valid0

/-- Two ghost variables at the same name agree on value.

    Coq: `ghost_var_agree` -/
theorem ghost_var_agree (γ : GName) (dq1 dq2 : DFrac F)
    (a1 a2 : A) :
    BIBase.sep
      (ghost_var (GF := GF) γ dq1 a1)
      (ghost_var (GF := GF) γ dq2 a2)
      ⊢ BIBase.pure (a1 = a2) :=
  (ghost_var_valid_2 γ dq1 dq2 a1 a2).trans (BI.pure_mono And.right)

/-! ## Updates -/

/-- Update a ghost variable with full ownership.

    Coq: `ghost_var_update` -/
theorem ghost_var_update (γ : GName) (a b : A) :
    ghost_var (GF := GF) (F := F) γ (DFrac.own 1) a
      ⊢ BUpd.bupd
          (ghost_var (GF := GF) (F := F) γ (DFrac.own 1) b) := by
  simp only [ghost_var]
  haveI : CMRA.Exclusive (DFrac.own (1 : F), toAgree a) :=
    ⟨fun y hv => CMRA.exclusive0_l (x := DFrac.own (1 : F)) y.1 hv.1⟩
  exact iOwn_update (GF := GF) (F := GhostVarF F A) (γ := γ)
    (Update.exclusive ⟨DFrac.valid_own_one, toAgree_valid b⟩)

/-- Update a ghost variable with two complementary fractions.

    Coq: `ghost_var_update_2` -/
theorem ghost_var_update_2 (γ : GName) (q1 q2 : F)
    (a1 a2 b : A) (hfull : (q1 + q2 : F) = 1) :
    BIBase.sep
      (ghost_var (GF := GF) γ (.own q1) a1)
      (ghost_var (GF := GF) γ (.own q2) a2)
      ⊢ BUpd.bupd (BIBase.sep
          (ghost_var (GF := GF) γ (.own q1) b)
          (ghost_var (GF := GF) γ (.own q2) b)) := by
  simp only [ghost_var]
  refine (iOwn_op (GF := GF) (F := GhostVarF F A) (γ := γ)).mpr.trans ?_
  have hupd : (DFrac.own q1, toAgree a1) • (DFrac.own q2, toAgree a2)
      ~~> (DFrac.own q1, toAgree b) • (DFrac.own q2, toAgree b) := by
    have hexcl : CMRA.Exclusive (DFrac.own (q1 + q2)) :=
      DFrac.own_whole_exclusive (hfull ▸ UFraction.one_whole)
    haveI : CMRA.Exclusive
        ((DFrac.own q1, toAgree a1) • (DFrac.own q2, toAgree a2)) :=
      ⟨fun y hv => hexcl.exclusive0_l y.1 hv.1⟩
    refine Update.exclusive ⟨?_, (toAgree_op_valid_iff_eq (α := A)).mpr rfl⟩
    show DFrac.valid (DFrac.own (q1 + q2))
    exact hfull ▸ DFrac.valid_own_one
  refine (iOwn_update (GF := GF) (F := GhostVarF F A) (γ := γ)
    hupd).trans ?_
  exact BIUpdate.mono (iOwn_op (GF := GF) (F := GhostVarF F A)
    (γ := γ)).mp

/-! ## Persistence -/

/-- Make a ghost variable read-only (persistent).

    Coq: `ghost_var_persist` (via `dfrac_agree_persist`) -/
theorem ghost_var_persist (γ : GName) (dq : DFrac F) (a : A) :
    ghost_var (GF := GF) γ dq a
      ⊢ BUpd.bupd
          (ghost_var (GF := GF) (F := F) γ .discard a) := by
  simp only [ghost_var]
  exact iOwn_update (GF := GF) (F := GhostVarF F A) (γ := γ)
    (Update.prod (dq, toAgree a)
      (DFrac.DFrac.update_discard) Update.id)

end Iris.BaseLogic

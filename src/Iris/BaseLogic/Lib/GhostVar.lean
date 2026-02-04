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

- `GhostVarR` — carrier CMRA: `DFrac F × Agree (LeibnizO A)`
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

/-! ## Constructor -/

/-- Construct the CMRA element for a ghost variable: `(DFrac.own q, toAgree a)`.

    Coq: `to_frac_agree` -/
private def to_frac_agree (dq : DFrac F) (a : A) : GhostVarR F A :=
  (dq, toAgree a)

/-! ## Definition -/

/-- Ghost variable predicate: `ghost_var γ dq a` asserts fractional
    ownership of ghost name `γ` holding value `a`.

    Coq: `ghost_var` -/
noncomputable def ghost_var (γ : GName) (dq : DFrac F) (a : A) :
    IProp GF :=
  iOwn (GF := GF) (F := GhostVarF F A) γ (to_frac_agree dq a)

/-! ## Instances -/

-- Timeless instance omitted: requires `ownM_timeless` infrastructure.
-- Fractional / AsFractional instances omitted: not yet ported.

/-- `ghost_var` with discarded fraction is persistent.

    Coq: `ghost_var_persistent` (via `dfrac_agree`) -/
instance ghost_var_persistent (γ : GName) (a : A) :
    Persistent (ghost_var (GF := GF) (F := F) γ .discard a) := by
  sorry

/-! ## Allocation -/

/-- Allocate a fresh ghost variable with full ownership.

    Coq: `ghost_var_alloc` -/
theorem ghost_var_alloc (a : A) :
    ⊢ BUpd.bupd (BIBase.«exists» fun γ =>
      ghost_var (GF := GF) (F := F) γ (DFrac.own 1) a) := by
  sorry

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
  sorry

/-- Two ghost variables at the same name agree on value.

    Coq: `ghost_var_agree` -/
theorem ghost_var_agree (γ : GName) (dq1 dq2 : DFrac F)
    (a1 a2 : A) :
    BIBase.sep
      (ghost_var (GF := GF) γ dq1 a1)
      (ghost_var (GF := GF) γ dq2 a2)
      ⊢ BIBase.pure (a1 = a2) := by
  sorry

/-! ## Updates -/

/-- Update a ghost variable with full ownership.

    Coq: `ghost_var_update` -/
theorem ghost_var_update (γ : GName) (a b : A) :
    ghost_var (GF := GF) (F := F) γ (DFrac.own 1) a
      ⊢ BUpd.bupd (ghost_var (GF := GF) (F := F) γ (DFrac.own 1) b) := by
  sorry

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
  sorry

/-! ## Persistence -/

/-- Make a ghost variable read-only (persistent).

    Coq: `ghost_var_persist` (via `dfrac_agree_persist`) -/
theorem ghost_var_persist (γ : GName) (dq : DFrac F) (a : A) :
    ghost_var (GF := GF) γ dq a
      ⊢ BUpd.bupd (ghost_var (GF := GF) (F := F) γ .discard a) := by
  sorry

end Iris.BaseLogic

/-
Copyright (c) 2026 Sam Hart. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sam Hart
-/
import Iris.Instances.IProp.Instance
import Iris.Algebra.Auth

/-! # Authoritative Ghost Ownership

Reference: `iris/base_logic/lib/own.v` (auth-specific composition lemmas)

BI-level theorems for the authoritative resource algebra (`Auth F A`),
lifting CMRA validity and update results into `iOwn`-based separation
logic propositions.

## Main Definitions

- `AuthOwnF` — constant functor for auth ghost state
- `auth_own_auth`, `auth_own_frag` — ghost ownership of auth/frag

## Main Results

- `auth_own_frag_included` — auth + frag entails fragment inclusion
- `auth_own_update` — local update lifts to BI-level bupd
- `auth_own_alloc` — allocate auth + frag from local update on unit
- `auth_own_update_alloc` — auth-only update that allocates a fragment
- `auth_own_update_dealloc` — auth+frag update that deallocates the frag

## Simplifications

`Fractional` / `AsFractional` / `Timeless` instances are omitted.
-/

namespace Iris.BaseLogic

open Iris Iris.Algebra Iris.Std Iris.BI COFE

variable {GF : BundledGFunctors} {F : Type _} [UFraction F]
variable {A : Type _} [UCMRA A]

/-! ## Carrier and Functor -/

/-- Constant functor for authoritative ghost state.

    Coq: `authR` / `authUR` in ghost state context -/
abbrev AuthOwnF (F : Type _) (A : Type _)
    [UFraction F] [UCMRA A] : OFunctorPre :=
  COFE.constOF (Auth F A)

variable [ElemG GF (AuthOwnF F A)]

/-! ## Ownership Definitions -/

/-- Authoritative ghost ownership: `auth_own_auth γ dq a` asserts
    ownership of the authoritative element `●{dq} a`.

    Coq: `own γ (●{dq} a)` -/
noncomputable def auth_own_auth
    (γ : GName) (dq : DFrac F) (a : A) : IProp GF :=
  iOwn (GF := GF) (F := AuthOwnF F A) γ (Auth.auth dq a)

/-- Fragment ghost ownership: `auth_own_frag γ b` asserts
    ownership of the fragment element `◯ b`.

    Coq: `own γ (◯ b)` -/
noncomputable def auth_own_frag
    (γ : GName) (b : A) : IProp GF :=
  iOwn (GF := GF) (F := AuthOwnF F A) γ (Auth.frag b)

/-! ## Validity and Inclusion -/

/-- Two auth+frag at the same name: the combined element is valid.

    Coq: `own_valid_2` specialized to auth -/
theorem auth_own_auth_frag_valid (γ : GName) (dq : DFrac F)
    (a b : A) :
    BIBase.sep
      (auth_own_auth (GF := GF) γ dq a)
      (auth_own_frag (GF := GF) (F := F) γ b)
      ⊢ UPred.cmraValid (Auth.auth dq a • Auth.frag b) := by
  simp only [auth_own_auth, auth_own_frag]
  exact iOwn_cmraValid_op (GF := GF) (F := AuthOwnF F A) (γ := γ)

/-- Auth + frag entails fragment inclusion and auth validity (discrete).

    For discrete `A`, `own γ (● a) ∗ own γ (◯ b) ⊢ ⌜b ≼ a ∧ ✓ a⌝`.

    Coq: `auth_both_valid_discrete` + `own_valid_2` -/
theorem auth_own_frag_included [OFE.Discrete A] [CMRA.Discrete A]
    (γ : GName) (a b : A) :
    BIBase.sep
      (auth_own_auth (GF := GF) (F := F) γ (DFrac.own 1) a)
      (auth_own_frag (GF := GF) (F := F) γ b)
      ⊢ BIBase.pure (b ≼ a ∧ CMRA.Valid a) := by
  simp only [auth_own_auth, auth_own_frag]
  refine (iOwn_cmraValid_op (GF := GF)
    (F := AuthOwnF F A) (γ := γ)).trans ?_
  refine (UPred.cmraValid_elim _).trans ?_
  exact BI.pure_mono fun h =>
    Auth.auth_both_valid_discrete.mp (CMRA.discrete_valid h)

/-- Dfrac variant: auth + frag entails valid fraction, inclusion, and
    auth validity.

    Coq: `auth_both_dfrac_valid_discrete` + `own_valid_2` -/
theorem auth_own_dfrac_frag_included [OFE.Discrete A] [CMRA.Discrete A]
    (γ : GName) (dq : DFrac F) (a b : A) :
    BIBase.sep
      (auth_own_auth (GF := GF) γ dq a)
      (auth_own_frag (GF := GF) (F := F) γ b)
      ⊢ BIBase.pure (DFrac.valid dq ∧ b ≼ a ∧ CMRA.Valid a) := by
  simp only [auth_own_auth, auth_own_frag]
  refine (iOwn_cmraValid_op (GF := GF)
    (F := AuthOwnF F A) (γ := γ)).trans ?_
  refine (UPred.cmraValid_elim _).trans ?_
  exact BI.pure_mono fun h =>
    Auth.both_dfrac_valid_discrete.mp (CMRA.discrete_valid h)

/-! ## Updates -/

/-- Local update lifts to BI-level bupd.

    Given `(a, b) ~l~> (a', b')`:
    `own γ (● a) ∗ own γ (◯ b) ⊢ |==> own γ (● a') ∗ own γ (◯ b')`

    Coq: `auth_update` + `own_update_2` -/
theorem auth_own_update (γ : GName) {a b a' b' : A}
    (Hupd : (a, b) ~l~> (a', b')) :
    BIBase.sep
      (auth_own_auth (GF := GF) (F := F) γ (DFrac.own 1) a)
      (auth_own_frag (GF := GF) (F := F) γ b)
      ⊢ BUpd.bupd (BIBase.sep
          (auth_own_auth (GF := GF) (F := F) γ (DFrac.own 1) a')
          (auth_own_frag (GF := GF) (F := F) γ b')) := by
  simp only [auth_own_auth, auth_own_frag]
  refine (iOwn_op (GF := GF) (F := AuthOwnF F A) (γ := γ)).mpr.trans ?_
  refine (iOwn_update (GF := GF) (F := AuthOwnF F A) (γ := γ)
    (Auth.auth_update Hupd)).trans ?_
  exact BIUpdate.mono
    (iOwn_op (GF := GF) (F := AuthOwnF F A) (γ := γ)).mp

/-- Allocate auth + frag from a local update on unit.

    Given `(a, ε) ~l~> (a', b')`:
    `own γ (● a) ⊢ |==> own γ (● a') ∗ own γ (◯ b')`

    Coq: `auth_update_alloc` + `own_update` -/
theorem auth_own_update_alloc (γ : GName) {a a' b' : A}
    (Hupd : (a, UCMRA.unit) ~l~> (a', b')) :
    auth_own_auth (GF := GF) (F := F) γ (DFrac.own 1) a
      ⊢ BUpd.bupd (BIBase.sep
          (auth_own_auth (GF := GF) (F := F) γ (DFrac.own 1) a')
          (auth_own_frag (GF := GF) (F := F) γ b')) := by
  simp only [auth_own_auth, auth_own_frag]
  refine (iOwn_update (GF := GF) (F := AuthOwnF F A) (γ := γ)
    (Auth.auth_update_alloc Hupd)).trans ?_
  exact BIUpdate.mono
    (iOwn_op (GF := GF) (F := AuthOwnF F A) (γ := γ)).mp

/-- Update auth + frag, deallocating the fragment.

    Given `(a, b) ~l~> (a', ε)`:
    `own γ (● a) ∗ own γ (◯ b) ⊢ |==> own γ (● a')`

    Coq: `auth_update_dealloc` + `own_update_2` -/
theorem auth_own_update_dealloc (γ : GName) {a b a' : A}
    (Hupd : (a, b) ~l~> (a', UCMRA.unit)) :
    BIBase.sep
      (auth_own_auth (GF := GF) (F := F) γ (DFrac.own 1) a)
      (auth_own_frag (GF := GF) (F := F) γ b)
      ⊢ BUpd.bupd
          (auth_own_auth (GF := GF) (F := F) γ (DFrac.own 1) a') := by
  simp only [auth_own_auth, auth_own_frag]
  refine (iOwn_op (GF := GF) (F := AuthOwnF F A) (γ := γ)).mpr.trans ?_
  exact iOwn_update (GF := GF) (F := AuthOwnF F A) (γ := γ)
    (Auth.auth_update_dealloc Hupd)

/-! ## Allocation -/

/-- Allocate a fresh auth ghost name with full authority and a fragment.

    Coq: `own_alloc` with `auth_both_valid` -/
theorem auth_own_alloc (a : A) (Ha : CMRA.Valid a) :
    ⊢ BUpd.bupd (BIBase.«exists» fun γ =>
      BIBase.sep
        (auth_own_auth (GF := GF) (F := F) γ (DFrac.own 1) a)
        (auth_own_frag (GF := GF) (F := F) γ a)) := by
  simp only [auth_own_auth, auth_own_frag]
  have hv : CMRA.Valid ((Auth.authFull a : Auth F A) • Auth.frag a) :=
    Auth.auth_both_valid_2 Ha (CMRA.inc_refl a)
  refine (iOwn_alloc (GF := GF) (F := AuthOwnF F A) _ hv).trans ?_
  exact BIUpdate.mono (BI.exists_elim fun γ =>
    BI.exists_intro' γ
      (iOwn_op (GF := GF) (F := AuthOwnF F A) (γ := γ)).mp)

/-! ## Persistence -/

/-- The auth fragment is persistent when the underlying element is
    a core identity.

    Coq: `own_core_persistent` specialized to frag -/
instance auth_own_frag_persistent (γ : GName) (b : A)
    [CMRA.CoreId b] :
    Persistent (auth_own_frag (GF := GF) (F := F) γ b) where
  persistent := by
    simp only [auth_own_frag]
    exact persistently_intro

end Iris.BaseLogic

/-
Copyright (c) 2026 Sam Hart. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sam Hart
-/
import Iris.Instances.UPred.Instance
import Iris.Algebra.Agree

/-! # Internal Equality for UPred

Reference: `iris/bi/internal_eq.v`, `iris/bi/algebra.v`

Internal equality in UPred is `UPred.eq`, which at step `n` asserts
`a ≡{n}≡ b` (step-indexed OFE equivalence). This is the Lean analog
of Coq's `a ≡ b` (internal equality as BI connective), which in the
UPred model unfolds to the same step-indexed equivalence.

This file provides bridge lemmas connecting `UPred.eq` to CMRA validity
(`UPred.cmraValid`), enabling extraction of internal equality from ghost
state ownership.

## Main Results

- `internal_eq_refl` — reflexivity of internal equality
- `internal_eq_persistent` — internal equality is persistent
- `cmraValid_agree_internal_eq` — agree CMRA validity entails internal eq
- `cmraValid_prod_fst`, `cmraValid_prod_snd` — product validity decomposition

## Simplifications

Only the lemmas required for `SavedProp.lean` agreement theorems are
ported. The full `internal_eq.v` (rewriting, symmetry, transitivity,
`f_equivI`, `discrete_eq`, later interaction, soundness) requires the
SBI infrastructure which is not yet ported.
-/

section UPredInternalEq

open Iris BI

namespace UPred

variable [UCMRA M]

/-! ## Basic Properties -/

/-- Internal equality is reflexive.

    Coq: `internal_eq_refl` -/
theorem internal_eq_refl [OFE O] (a : O) (P : UPred M) :
    P ⊢ UPred.eq a a :=
  fun _ _ _ _ => OFE.Dist.rfl

/-- Internal equality is persistent: it does not depend on the
    resource, so it is preserved by `persistently`.

    Coq: `internal_eq_persistent` -/
instance internal_eq_persistent [OFE O] (a b : O) :
    Persistent (UPred.eq a b : UPred M) where
  persistent := fun _ _ _ h => h

/-! ## Product Validity Decomposition -/

/-- Validity of a product entails validity of the first component.

    Coq: `prod_validI` (first projection) -/
theorem cmraValid_prod_fst [CMRA A] [CMRA B] (x : A × B) :
    (cmraValid x : UPred M) ⊢ cmraValid x.1 :=
  fun _ _ _ hv => hv.1

/-- Validity of a product entails validity of the second component.

    Coq: `prod_validI` (second projection) -/
theorem cmraValid_prod_snd [CMRA A] [CMRA B] (x : A × B) :
    (cmraValid x : UPred M) ⊢ cmraValid x.2 :=
  fun _ _ _ hv => hv.2

/-! ## CMRA Validity Bridge -/

/-- Validity of an agree-RA composition entails internal equality
    of the underlying values.

    At step `n`, `✓{n} (toAgree a • toAgree b)` gives `a ≡{n}≡ b`
    by `Agree.toAgree_op_validN_iff_dist`, which is exactly
    `(UPred.eq a b).holds n _`.

    Coq: `to_agree_op_validI` (forward direction) -/
theorem cmraValid_agree_internal_eq [OFE A] (a b : A) :
    (cmraValid (toAgree a • toAgree b) : UPred M) ⊢ UPred.eq a b :=
  fun _ _ _ hv => Agree.toAgree_op_validN_iff_dist.mp hv

end UPred

end UPredInternalEq

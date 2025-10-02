/-
Copyright (c) 2024. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: [Your names here]
-/

import Mathlib.LinearAlgebra.Matrix.SpecialLinearGroup
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic

/-!
# PSL(2,ℝ) - The Projective Special Linear Group

This file defines PSL(2,ℝ) as the quotient of SL(2,ℝ) by its center {±I}.

## Main definitions

* `PSL`: The projective special linear group PSL(n,R) = SL(n,R) / center(SL(n,R))
* `PSL2R`: Notation for PSL(2,ℝ)
* `moebiusAction`: The action of PSL(2,ℝ) on the upper half plane by Möbius transformations

## Implementation notes

We define PSL as a quotient group. The center of SL(2,ℝ) consists of {I, -I}.

## References

* Mathlib already has `SpecialLinearGroup` (SL) in
  `Mathlib.LinearAlgebra.Matrix.SpecialLinearGroup`
* Upper half plane is in `Mathlib.Analysis.Complex.UpperHalfPlane.Basic`

-/

open Matrix

variable (n : ℕ) (R : Type*) [CommRing R]

/-- The projective special linear group PSL(n,R) defined as the quotient
    SL(n,R) modulo its center. -/
def PSL := SpecialLinearGroup (Fin n) R ⧸ Subgroup.center (SpecialLinearGroup (Fin n) R)

/-- Notation for PSL(2,ℝ) -/
abbrev PSL2R := PSL 2 ℝ

namespace PSL2R

/-- The center of SL(2,ℝ) consists of scalar matrices ±I -/
lemma center_eq_scalar :
    ∃ (I : SpecialLinearGroup (Fin 2) ℝ),
    Subgroup.center (SpecialLinearGroup (Fin 2) ℝ) = Subgroup.zpowers I := by
  sorry

/-- PSL(2,ℝ) acts on the upper half plane by Möbius transformations.
    For a matrix [[a,b],[c,d]], the action is z ↦ (az+b)/(cz+d) -/
def moebiusAction : PSL2R → UpperHalfPlane → UpperHalfPlane := sorry

end PSL2R

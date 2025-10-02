/-
Copyright (c) 2024. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: [Your names here]
-/

import PSL2R.Basic
import PSL2R.UnitTangentBundle
import PSL2R.IsometryGroup

/-!
# Equivalences between T¹ℍ, PSL(2,ℝ), and Isom⁺(ℍ²)

This file will prove the main theorem: the three objects
- T¹ℍ (unit tangent bundle)
- PSL(2,ℝ) (projective special linear group)
- Isom⁺(ℍ²) (orientation-preserving isometry group)
are naturally equivalent.

## Main results (to be implemented)

* PSL(2,ℝ) ≅ Isom⁺(ℍ²) as topological groups
* T¹ℍ ≃ PSL(2,ℝ) as topological spaces
* The complete equivalence T¹ℍ ≅ PSL(2,ℝ) ≅ Isom⁺(ℍ²)

## Proof strategy

1. PSL(2,ℝ) → Isom⁺(ℍ²): via Möbius transformations
2. Isom⁺(ℍ²) → PSL(2,ℝ): every isometry comes from a unique PSL element
3. T¹ℍ → PSL(2,ℝ): map (z,v) to the unique element taking (i, ∂/∂x) to (z,v)

-/

namespace PSL2R

-- Future work: implement the equivalences

end PSL2R

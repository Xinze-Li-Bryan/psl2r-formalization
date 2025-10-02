/-
Copyright (c) 2024. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: [Your names here]
-/

import PSL2R.Basic
import PSL2R.UnitTangentBundle
import PSL2R.IsometryGroup
import PSL2R.Equivalences

/-!
# PSL(2,ℝ) and Hyperbolic Geometry

This project formalizes the equivalence between three important objects in hyperbolic geometry:
- The unit tangent bundle T¹ℍ of the hyperbolic plane
- The projective special linear group PSL(2,ℝ)
- The orientation-preserving isometry group Isom⁺(ℍ²)

## Main results

* `PSL2R.unitTangentBundleEquiv`: The unit tangent bundle is homeomorphic to PSL(2,ℝ)
* `PSL2R.isometryGroupEquiv`: PSL(2,ℝ) is isomorphic to the isometry group
* `PSL2R.mainEquivalence`: All three objects are naturally isomorphic

## References

* [Ratcliffe, Foundations of Hyperbolic Manifolds][ratcliffe2006]
* [Benedetti, Petronio, Lectures on Hyperbolic Geometry][benedetti1992]

-/

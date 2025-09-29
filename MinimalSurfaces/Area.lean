import MinimalSurfaces.Basic
import Mathlib.MeasureTheory.Measure.Hausdorff
import Mathlib.MeasureTheory.Constructions.BorelSpace.Basic

/-!
# Area Functional for Surfaces
定义曲面的面积泛函，使用2维Hausdorff测度。
-/

namespace MinimalSurfaces

open MeasureTheory MeasureTheory.Measure

variable {M : Type*} [ClosedRiemannian3Manifold M] [MeasurableSpace M] [BorelSpace M]

/-- 嵌入曲面的Hausdorff 2-测度（面积） -/
noncomputable def hausdorffArea (S : EmbeddedSurface M) : ℝ := 
  (hausdorffMeasure 2 : Measure M).real S.carrier

/-- 曲面面积的基本性质 -/
lemma area_nonneg (S : EmbeddedSurface M) : 0 ≤ hausdorffArea S := by
  sorry

/-- 空曲面面积为0 -/
lemma area_empty : 
  hausdorffArea (⟨∅, isClosed_empty, True.intro, True.intro⟩ : EmbeddedSurface M) = 0 := by
  sorry

end MinimalSurfaces

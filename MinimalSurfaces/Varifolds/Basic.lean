import Mathlib.MeasureTheory.Measure.Hausdorff
import Mathlib.Analysis.Distribution.SchwartzSpace
import MinimalSurfaces.Basic

/-!
# Varifolds (变分流形)

Varifolds是几何测度论中的核心概念，由Almgren引入。
k-varifold是Grassmann丛上的Radon测度。

## References
* Colding-De Lellis, Section 2
-/

namespace MinimalSurfaces

open MeasureTheory

/-- k维varifold在n维流形M中 -/
structure Varifold (k n : ℕ) (M : Type*) [MetricSpace M] [MeasurableSpace M] where
  /-- 底层测度 -/
  measure : Measure M
  /-- 测度是局部有限的 -/
  locally_finite : IsLocallyFiniteMeasure measure

/-- 整数倍varifold (integer rectifiable varifold) -/
structure IntegerVarifold (k n : ℕ) (M : Type*) [MetricSpace M] [MeasurableSpace M] where
  /-- 继承自Varifold -/
  toVarifold : Varifold k n M
  /-- 重数函数 -/
  multiplicity : M → ℕ
  
/-- varifold的质量(面积) -/
def mass {k n : ℕ} {M : Type*} [MetricSpace M] [MeasurableSpace M] 
  (V : Varifold k n M) : ℝ :=
  sorry

/-- varifold收敛的定义 -/
def convergesInVarifoldSense {k n : ℕ} {M : Type*} [MetricSpace M] [MeasurableSpace M]
  (Vₙ : ℕ → Varifold k n M) (V : Varifold k n M) : Prop :=
  sorry

end MinimalSurfaces

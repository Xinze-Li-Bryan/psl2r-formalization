import Mathlib.MeasureTheory.Measure.Hausdorff
import MinimalSurfaces.Basic

/-!
# Varifold 理论基础
-/

namespace MinimalSurfaces

open MeasureTheory
open MeasureTheory.Measure

/-- k维 varifold 在 n维流形 M 中 -/
structure Varifold (k n : ℕ) (M : Type*) [MetricSpace M] [MeasurableSpace M] where
  /-- 底层测度 -/
  measure : Measure M
  /-- 测度是局部有限的 -/
  locally_finite : IsLocallyFiniteMeasure measure

/-- 整数 varifold -/
structure IntegerVarifold (k n : ℕ) (M : Type*) [MetricSpace M] [MeasurableSpace M] extends
  Varifold k n M where
  /-- 重数函数是整数值的 -/
  integer_valued : True  -- 简化：需要精确定义

/-- Varifold的质量（总测度） -/
noncomputable def mass {k n : ℕ} {M : Type*} [MetricSpace M] [MeasurableSpace M]
  (V : Varifold k n M) : ENNReal :=
  V.measure Set.univ

/-- Varifold收敛性（弱收敛） -/
def convergesInVarifoldSense {k n : ℕ} {M : Type*} [MetricSpace M] [MeasurableSpace M]
  (Vₙ : ℕ → Varifold k n M) (V : Varifold k n M) : Prop :=
  sorry

/-- 将嵌入曲面转换为 varifold -/
noncomputable def EmbeddedSurface.toVarifold {M : Type*} [ClosedRiemannian3Manifold M]
  [MeasurableSpace M] [BorelSpace M] (S : EmbeddedSurface M) : Varifold 2 3 M :=
  ⟨hausdorffMeasure 2, sorry⟩  -- 使用2维Hausdorff测度，需要证明局部有限性

end MinimalSurfaces

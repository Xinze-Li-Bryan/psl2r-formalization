import MinimalSurfaces.Basic
import MinimalSurfaces.MinMax.Basic
import MinimalSurfaces.Varifolds.Basic

/-!
# Simon-Smith 存在性定理
-/

namespace MinimalSurfaces

open MeasureTheory

/-- Simon-Smith min-max 存在性定理 (Theorem 1.6) -/
theorem simon_smith {M : Type*} [ClosedRiemannian3Manifold M] [MeasurableSpace M]
  [BorelSpace M] (Λ : SaturatedSet M) :
  ∃ (seq : MinMaxSequence Λ) (S : EmbeddedSurface M) (V : IntegerVarifold 2 3 M),
    is_minimal S ∧
    area S = m0 Λ ∧
    -- min-max序列在varifold意义下收敛到V
    -- V由S及其重数组成（multiplicity allowed）
    convergesInVarifoldSense (fun n => (seq.surfaces n).toVarifold) V.toVarifold := by
  sorry

end MinimalSurfaces

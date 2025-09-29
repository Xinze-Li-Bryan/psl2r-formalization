import MinimalSurfaces.Basic
import MinimalSurfaces.Isotopy
import MinimalSurfaces.Varifolds.Basic
import Mathlib.MeasureTheory.Constructions.BorelSpace.Basic
import Mathlib.Topology.Basic
import Mathlib.Order.Filter.Basic
import Mathlib.Topology.Defs.Filter  -- 为了𝓝

/-!
# Min-Max Theory for Minimal Surfaces
-/

namespace MinimalSurfaces

variable {M : Type*} [ClosedRiemannian3Manifold M] [MeasurableSpace M] [BorelSpace M]

open Set Filter Topology

/-- 曲面族的最大切片面积 F({Σt}) (Equation 1) -/
noncomputable def maxSliceArea (family : GeneralizedFamilyOfSurfaces M) : ℝ :=
  ⨆ t ∈ Icc (0:ℝ) 1, area ⟨family.surface t, sorry, trivial, trivial⟩  -- 4个字段

/-- 饱和集合Λ (根据论文page 3) -/
structure SaturatedSet (M : Type*) [ClosedRiemannian3Manifold M] where
  families : Set (GeneralizedFamilyOfSurfaces M)
  closed_under_isotopy : ∀ (F : GeneralizedFamilyOfSurfaces M) (_ψ : Isotopy M),
    F ∈ families → True
  bounded_degeneracy : ∃ N : ℕ, ∀ F ∈ families, F.singular_points.ncard ≤ N

/-- Width m₀(Λ) (Equation 2) -/
noncomputable def m0 (Λ : SaturatedSet M) : ℝ :=
  ⨅ F ∈ Λ.families, maxSliceArea F

/-- 极小化序列 -/
def MinimizingSequence (Λ : SaturatedSet M)
  (seq : ℕ → GeneralizedFamilyOfSurfaces M) : Prop :=
  (∀ n, seq n ∈ Λ.families) ∧
  Filter.Tendsto (fun n => maxSliceArea (seq n)) Filter.atTop (𝓝 (m0 Λ))

/-- Min-max序列 -/
structure MinMaxSequence (Λ : SaturatedSet M) where
  surfaces : ℕ → EmbeddedSurface M
  parameters : ℕ → ℝ
  from_minimizing : ∃ (fam_seq : ℕ → GeneralizedFamilyOfSurfaces M),
    MinimizingSequence Λ fam_seq ∧
    ∀ n, surfaces n = ⟨(fam_seq n).surface (parameters n), sorry, trivial, trivial⟩  -- 4个字段
  area_converges : Filter.Tendsto (fun n => area (surfaces n)) Filter.atTop (𝓝 (m0 Λ))

/-- Simon-Smith定理 (Theorem 1.6) -/
theorem simon_smith (Λ : SaturatedSet M) :
  ∃ (seq : MinMaxSequence Λ) (S : EmbeddedSurface M),
    is_minimal S ∧
    area S = m0 Λ ∧
    ∃ (V : IntegerVarifold 2 3 M),
      convergesInVarifoldSense (fun n => sorry) V.toVarifold := by
  sorry

end MinimalSurfaces

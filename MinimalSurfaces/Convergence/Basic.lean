import MinimalSurfaces.MinMax.Basic

/-!
# Convergence Theory

定义各种收敛概念，特别是varifold意义下的收敛。

## References
* Colding-De Lellis, Section 5
-/

namespace MinimalSurfaces

variable {M : Type*} [ClosedRiemannian3Manifold M] [MeasurableSpace M]

/-- 曲面序列的varifold收敛 -/
def surfaceConvergesToVarifold 
  (Sₙ : ℕ → EmbeddedSurface M) 
  (V : Varifold 2 3 M) : Prop :=
  sorry

/-- 收敛的正则性 -/
theorem convergence_regularity 
  {Λ : SaturatedSet M}
  (seq : MinMaxSequence M Λ) 
  (V : IntegerVarifold 2 3 M)
  (h : convergesInVarifoldSense (fun n => sorry) V.toVarifold) :
  ∃ S : EmbeddedSurface M, is_minimal S :=
  sorry

end MinimalSurfaces

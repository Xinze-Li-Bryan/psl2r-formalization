import MinimalSurfaces.Basic
import Mathlib.Topology.ContinuousMap.Basic

/-!
# Isotopies and Diffeomorphisms

定义isotopy（同痕）和相关概念，这是min-max理论的核心。
根据论文Definition 1.1和1.2。
-/

namespace MinimalSurfaces

variable {M : Type*} [ClosedRiemannian3Manifold M]

/-- Isotopy: 从[0,1]×M到M的连续映射，每个时刻是微分同胚 -/
structure Isotopy (M : Type*) [ClosedRiemannian3Manifold M] where
  /-- 底层映射 -/
  toFun : ℝ × M → M  
  /-- 连续性 -/
  continuous : Continuous toFun
  /-- 在t=0时是恒等映射 -/
  identity_at_zero : ∀ x : M, toFun (0, x) = x
  /-- 每个t时刻是微分同胚（简化） -/
  is_diffeo_at_t : ∀ t ∈ Set.Icc (0:ℝ) 1, True  -- 需要更精确的定义
  
/-- 支撑在U上的isotopy -/
def Isotopy.supportedIn (ψ : Isotopy M) (U : Set M) : Prop :=
  ∀ t x, x ∉ U → ψ.toFun (t, x) = x

/-- 广义曲面族（根据论文Definition 1.2） -/
structure GeneralizedFamilyOfSurfaces (M : Type*) [ClosedRiemannian3Manifold M] where
  /-- 参数t对应的曲面 -/
  surface : ℝ → Set M
  /-- 退化点集合T ⊂ [0,1] -/
  degenerate_times : Set ℝ
  /-- 奇异点集合P ⊂ M -/
  singular_points : Set M
  /-- T是有限集 -/
  finite_degenerate : Set.Finite degenerate_times
  /-- P是有限集 -/
  finite_singular : Set.Finite singular_points
  /-- 面积连续性（简化） -/
  area_continuous : True

end MinimalSurfaces

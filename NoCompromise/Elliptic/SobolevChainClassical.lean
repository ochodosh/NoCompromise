import NoCompromise.Sobolev.H1Mollification
import Mathlib.Analysis.Calculus.UniformLimitsDeriv

/-!
# Identifying continuous weak gradients with classical derivatives

Locally uniform approximation by normalized smooth bumps and the elementary
uniform-limit derivative theorem identify a continuous weak gradient pointwise.
-/

noncomputable section

open MeasureTheory Filter Metric Set InnerProductSpace
open scoped NNReal ENNReal Topology Gradient Convolution

namespace LiquidDrop

/-- Bump convolution converges locally uniformly to any continuous Banach-valued function. -/
theorem sobolevChain_tendstoLocallyUniformly_bump_convolution {n : ℕ} {F : Type*}
    [NormedAddCommGroup F] [NormedSpace ℝ F] [CompleteSpace F]
    {g : EuclideanSpace ℝ (Fin n) → F} (hg : Continuous g)
    {ι : Type*} {l : Filter ι} {φ : ι → ContDiffBump (0 : EuclideanSpace ℝ (Fin n))}
    (hφ : Tendsto (fun j => (φ j).rOut) l (𝓝 0)) :
    TendstoLocallyUniformly
      (fun j => (φ j).normed volume ⋆[ContinuousLinearMap.lsmul ℝ ℝ] g) g l := by
  apply tendstoLocallyUniformly_iff_filter.mpr
  intro x
  have hconv : Tendsto (fun p : ι × EuclideanSpace ℝ (Fin n) =>
      ((φ p.1).normed volume ⋆[ContinuousLinearMap.lsmul ℝ ℝ] g) p.2)
      (l ×ˢ 𝓝 x) (𝓝 (g x)) :=
    ContDiffBump.convolution_tendsto_right (hφ.comp tendsto_fst)
      (Eventually.of_forall fun _ => hg.aestronglyMeasurable)
      ((hg.tendsto x).comp tendsto_snd) tendsto_snd
  exact (((hg.tendsto x).comp tendsto_snd).prodMk_nhds hconv).mono_right (nhds_le_uniformity _)

/-- A continuous weak gradient is the classical derivative of a continuous representative. -/
theorem HasWeakGradientOn.hasFDerivAt_of_continuous {n : ℕ}
    {u : EuclideanSpace ℝ (Fin n) → ℝ}
    {G : EuclideanSpace ℝ (Fin n) → EuclideanSpace ℝ (Fin n)}
    (h : HasWeakGradientOn u G univ) (hu : Continuous u) (hG : Continuous G)
    (x : EuclideanSpace ℝ (Fin n)) : HasFDerivAt u (toDual ℝ _ (G x)) x := by
  let φ (j : ℕ) : ContDiffBump (0 : EuclideanSpace ℝ (Fin n)) :=
    ⟨(1 / ((j : ℝ) + 1)) / 2, 1 / ((j : ℝ) + 1), by positivity,
      half_lt_self (by positivity)⟩
  have hφ : Tendsto (fun j => (φ j).rOut) atTop (𝓝 0) :=
    tendsto_one_div_add_atTop_nhds_zero_nat (𝕜 := ℝ)
  let v (j : ℕ) := (φ j).normed volume ⋆[ContinuousLinearMap.lsmul ℝ ℝ] u
  have hv (j) : ContDiff ℝ (⊤ : ℕ∞) (v j) :=
    (φ j).hasCompactSupport_normed.contDiff_convolution_left _ (φ j).contDiff_normed
      (locallyIntegrableOn_univ.mp h.locallyIntegrable_function)
  have hgrad (j) : gradient (v j) =
      (φ j).normed volume ⋆[ContinuousLinearMap.lsmul ℝ ℝ] G :=
    funext (h.gradient_convolution (φ j).contDiff_normed
      (φ j).hasCompactSupport_normed)
  have hder (j) : fderiv ℝ (v j) = fun y => toDual ℝ _
      (((φ j).normed volume ⋆[ContinuousLinearMap.lsmul ℝ ℝ] G) y) := by
    funext y
    rw [← toDual_gradient, hgrad]
  have hconv := sobolevChain_tendstoLocallyUniformly_bump_convolution hG hφ
  have ht : TendstoLocallyUniformly (fun j => fderiv ℝ (v j)) (fun y => toDual ℝ _ (G y))
      atTop := by
    simpa only [Function.comp_def, hder] using
      (toDual ℝ (EuclideanSpace ℝ (Fin n))).isometry.uniformContinuous
        |>.comp_tendstoLocallyUniformly hconv
  apply hasFDerivAt_of_tendstoLocallyUniformlyOn isOpen_univ ht.tendstoLocallyUniformlyOn
    (fun j y _ => ((hv j).differentiable (by simp) y).hasFDerivAt)
    (fun y _ => ContDiffBump.convolution_tendsto_right_of_continuous hφ hu y) (mem_univ x)

/-- The C¹ conclusion retains the exact continuous weak gradient. -/
theorem HasWeakGradientOn.contDiff_one_of_continuous {n : ℕ}
    {u : EuclideanSpace ℝ (Fin n) → ℝ}
    {G : EuclideanSpace ℝ (Fin n) → EuclideanSpace ℝ (Fin n)}
    (h : HasWeakGradientOn u G univ) (hu : Continuous u) (hG : Continuous G) :
    ContDiff ℝ 1 u ∧ gradient u = G := by
  have hd := h.hasFDerivAt_of_continuous hu hG
  refine ⟨contDiff_one_iff_hasFDerivAt.mpr ⟨fun x => toDual ℝ _ (G x),
    (toDual ℝ _).continuous.comp hG, hd⟩, ?_⟩
  funext x
  apply (toDual ℝ _).injective
  rw [toDual_gradient, (hd x).fderiv]

end LiquidDrop

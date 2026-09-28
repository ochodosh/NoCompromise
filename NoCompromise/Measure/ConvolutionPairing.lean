import NoCompromise.BV.StrictApprox
import Mathlib.MeasureTheory.Function.LpSpace.ContinuousFunctions

/-!
# Pairing measure convolutions with bounded continuous fields

Fubini transfers a compact even convolution kernel from an integrable vector
density to the test field. Normalized bump convolutions then converge against
bounded continuous fields by dominated convergence.
-/

noncomputable section
open MeasureTheory Set Filter Metric
open scoped Topology ENNReal Gradient Convolution
namespace LiquidDrop

lemma integral_inner_measure_convolution
    (μ : Measure AmbientSpace) [SFinite μ]
    {g : AmbientSpace → AmbientSpace} (hg : Integrable g μ)
    {k : AmbientSpace → ℝ} (hk : Integrable k) (hkc : Continuous k)
    (hke : ∀ z, k (-z) = k z) (X : BoundedContinuousFunction AmbientSpace AmbientSpace) :
    (∫ x, inner ℝ (X x) (∫ y, k (x - y) • g y ∂μ)) =
      ∫ y, inner ℝ ((k ⋆[ContinuousLinearMap.lsmul ℝ ℝ] X) y) (g y) ∂μ := by
  have hp := integrable_measure_convolution_integrand measurable_id hk hkc hg
  have hs : Integrable (fun p : AmbientSpace × AmbientSpace =>
      inner ℝ (X p.1) (k (p.1 - p.2) • g p.2)) (volume.prod μ) := by
    apply (hp.norm.const_mul ‖X‖).mono'
      (continuous_inner.comp_aestronglyMeasurable
        ((X.continuous.comp continuous_fst).aestronglyMeasurable.prodMk hp.aestronglyMeasurable))
    filter_upwards [] with p
    exact (norm_inner_le_norm _ _).trans (mul_le_mul_of_nonneg_right
      (X.norm_coe_le_norm p.1) (norm_nonneg _))
  calc
    _ = ∫ x, ∫ y, inner ℝ (X x) (k (x - y) • g y) ∂μ := by
      apply integral_congr_ae
      filter_upwards [hp.prod_right_ae] with x hx
      exact ((innerSL ℝ (X x)).integral_comp_comm hx).symm
    _ = ∫ y, (∫ x, inner ℝ (X x) (k (x - y) • g y)) ∂μ := integral_integral_swap hs
    _ = _ := by
      apply integral_congr_ae
      filter_upwards [] with y
      have hi : Integrable (fun x => k (x - y) • X x) :=
        (hk.comp_sub_right y).smul_of_top_left X.memLp_top
      have heq : (fun x => inner ℝ (X x) (k (x - y) • g y)) =
          (fun x => inner ℝ (g y) (k (x - y) • X x)) := by
        funext x
        simp only [inner_smul_right, real_inner_comm]
      have hlin : (∫ x, inner ℝ (g y) (k (x - y) • X x)) =
          inner ℝ (g y) (∫ x, k (x - y) • X x) := by
        exact (innerSL ℝ (g y)).integral_comp_comm hi
      rw [heq, hlin, real_inner_comm]
      congr 1
      rw [convolution_eq_swap]
      apply integral_congr_ae
      filter_upwards [] with x
      rw [show k (x - y) = k (y - x) from by rw [← hke (x - y), neg_sub]]
      rfl

/-- A normalized nonnegative bump preserves the uniform bound of a vector field. -/
lemma norm_bump_convolution_le (φ : ContDiffBump (0 : AmbientSpace))
    (X : BoundedContinuousFunction AmbientSpace AmbientSpace) (x : AmbientSpace) :
    ‖(φ.normed volume ⋆[ContinuousLinearMap.lsmul ℝ ℝ] X) x‖ ≤ ‖X‖ := by
  simpa only [dist_zero_right] using dist_convolution_le (μ := volume) (g := fun y => X y)
    (x₀ := x) (z₀ := (0 : AmbientSpace)) (norm_nonneg X)
    φ.support_normed_eq.subset φ.nonneg_normed φ.integral_normed
    X.continuous.aestronglyMeasurable
    (fun y _ => by simpa only [dist_zero_right] using X.norm_coe_le_norm y)

/-- Integrable vector densities converge against every bounded continuous field
under convolution by bumps shrinking to zero. -/
theorem tendsto_integral_inner_measure_convolution
    (μ : Measure AmbientSpace) [SFinite μ]
    {g : AmbientSpace → AmbientSpace} (hg : Integrable g μ)
    {φ : ℕ → ContDiffBump (0 : AmbientSpace)}
    (hφ : Tendsto (fun j => (φ j).rOut) atTop (𝓝 0))
    (X : BoundedContinuousFunction AmbientSpace AmbientSpace) :
    Tendsto (fun j => ∫ x, inner ℝ (X x)
      (∫ y, (φ j).normed volume (x - y) • g y ∂μ)) atTop
      (𝓝 (∫ y, inner ℝ (X y) (g y) ∂μ)) := by
  have heq (j : ℕ) := integral_inner_measure_convolution μ hg
    (φ j).integrable_normed (φ j).continuous_normed (φ j).normed_neg X
  simp_rw [heq]
  apply tendsto_integral_of_dominated_convergence (fun y => ‖X‖ * ‖g y‖)
  · intro j
    have hc := ((φ j).hasCompactSupport_normed (μ := volume)).continuous_convolution_left
      (μ := volume)
      (ContinuousLinearMap.lsmul ℝ ℝ) (φ j).continuous_normed X.continuous.locallyIntegrable
    exact continuous_inner.comp_aestronglyMeasurable
      (hc.aestronglyMeasurable.prodMk hg.aestronglyMeasurable)
  · exact hg.norm.const_mul ‖X‖
  · intro j
    filter_upwards [] with y
    exact (norm_inner_le_norm _ _).trans (mul_le_mul_of_nonneg_right
      (norm_bump_convolution_le (φ j) X y) (norm_nonneg _))
  · filter_upwards [] with y
    exact (ContDiffBump.convolution_tendsto_right_of_continuous
      (μ := volume) hφ X.continuous y).inner
      tendsto_const_nhds

/-- Local integrability suffices when the testing vector field has compact
support. A fixed compact neighborhood absorbs every sufficiently small kernel. -/
theorem LocallyIntegrable.tendsto_integral_inner_measure_convolution
    {μ : Measure AmbientSpace} [SFinite μ]
    {g : AmbientSpace → AmbientSpace} (hg : LocallyIntegrable g μ)
    {φ : ℕ → ContDiffBump (0 : AmbientSpace)}
    (hφ : Tendsto (fun j => (φ j).rOut) atTop (𝓝 0))
    (X : CompactlySupportedContinuousMap AmbientSpace AmbientSpace) :
    Tendsto (fun j => ∫ x, inner ℝ (X x)
      (∫ y, (φ j).normed volume (x - y) • g y ∂μ)) atTop
      (𝓝 (∫ y, inner ℝ (X y) (g y) ∂μ)) := by
  obtain ⟨R, hR, hXR⟩ := X.hasCompactSupport.isBounded.subset_ball_lt 0 (0 : AmbientSpace)
  let K := closedBall (0 : AmbientSpace) (R + 1)
  have hXK : tsupport X ⊆ K := hXR.trans (ball_subset_closedBall.trans
    (closedBall_subset_closedBall (by linarith)))
  have hgi : Integrable g (μ.restrict K) := hg.integrableOn_isCompact (isCompact_closedBall _ _)
  have hlim := LiquidDrop.tendsto_integral_inner_measure_convolution (μ.restrict K)
    hgi hφ X.toBoundedContinuousFunction
  have hright : (∫ y in K, inner ℝ (X y) (g y) ∂μ) =
      ∫ y, inner ℝ (X y) (g y) ∂μ := by
    apply setIntegral_eq_integral_of_forall_compl_eq_zero
    intro y hy
    rw [image_eq_zero_of_notMem_tsupport (fun hy' => hy (hXK hy')), inner_zero_left]
  change Tendsto (fun j => ∫ x, inner ℝ (X x)
    (∫ y in K, (φ j).normed volume (x - y) • g y ∂μ)) atTop
    (𝓝 (∫ y in K, inner ℝ (X y) (g y) ∂μ)) at hlim
  rw [hright] at hlim
  apply hlim.congr'
  filter_upwards [hφ.eventually (gt_mem_nhds (show (0 : ℝ) < 1 by norm_num))] with j hj
  apply integral_congr_ae
  filter_upwards [] with x
  by_cases hx : X x = 0
  · simp only [hx, inner_zero_left]
  · have hxR : ‖x‖ < R := by
      simpa only [mem_ball, dist_zero_right] using hXR (subset_tsupport X hx)
    congr 1
    apply setIntegral_eq_integral_of_forall_compl_eq_zero
    intro y hy
    have hyR : R + 1 < ‖y‖ := by
      simpa only [K, mem_closedBall, dist_zero_right, not_le] using hy
    have hn : ‖y‖ ≤ ‖x‖ + ‖x - y‖ := by
      simpa only [sub_sub_cancel] using norm_sub_le x (x - y)
    have hz : (φ j).normed volume (x - y) = 0 := by
      apply Function.notMem_support.mp
      rw [(φ j).support_normed_eq]
      simp only [mem_ball, dist_zero_right, not_lt]
      linarith
    rw [hz, zero_smul]

end LiquidDrop

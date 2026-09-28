import NoCompromise.Regularity.TangentScaling
import NoCompromise.BV.Density

/-!
# Exact dilation covariance of the density-one representative

This is a direct calculation with volume ratios. Consequently any invariance
modulo null sets under positive dilations becomes actual set invariance for the
canonical density-one representative.
-/

noncomputable section
open MeasureTheory Set Filter Metric
open scoped Topology ENNReal Pointwise
namespace LiquidDrop
set_option maxSynthPendingDepth 8

lemma tangent_densityRatio_pos_smul (F : Set AmbientSpace) (x : AmbientSpace)
    {r : ℝ} (hr : 0 < r) (s : ℝ) :
    densityRatio ((fun y => r • y) '' F) (r • x) (r * s) = densityRatio F x s := by
  have hinj : Function.Injective (fun y : AmbientSpace => r • y) :=
    (Homeomorph.smulOfNeZero r hr.ne').injective
  have hb : (fun y : AmbientSpace => r • y) '' ball x s = ball (r • x) (r * s) := by
    simpa only [Real.norm_eq_abs, abs_of_pos hr] using Metric.smul_image_ball hr.ne' x s
  rw [densityRatio, ← hb, ← image_inter hinj,
    volume_image_pos_smul _ hr, volume_image_pos_smul _ hr]
  simp only [ENNReal.toReal_mul, ENNReal.toReal_ofReal (pow_nonneg hr.le 3)]
  dsimp [densityRatio]
  field_simp [hr.ne']

lemma tangent_pos_mul_tendsto_zero {r : ℝ} (hr : 0 < r) :
    Tendsto (fun s : ℝ => r * s) (𝓝[>] (0 : ℝ)) (𝓝[>] (0 : ℝ)) := by
  apply tendsto_nhdsWithin_iff.mpr
  refine ⟨?_, ?_⟩
  · have hid : Tendsto (fun s : ℝ => s) (𝓝[>] (0 : ℝ)) (𝓝 0) :=
      tendsto_id.mono_left nhdsWithin_le_nhds
    simpa only [mul_zero] using hid.const_mul r
  · filter_upwards [self_mem_nhdsWithin] with s hs
    exact mul_pos hr hs

lemma tangent_mem_densityOne_pos_smul_iff (F : Set AmbientSpace) (x : AmbientSpace)
    {r : ℝ} (hr : 0 < r) :
    r • x ∈ densityOne ((fun y => r • y) '' F) ↔ x ∈ densityOne F := by
  change Tendsto (densityRatio ((fun y => r • y) '' F) (r • x)) (𝓝[>] (0 : ℝ)) (𝓝 1) ↔
    Tendsto (densityRatio F x) (𝓝[>] (0 : ℝ)) (𝓝 1)
  constructor
  · intro h
    have ht := h.comp (tangent_pos_mul_tendsto_zero hr)
    simpa only [Function.comp_def, tangent_densityRatio_pos_smul F x hr] using ht
  · intro h
    have ht := h.comp (tangent_pos_mul_tendsto_zero (inv_pos.mpr hr))
    apply ht.congr'
    apply Eventually.of_forall
    intro s
    have he := tangent_densityRatio_pos_smul F x hr (r⁻¹ * s)
    rw [← mul_assoc, mul_inv_cancel₀ hr.ne', one_mul] at he
    exact he.symm

/-- Exact covariance, with no measurability hypothesis needed for the volume-ratio calculation. -/
theorem tangent_densityOne_pos_smul (F : Set AmbientSpace) {r : ℝ} (hr : 0 < r) :
    densityOne ((fun y => r • y) '' F) = (fun y => r • y) '' densityOne F := by
  ext y
  obtain ⟨x, rfl⟩ := (Homeomorph.smulOfNeZero r hr.ne').surjective y
  change r • x ∈ densityOne ((fun y => r • y) '' F) ↔
    r • x ∈ (fun y => r • y) '' densityOne F
  rw [tangent_mem_densityOne_pos_smul_iff F x hr]
  constructor
  · intro hx
    exact ⟨x, hx, rfl⟩
  · rintro ⟨y, hy, he⟩
    have hyx : y = x := (Homeomorph.smulOfNeZero r hr.ne').injective he
    rwa [← hyx]

/-- AE invariance of a measurable representative induces exact cone invariance
of its density-one representative. -/
theorem tangent_densityOne_invariant_of_ae {F : Set AmbientSpace} {r : ℝ} (hr : 0 < r)
    (h : ((fun y => r • y) '' F : Set AmbientSpace) =ᵐ[volume] F) :
    (fun y => r • y) '' densityOne F = densityOne F := by
  rw [← tangent_densityOne_pos_smul F hr]
  exact densityOne_congr_ae h

end LiquidDrop

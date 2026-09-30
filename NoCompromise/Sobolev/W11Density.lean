module

public import NoCompromise.Sobolev.W11Space
public import NoCompromise.Sobolev.W11Extension

@[expose] public section

/-!
# Smooth density in W¹,¹ on bounded Lipschitz domains

The constructed extension and ordinary convolution give actual globally smooth
representatives whose functions and gradients converge in L¹ on the domain.
Continuous weak-gradient pairs therefore have dense image in W¹,¹.
-/

noncomputable section
open MeasureTheory Set Filter
open scoped ENNReal NNReal Topology Gradient Convolution
namespace LiquidDrop
set_option maxSynthPendingDepth 8

theorem HasW11GradientOn.exists_smooth_approx_on_domain {n : ℕ}
    {D : Set (EuclideanSpace ℝ (Fin n))} (hD : IsOpen D)
    (hbD : Bornology.IsBounded D) (hL : HasLipschitzBoundary D)
    {f : EuclideanSpace ℝ (Fin n) → ℝ}
    {G : EuclideanSpace ℝ (Fin n) → EuclideanSpace ℝ (Fin n)} (hf : HasW11GradientOn f G D) :
    ∃ v : ℕ → EuclideanSpace ℝ (Fin n) → ℝ,
      (∀ j, ContDiff ℝ (⊤ : ℕ∞) (v j) ∧ HasW11GradientOn (v j) (gradient (v j)) univ) ∧
      Tendsto (fun j => ∫ x in D, ‖v j x - f x‖) atTop (𝓝 0) ∧
      Tendsto (fun j => ∫ x in D, ‖gradient (v j) x - G x‖) atTop (𝓝 0) := by
  obtain ⟨T, _, _, _, _, _, hT⟩ := exists_w11_extension_linearMap_preserving_continuity hD hbD hL
  obtain ⟨H, hH, heq, _, _⟩ := hT f G hf
  have hEq : T f =ᵐ[volume.restrict D] f :=
    ae_restrict_of_forall_mem hD.measurableSet heq
  have hGradEq : H =ᵐ[volume.restrict D] G := HasWeakGradientOn.unique hD
    (((hH.mono (subset_univ D)).toHasWeakGradientOn).congr_ae hEq EventuallyEq.rfl)
    hf.toHasWeakGradientOn
  let φ (j : ℕ) : ContDiffBump (0 : EuclideanSpace ℝ (Fin n)) :=
    ⟨(1 / ((j : ℝ) + 1)) / 2, 1 / ((j : ℝ) + 1), by positivity,
      half_lt_self (by positivity)⟩
  have hφ : Tendsto (fun j => (φ j).rOut) atTop (𝓝 0) :=
    tendsto_one_div_add_atTop_nhds_zero_nat (𝕜 := ℝ)
  let v (j : ℕ) := (φ j).normed volume ⋆[ContinuousLinearMap.lsmul ℝ ℝ] (T f)
  have hv (j) : HasW11GradientOn (v j) (gradient (v j)) univ := by
    have hj := hH.bump_convolution (φ j)
    exact hj.2.2.congr_ae EventuallyEq.rfl (Eventually.of_forall fun x => (hj.2.1 x).symm)
  have hif : Integrable (T f) := by
    simpa only [IntegrableOn, Measure.restrict_univ] using hH.integrable_function
  have hiG : Integrable H := by
    simpa only [IntegrableOn, Measure.restrict_univ] using hH.integrable_gradient
  have hconv := hH.tendsto_bump_convolution hφ
  refine ⟨v, fun j => ⟨(hH.bump_convolution (φ j)).1, hv j⟩, ?_, ?_⟩
  · apply tendsto_integral_norm_sub_restrict_of_ae_eq (fun j => ?_) hif hEq hconv.1
    simpa only [IntegrableOn, Measure.restrict_univ] using (hv j).integrable_function
  · apply tendsto_integral_norm_sub_restrict_of_ae_eq (fun j => ?_) hiG hGradEq hconv.2
    simpa only [IntegrableOn, Measure.restrict_univ] using (hv j).integrable_gradient

namespace W11Space

theorem exists_smooth_approx_on_domain {n : ℕ}
    {D : Set (EuclideanSpace ℝ (Fin n))} (hD : IsOpen D)
    (hbD : Bornology.IsBounded D) (hL : HasLipschitzBoundary D) (u : W11Space D) :
    ∃ v : ℕ → EuclideanSpace ℝ (Fin n) → ℝ,
    ∃ hv : ∀ j, HasW11GradientOn (v j) (gradient (v j)) D,
      (∀ j, ContDiff ℝ (⊤ : ℕ∞) (v j)) ∧
      Tendsto (fun j => ofFunction (v j) (gradient (v j)) (hv j)) atTop (𝓝 u) := by
  obtain ⟨v, hmeta, hcf, hcG⟩ := u.hasW11GradientOn.exists_smooth_approx_on_domain hD hbD hL
  let hv (j) := (hmeta j).2.mono (subset_univ D)
  refine ⟨v, hv, fun j => (hmeta j).1, ?_⟩
  have heq : ofFunction u u.gradientLp u.hasW11GradientOn = u :=
    ext_ae hD (coeFn_ofFunction _ _ _)
  rw [← heq, tendsto_iff_norm_sub_tendsto_zero]
  apply squeeze_zero (fun _ => norm_nonneg _) (fun j => ?_)
    (by simpa only [zero_add] using hcf.add hcG)
  have hb := norm_ofFunction_sub_le hD (hv j) u.hasW11GradientOn
  rw [lpNorm_one_eq_integral_norm ((hv j).memLp_function.sub
    u.hasW11GradientOn.memLp_function).aestronglyMeasurable,
    lpNorm_one_eq_integral_norm ((hv j).memLp_gradient.sub
      u.hasW11GradientOn.memLp_gradient).aestronglyMeasurable] at hb
  exact hb

end W11Space

/-- Actual continuous scalar functions paired with their actual W¹,¹ weak gradients. -/
def continuousW11Data {n : ℕ} (D : Set (EuclideanSpace ℝ (Fin n))) :
    Submodule ℝ ((EuclideanSpace ℝ (Fin n) → ℝ) ×
      (EuclideanSpace ℝ (Fin n) → EuclideanSpace ℝ (Fin n))) where
  carrier := {p | Continuous p.1 ∧ HasW11GradientOn p.1 p.2 D}
  zero_mem' := ⟨continuous_const, HasW11GradientOn.zero D⟩
  add_mem' hp hq := ⟨hp.1.add hq.1, hp.2.add hq.2⟩
  smul_mem' c _ hp := ⟨continuous_const.mul hp.1, hp.2.const_mul c⟩

/-- Continuous weak-gradient pairs map linearly to their W¹,¹ classes. -/
def continuousW11Data_toW11Space {n : ℕ} {D : Set (EuclideanSpace ℝ (Fin n))}
    (hD : IsOpen D) : continuousW11Data D →ₗ[ℝ] W11Space D where
  toFun p := W11Space.ofFunction p.val.1 p.val.2 p.property.2
  map_add' p q := by
    apply W11Space.ext_ae hD
    filter_upwards [W11Space.coeFn_ofFunction (p + q).val.1 (p + q).val.2 (p + q).property.2,
      W11Space.coeFn_add (W11Space.ofFunction p.val.1 p.val.2 p.property.2)
        (W11Space.ofFunction q.val.1 q.val.2 q.property.2),
      W11Space.coeFn_ofFunction p.val.1 p.val.2 p.property.2,
      W11Space.coeFn_ofFunction q.val.1 q.val.2 q.property.2] with x w11 h2 h3 h4
    rw [h3, h4] at h2
    exact w11.trans ((show (p + q).val.1 x = p.val.1 x + q.val.1 x from rfl).trans h2.symm)
  map_smul' c p := by
    apply W11Space.ext_ae hD
    filter_upwards [W11Space.coeFn_ofFunction (c • p).val.1 (c • p).val.2 (c • p).property.2,
      W11Space.coeFn_smul c (W11Space.ofFunction p.val.1 p.val.2 p.property.2),
      W11Space.coeFn_ofFunction p.val.1 p.val.2 p.property.2] with x w11 h2 h3
    rw [h3] at h2
    exact w11.trans ((show (c • p).val.1 x = c * p.val.1 x from rfl).trans h2.symm)

/-- Smooth approximation proves density of the continuous representatives. -/
theorem denseRange_continuousW11Data_toW11Space {n : ℕ}
    {D : Set (EuclideanSpace ℝ (Fin n))} (hD : IsOpen D)
    (hbD : Bornology.IsBounded D) (hL : HasLipschitzBoundary D) :
    DenseRange (continuousW11Data_toW11Space hD) := by
  intro u
  obtain ⟨v, hv, hc, hconv⟩ := W11Space.exists_smooth_approx_on_domain hD hbD hL u
  apply mem_closure_of_tendsto hconv
  exact Eventually.of_forall fun j =>
    ⟨⟨(v j, gradient (v j)), (hc j).continuous, hv j⟩, rfl⟩

lemma continuousW11Data_sum_lpNorm_le {n : ℕ}
    {D : Set (EuclideanSpace ℝ (Fin n))} (hD : IsOpen D) (p : continuousW11Data D) :
    lpNorm p.val.1 1 (volume.restrict D) + lpNorm p.val.2 1 (volume.restrict D) ≤
      2 * ‖continuousW11Data_toW11Space hD p‖ := by
  change _ ≤ 2 * ‖W11Space.ofFunction p.val.1 p.val.2 p.property.2‖
  have h := (W11Space.ofFunction p.val.1 p.val.2 p.property.2).sum_norm_le
  change ‖p.property.2.memLp_function.toLp p.val.1‖ +
    ‖p.property.2.memLp_gradient.toLp p.val.2‖ ≤ _ at h
  simpa only [Lp.norm_toLp, toReal_eLpNorm,
    toReal_eLpNorm] using h

end LiquidDrop

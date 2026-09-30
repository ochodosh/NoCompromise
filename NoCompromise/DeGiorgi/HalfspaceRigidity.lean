module

public import NoCompromise.DeGiorgi.PolarDifferentiation
public import NoCompromise.BV.StrictApprox
public import Mathlib.Analysis.Calculus.BumpFunction.Convolution
public import Mathlib.Analysis.Calculus.Deriv.MeanValue
public import Mathlib.MeasureTheory.Measure.Lebesgue.EqHaar

@[expose] public section

/-!
# Rigidity of a constant distributional normal

A constant outward polar direction forces every positive mollification of the
indicator to decrease with height in that direction. Almost-everywhere
convergence transfers this ordering to the indicator. Positive volume of both
phases in every ball at the origin places the separating plane at height zero.
-/

noncomputable section
open MeasureTheory Set Filter Metric InnerProductSpace
open scoped Topology ENNReal Gradient CompactlySupported Convolution
namespace LiquidDrop
set_option maxSynthPendingDepth 8

/-- The exact compact-test identity `D χ_E = -ν μ`, for a constant vector `ν`. -/
def HasConstantIndicatorPolar (E : Set AmbientSpace) (μ : Measure AmbientSpace)
    (ν : AmbientSpace) : Prop :=
  ∀ (i : Fin 3) (φ : CompactlySupportedContinuousMap AmbientSpace ℝ), ContDiff ℝ 1 φ →
    -(∫ x, E.indicator (fun _ => (1 : ℝ)) x *
      fderiv ℝ φ x (EuclideanSpace.single i 1)) = ∫ x, φ x * (-ν i) ∂μ

/-- A constant ambient outward polar field supplies the exact coordinate-test identity. -/
lemma IsAmbientOutwardPerimeterPolar.hasConstantIndicatorPolar
    {E : Set AmbientSpace} {μ : Measure AmbientSpace} {ν : AmbientSpace}
    (h : IsAmbientOutwardPerimeterPolar E μ (fun _ => ν)) :
    HasConstantIndicatorPolar E μ ν := h.coordinate_eq

/-- A nonnegative scalar multiple of a fixed negative gradient gives global height ordering. -/
lemma height_antitone_of_gradient {f : AmbientSpace → ℝ} {ν : AmbientSpace}
    (hf : Differentiable ℝ f) (hgrad : ∀ x, ∃ a : ℝ, 0 ≤ a ∧ gradient f x = -a • ν)
    {x y : AmbientSpace} (hxy : inner ℝ ν x ≤ inner ℝ ν y) : f y ≤ f x := by
  obtain ⟨z, _, hz⟩ := domain_mvt (s := (univ : Set AmbientSpace))
    (fun x _ => (hf x).hasFDerivAt.hasFDerivWithinAt) convex_univ (mem_univ x) (mem_univ y)
  obtain ⟨a, ha, hza⟩ := hgrad z
  rw [← inner_gradient_left, hza, inner_smul_left, inner_sub_right] at hz
  simp only [starRingEnd_apply, star_trivial] at hz
  have hnonpos : -a * (inner ℝ ν y - inner ℝ ν x) ≤ 0 :=
    mul_nonpos_of_nonpos_of_nonneg (neg_nonpos.mpr ha) (sub_nonneg.mpr hxy)
  linarith

/-- A genuine hyperplane has zero ambient volume. -/
lemma volume_inner_eq_zero_of_unit {ν : AmbientSpace} (hν : ‖ν‖ = 1) :
    volume {x : AmbientSpace | inner ℝ ν x = 0} = 0 := by
  let L : AmbientSpace →ₗ[ℝ] ℝ := (innerSL ℝ ν).toLinearMap
  have hL : LinearMap.ker L ≠ ⊤ := by
    intro htop
    have hm : ν ∈ LinearMap.ker L := by rw [htop]; trivial
    have hz : inner ℝ ν ν = 0 := hm
    rw [real_inner_self_eq_norm_sq, hν] at hz
    norm_num at hz
  exact Measure.addHaar_submodule volume (LinearMap.ker L) hL

/-- Almost-everywhere height ordering of an indicator and both-phase density at the origin
identify its unique separating halfspace. -/
theorem indicator_halfspace_of_height_order {E S : Set AmbientSpace} {ν : AmbientSpace}
    (hν : ‖ν‖ = 1) (hS : ∀ᵐ x : AmbientSpace, x ∈ S)
    (horder : ∀ x ∈ S, ∀ y ∈ S, inner ℝ ν x ≤ inner ℝ ν y →
      E.indicator (fun _ => (1 : ℝ)) y ≤ E.indicator (fun _ => (1 : ℝ)) x)
    (hphases : ∀ r : ℝ, 0 < r →
      0 < volume (E ∩ ball (0 : AmbientSpace) r) ∧
      0 < volume (ball (0 : AmbientSpace) r \ E)) :
    E =ᵐ[volume] {x : AmbientSpace | inner ℝ ν x < 0} := by
  have hplane : ∀ᵐ x : AmbientSpace, inner ℝ ν x ≠ 0 := by
    rw [ae_iff]
    simpa using volume_inner_eq_zero_of_unit hν
  filter_upwards [hS, hplane] with x hx hx0
  apply propext
  change x ∈ E ↔ inner ℝ ν x < 0
  have hnorm (y : AmbientSpace) : |inner ℝ ν y| ≤ ‖y‖ := by
    simpa only [hν, one_mul] using abs_real_inner_le_norm ν y
  rcases lt_or_gt_of_ne hx0 with hneg | hpos
  · have hp := (hphases (-inner ℝ ν x / 2) (by linarith)).1
    obtain ⟨y, hy, hyS⟩ := Measure.exists_mem_of_measure_ne_zero_of_ae hp.ne'
      (ae_restrict_of_ae hS)
    have hyball : ‖y‖ < -inner ℝ ν x / 2 := by
      simpa only [mem_ball, dist_zero_right] using hy.2
    have hxy : inner ℝ ν x ≤ inner ℝ ν y := by
      have := hnorm y
      have := neg_le_abs (inner ℝ ν y)
      linarith
    have ho := horder x hx y hyS hxy
    have hxE : x ∈ E := by
      by_contra hn
      simp only [indicator_of_mem hy.1, indicator_of_notMem hn] at ho
      norm_num at ho
    exact ⟨fun _ => hneg, fun _ => hxE⟩
  · have hp := (hphases (inner ℝ ν x / 2) (half_pos hpos)).2
    obtain ⟨y, hy, hyS⟩ := Measure.exists_mem_of_measure_ne_zero_of_ae hp.ne'
      (ae_restrict_of_ae hS)
    have hyball : ‖y‖ < inner ℝ ν x / 2 := by
      simpa only [mem_ball, dist_zero_right] using hy.1
    have hyx : inner ℝ ν y ≤ inner ℝ ν x := by
      have := hnorm y
      have := le_abs_self (inner ℝ ν y)
      linarith
    have ho := horder y hyS x hx hyx
    have hxE : x ∉ E := by
      intro hin
      simp only [indicator_of_mem hin, indicator_of_notMem hy.2] at ho
      norm_num at ho
    exact ⟨fun hin => (hxE hin).elim, fun hn => (not_lt_of_gt hpos hn).elim⟩

/-- The distributional coordinate identities differentiate any compact smooth convolution. -/
theorem HasConstantIndicatorPolar.gradient_convolution_eq
    {E : Set AmbientSpace} {μ : Measure AmbientSpace} {ν : AmbientSpace}
    (h : HasConstantIndicatorPolar E μ ν) (hE : NullMeasurableSet E volume)
    {k : AmbientSpace → ℝ} (hk : ContDiff ℝ 1 k) (hck : HasCompactSupport k)
    (x : AmbientSpace) :
    gradient (k ⋆[ContinuousLinearMap.lsmul ℝ ℝ] E.indicator (fun _ => (1 : ℝ))) x =
      -(∫ y, k (x - y) ∂μ) • ν := by
  let φ : CompactlySupportedContinuousMap AmbientSpace ℝ :=
    ⟨⟨fun y => k (x - y), hk.continuous.comp (continuous_const.sub continuous_id)⟩,
      hck.comp_homeomorph (Homeomorph.subLeft x)⟩
  have hφ : ContDiff ℝ 1 φ := hk.comp (contDiff_const.sub contDiff_id)
  have hf := locallyIntegrable_indicator_one hE
  have hcgrad : HasCompactSupport (gradient k) :=
    hck.of_isClosed_subset (isClosed_tsupport _) (tsupport_gradient_subset k)
  have hiG := hcgrad.convolutionExists_right (μ := volume) (ContinuousLinearMap.lsmul ℝ ℝ)
    hf (continuous_gradient_of_contDiff hk) x
  change Integrable (fun y => E.indicator (fun _ => (1 : ℝ)) y • gradient k (x - y)) at hiG
  rw [gradient_convolution_left hf hk hck x]
  apply PiLp.ext
  intro i
  rw [eval_integral_piLp hiG.eval_piLp]
  have ht := h i φ hφ
  have hd (y : AmbientSpace) : fderiv ℝ φ y (EuclideanSpace.single i 1) =
      -gradient k (x - y) i := by
    rw [gradient_apply_eq_fderiv_single]
    exact fderiv_comp_const_sub hk x y _
  simp_rw [hd, mul_neg, integral_neg, neg_neg] at ht
  rw [integral_mul_const] at ht
  change (∫ y, E.indicator (fun _ => (1 : ℝ)) y * gradient k (x - y) i) =
    -((∫ y, k (x - y) ∂μ) * ν i) at ht
  simpa only [PiLp.smul_apply, smul_eq_mul, neg_mul] using ht

/-- Positive mollifications are nonincreasing under any increase of normal height. -/
theorem HasConstantIndicatorPolar.bump_convolution_height_order
    {E : Set AmbientSpace} {μ : Measure AmbientSpace} {ν : AmbientSpace}
    (h : HasConstantIndicatorPolar E μ ν) (hE : NullMeasurableSet E volume)
    (φ : ContDiffBump (0 : AmbientSpace)) {x y : AmbientSpace}
    (hxy : inner ℝ ν x ≤ inner ℝ ν y) :
    (φ.normed volume ⋆[ContinuousLinearMap.lsmul ℝ ℝ] E.indicator (fun _ => (1 : ℝ))) y ≤
      (φ.normed volume ⋆[ContinuousLinearMap.lsmul ℝ ℝ] E.indicator (fun _ => (1 : ℝ))) x := by
  have hs : ContDiff ℝ 1
      (φ.normed volume ⋆[ContinuousLinearMap.lsmul ℝ ℝ] E.indicator (fun _ => (1 : ℝ))) :=
    φ.hasCompactSupport_normed.contDiff_convolution_left _ φ.contDiff_normed
      (locallyIntegrable_indicator_one hE)
  apply height_antitone_of_gradient (hs.differentiable one_ne_zero) _ hxy
  intro z
  exact ⟨∫ w, φ.normed volume (z - w) ∂μ,
    integral_nonneg (fun _ => φ.nonneg_normed (μ := volume) _),
    h.gradient_convolution_eq hE φ.contDiff_normed φ.hasCompactSupport_normed z⟩

/-- A constant nonnegative distributional normal and both-phase volume in every origin
ball force the indicated halfspace, modulo ambient volume. -/
theorem halfspace_rigidity_of_constant_indicator_polar
    {E : Set AmbientSpace} {μ : Measure AmbientSpace} {ν : AmbientSpace}
    (hE : NullMeasurableSet E volume) (hν : ‖ν‖ = 1)
    (h : HasConstantIndicatorPolar E μ ν)
    (hphases : ∀ r : ℝ, 0 < r →
      0 < volume (E ∩ ball (0 : AmbientSpace) r) ∧
      0 < volume (ball (0 : AmbientSpace) r \ E)) :
    E =ᵐ[volume] {x : AmbientSpace | inner ℝ ν x < 0} := by
  let φ (j : ℕ) : ContDiffBump (0 : AmbientSpace) :=
    ⟨(1 / ((j : ℝ) + 1)) / 2, 1 / ((j : ℝ) + 1), by positivity,
      half_lt_self (by positivity)⟩
  have hlim : Tendsto (fun j => (φ j).rOut) atTop (𝓝 0) :=
    tendsto_one_div_add_atTop_nhds_zero_nat (𝕜 := ℝ)
  have hratio : ∀ᶠ j in atTop, (φ j).rOut ≤ 2 * (φ j).rIn := by
    filter_upwards with j
    dsimp only [φ]
    linarith
  have hae := ContDiffBump.ae_convolution_tendsto_right_of_locallyIntegrable hlim hratio
    (locallyIntegrable_indicator_one hE)
  let S := {x : AmbientSpace | Tendsto
    (fun j => ((φ j).normed volume ⋆[ContinuousLinearMap.lsmul ℝ ℝ]
      E.indicator (fun _ => (1 : ℝ))) x) atTop (𝓝 (E.indicator (fun _ => (1 : ℝ)) x))}
  apply indicator_halfspace_of_height_order (S := S) hν hae _ hphases
  intro x hx y hy hxy
  exact le_of_tendsto_of_tendsto hy hx
    (Eventually.of_forall fun j => h.bump_convolution_height_order hE (φ j) hxy)

/-- Constant ambient polar fields specialize the raw distributional rigidity theorem. -/
theorem IsAmbientOutwardPerimeterPolar.halfspace_rigidity
    {E : Set AmbientSpace} {μ : Measure AmbientSpace} {ν : AmbientSpace}
    (h : IsAmbientOutwardPerimeterPolar E μ (fun _ => ν))
    (hE : NullMeasurableSet E volume) (hν : ‖ν‖ = 1)
    (hphases : ∀ r : ℝ, 0 < r →
      0 < volume (E ∩ ball (0 : AmbientSpace) r) ∧
      0 < volume (ball (0 : AmbientSpace) r \ E)) :
    E =ᵐ[volume] {x : AmbientSpace | inner ℝ ν x < 0} :=
  halfspace_rigidity_of_constant_indicator_polar hE hν h.hasConstantIndicatorPolar hphases

/-- Changing the polar field on a perimeter-null set does not change the test identity. -/
lemma IsAmbientOutwardPerimeterPolar.hasConstantIndicatorPolar_of_ae_eq
    {E : Set AmbientSpace} {μ : Measure AmbientSpace}
    {σ : AmbientSpace → AmbientSpace} {ν : AmbientSpace}
    (h : IsAmbientOutwardPerimeterPolar E μ σ) (hσ : σ =ᵐ[μ] fun _ => ν) :
    HasConstantIndicatorPolar E μ ν := by
  intro i φ hφ
  apply (h.coordinate_eq i φ hφ).trans
  apply integral_congr_ae
  filter_upwards [hσ] with x hx
  rw [hx]

/-- Almost-everywhere constancy of an ambient polar field suffices for halfspace rigidity. -/
theorem IsAmbientOutwardPerimeterPolar.halfspace_rigidity_of_ae_eq
    {E : Set AmbientSpace} {μ : Measure AmbientSpace}
    {σ : AmbientSpace → AmbientSpace} {ν : AmbientSpace}
    (h : IsAmbientOutwardPerimeterPolar E μ σ)
    (hE : NullMeasurableSet E volume) (hν : ‖ν‖ = 1)
    (hσ : σ =ᵐ[μ] fun _ => ν)
    (hphases : ∀ r : ℝ, 0 < r →
      0 < volume (E ∩ ball (0 : AmbientSpace) r) ∧
      0 < volume (ball (0 : AmbientSpace) r \ E)) :
    E =ᵐ[volume] {x : AmbientSpace | inner ℝ ν x < 0} :=
  halfspace_rigidity_of_constant_indicator_polar hE hν
    (h.hasConstantIndicatorPolar_of_ae_eq hσ) hphases

end LiquidDrop

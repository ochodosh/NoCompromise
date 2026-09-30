module

public import NoCompromise.Regularity.MonotonicityWeighted

@[expose] public section

/-!
# Finite annular tilt measures and sharp radial endpoint comparison

The tilt measure is truncated to a positive annulus before applying the
one-dimensional weak derivative inequality. Its mass is therefore proved finite
without any prior finiteness assumption at the center.
-/

noncomputable section
open MeasureTheory Set Filter Metric InnerProductSpace
open scoped ENNReal Topology
namespace LiquidDrop
set_option maxSynthPendingDepth 8

def radialTiltDensity (ω : ℝ) (x : AmbientSpace)
    (ν : AmbientSpace → AmbientSpace) (y : AmbientSpace) : ℝ :=
  Real.exp (ω * ‖y - x‖) * (inner ℝ (y - x) (ν y)) ^ 2 / ‖y - x‖ ^ 4

lemma radialTiltDensity_nonneg (ω : ℝ) (x : AmbientSpace)
    (ν : AmbientSpace → AmbientSpace) (y : AmbientSpace) :
    0 ≤ radialTiltDensity ω x ν y := by
  exact div_nonneg (mul_nonneg (Real.exp_nonneg _) (sq_nonneg _)) (pow_nonneg (norm_nonneg _) _)

lemma measurable_radialTiltDensity (ω : ℝ) (x : AmbientSpace)
    {ν : AmbientSpace → AmbientSpace} (hν : Measurable ν) :
    Measurable (radialTiltDensity ω x ν) := by
  unfold radialTiltDensity
  fun_prop

lemma integrableOn_radialTiltDensity (μ : Measure AmbientSpace)
    [IsFiniteMeasureOnCompacts μ] {ν : AmbientSpace → AmbientSpace}
    (hν : Measurable ν) (hn : ∀ᵐ y ∂μ, ‖ν y‖ = 1) {ω : ℝ} (hω : 0 ≤ ω)
    (x : AmbientSpace) {a b : ℝ} (ha : 0 < a) (hab : a < b) :
    IntegrableOn (radialTiltDensity ω x ν) {y | ‖y - x‖ ∈ Ioo a b} μ := by
  let S : Set AmbientSpace := {y | ‖y - x‖ ∈ Ioo a b}
  have hS : MeasurableSet S := measurableSet_Ioo.preimage (by fun_prop)
  have hf : μ S ≠ ∞ := (lt_of_le_of_lt (measure_mono (show S ⊆ closedBall x b from
    fun y hy => by simpa only [mem_closedBall, dist_eq_norm] using hy.2.le))
      (isCompact_closedBall x b).measure_lt_top).ne
  have hi : IntegrableOn (fun _ : AmbientSpace => Real.exp (ω * b) * b ^ 2 / a ^ 4) S μ :=
    integrableOn_const hf
  apply hi.mono' (measurable_radialTiltDensity ω x hν).aestronglyMeasurable
  filter_upwards [ae_restrict_mem hS, ae_restrict_of_ae hn] with y hy hyn
  rw [Real.norm_of_nonneg (radialTiltDensity_nonneg ω x ν y)]
  have hinner : |inner ℝ (y - x) (ν y)| ≤ ‖y - x‖ := by
    simpa only [Real.norm_eq_abs, hyn, mul_one] using norm_inner_le_norm (𝕜 := ℝ) (y - x) (ν y)
  have hsq : (inner ℝ (y - x) (ν y)) ^ 2 ≤ b ^ 2 := by
    nlinarith [sq_abs (inner ℝ (y - x) (ν y)), norm_nonneg (y - x),
      abs_nonneg (inner ℝ (y - x) (ν y)), hy.2]
  have he : Real.exp (ω * ‖y - x‖) ≤ Real.exp (ω * b) :=
    Real.exp_le_exp.mpr (mul_le_mul_of_nonneg_left hy.2.le hω)
  unfold radialTiltDensity
  exact div_le_div₀ (mul_nonneg (Real.exp_nonneg _) (sq_nonneg _))
    (mul_le_mul he hsq (sq_nonneg _) (Real.exp_nonneg _)) (pow_pos ha 4)
    (pow_le_pow_left₀ ha.le hy.1.le 4)

/-- The radial pushforward of a finite nonnegative density. -/
def radialWeightedMeasure (μ : Measure AmbientSpace) (w : AmbientSpace → ℝ)
    (x : AmbientSpace) : Measure ℝ :=
  Measure.map (fun y => ‖y - x‖) (μ.withDensity (fun y => ENNReal.ofReal (w y)))

lemma finite_radialWeightedMeasure (μ : Measure AmbientSpace) {w : AmbientSpace → ℝ}
    (hw : Integrable w μ) (hwn : ∀ y, 0 ≤ w y) (x : AmbientSpace) :
    IsFiniteMeasure (radialWeightedMeasure μ w x) := by
  let : IsFiniteMeasure (μ.withDensity fun y => ENNReal.ofReal (w y)) :=
    isFiniteMeasure_withDensity
      ((hasFiniteIntegral_iff_ofReal (Eventually.of_forall hwn)).mp hw.2).ne
  unfold radialWeightedMeasure
  infer_instance

lemma integral_radialWeightedMeasure (μ : Measure AmbientSpace) {w : AmbientSpace → ℝ}
    (hw : Measurable w) (hwn : ∀ y, 0 ≤ w y) (x : AmbientSpace)
    {φ : ℝ → ℝ} (hφ : Measurable φ) :
    (∫ r, φ r ∂radialWeightedMeasure μ w x) = ∫ y, φ ‖y - x‖ * w y ∂μ := by
  rw [radialWeightedMeasure, integral_map (by fun_prop) hφ.aestronglyMeasurable,
    integral_withDensity_eq_integral_toReal_smul (hw.ennreal_ofReal) (by simp)]
  simp only [ENNReal.toReal_ofReal (hwn _), smul_eq_mul, mul_comm]

lemma real_radialWeightedMeasure_Ico (μ : Measure AmbientSpace) {w : AmbientSpace → ℝ}
    (hw : Measurable w) (hwn : ∀ y, 0 ≤ w y) (x : AmbientSpace) (σ ρ : ℝ) :
    (radialWeightedMeasure μ w x).real (Ico σ ρ) =
      ∫ y in {y | ‖y - x‖ ∈ Ico σ ρ}, w y ∂μ := by
  have h := integral_radialWeightedMeasure μ hw hwn x
    (φ := (Ico σ ρ).indicator (fun _ => (1 : ℝ)))
    (measurable_const.indicator measurableSet_Ico)
  rw [integral_indicator measurableSet_Ico] at h
  simp only [setIntegral_const, smul_eq_mul, mul_one] at h
  rw [← integral_indicator (s := {y : AmbientSpace | ‖y - x‖ ∈ Ico σ ρ})
    (measurableSet_Ico.preimage (by fun_prop))]
  rw [h]
  apply integral_congr_ae
  exact Eventually.of_forall fun y => by
    change (Ico σ ρ).indicator (fun _ => (1 : ℝ)) ‖y - x‖ * w y =
      {y : AmbientSpace | ‖y - x‖ ∈ Ico σ ρ}.indicator w y
    by_cases hy : ‖y - x‖ ∈ Ico σ ρ
    · rw [indicator_of_mem hy, indicator_of_mem (show y ∈
        {y : AmbientSpace | ‖y - x‖ ∈ Ico σ ρ} from hy), one_mul]
    · rw [indicator_of_notMem hy, indicator_of_notMem (show y ∉
        {y : AmbientSpace | ‖y - x‖ ∈ Ico σ ρ} from hy), zero_mul]

lemma locallyIntegrableOn_weighted_ball_ratio (μ : Measure AmbientSpace)
    [IsFiniteMeasureOnCompacts μ] (ω : ℝ) (x : AmbientSpace) {a b : ℝ} (ha : 0 < a) :
    LocallyIntegrableOn (fun r : ℝ => Real.exp (ω * r) * μ.real (ball x r) / r ^ 2)
      (Ioo a b) volume := by
  apply (locallyIntegrableOn_iff isOpen_Ioo.isLocallyClosed).mpr
  intro K hK hcK
  have hc : ContinuousOn (fun r : ℝ => Real.exp (ω * r) / r ^ 2) K :=
    (Real.continuous_exp.comp (continuous_const.mul continuous_id)).continuousOn.div
      (continuous_id.pow 2).continuousOn (fun r hr => pow_ne_zero 2 (ne_of_gt (ha.trans (hK hr).1)))
  have hi := (locallyIntegrable_ball_mass μ x).integrableOn_isCompact hcK
  simpa only [div_eq_mul_inv, mul_comm, mul_left_comm, mul_assoc] using
    hi.mul_continuousOn hc hcK

lemma continuousWithinAt_weighted_ball_ratio (μ : Measure AmbientSpace)
    [IsFiniteMeasureOnCompacts μ] (ω : ℝ) (x : AmbientSpace) {r : ℝ} (hr : 0 < r) :
    ContinuousWithinAt (fun s : ℝ => Real.exp (ω * s) * μ.real (ball x s) / s ^ 2)
      (Iic r) r := by
  have hf : μ (ball x r) ≠ ∞ := (lt_of_le_of_lt (measure_mono ball_subset_closedBall)
    (isCompact_closedBall x r).measure_lt_top).ne
  have hc : ContinuousAt (fun s : ℝ => Real.exp (ω * s)) r := by fun_prop
  exact (hc.continuousWithinAt.mul
    (continuousWithinAt_measureReal_ball_radius μ x r hf)).div
      (continuous_id.pow 2).continuousAt.continuousWithinAt (pow_ne_zero 2 hr.ne')

/-- Sharp annular monotonicity from the actual first variation. Open balls
correspond exactly to the half-open radial interval `[σ, ρ)`. -/
theorem annular_monotonicity_of_bounded_first_variation (μ : Measure AmbientSpace)
    [IsFiniteMeasureOnCompacts μ] {ν : AmbientSpace → AmbientSpace}
    (hν : Measurable ν) (hn : ∀ᵐ y ∂μ, ‖ν y‖ = 1) {ω : ℝ} (hω : 0 ≤ ω)
    (x : AmbientSpace) (hx : μ {x} = 0)
    (hfv : ∀ X : AmbientSpace → AmbientSpace, ContDiff ℝ 1 X → HasCompactSupport X →
      tsupport X ⊆ ball x 1 → |∫ y, tangentialDivergence X ν y ∂μ| ≤
        ω * ∫ y, |inner ℝ (X y) (ν y)| ∂μ)
    {σ ρ : ℝ} (hσ : 0 < σ) (hσρ : σ ≤ ρ) (hρ : ρ < 1) :
    (∫ y in ball x ρ \ ball x σ, radialTiltDensity ω x ν y ∂μ) ≤
      Real.exp (ω * ρ) * μ.real (ball x ρ) / ρ ^ 2 -
        Real.exp (ω * σ) * μ.real (ball x σ) / σ ^ 2 := by
  let a := σ / 2
  let b := (ρ + 1) / 2
  have ha : 0 < a := by dsimp [a]; linarith
  have haσ : a < σ := by dsimp [a]; linarith
  have hρb : ρ < b := by dsimp [b]; linarith
  have hb : b < 1 := by dsimp [b]; linarith
  have hab : a < b := haσ.trans_le (hσρ.trans hρb.le)
  let S : Set AmbientSpace := {y | ‖y - x‖ ∈ Ioo a b}
  let w := S.indicator (radialTiltDensity ω x ν)
  have hS : MeasurableSet S := measurableSet_Ioo.preimage (by fun_prop)
  have hw : Measurable w := (measurable_radialTiltDensity ω x hν).indicator hS
  have hwn : ∀ y, 0 ≤ w y := fun y => indicator_nonneg (fun z _ =>
    radialTiltDensity_nonneg ω x ν z) y
  have hiw : Integrable w μ := (integrable_indicator_iff hS).mpr
    (integrableOn_radialTiltDensity μ hν hn hω x ha hab)
  let τ := radialWeightedMeasure μ w x
  let : IsFiniteMeasure τ := finite_radialWeightedMeasure μ hiw hwn x
  have hweak : ∀ φ : ℝ → ℝ, ContDiff ℝ 1 φ → HasCompactSupport φ →
      tsupport φ ⊆ Ioo a b → (∀ r, 0 ≤ φ r) →
      (∫ r, φ r ∂τ) ≤
        -(∫ r : ℝ, (Real.exp (ω * r) * μ.real (ball x r) / r ^ 2) * deriv φ r) := by
    intro φ hφ hcφ hsφ hnφ
    have he : (∫ r, φ r ∂τ) =
        ∫ y, φ ‖y - x‖ * radialTiltDensity ω x ν y ∂μ := by
      rw [integral_radialWeightedMeasure μ hw hwn x hφ.continuous.measurable]
      apply integral_congr_ae
      exact Eventually.of_forall fun y => by
        by_cases hy : y ∈ S
        · simp only [w, indicator_of_mem hy]
        · have hz : φ ‖y - x‖ = 0 := image_eq_zero_of_notMem_tsupport
            (fun h => hy (hsφ h))
          simp only [hz, zero_mul]
    rw [he]
    exact weighted_radial_first_variation_weak μ hν hn hω x hx hfv hφ hcφ hnφ ha hb hsφ
  have h := interval_mass_le_sub_of_weak_derivative τ
    (locallyIntegrableOn_weighted_ball_ratio μ ω x ha) haσ hσρ hρb
    (continuousWithinAt_weighted_ball_ratio μ ω x hσ)
    (continuousWithinAt_weighted_ball_ratio μ ω x (hσ.trans_le hσρ)) hweak
  have hT : MeasurableSet {y : AmbientSpace | ‖y - x‖ ∈ Ico σ ρ} :=
    measurableSet_Ico.preimage (by fun_prop)
  have he : τ.real (Ico σ ρ) =
      ∫ y in {y | ‖y - x‖ ∈ Ico σ ρ}, radialTiltDensity ω x ν y ∂μ := by
    rw [real_radialWeightedMeasure_Ico μ hw hwn x]
    apply setIntegral_congr_fun hT
    intro y hy
    exact indicator_of_mem (show y ∈ S from
      ⟨haσ.trans_le hy.1, hy.2.trans hρb⟩) _
  have hset : {y : AmbientSpace | ‖y - x‖ ∈ Ico σ ρ} = ball x ρ \ ball x σ := by
    ext y
    simp only [Set.mem_ofPred_eq, mem_Ico, Set.mem_sdiff, mem_ball, dist_eq_norm, not_lt]
    exact and_comm
  rwa [he, hset] at h

end LiquidDrop

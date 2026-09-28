import NoCompromise.Regularity.TangentBoundary
import NoCompromise.Regularity.TangentScaling

/-!
# Vanishing radial pairing from constant perimeter ratios

For a zero-error quasiminimizer, the quantitative annular monotonicity formula
has zero right side when all centered density ratios agree. Its nonnegative
integrand therefore vanishes almost everywhere. The genuine perimeter polar
identity then makes every radial test-field pairing vanish in the inner ball.
-/

noncomputable section
open MeasureTheory Set Filter Metric InnerProductSpace
open scoped Topology ENNReal RealInnerProductSpace
namespace LiquidDrop
set_option maxSynthPendingDepth 8

lemma IsOmegaMinimal.annular_tilt_eq_zero {F : Set AmbientSpace}
    (hF : IsOmegaMinimal F 0) {θ : ℝ}
    (hd : ∀ R : ℝ, 0 < R → (perimeterIn F (ball 0 R)).toReal / R ^ 2 = θ)
    {σ ρ : ℝ} (hσ : 0 < σ) (hσρ : σ ≤ ρ) (hρ : ρ < 1) :
    (∫ y in (ball 0 ρ \ ball 0 σ) ∩ reducedBoundary F hF.locallyFinite hF.nullMeasurable,
      radialTiltDensity 0 0 (reducedNormal F hF.locallyFinite hF.nullMeasurable) y
        ∂hausdorffMeasure2 3) = 0 := by
  have hb := hF.annular_monotonicity 0 hσ hσρ hρ
  have hρ0 : 0 < ρ := hσ.trans_le hσρ
  simp only [zero_mul, Real.exp_zero, one_mul, hd ρ hρ0, hd σ hσ, sub_self] at hb
  exact le_antisymm hb (integral_nonneg (radialTiltDensity_nonneg _ _ _))

lemma IsOmegaMinimal.ae_annular_radial_inner_eq_zero {F : Set AmbientSpace}
    (hF : IsOmegaMinimal F 0) {θ : ℝ}
    (hd : ∀ R : ℝ, 0 < R → (perimeterIn F (ball 0 R)).toReal / R ^ 2 = θ)
    {σ ρ : ℝ} (hσ : 0 < σ) (hσρ : σ ≤ ρ) (hρ : ρ < 1) :
    ∀ᵐ y ∂(hausdorffMeasure2 3).restrict
      ((ball 0 ρ \ ball 0 σ) ∩ reducedBoundary F hF.locallyFinite hF.nullMeasurable),
      inner ℝ y (reducedNormal F hF.locallyFinite hF.nullMeasurable y) = 0 := by
  have hi := hF.integrableOn_annular_tilt 0 hσ hσρ
  have hz := (integral_eq_zero_iff_of_nonneg
    (radialTiltDensity_nonneg 0 0 _) hi).mp (hF.annular_tilt_eq_zero hd hσ hσρ hρ)
  have hm : MeasurableSet ((ball 0 ρ \ ball 0 σ) ∩
      reducedBoundary F hF.locallyFinite hF.nullMeasurable) :=
    (measurableSet_ball.diff measurableSet_ball).inter
      (measurableSet_reducedBoundary F hF.locallyFinite hF.nullMeasurable)
  filter_upwards [hz, ae_restrict_mem hm] with y hy hym
  have hn : σ ≤ ‖y‖ := by
    simpa only [mem_ball, dist_zero_right, not_lt] using hym.1.2
  have hnorm : ‖y‖ ≠ 0 := (hσ.trans_le hn).ne'
  simp only [radialTiltDensity, zero_mul, Real.exp_zero, one_mul, sub_zero] at hy
  exact sq_eq_zero_iff.mp ((div_eq_zero_iff.mp hy).resolve_right (pow_ne_zero _ hnorm))

lemma IsOmegaMinimal.ae_radial_inner_eq_zero_halfBall {F : Set AmbientSpace}
    (hF : IsOmegaMinimal F 0) {θ : ℝ}
    (hd : ∀ R : ℝ, 0 < R → (perimeterIn F (ball 0 R)).toReal / R ^ 2 = θ) :
    ∀ᵐ y ∂(hausdorffMeasure2 3).restrict
      (reducedBoundary F hF.locallyFinite hF.nullMeasurable),
      y ∈ ball 0 (1 / 2 : ℝ) →
        inner ℝ y (reducedNormal F hF.locallyFinite hF.nullMeasurable y) = 0 := by
  let μ := (hausdorffMeasure2 3).restrict
    (reducedBoundary F hF.locallyFinite hF.nullMeasurable)
  have hseq (m : ℕ) : ∀ᵐ y ∂μ,
      y ∈ ball 0 (3 / 4 : ℝ) \ ball 0 (1 / ((m : ℝ) + 3)) →
        inner ℝ y (reducedNormal F hF.locallyFinite hF.nullMeasurable y) = 0 := by
    have hσ : 0 < 1 / ((m : ℝ) + 3) := by positivity
    have hσρ : 1 / ((m : ℝ) + 3) ≤ 3 / 4 := by
      rw [div_le_iff₀ (by positivity : 0 < (m : ℝ) + 3)]
      nlinarith [Nat.cast_nonneg (α := ℝ) m]
    have hz := hF.ae_annular_radial_inner_eq_zero hd hσ hσρ (by norm_num)
    have hz' : ∀ᵐ y ∂μ.restrict
        (ball 0 (3 / 4 : ℝ) \ ball 0 (1 / ((m : ℝ) + 3))),
        inner ℝ y (reducedNormal F hF.locallyFinite hF.nullMeasurable y) = 0 := by
      simpa only [μ, Measure.restrict_restrict
        (measurableSet_ball.diff measurableSet_ball)] using hz
    exact (ae_restrict_iff' (measurableSet_ball.diff measurableSet_ball)).mp hz'
  filter_upwards [ae_all_iff.mpr hseq] with y hy hyball
  by_cases hy0 : y = 0
  · simp only [hy0, inner_zero_left]
  obtain ⟨m, hm⟩ := exists_nat_one_div_lt (norm_pos_iff.mpr hy0)
  have hle : 1 / ((m : ℝ) + 3) ≤ 1 / ((m : ℝ) + 1) := by
    apply one_div_le_one_div_of_le (by positivity)
    linarith
  apply hy m
  refine ⟨ball_subset_ball (by norm_num : (1 / 2 : ℝ) ≤ 3 / 4) hyball, ?_⟩
  simpa only [mem_ball, dist_zero_right, not_lt] using (hle.trans hm.le)

/-- The actual radial distributional derivative vanishes on the inner ball. -/
theorem IsOmegaMinimal.radial_pairing_eq_zero_halfBall {F : Set AmbientSpace}
    (hF : IsOmegaMinimal F 0) {θ : ℝ}
    (hd : ∀ R : ℝ, 0 < R → (perimeterIn F (ball 0 R)).toReal / R ^ 2 = θ)
    {φ : AmbientSpace → ℝ} (hφ : ContDiff ℝ 1 φ) (hcφ : HasCompactSupport φ)
    (hsφ : tsupport φ ⊆ ball 0 (1 / 2 : ℝ)) :
    (∫ y in F, divergenceN (fun z => φ z • z) y) = 0 := by
  have hp := reducedBoundary_outwardPerimeterPolar F hF.locallyFinite hF.nullMeasurable
  rw [hp.divergence_eq (fun z => φ z • z) (by fun_prop) hcφ.smul_right]
  apply integral_eq_zero_of_ae
  filter_upwards [hF.ae_radial_inner_eq_zero_halfBall hd] with y hy
  by_cases hφy : φ y = 0
  · simp only [hφy, zero_smul, inner_zero_left, Pi.zero_apply]
  have hys : y ∈ tsupport φ := subset_tsupport φ hφy
  rw [inner_smul_left, hy (hsφ hys)]
  simp

end LiquidDrop

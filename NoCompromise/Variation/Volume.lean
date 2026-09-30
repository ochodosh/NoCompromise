module

public import NoCompromise.Variation.StraightCofactor
public import Mathlib.MeasureTheory.Function.Jacobian

@[expose] public section

/-!
# First variation of volume

For a Lebesgue-measurable set of finite volume and a compactly supported `C¹`
field, the real volume of its actual straight image has derivative equal to the
bulk integral of divergence. No finite-perimeter or Gauss--Green theorem is used.
-/

noncomputable section

open Set Filter MeasureTheory
open scoped Topology NNReal ENNReal

namespace LiquidDrop

set_option maxSynthPendingDepth 8

local notation "E₃" => EuclideanSpace ℝ (Fin 3)
local notation "L₃" => E₃ →L[ℝ] E₃

/-- A continuous function of a compactly supported continuous derivative is bounded. -/
lemma exists_bound_comp_fderiv {X : E₃ → E₃} (hXC : ContDiff ℝ 1 X)
    (hXc : HasCompactSupport X) {g : L₃ → ℝ} (hg : Continuous g) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ x : E₃, ‖g (fderiv ℝ X x)‖ ≤ C := by
  have hK := (hXc.fderiv ℝ).isCompact_range (hXC.continuous_fderiv (by simp))
  obtain ⟨C, hC⟩ := hK.exists_bound_of_continuousOn hg.continuousOn
  exact ⟨max C 0, le_max_right _ _, fun x =>
    (hC _ (mem_range_self x)).trans (le_max_left _ _)⟩

/-- Continuous derivative expressions are integrable on every finite-volume set. -/
lemma integrableOn_comp_fderiv_of_finiteVolume {X : E₃ → E₃} (hXC : ContDiff ℝ 1 X)
    (hXc : HasCompactSupport X) {E : Set E₃} (hEfin : volume E < ∞)
    {g : L₃ → ℝ} (hg : Continuous g) : IntegrableOn (fun x => g (fderiv ℝ X x)) E := by
  have : IsFiniteMeasure (volume.restrict E) := ⟨by simpa using hEfin⟩
  obtain ⟨C, _, hC⟩ := exists_bound_comp_fderiv hXC hXc hg
  exact (integrable_const C).mono'
    (hg.comp (hXC.continuous_fderiv (by simp))).aestronglyMeasurable
    (Eventually.of_forall hC)

lemma integrableOn_divergenceN_of_finiteVolume {X : E₃ → E₃} (hXC : ContDiff ℝ 1 X)
    (hXc : HasCompactSupport X) {E : Set E₃} (hEfin : volume E < ∞) :
    IntegrableOn (divergenceN X) E :=
  integrableOn_comp_fderiv_of_finiteVolume hXC hXc hEfin
    continuous_standardMatrix3.matrix_trace

/-- Change of variables for actual straight images of Lebesgue-measurable sets. -/
lemma volume_straightPerturbation_image_eq_lintegral_abs_det {X : E₃ → E₃} {L : ℝ≥0}
    (hXD : Differentiable ℝ X) (hXL : LipschitzWith L X) {t : ℝ} (ht : |t| * L < 1)
    {E : Set E₃} (hE : NullMeasurableSet E volume) :
    volume (straightPerturbation X t '' E) =
      ∫⁻ x in E, ENNReal.ofReal |(ContinuousLinearMap.id ℝ E₃ + t • fderiv ℝ X x).det| := by
  exact (lintegral_abs_det_fderiv_eq_addHaar_image₀ volume hE
    (fun x _ => (hasFDerivAt_straightPerturbation (hXD x).hasFDerivAt t).hasFDerivWithinAt)
    (straightPerturbation_bijective hXL ht).1.injOn).symm

lemma nullMeasurableSet_straightPerturbation_image {X : E₃ → E₃} {L : ℝ≥0}
    (hXD : Differentiable ℝ X) (hXL : LipschitzWith L X) {t : ℝ} (ht : |t| * L < 1)
    {E : Set E₃} (hE : NullMeasurableSet E volume) :
    NullMeasurableSet (straightPerturbation X t '' E) volume :=
  nullMeasurable_image_of_fderivWithin volume hE
    (fun x _ => (hasFDerivAt_straightPerturbation (hXD x).hasFDerivAt t).hasFDerivWithinAt)
    (straightPerturbation_bijective hXL ht).1.injOn

/-- Change of variables produces finite image volume and the correct real integral. -/
lemma volume_straightPerturbation_image_finite_and_toReal {X : E₃ → E₃}
    (hXC : ContDiff ℝ 1 X) (hXc : HasCompactSupport X) {t : ℝ}
    (ht : |t| * ‖straightDerivativeField hXC hXc‖ < 1)
    {E : Set E₃} (hE : NullMeasurableSet E volume) (hEfin : volume E < ∞) :
    volume (straightPerturbation X t '' E) < ∞ ∧
      (volume (straightPerturbation X t '' E)).toReal =
        ∫ x in E, |(ContinuousLinearMap.id ℝ E₃ + t • fderiv ℝ X x).det| := by
  have hi : IntegrableOn
      (fun x => |(ContinuousLinearMap.id ℝ E₃ + t • fderiv ℝ X x).det|) E :=
    integrableOn_comp_fderiv_of_finiteVolume hXC hXc hEfin
      (g := fun A : L₃ => |(ContinuousLinearMap.id ℝ E₃ + t • A).det|)
      ((ContinuousLinearMap.continuous_det.comp
        (show Continuous (fun A : L₃ => ContinuousLinearMap.id ℝ E₃ + t • A) by
          fun_prop)).abs)
  rw [volume_straightPerturbation_image_eq_lintegral_abs_det
    (hXC.differentiable (by simp)) (lipschitzWith_straightDerivativeField hXC hXc) ht hE]
  have heq := ofReal_integral_eq_lintegral_ofReal hi
    (Eventually.of_forall fun x => abs_nonneg
      (ContinuousLinearMap.id ℝ E₃ + t • fderiv ℝ X x).det)
  rw [← heq]
  exact ⟨ENNReal.ofReal_lt_top, ENNReal.toReal_ofReal (integral_nonneg fun _ => abs_nonneg _)⟩

/-- Straight derivatives preserve orientation throughout one common neighborhood of time zero. -/
lemma exists_pos_det_straightPerturbation {X : E₃ → E₃}
    (hXC : ContDiff ℝ 1 X) (hXc : HasCompactSupport X) :
    ∃ δ : ℝ, 0 < δ ∧ ∀ t : ℝ, |t| < δ → ∀ x : E₃,
      0 < (fderiv ℝ (straightPerturbation X t) x).det := by
  obtain ⟨C, hC, hrem⟩ := exists_uniform_straight_cofactor_expansion hXC hXc
  obtain ⟨B, hB, hb⟩ := exists_bound_comp_fderiv hXC hXc
    continuous_standardMatrix3.matrix_trace
  refine ⟨min 1 (1 / (2 * (B + C + 1))), lt_min zero_lt_one (by positivity), ?_⟩
  intro t ht x
  have ht1 : |t| ≤ 1 := (ht.trans_le (min_le_left _ _)).le
  have hsmall : |t| * (2 * (B + C + 1)) < 1 :=
    (lt_div_iff₀ (by positivity : 0 < 2 * (B + C + 1))).mp
      (ht.trans_le (min_le_right _ _))
  have htsq : t ^ 2 ≤ |t| := by
    nlinarith [sq_abs t, mul_nonneg (abs_nonneg t) (sub_nonneg.mpr ht1)]
  have hdiv : |divergenceN X x| ≤ B := by
    simpa only [Real.norm_eq_abs, standardMatrix3_fderiv_trace] using hb x
  have herror : |(fderiv ℝ (straightPerturbation X t) x).det - 1| ≤ (C + B) * |t| := by
    calc
      _ = |((fderiv ℝ (straightPerturbation X t) x).det - 1 - t * divergenceN X x) +
          t * divergenceN X x| := by congr 1; ring
      _ ≤ |(fderiv ℝ (straightPerturbation X t) x).det - 1 - t * divergenceN X x| +
          |t * divergenceN X x| := abs_add_le _ _
      _ ≤ C * t ^ 2 + |t| * B := by
        rw [abs_mul]
        exact add_le_add (hrem t ht1 x).2.1
          (mul_le_mul_of_nonneg_left hdiv (abs_nonneg t))
      _ ≤ _ := by nlinarith [mul_le_mul_of_nonneg_left htsq hC]
  have hCB : 0 ≤ (C + B) * |t| := mul_nonneg (by linarith) (abs_nonneg t)
  have := (abs_le.mp herror).1
  nlinarith [abs_nonneg t]

/-- Near the identity, volume is an exact cubic polynomial in the perturbation time. -/
lemma volume_straightPerturbation_image_toReal_eq_polynomial {X : E₃ → E₃}
    (hXC : ContDiff ℝ 1 X) (hXc : HasCompactSupport X) {E : Set E₃}
    (hE : NullMeasurableSet E volume) (hEfin : volume E < ∞) {t : ℝ}
    (ht : |t| * ‖straightDerivativeField hXC hXc‖ < 1)
    (hpos : ∀ x : E₃, 0 < (fderiv ℝ (straightPerturbation X t) x).det) :
    (volume (straightPerturbation X t '' E)).toReal = (volume E).toReal +
      t * (∫ x in E, divergenceN X x) +
      t ^ 2 * (∫ x in E, (standardMatrix3 (cofactor3 (fderiv ℝ X x))).trace) +
      t ^ 3 * (∫ x in E, (fderiv ℝ X x).det) := by
  have : IsFiniteMeasure (volume.restrict E) := ⟨by simpa using hEfin⟩
  have i0 : Integrable (fun _ : E₃ => (1 : ℝ)) (volume.restrict E) := integrable_const 1
  have i1 := integrableOn_divergenceN_of_finiteVolume hXC hXc hEfin
  have i2 : IntegrableOn (fun x => (standardMatrix3 (cofactor3 (fderiv ℝ X x))).trace) E :=
    integrableOn_comp_fderiv_of_finiteVolume hXC hXc hEfin
      (continuous_standardMatrix3.comp continuous_cofactor3).matrix_trace
  have i3 : IntegrableOn (fun x => (fderiv ℝ X x).det) E :=
    integrableOn_comp_fderiv_of_finiteVolume hXC hXc hEfin ContinuousLinearMap.continuous_det
  rw [(volume_straightPerturbation_image_finite_and_toReal hXC hXc ht hE hEfin).2]
  have habs (x : E₃) : |(ContinuousLinearMap.id ℝ E₃ + t • fderiv ℝ X x).det| =
      (ContinuousLinearMap.id ℝ E₃ + t • fderiv ℝ X x).det := by
    apply abs_of_pos
    simpa only [fderiv_straightPerturbation (hXC.differentiable (by simp) x) t] using hpos x
  simp_rw [habs, det_id_add_smul_three, standardMatrix3_fderiv_trace]
  have i01 : Integrable (fun x => 1 + t * divergenceN X x) (volume.restrict E) :=
    i0.add (i1.const_mul t)
  have i012 : Integrable (fun x => 1 + t * divergenceN X x +
      t ^ 2 * (standardMatrix3 (cofactor3 (fderiv ℝ X x))).trace) (volume.restrict E) :=
    i01.add (i2.const_mul (t ^ 2))
  rw [integral_add i012 (i3.const_mul (t ^ 3)),
    integral_add i01 (i2.const_mul (t ^ 2)), integral_add i0 (i1.const_mul t)]
  simp only [integral_const_mul, integral_const, smul_eq_mul, mul_one, measureReal_def,
    Measure.restrict_apply_univ]

/-- The cubic volume identity holds on one genuine neighborhood of time zero. -/
lemma eventually_volume_straightPerturbation_image_toReal_eq_polynomial {X : E₃ → E₃}
    (hXC : ContDiff ℝ 1 X) (hXc : HasCompactSupport X) {E : Set E₃}
    (hE : NullMeasurableSet E volume) (hEfin : volume E < ∞) :
    ∀ᶠ t : ℝ in 𝓝 0, (volume (straightPerturbation X t '' E)).toReal = (volume E).toReal +
      t * (∫ x in E, divergenceN X x) +
      t ^ 2 * (∫ x in E, (standardMatrix3 (cofactor3 (fderiv ℝ X x))).trace) +
      t ^ 3 * (∫ x in E, (fderiv ℝ X x).det) := by
  obtain ⟨δ, hδ, hpos⟩ := exists_pos_det_straightPerturbation hXC hXc
  have htδ : ∀ᶠ t : ℝ in 𝓝 0, |t| < δ := by
    filter_upwards [Metric.ball_mem_nhds (0 : ℝ) hδ] with t ht
    simpa only [Metric.mem_ball, dist_zero_right, Real.norm_eq_abs] using ht
  have hsmall : ∀ᶠ t : ℝ in 𝓝 0, |t| * ‖straightDerivativeField hXC hXc‖ < 1 := by
    have hc : Continuous (fun t : ℝ => |t| * ‖straightDerivativeField hXC hXc‖) := by fun_prop
    exact hc.continuousAt.eventually (gt_mem_nhds (by simp))
  filter_upwards [htδ, hsmall] with t htδ ht
  exact volume_straightPerturbation_image_toReal_eq_polynomial hXC hXc hE hEfin ht (hpos t htδ)

/-- The bulk first variation of actual volume. Lebesgue measurability and finite volume
are enough; finite perimeter is not a premise. -/
theorem hasDerivAt_volume_straightPerturbation_image {X : E₃ → E₃}
    (hXC : ContDiff ℝ 1 X) (hXc : HasCompactSupport X) {E : Set E₃}
    (hE : NullMeasurableSet E volume) (hEfin : volume E < ∞) :
    HasDerivAt (fun t : ℝ => (volume (straightPerturbation X t '' E)).toReal)
      (∫ x in E, divergenceN X x) 0 := by
  have hpoly : HasDerivAt (fun t : ℝ => (volume E).toReal +
      t * (∫ x in E, divergenceN X x) +
      t ^ 2 * (∫ x in E, (standardMatrix3 (cofactor3 (fderiv ℝ X x))).trace) +
      t ^ 3 * (∫ x in E, (fderiv ℝ X x).det)) (∫ x in E, divergenceN X x) 0 := by
    simpa [Pi.add_def, Pi.pow_def] using (((hasDerivAt_const (0 : ℝ) (volume E).toReal).add
      ((hasDerivAt_id (0 : ℝ)).mul_const (∫ x in E, divergenceN X x))).add
      (((hasDerivAt_id (0 : ℝ)).pow 2).mul_const
        (∫ x in E, (standardMatrix3 (cofactor3 (fderiv ℝ X x))).trace))).add
      (((hasDerivAt_id (0 : ℝ)).pow 3).mul_const (∫ x in E, (fderiv ℝ X x).det))
  exact hpoly.congr_of_eventuallyEq
    (eventually_volume_straightPerturbation_image_toReal_eq_polynomial hXC hXc hE hEfin)

lemma deriv_volume_straightPerturbation_image {X : E₃ → E₃}
    (hXC : ContDiff ℝ 1 X) (hXc : HasCompactSupport X) {E : Set E₃}
    (hE : NullMeasurableSet E volume) (hEfin : volume E < ∞) :
    deriv (fun t : ℝ => (volume (straightPerturbation X t '' E)).toReal) 0 =
      ∫ x in E, divergenceN X x :=
  (hasDerivAt_volume_straightPerturbation_image hXC hXc hE hEfin).deriv

/-- An injective straight perturbation fixes every set containing the field's support. -/
lemma straightPerturbation_image_eq_self_of_tsupport_subset {X : E₃ → E₃} {L : ℝ≥0}
    (hXL : LipschitzWith L X) {t : ℝ} (ht : |t| * L < 1)
    {A : Set E₃} (hXA : tsupport X ⊆ A) : straightPerturbation X t '' A = A := by
  classical
  obtain ⟨hinj, hsurj⟩ := straightPerturbation_bijective hXL ht
  have hfix (x : E₃) (hx : x ∉ A) : straightPerturbation X t x = x :=
    straightPerturbation_eq_self_of_notMem_tsupport X t (fun h => hx (hXA h))
  have hmem (x : E₃) : straightPerturbation X t x ∈ A ↔ x ∈ A := by
    constructor
    · intro hx
      by_contra hxa
      rw [hfix x hxa] at hx
      exact hxa hx
    · intro hx
      by_contra hfa
      have heq := hinj (hfix (straightPerturbation X t x) hfa)
      rw [heq] at hfa
      exact hfa hx
  ext y
  constructor
  · rintro ⟨x, hx, rfl⟩
    exact (hmem x).2 hx
  · intro hy
    obtain ⟨x, rfl⟩ := hsurj y
    exact ⟨x, (hmem x).1 hy, rfl⟩

lemma straightPerturbation_image_inter_eq {X : E₃ → E₃} {L : ℝ≥0}
    (hXL : LipschitzWith L X) {t : ℝ} (ht : |t| * L < 1)
    {A : Set E₃} (hXA : tsupport X ⊆ A) (E : Set E₃) :
    straightPerturbation X t '' (E ∩ A) = straightPerturbation X t '' E ∩ A := by
  rw [Set.image_inter (straightPerturbation_bijective hXL ht).1,
    straightPerturbation_image_eq_self_of_tsupport_subset hXL ht hXA]

/-- Localized volume variation inside a finite-volume containing set. The original set
may have infinite total volume. -/
theorem hasDerivAt_volume_straightPerturbation_image_inter {X : E₃ → E₃}
    (hXC : ContDiff ℝ 1 X) (hXc : HasCompactSupport X) {E A : Set E₃}
    (hE : NullMeasurableSet E volume) (hA : NullMeasurableSet A volume)
    (hAfin : volume A < ∞) (hXA : tsupport X ⊆ A) :
    HasDerivAt (fun t : ℝ => (volume (straightPerturbation X t '' E ∩ A)).toReal)
      (∫ x in E ∩ A, divergenceN X x) 0 := by
  have hD := hasDerivAt_volume_straightPerturbation_image hXC hXc (hE.inter hA)
    ((measure_mono inter_subset_right).trans_lt hAfin)
  apply hD.congr_of_eventuallyEq
  have hsmall : ∀ᶠ t : ℝ in 𝓝 0, |t| * ‖straightDerivativeField hXC hXc‖ < 1 := by
    have hc : Continuous (fun t : ℝ => |t| * ‖straightDerivativeField hXC hXc‖) := by fun_prop
    exact hc.continuousAt.eventually (gt_mem_nhds (by simp))
  filter_upwards [hsmall] with t ht
  rw [straightPerturbation_image_inter_eq (lipschitzWith_straightDerivativeField hXC hXc) ht hXA]

end LiquidDrop


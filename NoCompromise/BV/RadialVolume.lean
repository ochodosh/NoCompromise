module

public import NoCompromise.BV.SphericalSlicing
public import Mathlib.MeasureTheory.Integral.IntervalIntegral.LebesgueDifferentiationThm

@[expose] public section

/-!
# Radial volume and spherical section area

The actual volume inside a ball is the primitive of the area of the density-one
spherical section. The uniform sphere-area bound gives local Lipschitz control
and the almost-everywhere radial derivative without perimeter assumptions.
-/

noncomputable section
open MeasureTheory Set Filter Metric
open scoped Topology ENNReal NNReal
namespace LiquidDrop

/-- Real volume of the part of a set inside a finite-radius ball. -/
def radialVolume (E : Set AmbientSpace) (c : AmbientSpace) (r : ℝ) : ℝ :=
  (volume (E ∩ ball c r)).toReal

/-- Real Hausdorff area of the density-one representative on a sphere. -/
def radialSectionArea (E : Set AmbientSpace) (c : AmbientSpace) (r : ℝ) : ℝ :=
  (hausdorffMeasure2 3 (densityOne E ∩ sphere c r)).toReal

lemma radialSectionArea_nonneg (E : Set AmbientSpace) (c : AmbientSpace) (r : ℝ) :
    0 ≤ radialSectionArea E c r := ENNReal.toReal_nonneg

lemma hausdorffMeasure2_spherical_section_eq_zero_of_nonpos
    (E : Set AmbientSpace) (c : AmbientSpace) {r : ℝ} (hr : r ≤ 0) :
    hausdorffMeasure2 3 (densityOne E ∩ sphere c r) = 0 := by
  rcases lt_or_eq_of_le hr with hlt | rfl
  · rw [sphere_eq_empty_of_neg hlt, inter_empty, measure_empty]
  · rw [sphere_zero]
    exact hausdorffMeasure2_subsingleton (Set.subsingleton_singleton.anti inter_subset_right)

lemma hausdorffMeasure2_spherical_section_lt_top
    (E : Set AmbientSpace) (c : AmbientSpace) (r : ℝ) :
    hausdorffMeasure2 3 (densityOne E ∩ sphere c r) < ∞ := by
  by_cases hr : 0 < r
  · apply (measure_mono inter_subset_right).trans_lt
    rw [hausdorffMeasure2_sphere c hr]
    exact ENNReal.ofReal_lt_top
  · rw [hausdorffMeasure2_spherical_section_eq_zero_of_nonpos E c (le_of_not_gt hr)]
    exact ENNReal.zero_lt_top

lemma radialSectionArea_le (E : Set AmbientSpace) (c : AmbientSpace) (r : ℝ) :
    radialSectionArea E c r ≤ 4 * Real.pi * r ^ 2 := by
  by_cases hr : 0 < r
  · have hle := ENNReal.toReal_mono
      (show hausdorffMeasure2 3 (sphere c r) ≠ ∞ by
        rw [hausdorffMeasure2_sphere c hr]; exact ENNReal.ofReal_ne_top)
      (measure_mono (inter_subset_right : densityOne E ∩ sphere c r ⊆ sphere c r))
    simpa only [radialSectionArea, hausdorffMeasure2_sphere c hr,
      ENNReal.toReal_ofReal (by positivity : 0 ≤ 4 * Real.pi * r ^ 2)] using hle
  · simp only [radialSectionArea,
      hausdorffMeasure2_spherical_section_eq_zero_of_nonpos E c (le_of_not_gt hr),
      ENNReal.toReal_zero]
    positivity

lemma measurable_radialSectionArea {E : Set AmbientSpace}
    (hE : NullMeasurableSet E volume) (c : AmbientSpace) :
    Measurable (radialSectionArea E c) :=
  (measurable_sphere_sections (measurableSet_densityOne hE) c).ennreal_toReal

lemma locallyIntegrable_radialSectionArea {E : Set AmbientSpace}
    (hE : NullMeasurableSet E volume) (c : AmbientSpace) :
    LocallyIntegrable (radialSectionArea E c) := by
  have hcont : Continuous (fun r : ℝ => 4 * Real.pi * r ^ 2) := by fun_prop
  apply hcont.locallyIntegrable.mono (measurable_radialSectionArea hE c).aestronglyMeasurable
  apply Eventually.of_forall
  intro r
  rw [Real.norm_of_nonneg (radialSectionArea_nonneg E c r)]
  exact (radialSectionArea_le E c r).trans (le_abs_self _)

/-- Spherical slicing gives the exact real-valued primitive at every radius. -/
theorem radialVolume_eq_integral {E : Set AmbientSpace}
    (hE : NullMeasurableSet E volume) (c : AmbientSpace) (r : ℝ) :
    radialVolume E c r = ∫ t in Ioo 0 r, radialSectionArea E c t := by
  have hs := spherical_slicing hE c (a := 0) le_rfl r
  simp only [ball_zero, sdiff_empty] at hs
  have hmeas := measurable_sphere_sections (measurableSet_densityOne hE) c
  have hm := hmeas.aemeasurable (μ := volume.restrict (Ioo 0 r))
  have ht := integral_toReal hm
    (Eventually.of_forall fun t => hausdorffMeasure2_spherical_section_lt_top E c t)
  simpa only [hs, radialVolume, radialSectionArea] using ht.symm

@[simp]
lemma radialVolume_zero (E : Set AmbientSpace) (c : AmbientSpace) :
    radialVolume E c 0 = 0 := by simp [radialVolume]

lemma radialVolume_nonneg (E : Set AmbientSpace) (c : AmbientSpace) (r : ℝ) :
    0 ≤ radialVolume E c r := ENNReal.toReal_nonneg

lemma radialVolume_eq_intervalIntegral {E : Set AmbientSpace}
    (hE : NullMeasurableSet E volume) (c : AmbientSpace) {r : ℝ} (hr : 0 ≤ r) :
    radialVolume E c r = ∫ t in 0..r, radialSectionArea E c t := by
  rw [radialVolume_eq_integral hE, intervalIntegral.integral_of_le hr,
    integral_Ioc_eq_integral_Ioo]

lemma intervalIntegrable_radialSectionArea {E : Set AmbientSpace}
    (hE : NullMeasurableSet E volume) (c : AmbientSpace) (a b : ℝ) :
    IntervalIntegrable (radialSectionArea E c) volume a b := by
  have hi := (locallyIntegrable_radialSectionArea hE c).integrableOn_isCompact
    (k := uIcc a b) isCompact_uIcc
  exact intervalIntegrable_iff.mpr (hi.mono_set uIoc_subset_uIcc)

/-- Radial volume is Lipschitz on each bounded nonnegative radius interval. -/
theorem lipschitzOnWith_radialVolume {E : Set AmbientSpace}
    (hE : NullMeasurableSet E volume) (c : AmbientSpace) (R : ℝ) :
    LipschitzOnWith (⟨4 * Real.pi * R ^ 2, by positivity⟩ : ℝ≥0)
      (radialVolume E c) (Icc 0 R) := by
  apply LipschitzOnWith.of_dist_le_mul
  intro a ha b hb
  rw [Real.dist_eq, Real.dist_eq,
    radialVolume_eq_intervalIntegral hE c ha.1,
    radialVolume_eq_intervalIntegral hE c hb.1,
    intervalIntegral.integral_interval_sub_left
      (intervalIntegrable_radialSectionArea hE c 0 a)
      (intervalIntegrable_radialSectionArea hE c 0 b)]
  change ‖∫ t in b..a, radialSectionArea E c t‖ ≤ (4 * Real.pi * R ^ 2) * |a - b|
  apply intervalIntegral.norm_integral_le_of_norm_le_const
  intro t ht
  have ht0 : 0 ≤ t := (le_min hb.1 ha.1).trans ht.1.le
  have htR : t ≤ R := ht.2.trans (max_le hb.2 ha.2)
  rw [Real.norm_of_nonneg (radialSectionArea_nonneg E c t)]
  exact (radialSectionArea_le E c t).trans
    (mul_le_mul_of_nonneg_left (pow_le_pow_left₀ ht0 htR 2) (by positivity))

/-- The genuine radial derivative is the area of the density-one spherical section. -/
theorem ae_hasDerivAt_radialVolume {E : Set AmbientSpace}
    (hE : NullMeasurableSet E volume) (c : AmbientSpace) :
    ∀ᵐ r : ℝ, 0 < r → HasDerivAt (radialVolume E c) (radialSectionArea E c r) r := by
  filter_upwards [LocallyIntegrable.ae_hasDerivAt_integral
    (locallyIntegrable_radialSectionArea hE c)]
    with r hr
  intro hrpos
  apply (hr 0).congr_of_eventuallyEq
  filter_upwards [Ioi_mem_nhds hrpos] with t ht
  exact radialVolume_eq_intervalIntegral hE c ht.le

lemma ae_deriv_radialVolume {E : Set AmbientSpace}
    (hE : NullMeasurableSet E volume) (c : AmbientSpace) :
    ∀ᵐ r : ℝ, 0 < r → deriv (radialVolume E c) r = radialSectionArea E c r := by
  filter_upwards [ae_hasDerivAt_radialVolume hE c] with r hr
  exact fun hrpos => (hr hrpos).deriv

end LiquidDrop

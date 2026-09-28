import NoCompromise.DeGiorgi.PolarDifferentiation

/-!
# Transporting a locally integrable vector density

The norm of a vector density defines a locally finite positive measure. A
homeomorphism transports that measure and its normalized field, preserving the
vector pairing. These statements do not require finite total mass or a
nonvanishing density everywhere.
-/

noncomputable section
open MeasureTheory Set Filter Metric
open scoped Topology ENNReal
namespace LiquidDrop

/-- Positive measure associated to the norm of a vector density. -/
def weightedPolarMeasure (μ : Measure AmbientSpace) (w : AmbientSpace → AmbientSpace) :
    Measure AmbientSpace := μ.withDensity (fun x => ENNReal.ofReal ‖w x‖)

/-- The positive variation candidate after a homeomorphism. -/
def transportedPolarMeasure (Φ : AmbientSpace ≃ₜ AmbientSpace)
    (μ : Measure AmbientSpace) (w : AmbientSpace → AmbientSpace) : Measure AmbientSpace :=
  Measure.map Φ (weightedPolarMeasure μ w)

/-- Normalized vector density in the target coordinates. It is zero where the input is zero. -/
def transportedUnitPolar (Φ : AmbientSpace ≃ₜ AmbientSpace)
    (w : AmbientSpace → AmbientSpace) (y : AmbientSpace) : AmbientSpace :=
  ‖w (Φ.symm y)‖⁻¹ • w (Φ.symm y)

lemma measurable_transportedUnitPolar (Φ : AmbientSpace ≃ₜ AmbientSpace)
    {w : AmbientSpace → AmbientSpace} (hw : Measurable w) :
    Measurable (transportedUnitPolar Φ w) :=
  ((hw.comp Φ.symm.continuous.measurable).norm.inv).smul
    (hw.comp Φ.symm.continuous.measurable)

lemma weightedPolarMeasure_finiteOnCompacts (μ : Measure AmbientSpace)
    {w : AmbientSpace → AmbientSpace} (hw : LocallyIntegrable w μ) :
    IsFiniteMeasureOnCompacts (weightedPolarMeasure μ w) := by
  constructor
  intro K hK
  rw [weightedPolarMeasure, withDensity_apply _ hK.measurableSet]
  exact (hasFiniteIntegral_iff_norm _).mp (hw.integrableOn_isCompact hK).hasFiniteIntegral

lemma transportedPolarMeasure_regular (Φ : AmbientSpace ≃ₜ AmbientSpace)
    (μ : Measure AmbientSpace) {w : AmbientSpace → AmbientSpace} (hw : LocallyIntegrable w μ) :
    (transportedPolarMeasure Φ μ w).Regular := by
  let := weightedPolarMeasure_finiteOnCompacts μ hw
  let : (weightedPolarMeasure μ w).Regular := inferInstance
  exact Measure.Regular.map Φ

/-- The normalized transported field is a unit vector almost everywhere
for the transported measure. -/
theorem norm_transportedUnitPolar_ae (Φ : AmbientSpace ≃ₜ AmbientSpace)
    (μ : Measure AmbientSpace) {w : AmbientSpace → AmbientSpace} (hw : Measurable w) :
    ∀ᵐ y ∂transportedPolarMeasure Φ μ w, ‖transportedUnitPolar Φ w y‖ = 1 := by
  rw [transportedPolarMeasure, Φ.measurableEmbedding.ae_map_iff]
  simp only [transportedUnitPolar, Φ.symm_apply_apply]
  rw [weightedPolarMeasure, ae_withDensity_iff hw.norm.ennreal_ofReal]
  filter_upwards [] with x hx
  apply norm_smul_inv_norm
  intro hzero
  simp [hzero] at hx

/-- Borel image masses are the exact weighted masses in source coordinates. -/
theorem transportedPolarMeasure_image (Φ : AmbientSpace ≃ₜ AmbientSpace)
    (μ : Measure AmbientSpace) (w : AmbientSpace → AmbientSpace)
    {A : Set AmbientSpace} (hA : MeasurableSet A) :
    transportedPolarMeasure Φ μ w (Φ '' A) = ∫⁻ x in A, ENNReal.ofReal ‖w x‖ ∂μ := by
  rw [transportedPolarMeasure, Φ.measurableEmbedding.map_apply,
    Set.preimage_image_eq _ Φ.injective, weightedPolarMeasure,
    withDensity_apply _ hA]

/-- Vector pairing is unchanged by weighting, normalization, and a homeomorphism. -/
theorem integral_inner_transportedUnitPolar (Φ : AmbientSpace ≃ₜ AmbientSpace)
    (μ : Measure AmbientSpace) {w : AmbientSpace → AmbientSpace} (hw : Measurable w)
    (X : AmbientSpace → AmbientSpace) :
    (∫ y, inner ℝ (X y) (transportedUnitPolar Φ w y) ∂transportedPolarMeasure Φ μ w) =
      ∫ x, inner ℝ (X (Φ x)) (w x) ∂μ := by
  rw [transportedPolarMeasure, Φ.measurableEmbedding.integral_map, weightedPolarMeasure,
    integral_withDensity_eq_integral_toReal_smul hw.norm.ennreal_ofReal
      (Eventually.of_forall fun _ => ENNReal.ofReal_lt_top)]
  apply integral_congr_ae
  filter_upwards [] with x
  simp only [transportedUnitPolar, Φ.symm_apply_apply,
    ENNReal.toReal_ofReal (norm_nonneg _), smul_eq_mul, inner_smul_right]
  by_cases hx : w x = 0
  · simp [hx]
  · rw [← mul_assoc, mul_inv_cancel₀ (norm_ne_zero_iff.mpr hx), one_mul]

/-- A continuous linear field applied to a measurable unit vector field is locally integrable. -/
lemma locallyIntegrable_continuous_linear_apply_unit
    (μ : Measure AmbientSpace) [IsLocallyFiniteMeasure μ]
    {C : AmbientSpace → AmbientSpace →L[ℝ] AmbientSpace}
    {ν : AmbientSpace → AmbientSpace} (hC : Continuous C) (hν : Measurable ν)
    (hnorm : ∀ᵐ x ∂μ, ‖ν x‖ = 1) : LocallyIntegrable (fun x => C x (ν x)) μ := by
  apply locallyIntegrable_iff.mpr
  intro K hK
  have hm : Measurable (fun x => C x (ν x)) := by fun_prop
  apply (hC.norm.continuousOn.integrableOn_compact hK).mono'
    hm.aestronglyMeasurable.restrict
  filter_upwards [ae_restrict_of_ae hnorm] with x hx
  simpa only [hx, mul_one] using (C x).le_opNorm (ν x)

end LiquidDrop

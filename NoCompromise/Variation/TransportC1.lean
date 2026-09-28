import NoCompromise.Variation.TransportC1Pairing
import Mathlib.Data.Real.Sign

/-!
# Perimeter and normal transport under global C¹ diffeomorphisms

The C¹ distributional pairing constructs the actual image polar. Its measure is
cofactor-weighted source perimeter, and its unit field is the transported normal.
No second derivative of the diffeomorphism is used.
-/

noncomputable section
open MeasureTheory Set Filter Metric
open scoped Topology ENNReal Gradient
namespace LiquidDrop

/-- The complete ambient perimeter polar after a C¹ homeomorphism of fixed orientation. -/
theorem ambientOutwardPerimeterPolar_image_C1
    (Φ : AmbientSpace ≃ₜ AmbientSpace) (hΦ : ContDiff ℝ 1 Φ)
    (hiΦ : ContDiff ℝ 1 Φ.symm)
    (E : Set AmbientSpace) (hE : HasLocallyFinitePerimeter E) (hmE : NullMeasurableSet E volume)
    (s : ℝ) (hsgn : ∀ x, |(fderiv ℝ Φ x).det| = s * (fderiv ℝ Φ x).det) :
    IsAmbientOutwardPerimeterPolar (Φ '' E)
      (transportedPolarMeasure Φ (canonicalPerimeterMeasure E hE hmE)
        (cofactorTransportDensity Φ s E hE hmE))
      (transportedUnitPolar Φ (cofactorTransportDensity Φ s E hE hmE)) := by
  let μ := canonicalPerimeterMeasure E hE hmE
  let w := cofactorTransportDensity Φ s E hE hmE
  have hm : Measurable w := measurable_cofactorTransportDensity hΦ s E hE hmE
  have hi : LocallyIntegrable w μ :=
    locallyIntegrable_cofactorTransportDensity hΦ s E hE hmE
  let := transportedPolarMeasure_regular Φ μ hi
  apply ambientOutwardPerimeterPolar_of_divergence_pairing
    (nullMeasurableSet_image_of_differentiable (hΦ.differentiable one_ne_zero) Φ.injective hmE)
    (measurable_transportedUnitPolar Φ hm) (norm_transportedUnitPolar_ae Φ μ hm)
  intro X hX hcX
  rw [integral_inner_transportedUnitPolar Φ μ hm X]
  exact (canonicalPerimeterPolar E hE hmE).integral_image_divergence_C1
    hmE Φ hΦ hiΦ hX hcX hsgn

/-- C¹ homeomorphic transport with fixed orientation preserves local finite perimeter. -/
theorem hasLocallyFinitePerimeter_image_C1
    (Φ : AmbientSpace ≃ₜ AmbientSpace) (hΦ : ContDiff ℝ 1 Φ)
    (hiΦ : ContDiff ℝ 1 Φ.symm)
    (E : Set AmbientSpace) (hE : HasLocallyFinitePerimeter E) (hmE : NullMeasurableSet E volume)
    (s : ℝ) (hsgn : ∀ x, |(fderiv ℝ Φ x).det| = s * (fderiv ℝ Φ x).det) :
    HasLocallyFinitePerimeter (Φ '' E) :=
  (ambientOutwardPerimeterPolar_image_C1 Φ hΦ hiΦ E hE hmE s hsgn).hasLocallyFinitePerimeter

/-- The exact perimeter transport formula on Borel images for a C¹ homeomorphism. -/
theorem perimeter_transport_C1
    (Φ : AmbientSpace ≃ₜ AmbientSpace) (hΦ : ContDiff ℝ 1 Φ)
    (hiΦ : ContDiff ℝ 1 Φ.symm)
    (E : Set AmbientSpace) (hE : HasLocallyFinitePerimeter E) (hmE : NullMeasurableSet E volume)
    (hF : HasLocallyFinitePerimeter (Φ '' E)) (hmF : NullMeasurableSet (Φ '' E) volume)
    {s : ℝ} (hs : |s| = 1)
    (hsgn : ∀ x, |(fderiv ℝ Φ x).det| = s * (fderiv ℝ Φ x).det)
    {A : Set AmbientSpace} (hA : MeasurableSet A) :
    canonicalPerimeterMeasure (Φ '' E) hF hmF (Φ '' A) =
      ∫⁻ x in A, ENNReal.ofReal ‖cofactor3 (fderiv ℝ Φ x)
        (canonicalOutwardPolarDensity E hE hmE x)‖
        ∂canonicalPerimeterMeasure E hE hmE := by
  have hp := ambientOutwardPerimeterPolar_image_C1 Φ hΦ hiΦ E hE hmE s hsgn
  rw [hp.canonicalPerimeterMeasure_eq hF hmF, transportedPolarMeasure_image Φ _ _ hA]
  apply setLIntegral_congr_fun hA
  intro x _
  simp only [cofactorTransportDensity, norm_smul, Real.norm_eq_abs, hs, one_mul]

/-- The C¹ Borel-image formula in the blueprint's reduced-boundary area convention. -/
theorem perimeter_transport_C1_reducedBoundary
    (Φ : AmbientSpace ≃ₜ AmbientSpace) (hΦ : ContDiff ℝ 1 Φ)
    (hiΦ : ContDiff ℝ 1 Φ.symm)
    (E : Set AmbientSpace) (hE : HasLocallyFinitePerimeter E) (hmE : NullMeasurableSet E volume)
    (hF : HasLocallyFinitePerimeter (Φ '' E)) (hmF : NullMeasurableSet (Φ '' E) volume)
    {s : ℝ} (hs : |s| = 1)
    (hsgn : ∀ x, |(fderiv ℝ Φ x).det| = s * (fderiv ℝ Φ x).det)
    {A : Set AmbientSpace} (hA : MeasurableSet A) :
    canonicalPerimeterMeasure (Φ '' E) hF hmF (Φ '' A) =
      ∫⁻ x in A ∩ reducedBoundary E hE hmE,
        ENNReal.ofReal ‖cofactor3 (fderiv ℝ Φ x)
          (reducedNormal E hE hmE x)‖ ∂hausdorffMeasure2 3 := by
  rw [perimeter_transport_C1 Φ hΦ hiΦ E hE hmE hF hmF hs hsgn hA]
  have hν := reducedNormal_ae_eq_polarDensity E hE hmE
  have heq : (∫⁻ x in A, ENNReal.ofReal ‖cofactor3 (fderiv ℝ Φ x)
      (canonicalOutwardPolarDensity E hE hmE x)‖
      ∂canonicalPerimeterMeasure E hE hmE) =
      ∫⁻ x in A, ENNReal.ofReal ‖cofactor3 (fderiv ℝ Φ x)
        (reducedNormal E hE hmE x)‖
        ∂canonicalPerimeterMeasure E hE hmE := by
    apply lintegral_congr_ae
    filter_upwards [ae_restrict_of_ae hν] with x hx
    rw [hx]
  rw [heq, canonicalPerimeterMeasure_eq_reducedBoundary_area E hE hmE,
    Measure.restrict_restrict hA]

/-- The transported unit field is the actual reduced normal almost everywhere
for the perimeter measure of the image. -/
theorem reducedNormal_image_C1_ae
    (Φ : AmbientSpace ≃ₜ AmbientSpace) (hΦ : ContDiff ℝ 1 Φ)
    (hiΦ : ContDiff ℝ 1 Φ.symm)
    (E : Set AmbientSpace) (hE : HasLocallyFinitePerimeter E) (hmE : NullMeasurableSet E volume)
    (hF : HasLocallyFinitePerimeter (Φ '' E)) (hmF : NullMeasurableSet (Φ '' E) volume)
    (s : ℝ) (hsgn : ∀ x, |(fderiv ℝ Φ x).det| = s * (fderiv ℝ Φ x).det) :
    reducedNormal (Φ '' E) hF hmF =ᵐ[canonicalPerimeterMeasure (Φ '' E) hF hmF]
      transportedUnitPolar Φ (cofactorTransportDensity Φ s E hE hmE) := by
  have hp := ambientOutwardPerimeterPolar_image_C1 Φ hΦ hiΦ E hE hmE s hsgn
  have hν := hp.ae_eq_canonicalOutwardPolarDensity hF hmF
  rw [← hp.canonicalPerimeterMeasure_eq hF hmF] at hν
  exact (reducedNormal_ae_eq_polarDensity (Φ '' E) hF hmF).trans hν.symm

/-- At almost every source reduced point, the image normal is the signed normalized cofactor. -/
theorem reducedNormal_image_C1_ae_source
    (Φ : AmbientSpace ≃ₜ AmbientSpace) (hΦ : ContDiff ℝ 1 Φ)
    (hiΦ : ContDiff ℝ 1 Φ.symm)
    (E : Set AmbientSpace) (hE : HasLocallyFinitePerimeter E) (hmE : NullMeasurableSet E volume)
    (hF : HasLocallyFinitePerimeter (Φ '' E)) (hmF : NullMeasurableSet (Φ '' E) volume)
    {s : ℝ} (hs : |s| = 1)
    (hsgn : ∀ x, |(fderiv ℝ Φ x).det| = s * (fderiv ℝ Φ x).det)
    (hdet : ∀ x, (fderiv ℝ Φ x).det ≠ 0) :
    ∀ᵐ x ∂canonicalPerimeterMeasure E hE hmE,
      reducedNormal (Φ '' E) hF hmF (Φ x) =
        s • (‖cofactor3 (fderiv ℝ Φ x) (reducedNormal E hE hmE x)‖⁻¹ •
          cofactor3 (fderiv ℝ Φ x) (reducedNormal E hE hmE x)) := by
  let μ := canonicalPerimeterMeasure E hE hmE
  let w := cofactorTransportDensity Φ s E hE hmE
  have hm : Measurable w :=
    measurable_cofactorTransportDensity (hΦ) s E hE hmE
  have hs0 : s ≠ 0 := by intro hz; simp [hz] at hs
  have hnonzero : ∀ᵐ x ∂μ, ENNReal.ofReal ‖w x‖ ≠ 0 := by
    filter_upwards [(canonicalPerimeterPolar E hE hmE).norm_ae] with x hx
    have hn : canonicalOutwardPolarDensity E hE hmE x ≠ 0 := by
      intro hz
      simp [hz] at hx
    have hc : cofactor3 (fderiv ℝ Φ x)
        (canonicalOutwardPolarDensity E hE hmE x) ≠ 0 := by
      simpa only [map_zero] using (cofactor3_injective_of_det_ne_zero _ (hdet x)).ne hn
    have hw : w x ≠ 0 := smul_ne_zero hs0 hc
    exact (ENNReal.ofReal_pos.mpr (norm_pos_iff.mpr hw)).ne'
  have hac : μ ≪ weightedPolarMeasure μ w :=
    withDensity_absolutelyContinuous' hm.norm.ennreal_ofReal.aemeasurable hnonzero
  have hp := ambientOutwardPerimeterPolar_image_C1 Φ hΦ hiΦ E hE hmE s hsgn
  have hn := reducedNormal_image_C1_ae Φ hΦ hiΦ E hE hmE hF hmF s hsgn
  rw [hp.canonicalPerimeterMeasure_eq hF hmF] at hn
  change ∀ᵐ y ∂Measure.map Φ (weightedPolarMeasure μ w),
    reducedNormal (Φ '' E) hF hmF y = transportedUnitPolar Φ w y at hn
  rw [Φ.measurableEmbedding.ae_map_iff] at hn
  filter_upwards [hac.ae_le hn,
    reducedNormal_ae_eq_polarDensity E hE hmE] with x hx hν
  rw [hx]
  simp only [transportedUnitPolar, Φ.symm_apply_apply, w, cofactorTransportDensity,
    norm_smul, Real.norm_eq_abs, hs, one_mul, hν, smul_comm s]

/-- Every global C¹ diffeomorphism preserves locally finite perimeter. -/
theorem hasLocallyFinitePerimeter_image_of_C1_diffeomorphism
    (Φ : AmbientSpace ≃ₜ AmbientSpace) (hΦ : ContDiff ℝ 1 Φ)
    (hiΦ : ContDiff ℝ 1 Φ.symm) (E : Set AmbientSpace)
    (hE : HasLocallyFinitePerimeter E) (hmE : NullMeasurableSet E volume) :
    HasLocallyFinitePerimeter (Φ '' E) := by
  obtain ⟨s, _, hs⟩ := exists_fixed_orientation_of_continuous_det hΦ
    (det_fderiv_ne_zero_of_differentiable_inverse Φ
      (hΦ.differentiable one_ne_zero) (hiΦ.differentiable one_ne_zero))
  exact hasLocallyFinitePerimeter_image_C1 Φ hΦ hiΦ E hE hmE s hs

/-- Exact Borel-image perimeter for global C¹ diffeomorphisms, without an
orientation premise. -/
theorem perimeter_transport_of_C1_diffeomorphism
    (Φ : AmbientSpace ≃ₜ AmbientSpace) (hΦ : ContDiff ℝ 1 Φ)
    (hiΦ : ContDiff ℝ 1 Φ.symm) (E : Set AmbientSpace)
    (hE : HasLocallyFinitePerimeter E) (hmE : NullMeasurableSet E volume)
    (hF : HasLocallyFinitePerimeter (Φ '' E)) (hmF : NullMeasurableSet (Φ '' E) volume)
    {A : Set AmbientSpace} (hA : MeasurableSet A) :
    canonicalPerimeterMeasure (Φ '' E) hF hmF (Φ '' A) =
      ∫⁻ x in A ∩ reducedBoundary E hE hmE,
        ENNReal.ofReal ‖cofactor3 (fderiv ℝ Φ x)
          (reducedNormal E hE hmE x)‖ ∂hausdorffMeasure2 3 := by
  obtain ⟨s, hs, hsgn⟩ := exists_fixed_orientation_of_continuous_det hΦ
    (det_fderiv_ne_zero_of_differentiable_inverse Φ
      (hΦ.differentiable one_ne_zero) (hiΦ.differentiable one_ne_zero))
  exact perimeter_transport_C1_reducedBoundary Φ hΦ hiΦ E hE hmE hF hmF hs hsgn hA

/-- The reduced-normal transformation with the actual determinant sign,
almost everywhere for source boundary area. -/
theorem reducedNormal_image_of_C1_diffeomorphism
    (Φ : AmbientSpace ≃ₜ AmbientSpace) (hΦ : ContDiff ℝ 1 Φ)
    (hiΦ : ContDiff ℝ 1 Φ.symm) (E : Set AmbientSpace)
    (hE : HasLocallyFinitePerimeter E) (hmE : NullMeasurableSet E volume)
    (hF : HasLocallyFinitePerimeter (Φ '' E)) (hmF : NullMeasurableSet (Φ '' E) volume) :
    ∀ᵐ x ∂(hausdorffMeasure2 3).restrict (reducedBoundary E hE hmE),
      reducedNormal (Φ '' E) hF hmF (Φ x) =
        Real.sign (fderiv ℝ Φ x).det •
          (‖cofactor3 (fderiv ℝ Φ x) (reducedNormal E hE hmE x)‖⁻¹ •
            cofactor3 (fderiv ℝ Φ x) (reducedNormal E hE hmE x)) := by
  have hdet := det_fderiv_ne_zero_of_differentiable_inverse Φ
    (hΦ.differentiable one_ne_zero) (hiΦ.differentiable one_ne_zero)
  obtain ⟨s, hs, hsgn⟩ := exists_fixed_orientation_of_continuous_det hΦ hdet
  have hsign (x : AmbientSpace) : s = Real.sign (fderiv ℝ Φ x).det := by
    rcases lt_or_gt_of_ne (hdet x) with hn | hp
    · rw [Real.sign_of_neg hn]
      have hd := hsgn x
      rw [abs_of_neg hn] at hd
      nlinarith
    · rw [Real.sign_of_pos hp]
      have hd := hsgn x
      rw [abs_of_pos hp] at hd
      nlinarith
  have hn := reducedNormal_image_C1_ae_source Φ hΦ hiΦ E hE hmE hF hmF hs hsgn hdet
  rw [canonicalPerimeterMeasure_eq_reducedBoundary_area E hE hmE] at hn
  filter_upwards [hn] with x hx
  simpa only [hsign x] using hx

end LiquidDrop

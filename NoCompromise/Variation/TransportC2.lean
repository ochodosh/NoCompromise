module

public import NoCompromise.Variation.PiolaPullback
public import NoCompromise.Variation.StraightCofactor
public import NoCompromise.DeGiorgi.AmbientPolar
public import NoCompromise.Measure.PolarTransport

@[expose] public section


/-!
# Perimeter and normal transport under global C² diffeomorphisms

The Piola pullback pairing constructs an actual image perimeter polar by
transporting the source cofactor density. The image has locally finite perimeter;
Borel image masses are exactly the cofactor-weighted reduced-boundary area, and
the image normal is the signed normalized cofactor at almost every source point.
A differentiable inverse supplies nonzero determinants, and connectedness gives
a fixed orientation sign. The local C¹ transport theorem remains a separate step.
-/

noncomputable section
open MeasureTheory Set Filter Metric
open scoped Topology ENNReal Gradient
namespace LiquidDrop

lemma ambientOutwardPerimeterPolar_of_divergence_pairing
    {E : Set AmbientSpace} {μ : Measure AmbientSpace} [μ.Regular]
    {ν : AmbientSpace → AmbientSpace} (hmE : NullMeasurableSet E volume)
    (hν : Measurable ν) (hnorm : ∀ᵐ x ∂μ, ‖ν x‖ = 1)
    (hdiv : ∀ X : AmbientSpace → AmbientSpace, ContDiff ℝ 1 X → HasCompactSupport X →
      (∫ x in E, divergenceN X x) = ∫ x, inner ℝ (X x) (ν x) ∂μ) :
    IsAmbientOutwardPerimeterPolar E μ ν := by
  apply ambientOutwardPerimeterPolar_of_coordinate_pairing hmE hν hnorm
  intro i φ hφ
  let X (x : AmbientSpace) : AmbientSpace := φ x • EuclideanSpace.single i 1
  have hX : ContDiff ℝ 1 X := hφ.smul contDiff_const
  have hcX : HasCompactSupport X := φ.hasCompactSupport.smul_right
  have heq := hdiv X hX hcX
  have hd (x) : divergenceN X x = fderiv ℝ φ x (EuclideanSpace.single i 1) := by
    change divergenceN (fun y => φ y • EuclideanSpace.single i 1) x = _
    simp [divergenceN, fderiv_smul_const (hφ.differentiable one_ne_zero x)]
  have hleft : (fun x => E.indicator (fun _ => (1 : ℝ)) x *
      fderiv ℝ φ x (EuclideanSpace.single i 1)) =
      E.indicator (fun x => fderiv ℝ φ x (EuclideanSpace.single i 1)) := by
    funext x
    by_cases hx : x ∈ E <;> simp [hx]
  rw [hleft, integral_indicator₀ hmE]
  simp only [hd, X, real_inner_smul_left, EuclideanSpace.inner_single_left,
    one_mul, conj_trivial] at heq
  rw [heq]
  simp only [mul_neg, integral_neg]

/-- Source vector density for the cofactor transport with a fixed orientation sign. -/
def cofactorTransportDensity (Φ : AmbientSpace → AmbientSpace) (s : ℝ)
    (E : Set AmbientSpace) (hE : HasLocallyFinitePerimeter E)
    (hmE : NullMeasurableSet E volume) (x : AmbientSpace) : AmbientSpace :=
  s • cofactor3 (fderiv ℝ Φ x) (canonicalOutwardPolarDensity E hE hmE x)

lemma measurable_cofactorTransportDensity
    {Φ : AmbientSpace → AmbientSpace} (hΦ : ContDiff ℝ 1 Φ) (s : ℝ)
    (E : Set AmbientSpace) (hE : HasLocallyFinitePerimeter E)
    (hmE : NullMeasurableSet E volume) : Measurable (cofactorTransportDensity Φ s E hE hmE) := by
  let C (x : AmbientSpace) := cofactor3 (fderiv ℝ Φ x)
  have hC : Continuous C := continuous_cofactor3.comp (hΦ.continuous_fderiv one_ne_zero)
  have hν := (canonicalPerimeterPolar E hE hmE).measurable
  have hw : Measurable (fun x => C x (canonicalOutwardPolarDensity E hE hmE x)) := by fun_prop
  exact (measurable_const (a := s)).smul hw

lemma locallyIntegrable_cofactorTransportDensity
    {Φ : AmbientSpace → AmbientSpace} (hΦ : ContDiff ℝ 1 Φ) (s : ℝ)
    (E : Set AmbientSpace) (hE : HasLocallyFinitePerimeter E)
    (hmE : NullMeasurableSet E volume) :
    LocallyIntegrable (cofactorTransportDensity Φ s E hE hmE)
      (canonicalPerimeterMeasure E hE hmE) := by
  have h := canonicalPerimeterPolar E hE hmE
  let := h.finiteOnCompacts
  have hi := locallyIntegrable_continuous_linear_apply_unit _
    (continuous_cofactor3.comp (hΦ.continuous_fderiv one_ne_zero)) h.measurable h.norm_ae
  exact hi.smul s

/-- The complete ambient perimeter polar after a C² homeomorphism of fixed orientation. -/
theorem ambientOutwardPerimeterPolar_image_C2
    (Φ : AmbientSpace ≃ₜ AmbientSpace) (hΦ : ContDiff ℝ 2 Φ)
    (E : Set AmbientSpace) (hE : HasLocallyFinitePerimeter E) (hmE : MeasurableSet E)
    (s : ℝ) (hsgn : ∀ x ∈ E, |(fderiv ℝ Φ x).det| = s * (fderiv ℝ Φ x).det) :
    IsAmbientOutwardPerimeterPolar (Φ '' E)
      (transportedPolarMeasure Φ (canonicalPerimeterMeasure E hE hmE.nullMeasurableSet)
        (cofactorTransportDensity Φ s E hE hmE.nullMeasurableSet))
      (transportedUnitPolar Φ (cofactorTransportDensity Φ s E hE hmE.nullMeasurableSet)) := by
  let μ := canonicalPerimeterMeasure E hE hmE.nullMeasurableSet
  let w := cofactorTransportDensity Φ s E hE hmE.nullMeasurableSet
  have hΦ1 : ContDiff ℝ 1 Φ := hΦ.of_le (by norm_num)
  have hm : Measurable w := measurable_cofactorTransportDensity hΦ1 s E hE hmE.nullMeasurableSet
  have hi : LocallyIntegrable w μ :=
    locallyIntegrable_cofactorTransportDensity hΦ1 s E hE hmE.nullMeasurableSet
  let := transportedPolarMeasure_regular Φ μ hi
  apply ambientOutwardPerimeterPolar_of_divergence_pairing
    (Φ.measurableEmbedding.measurableSet_image.mpr hmE).nullMeasurableSet
    (measurable_transportedUnitPolar Φ hm) (norm_transportedUnitPolar_ae Φ μ hm)
  intro X hX hcX
  rw [integral_inner_transportedUnitPolar Φ μ hm X,
    integral_image_divergence_eq_piolaPullback hmE (fun x _ => hΦ.contDiffAt)
      Φ.injective.injOn (fun x _ => hX.differentiable one_ne_zero (Φ x)) hsgn,
    (canonicalPerimeterPolar E hE hmE.nullMeasurableSet).divergence_eq
      (piolaPullback Φ X) (contDiff_piolaPullback hΦ hX)
      (hasCompactSupport_piolaPullback Φ hcX), ← integral_const_mul]
  apply integral_congr_ae
  filter_upwards [] with x
  change s * inner ℝ ((cofactor3 (fderiv ℝ Φ x)).adjoint (X (Φ x)))
      (canonicalOutwardPolarDensity E hE hmE.nullMeasurableSet x) =
    inner ℝ (X (Φ x))
      (s • cofactor3 (fderiv ℝ Φ x) (canonicalOutwardPolarDensity E hE hmE.nullMeasurableSet x))
  rw [inner_smul_right, ContinuousLinearMap.adjoint_inner_left]

/-- C² homeomorphic transport with fixed orientation preserves local finite perimeter. -/
theorem hasLocallyFinitePerimeter_image_C2
    (Φ : AmbientSpace ≃ₜ AmbientSpace) (hΦ : ContDiff ℝ 2 Φ)
    (E : Set AmbientSpace) (hE : HasLocallyFinitePerimeter E) (hmE : MeasurableSet E)
    (s : ℝ) (hsgn : ∀ x ∈ E, |(fderiv ℝ Φ x).det| = s * (fderiv ℝ Φ x).det) :
    HasLocallyFinitePerimeter (Φ '' E) :=
  (ambientOutwardPerimeterPolar_image_C2 Φ hΦ E hE hmE s hsgn).hasLocallyFinitePerimeter

/-- The exact perimeter transport formula on Borel images for a C² homeomorphism. -/
theorem perimeter_transport_C2
    (Φ : AmbientSpace ≃ₜ AmbientSpace) (hΦ : ContDiff ℝ 2 Φ)
    (E : Set AmbientSpace) (hE : HasLocallyFinitePerimeter E) (hmE : MeasurableSet E)
    (hF : HasLocallyFinitePerimeter (Φ '' E)) (hmF : NullMeasurableSet (Φ '' E) volume)
    {s : ℝ} (hs : |s| = 1)
    (hsgn : ∀ x ∈ E, |(fderiv ℝ Φ x).det| = s * (fderiv ℝ Φ x).det)
    {A : Set AmbientSpace} (hA : MeasurableSet A) :
    canonicalPerimeterMeasure (Φ '' E) hF hmF (Φ '' A) =
      ∫⁻ x in A, ENNReal.ofReal ‖cofactor3 (fderiv ℝ Φ x)
        (canonicalOutwardPolarDensity E hE hmE.nullMeasurableSet x)‖
        ∂canonicalPerimeterMeasure E hE hmE.nullMeasurableSet := by
  have hp := ambientOutwardPerimeterPolar_image_C2 Φ hΦ E hE hmE s hsgn
  rw [hp.canonicalPerimeterMeasure_eq hF hmF, transportedPolarMeasure_image Φ _ _ hA]
  apply setLIntegral_congr_fun hA
  intro x _
  simp only [cofactorTransportDensity, norm_smul, Real.norm_eq_abs, hs, one_mul]

/-- The C² Borel-image formula in the blueprint's reduced-boundary area convention. -/
theorem perimeter_transport_C2_reducedBoundary
    (Φ : AmbientSpace ≃ₜ AmbientSpace) (hΦ : ContDiff ℝ 2 Φ)
    (E : Set AmbientSpace) (hE : HasLocallyFinitePerimeter E) (hmE : MeasurableSet E)
    (hF : HasLocallyFinitePerimeter (Φ '' E)) (hmF : NullMeasurableSet (Φ '' E) volume)
    {s : ℝ} (hs : |s| = 1)
    (hsgn : ∀ x ∈ E, |(fderiv ℝ Φ x).det| = s * (fderiv ℝ Φ x).det)
    {A : Set AmbientSpace} (hA : MeasurableSet A) :
    canonicalPerimeterMeasure (Φ '' E) hF hmF (Φ '' A) =
      ∫⁻ x in A ∩ reducedBoundary E hE hmE.nullMeasurableSet,
        ENNReal.ofReal ‖cofactor3 (fderiv ℝ Φ x)
          (reducedNormal E hE hmE.nullMeasurableSet x)‖ ∂hausdorffMeasure2 3 := by
  rw [perimeter_transport_C2 Φ hΦ E hE hmE hF hmF hs hsgn hA]
  have hν := reducedNormal_ae_eq_polarDensity E hE hmE.nullMeasurableSet
  have heq : (∫⁻ x in A, ENNReal.ofReal ‖cofactor3 (fderiv ℝ Φ x)
      (canonicalOutwardPolarDensity E hE hmE.nullMeasurableSet x)‖
      ∂canonicalPerimeterMeasure E hE hmE.nullMeasurableSet) =
      ∫⁻ x in A, ENNReal.ofReal ‖cofactor3 (fderiv ℝ Φ x)
        (reducedNormal E hE hmE.nullMeasurableSet x)‖
        ∂canonicalPerimeterMeasure E hE hmE.nullMeasurableSet := by
    apply lintegral_congr_ae
    filter_upwards [ae_restrict_of_ae hν] with x hx
    rw [hx]
  rw [heq, canonicalPerimeterMeasure_eq_reducedBoundary_area E hE hmE.nullMeasurableSet,
    Measure.restrict_restrict hA]

/-- The transported unit field is the actual reduced normal almost everywhere
for the perimeter measure of the image. -/
theorem reducedNormal_image_C2_ae
    (Φ : AmbientSpace ≃ₜ AmbientSpace) (hΦ : ContDiff ℝ 2 Φ)
    (E : Set AmbientSpace) (hE : HasLocallyFinitePerimeter E) (hmE : MeasurableSet E)
    (hF : HasLocallyFinitePerimeter (Φ '' E)) (hmF : NullMeasurableSet (Φ '' E) volume)
    (s : ℝ) (hsgn : ∀ x ∈ E, |(fderiv ℝ Φ x).det| = s * (fderiv ℝ Φ x).det) :
    reducedNormal (Φ '' E) hF hmF =ᵐ[canonicalPerimeterMeasure (Φ '' E) hF hmF]
      transportedUnitPolar Φ (cofactorTransportDensity Φ s E hE hmE.nullMeasurableSet) := by
  have hp := ambientOutwardPerimeterPolar_image_C2 Φ hΦ E hE hmE s hsgn
  have hν := hp.ae_eq_canonicalOutwardPolarDensity hF hmF
  rw [← hp.canonicalPerimeterMeasure_eq hF hmF] at hν
  exact (reducedNormal_ae_eq_polarDensity (Φ '' E) hF hmF).trans hν.symm

lemma adjoint_comp_cofactor3 (L : AmbientSpace →L[ℝ] AmbientSpace) :
    L.adjoint.comp (cofactor3 L) = L.det • ContinuousLinearMap.id ℝ AmbientSpace := by
  suffices h : (L.adjoint.comp (cofactor3 L)).toLinearMap =
      (L.det • ContinuousLinearMap.id ℝ AmbientSpace).toLinearMap by
    exact ContinuousLinearMap.ext (fun x => LinearMap.congr_fun h x)
  apply Matrix.toEuclideanLin.symm.injective
  change (Matrix.toLpLin 2 2).symm
    (L.adjoint.toLinearMap.comp (cofactor3 L).toLinearMap) =
      (Matrix.toLpLin 2 2).symm (L.det • LinearMap.id)
  rw [Matrix.toLpLin_symm_comp]
  change standardMatrix3 L.adjoint * standardMatrix3 (cofactor3 L) = _
  rw [standardMatrix3_adjoint, standardMatrix3_cofactor3,
    ← Matrix.transpose_mul, Matrix.adjugate_mul, Matrix.transpose_smul,
    Matrix.transpose_one, standardMatrix3_det]
  simp [map_smul, Matrix.toLpLin_symm_id]

lemma cofactor3_injective_of_det_ne_zero (L : AmbientSpace →L[ℝ] AmbientSpace)
    (hL : L.det ≠ 0) : Function.Injective (cofactor3 L) := by
  intro u v huv
  have h := congrArg L.adjoint huv
  have heq (z : AmbientSpace) : L.adjoint (cofactor3 L z) = L.det • z :=
    congrArg (fun A : AmbientSpace →L[ℝ] AmbientSpace => A z) (adjoint_comp_cofactor3 L)
  rw [heq, heq] at h
  have hh := congrArg (fun z : AmbientSpace => L.det⁻¹ • z) h
  simpa only [smul_smul, inv_mul_cancel₀ hL, one_smul] using hh

/-- At almost every source reduced point, the image normal is the signed normalized cofactor. -/
theorem reducedNormal_image_C2_ae_source
    (Φ : AmbientSpace ≃ₜ AmbientSpace) (hΦ : ContDiff ℝ 2 Φ)
    (E : Set AmbientSpace) (hE : HasLocallyFinitePerimeter E) (hmE : MeasurableSet E)
    (hF : HasLocallyFinitePerimeter (Φ '' E)) (hmF : NullMeasurableSet (Φ '' E) volume)
    {s : ℝ} (hs : |s| = 1)
    (hsgn : ∀ x ∈ E, |(fderiv ℝ Φ x).det| = s * (fderiv ℝ Φ x).det)
    (hdet : ∀ x, (fderiv ℝ Φ x).det ≠ 0) :
    ∀ᵐ x ∂canonicalPerimeterMeasure E hE hmE.nullMeasurableSet,
      reducedNormal (Φ '' E) hF hmF (Φ x) =
        s • (‖cofactor3 (fderiv ℝ Φ x) (reducedNormal E hE hmE.nullMeasurableSet x)‖⁻¹ •
          cofactor3 (fderiv ℝ Φ x) (reducedNormal E hE hmE.nullMeasurableSet x)) := by
  let μ := canonicalPerimeterMeasure E hE hmE.nullMeasurableSet
  let w := cofactorTransportDensity Φ s E hE hmE.nullMeasurableSet
  have hm : Measurable w :=
    measurable_cofactorTransportDensity (hΦ.of_le (by norm_num)) s E hE hmE.nullMeasurableSet
  have hs0 : s ≠ 0 := by intro hz; simp [hz] at hs
  have hnonzero : ∀ᵐ x ∂μ, ENNReal.ofReal ‖w x‖ ≠ 0 := by
    filter_upwards [(canonicalPerimeterPolar E hE hmE.nullMeasurableSet).norm_ae] with x hx
    have hn : canonicalOutwardPolarDensity E hE hmE.nullMeasurableSet x ≠ 0 := by
      intro hz
      simp [hz] at hx
    have hc : cofactor3 (fderiv ℝ Φ x)
        (canonicalOutwardPolarDensity E hE hmE.nullMeasurableSet x) ≠ 0 := by
      simpa only [map_zero] using (cofactor3_injective_of_det_ne_zero _ (hdet x)).ne hn
    have hw : w x ≠ 0 := smul_ne_zero hs0 hc
    exact (ENNReal.ofReal_pos.mpr (norm_pos_iff.mpr hw)).ne'
  have hac : μ ≪ weightedPolarMeasure μ w :=
    withDensity_absolutelyContinuous' hm.norm.ennreal_ofReal.aemeasurable hnonzero
  have hp := ambientOutwardPerimeterPolar_image_C2 Φ hΦ E hE hmE s hsgn
  have hn := reducedNormal_image_C2_ae Φ hΦ E hE hmE hF hmF s hsgn
  rw [hp.canonicalPerimeterMeasure_eq hF hmF] at hn
  change ∀ᵐ y ∂Measure.map Φ (weightedPolarMeasure μ w),
    reducedNormal (Φ '' E) hF hmF y = transportedUnitPolar Φ w y at hn
  rw [Φ.measurableEmbedding.ae_map_iff] at hn
  filter_upwards [hac.ae_le hn,
    reducedNormal_ae_eq_polarDensity E hE hmE.nullMeasurableSet] with x hx hν
  rw [hx]
  simp only [transportedUnitPolar, Φ.symm_apply_apply, w, cofactorTransportDensity,
    norm_smul, Real.norm_eq_abs, hs, one_mul, hν, smul_comm s]

lemma det_fderiv_ne_zero_of_differentiable_inverse
    (Φ : AmbientSpace ≃ₜ AmbientSpace) (hΦ : Differentiable ℝ Φ)
    (hΦi : Differentiable ℝ Φ.symm) (x : AmbientSpace) : (fderiv ℝ Φ x).det ≠ 0 := by
  have hh := (hΦi (Φ x)).hasFDerivAt.comp x (hΦ x).hasFDerivAt
  have hid : (Φ.symm : AmbientSpace → AmbientSpace) ∘ Φ = id := by
    funext y
    exact Φ.symm_apply_apply y
  rw [hid] at hh
  have hc := hh.unique (hasFDerivAt_id x)
  have hd := congrArg (fun L : AmbientSpace →L[ℝ] AmbientSpace => L.toLinearMap.det) hc
  change ((fderiv ℝ Φ.symm (Φ x)).toLinearMap.comp (fderiv ℝ Φ x).toLinearMap).det =
    (LinearMap.id : AmbientSpace →ₗ[ℝ] AmbientSpace).det at hd
  rw [LinearMap.det_comp, LinearMap.det_id] at hd
  intro hz
  have hz' : (fderiv ℝ Φ x).toLinearMap.det = 0 := by simpa only using! hz
  rw [hz', mul_zero] at hd
  exact zero_ne_one hd

lemma exists_fixed_orientation_of_continuous_det
    {Φ : AmbientSpace → AmbientSpace} (hΦ : ContDiff ℝ 1 Φ)
    (hdet : ∀ x, (fderiv ℝ Φ x).det ≠ 0) :
    ∃ s : ℝ, |s| = 1 ∧ ∀ x, |(fderiv ℝ Φ x).det| = s * (fderiv ℝ Φ x).det := by
  let d (x : AmbientSpace) := (fderiv ℝ Φ x).det
  have hd : Continuous d := ContinuousLinearMap.continuous_det.comp
    (hΦ.continuous_fderiv one_ne_zero)
  rcases lt_or_gt_of_ne (hdet 0) with hn | hp
  · refine ⟨-1, by norm_num, fun x => ?_⟩
    have hx : d x < 0 := by
      by_contra hx
      obtain ⟨y, hy⟩ := intermediate_value_univ (0 : AmbientSpace) x hd
        (show (0 : ℝ) ∈ Icc (d 0) (d x) from ⟨hn.le, le_of_not_gt hx⟩)
      exact hdet y hy
    rw [abs_of_neg hx]
    ring
  · refine ⟨1, by norm_num, fun x => ?_⟩
    have hx : 0 < d x := by
      by_contra hx
      obtain ⟨y, hy⟩ := intermediate_value_univ x (0 : AmbientSpace) hd
        (show (0 : ℝ) ∈ Icc (d x) (d 0) from ⟨le_of_not_gt hx, hp.le⟩)
      exact hdet y hy
    rw [abs_of_pos hx, one_mul]

/-- No orientation hypothesis is needed when the global C² map has a C¹ inverse. -/
theorem hasLocallyFinitePerimeter_image_of_C2_diffeomorphism
    (Φ : AmbientSpace ≃ₜ AmbientSpace) (hΦ : ContDiff ℝ 2 Φ)
    (hΦi : ContDiff ℝ 1 Φ.symm) (E : Set AmbientSpace)
    (hE : HasLocallyFinitePerimeter E) (hmE : MeasurableSet E) :
    HasLocallyFinitePerimeter (Φ '' E) := by
  obtain ⟨s, _, hs⟩ := exists_fixed_orientation_of_continuous_det
    (hΦ.of_le (by norm_num)) (det_fderiv_ne_zero_of_differentiable_inverse Φ
      (hΦ.differentiable (by norm_num)) (hΦi.differentiable one_ne_zero))
  exact hasLocallyFinitePerimeter_image_C2 Φ hΦ E hE hmE s (fun x _ => hs x)

/-- The exact Borel-image area formula for a global C² diffeomorphism. -/
theorem perimeter_transport_of_C2_diffeomorphism
    (Φ : AmbientSpace ≃ₜ AmbientSpace) (hΦ : ContDiff ℝ 2 Φ)
    (hΦi : ContDiff ℝ 1 Φ.symm) (E : Set AmbientSpace)
    (hE : HasLocallyFinitePerimeter E) (hmE : MeasurableSet E)
    (hF : HasLocallyFinitePerimeter (Φ '' E)) (hmF : NullMeasurableSet (Φ '' E) volume)
    {A : Set AmbientSpace} (hA : MeasurableSet A) :
    canonicalPerimeterMeasure (Φ '' E) hF hmF (Φ '' A) =
      ∫⁻ x in A ∩ reducedBoundary E hE hmE.nullMeasurableSet,
        ENNReal.ofReal ‖cofactor3 (fderiv ℝ Φ x)
          (reducedNormal E hE hmE.nullMeasurableSet x)‖ ∂hausdorffMeasure2 3 := by
  obtain ⟨s, hs, hsgn⟩ := exists_fixed_orientation_of_continuous_det
    (hΦ.of_le (by norm_num)) (det_fderiv_ne_zero_of_differentiable_inverse Φ
      (hΦ.differentiable (by norm_num)) (hΦi.differentiable one_ne_zero))
  exact perimeter_transport_C2_reducedBoundary Φ hΦ E hE hmE hF hmF hs (fun x _ => hsgn x) hA

end LiquidDrop

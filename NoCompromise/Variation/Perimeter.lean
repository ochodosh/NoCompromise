import NoCompromise.Variation.TransportC1
import NoCompromise.Variation.PerimeterJacobian

/-!
# First variation of perimeter

The exact C¹ transport formula identifies local perimeter with the cofactor
area integral. Its uniform quadratic remainder gives the derivative on every
open region of finite perimeter containing the field's support.
-/

noncomputable section
open MeasureTheory Set Filter Metric
open scoped Topology ENNReal
namespace LiquidDrop

lemma perimeterIn_straight_image_eq_cofactor_integral
    (E : Set AmbientSpace) (hE : HasLocallyFinitePerimeter E)
    (hmE : NullMeasurableSet E volume) {X : AmbientSpace → AmbientSpace}
    (hX : ContDiff ℝ 1 X) (hcX : HasCompactSupport X)
    {A : Set AmbientSpace} (hA : IsOpen A) (hXA : tsupport X ⊆ A)
    {t : ℝ} (ht : |t| * ‖straightDerivativeField hX hcX‖ < 1) :
    (perimeterIn (straightPerturbation X t '' E) A).toReal =
      ∫ x in A, ‖cofactor3 (fderiv ℝ (straightPerturbation X t) x)
        (canonicalOutwardPolarDensity E hE hmE x)‖ ∂canonicalPerimeterMeasure E hE hmE := by
  obtain ⟨Φ, heq, hΦ, hiΦ, _, _, _⟩ :=
    straightPerturbation_compactlySupported_diffeomorphism hX hcX ht
  have hcoe : (Φ : AmbientSpace → AmbientSpace) = straightPerturbation X t := funext heq
  have hFA : Φ '' A = A := by
    rw [hcoe]
    exact straightPerturbation_image_eq_self_of_tsupport_subset
      (lipschitzWith_straightDerivativeField hX hcX) ht hXA
  have hF := hasLocallyFinitePerimeter_image_of_C1_diffeomorphism Φ hΦ hiΦ E hE hmE
  have hmF := nullMeasurableSet_image_of_differentiable
    (hΦ.differentiable one_ne_zero) Φ.injective hmE
  obtain ⟨s, hs, hsgn⟩ := exists_fixed_orientation_of_continuous_det hΦ
    (det_fderiv_ne_zero_of_differentiable_inverse Φ
      (hΦ.differentiable one_ne_zero) (hiΦ.differentiable one_ne_zero))
  have hp := perimeter_transport_C1 Φ hΦ hiΦ E hE hmE hF hmF hs hsgn hA.measurableSet
  rw [hFA, canonicalPerimeterMeasure_open _ hF hmF hA, hcoe] at hp
  rw [hp]
  symm
  apply integral_eq_lintegral_of_nonneg_ae (Eventually.of_forall fun x => norm_nonneg _)
  let C (x : AmbientSpace) := cofactor3 (fderiv ℝ (straightPerturbation X t) x)
  have hC : Continuous C := continuous_cofactor3.comp
    ((contDiff_straightPerturbation hX t).continuous_fderiv one_ne_zero)
  have hν := (canonicalPerimeterPolar E hE hmE).measurable
  have hm : Measurable (fun x => C x (canonicalOutwardPolarDensity E hE hmE x)) := by fun_prop
  exact hm.norm.aestronglyMeasurable

/-- Perimeter first variation on every open finite-perimeter region containing
the support of the field. -/
theorem hasDerivAt_perimeterIn_straight_image
    (E : Set AmbientSpace) (hE : HasLocallyFinitePerimeter E)
    (hmE : NullMeasurableSet E volume) {X : AmbientSpace → AmbientSpace}
    (hX : ContDiff ℝ 1 X) (hcX : HasCompactSupport X)
    {A : Set AmbientSpace} (hA : IsOpen A) (hfin : perimeterIn E A < ∞)
    (hXA : tsupport X ⊆ A) :
    HasDerivAt (fun t : ℝ => (perimeterIn (straightPerturbation X t '' E) A).toReal)
      (∫ x in A, tangentialDivergence X (canonicalOutwardPolarDensity E hE hmE) x
        ∂canonicalPerimeterMeasure E hE hmE) 0 := by
  let μ := canonicalPerimeterMeasure E hE hmE
  let ν := canonicalOutwardPolarDensity E hE hmE
  have hp := canonicalPerimeterPolar E hE hmE
  have hfμ : μ A < ∞ := by rwa [hp.open_eq A hA]
  let : IsFiniteMeasure (μ.restrict A) := ⟨by simpa only [Measure.restrict_apply_univ] using hfμ⟩
  have hd := hasDerivAt_integral_straight_cofactor_norm (μ := μ.restrict A)
    hX hcX hp.measurable (ae_restrict_of_ae hp.norm_ae)
  apply hd.congr_of_eventuallyEq
  have hsmall : ∀ᶠ t : ℝ in 𝓝 0, |t| * ‖straightDerivativeField hX hcX‖ < 1 :=
    (continuous_abs.mul_const _).continuousAt.eventually
      (gt_mem_nhds (by simp : |(0 : ℝ)| * ‖straightDerivativeField hX hcX‖ < 1))
  filter_upwards [hsmall] with t ht
  exact perimeterIn_straight_image_eq_cofactor_integral E hE hmE hX hcX hA hXA ht

/-- Canonical perimeter integration agrees with the reduced-normal area convention. -/
lemma integral_tangentialDivergence_perimeter_eq_area
    (E : Set AmbientSpace) (hE : HasLocallyFinitePerimeter E)
    (hmE : NullMeasurableSet E volume) (X : AmbientSpace → AmbientSpace)
    {A : Set AmbientSpace} (hA : MeasurableSet A) :
    (∫ x in A, tangentialDivergence X (canonicalOutwardPolarDensity E hE hmE) x
      ∂canonicalPerimeterMeasure E hE hmE) =
      ∫ x in A ∩ reducedBoundary E hE hmE,
        tangentialDivergence X (reducedNormal E hE hmE) x ∂hausdorffMeasure2 3 := by
  calc
    _ = ∫ x in A, tangentialDivergence X (reducedNormal E hE hmE) x
        ∂canonicalPerimeterMeasure E hE hmE := by
      apply integral_congr_ae
      filter_upwards [ae_restrict_of_ae (reducedNormal_ae_eq_polarDensity E hE hmE)] with x hx
      simp only [tangentialDivergence, hx]
    _ = _ := by
      rw [canonicalPerimeterMeasure_eq_reducedBoundary_area E hE hmE,
        Measure.restrict_restrict hA]

lemma integral_boundary_tangentialDivergence_restrict_eq
    (E : Set AmbientSpace) (hE : HasLocallyFinitePerimeter E)
    (hmE : NullMeasurableSet E volume) {X : AmbientSpace → AmbientSpace}
    {A : Set AmbientSpace} (hA : MeasurableSet A) (hXA : tsupport X ⊆ A) :
    (∫ x in A ∩ reducedBoundary E hE hmE,
      tangentialDivergence X (reducedNormal E hE hmE) x ∂hausdorffMeasure2 3) =
      ∫ x in reducedBoundary E hE hmE,
        tangentialDivergence X (reducedNormal E hE hmE) x ∂hausdorffMeasure2 3 := by
  rw [← Measure.restrict_restrict hA]
  apply setIntegral_eq_integral_of_forall_compl_eq_zero
  intro x hx
  exact tangentialDivergence_eq_zero_of_notMem_tsupport (fun h => hx (hXA h))

/-- The complete local first-variation formula on bounded open regions. -/
theorem first_variation_perimeter
    (E : Set AmbientSpace) (hE : HasLocallyFinitePerimeter E)
    (hmE : NullMeasurableSet E volume) {X : AmbientSpace → AmbientSpace}
    (hX : ContDiff ℝ 1 X) (hcX : HasCompactSupport X)
    {A : Set AmbientSpace} (hA : IsOpen A) (hbA : Bornology.IsBounded A)
    (hXA : tsupport X ⊆ A) :
    HasDerivAt (fun t : ℝ => (perimeterIn (straightPerturbation X t '' E) A).toReal)
      (∫ x in reducedBoundary E hE hmE,
        tangentialDivergence X (reducedNormal E hE hmE) x ∂hausdorffMeasure2 3) 0 := by
  let := (canonicalPerimeterPolar E hE hmE).finiteOnCompacts
  have hfin : perimeterIn E A < ∞ := by
    rw [← canonicalPerimeterMeasure_open E hE hmE hA]
    exact hbA.measure_lt_top
  have h := hasDerivAt_perimeterIn_straight_image E hE hmE hX hcX hA hfin hXA
  rw [integral_tangentialDivergence_perimeter_eq_area E hE hmE X hA.measurableSet,
    integral_boundary_tangentialDivergence_restrict_eq E hE hmE hA.measurableSet hXA] at h
  exact h

/-- Global first variation when total perimeter is finite, using the original
perimeter definition. -/
theorem first_variation_perimeter_global
    (E : Set AmbientSpace) (hE : HasLocallyFinitePerimeter E)
    (hmE : NullMeasurableSet E volume) (hfin : perimeter E < ∞)
    {X : AmbientSpace → AmbientSpace} (hX : ContDiff ℝ 1 X) (hcX : HasCompactSupport X) :
    HasDerivAt (fun t : ℝ => (perimeter (straightPerturbation X t '' E)).toReal)
      (∫ x in reducedBoundary E hE hmE,
        tangentialDivergence X (reducedNormal E hE hmE) x ∂hausdorffMeasure2 3) 0 := by
  have hf : perimeterIn E univ < ∞ := by
    change perimeterN E < ∞
    rwa [perimeterN_eq_perimeter E hmE]
  have hd := hasDerivAt_perimeterIn_straight_image E hE hmE hX hcX isOpen_univ hf
    (subset_univ _)
  rw [integral_tangentialDivergence_perimeter_eq_area E hE hmE X MeasurableSet.univ,
    univ_inter] at hd
  apply hd.congr_of_eventuallyEq
  have hsmall : ∀ᶠ t : ℝ in 𝓝 0, |t| * ‖straightDerivativeField hX hcX‖ < 1 :=
    (continuous_abs.mul_const _).continuousAt.eventually
      (gt_mem_nhds (by simp : |(0 : ℝ)| * ‖straightDerivativeField hX hcX‖ < 1))
  filter_upwards [hsmall] with t ht
  obtain ⟨hi, _⟩ := straightPerturbation_bijective
    (lipschitzWith_straightDerivativeField hX hcX) ht
  have hm := nullMeasurableSet_image_of_differentiable
    ((contDiff_straightPerturbation hX t).differentiable one_ne_zero) hi hmE
  exact congrArg ENNReal.toReal (perimeterN_eq_perimeter _ hm).symm

/-- The straight perturbation preserves every region containing its support
for all sufficiently small parameters. -/
theorem eventually_straight_image_eq_self
    {X : AmbientSpace → AmbientSpace} (hX : ContDiff ℝ 1 X)
    (hcX : HasCompactSupport X) {A : Set AmbientSpace} (hXA : tsupport X ⊆ A) :
    ∀ᶠ t : ℝ in 𝓝 0, straightPerturbation X t '' A = A := by
  have hsmall : ∀ᶠ t : ℝ in 𝓝 0, |t| * ‖straightDerivativeField hX hcX‖ < 1 :=
    (continuous_abs.mul_const _).continuousAt.eventually
      (gt_mem_nhds (by simp : |(0 : ℝ)| * ‖straightDerivativeField hX hcX‖ < 1))
  filter_upwards [hsmall] with t ht
  exact straightPerturbation_image_eq_self_of_tsupport_subset
    (lipschitzWith_straightDerivativeField hX hcX) ht hXA

end LiquidDrop

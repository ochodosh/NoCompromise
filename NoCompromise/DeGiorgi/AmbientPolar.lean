import NoCompromise.DeGiorgi.Reduced
import Mathlib.Analysis.Distribution.AEEqOfIntegralContDiff

/-!
# Constructing ambient perimeter polars from coordinate pairings

A regular locally finite measure and a Borel unit outward field satisfying the
compact C¹ coordinate pairings determine relative perimeter on all open sets.
They also force local finite perimeter and give the full divergence formula.
No global finite-mass hypothesis is used.
-/

noncomputable section
open MeasureTheory Set Filter Metric
open scoped Topology ENNReal
namespace LiquidDrop

/-- An ambient outward coordinate pairing gives a genuine distributional polar
on the whole-space subtype, with the derivative's negative sign. -/
lemma univ_indicator_polar_of_coordinate_pairing
    {E : Set AmbientSpace} {μ : Measure AmbientSpace} {ν : AmbientSpace → AmbientSpace}
    (hν : Measurable ν) (hnorm : ∀ᵐ x ∂μ, ‖ν x‖ = 1)
    (hpair : ∀ (i : Fin 3) (φ : CompactlySupportedContinuousMap AmbientSpace ℝ),
      ContDiff ℝ 1 φ →
      -(∫ x, E.indicator (fun _ => (1 : ℝ)) x *
        fderiv ℝ φ x (EuclideanSpace.single i 1)) = ∫ x, φ x * (-ν x i) ∂μ) :
    IsDistributionalPolarRepresentation (E.indicator (fun _ => (1 : ℝ))) univ
      (Measure.map (Homeomorph.Set.univ AmbientSpace).symm μ)
      (fun x => -ν x.val) := by
  have hv (x : AmbientSpace) : ((Homeomorph.Set.univ AmbientSpace).symm x).val = x := rfl
  refine ⟨(hν.comp measurable_subtype_coe).neg, ?_, ?_⟩
  · rw [(Homeomorph.Set.univ AmbientSpace).symm.measurableEmbedding.ae_map_iff]
    simpa only [hv, norm_neg] using hnorm
  · intro i φ hφ _
    rw [Measure.restrict_univ,
      (Homeomorph.Set.univ AmbientSpace).symm.measurableEmbedding.integral_map]
    simpa only [hv, PiLp.neg_apply] using hpair i φ hφ

/-- Unit coordinate pairings identify perimeter on every open region. -/
theorem perimeterIn_eq_of_ambient_coordinate_pairing
    {E : Set AmbientSpace} {μ : Measure AmbientSpace} [μ.Regular]
    {ν : AmbientSpace → AmbientSpace} (hmE : NullMeasurableSet E volume)
    (hν : Measurable ν) (hnorm : ∀ᵐ x ∂μ, ‖ν x‖ = 1)
    (hpair : ∀ (i : Fin 3) (φ : CompactlySupportedContinuousMap AmbientSpace ℝ),
      ContDiff ℝ 1 φ →
      -(∫ x, E.indicator (fun _ => (1 : ℝ)) x *
        fderiv ℝ φ x (EuclideanSpace.single i 1)) = ∫ x, φ x * (-ν x i) ∂μ)
    {O : Set AmbientSpace} (hO : IsOpen O) : perimeterIn E O = μ O := by
  let e := Homeomorph.Set.univ AmbientSpace
  let ρ := Measure.map e.symm μ
  let : ρ.Regular := Measure.Regular.map e.symm
  have hp := univ_indicator_polar_of_coordinate_pairing hν hnorm hpair
  have hv := hp.variation_eq_measure isOpen_univ hO (subset_univ O)
    ((locallyIntegrable_indicator_one hmE).locallyIntegrableOn univ)
  change perimeterIn E O = ρ (Subtype.val ⁻¹' O) at hv
  rw [show ρ = Measure.map e.symm μ from rfl,
    Measure.map_apply e.symm.continuous.measurable
      (hO.measurableSet.preimage measurable_subtype_coe)] at hv
  exact hv

/-- Coordinate distribution identities construct the complete ambient polar interface. -/
theorem ambientOutwardPerimeterPolar_of_coordinate_pairing
    {E : Set AmbientSpace} {μ : Measure AmbientSpace} [μ.Regular]
    {ν : AmbientSpace → AmbientSpace} (hmE : NullMeasurableSet E volume)
    (hν : Measurable ν) (hnorm : ∀ᵐ x ∂μ, ‖ν x‖ = 1)
    (hpair : ∀ (i : Fin 3) (φ : CompactlySupportedContinuousMap AmbientSpace ℝ),
      ContDiff ℝ 1 φ →
      -(∫ x, E.indicator (fun _ => (1 : ℝ)) x *
        fderiv ℝ φ x (EuclideanSpace.single i 1)) = ∫ x, φ x * (-ν x i) ∂μ) :
    IsAmbientOutwardPerimeterPolar E μ ν := by
  refine ⟨inferInstance, inferInstance, hν, hnorm,
    fun O hO => (perimeterIn_eq_of_ambient_coordinate_pairing hmE hν hnorm hpair hO).symm,
    hpair, ?_⟩
  intro X hX hcX
  let e := Homeomorph.Set.univ AmbientSpace
  let ρ := Measure.map e.symm μ
  let : ρ.Regular := Measure.Regular.map e.symm
  have hp := univ_indicator_polar_of_coordinate_pairing hν hnorm hpair
  have hd := hp.integral_divergence_eq
    ((locallyIntegrable_indicator_one hmE).locallyIntegrableOn univ) hX hcX (subset_univ _)
  rw [Measure.restrict_univ, e.symm.measurableEmbedding.integral_map] at hd
  have heq : (fun x => E.indicator (fun _ => (1 : ℝ)) x * divergenceN X x) =
      E.indicator (divergenceN X) := by
    funext x
    by_cases hx : x ∈ E <;> simp [hx]
  change -(∫ x, E.indicator (fun _ => (1 : ℝ)) x * divergenceN X x) =
    ∫ x, inner ℝ (X x) (-ν x) ∂μ at hd
  simpa only [heq, integral_indicator₀ hmE, inner_neg_right, integral_neg, neg_inj] using hd

/-- A regular unit distributional polar forces local finite perimeter. -/
theorem IsAmbientOutwardPerimeterPolar.hasLocallyFinitePerimeter
    {E : Set AmbientSpace} {μ : Measure AmbientSpace} {ν : AmbientSpace → AmbientSpace}
    (h : IsAmbientOutwardPerimeterPolar E μ ν) : HasLocallyFinitePerimeter E := by
  let := h.finiteOnCompacts
  intro A hA hcA
  rw [← h.open_eq A hA]
  exact (measure_mono subset_closure).trans_lt hcA.measure_lt_top

/-- The measure of any ambient unit perimeter polar is the canonical perimeter measure. -/
theorem IsAmbientOutwardPerimeterPolar.canonicalPerimeterMeasure_eq
    {E : Set AmbientSpace} {μ : Measure AmbientSpace} {ν : AmbientSpace → AmbientSpace}
    (h : IsAmbientOutwardPerimeterPolar E μ ν)
    (hE : HasLocallyFinitePerimeter E) (hmE : NullMeasurableSet E volume) :
    canonicalPerimeterMeasure E hE hmE = μ := by
  let := h.regular
  let := (canonicalPerimeterPolar E hE hmE).regular
  apply Measure.OuterRegular.ext_isOpen
  intro O hO
  rw [canonicalPerimeterMeasure_open E hE hmE hO, h.open_eq O hO]

/-- With the perimeter measure fixed, the outward polar field is unique almost everywhere. -/
theorem IsAmbientOutwardPerimeterPolar.density_unique
    {E : Set AmbientSpace} {μ : Measure AmbientSpace} {ν η : AmbientSpace → AmbientSpace}
    (h : IsAmbientOutwardPerimeterPolar E μ ν)
    (hη : IsAmbientOutwardPerimeterPolar E μ η) : ν =ᵐ[μ] η := by
  have hc (i : Fin 3) : (fun x => ν x i) =ᵐ[μ] (fun x => η x i) := by
    have hi (w : AmbientSpace → AmbientSpace) (hw : LocallyIntegrable w μ) :
        LocallyIntegrable (fun x => w x i) μ := by
      apply locallyIntegrable_iff.mpr
      intro K hK
      simpa only [Function.comp_def] using!
        (EuclideanSpace.proj i : AmbientSpace →L[ℝ] ℝ).integrable_comp
          (hw.integrableOn_isCompact hK)
    apply ae_eq_of_integral_contDiff_smul_eq (hi ν h.locallyIntegrable) (hi η hη.locallyIntegrable)
    intro g hg hgc
    let φ : CompactlySupportedContinuousMap AmbientSpace ℝ := ⟨⟨g, hg.continuous⟩, hgc⟩
    have hφ : ContDiff ℝ 1 φ := hg.of_le (by simp)
    have heq := (h.coordinate_eq i φ hφ).symm.trans (hη.coordinate_eq i φ hφ)
    simp only [mul_neg, integral_neg, neg_inj] at heq
    simpa [φ, smul_eq_mul] using heq
  filter_upwards [ae_all_iff.mpr hc] with x hx
  exact PiLp.ext hx

/-- Every ambient outward polar agrees with the normal chosen by the canonical construction. -/
theorem IsAmbientOutwardPerimeterPolar.ae_eq_canonicalOutwardPolarDensity
    {E : Set AmbientSpace} {μ : Measure AmbientSpace} {ν : AmbientSpace → AmbientSpace}
    (h : IsAmbientOutwardPerimeterPolar E μ ν)
    (hE : HasLocallyFinitePerimeter E) (hmE : NullMeasurableSet E volume) :
    ν =ᵐ[μ] canonicalOutwardPolarDensity E hE hmE := by
  apply h.density_unique
  rw [← h.canonicalPerimeterMeasure_eq hE hmE]
  exact canonicalPerimeterPolar E hE hmE

end LiquidDrop

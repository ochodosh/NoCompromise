import NoCompromise.DeGiorgi.HalfspaceRigidity
import NoCompromise.DeGiorgi.Reduced

/-!
# Identification of a constant polar measure with perimeter

A genuine constant unit distributional polar determines the original BV
variation on every open set. This uses the proved polar representation theorem,
without assuming finite total mass or a boundary representation formula.
-/

noncomputable section
open MeasureTheory Set Filter Metric
open scoped Topology ENNReal
namespace LiquidDrop

/-- Transport a constant ambient distributional polar to the whole-space subtype. -/
lemma HasConstantIndicatorPolar.univ_representation {E : Set AmbientSpace}
    {μ : Measure AmbientSpace} {ν : AmbientSpace}
    (h : HasConstantIndicatorPolar E μ ν) (hν : ‖ν‖ = 1) :
    IsDistributionalPolarRepresentation (E.indicator (fun _ => (1 : ℝ))) univ
      (Measure.map (Homeomorph.Set.univ AmbientSpace).symm μ) (fun _ => -ν) := by
  refine ⟨measurable_const, Eventually.of_forall fun _ => by simpa only [norm_neg] using hν, ?_⟩
  intro i φ hφ _
  rw [Measure.restrict_univ,
    (Homeomorph.Set.univ AmbientSpace).symm.measurableEmbedding.integral_map]
  exact h i φ hφ

/-- The positive polar measure agrees with relative perimeter on every open region. -/
theorem HasConstantIndicatorPolar.perimeterIn_eq {E : Set AmbientSpace}
    {μ : Measure AmbientSpace} [μ.Regular] {ν : AmbientSpace}
    (h : HasConstantIndicatorPolar E μ ν) (hE : NullMeasurableSet E volume)
    (hν : ‖ν‖ = 1) {O : Set AmbientSpace} (hO : IsOpen O) : perimeterIn E O = μ O := by
  let e := Homeomorph.Set.univ AmbientSpace
  let ρ := Measure.map e.symm μ
  let : ρ.Regular := Measure.Regular.map e.symm
  have hp := h.univ_representation hν
  have hv := hp.variation_eq_measure isOpen_univ hO (subset_univ O)
    ((locallyIntegrable_indicator_one hE).locallyIntegrableOn univ)
  change perimeterIn E O = ρ (Subtype.val ⁻¹' O) at hv
  rw [show ρ = Measure.map e.symm μ from rfl,
    Measure.map_apply e.symm.continuous.measurable
      (hO.measurableSet.preimage measurable_subtype_coe)] at hv
  exact hv

/-- A unit constant distributional polar supplies the complete ambient polar interface. -/
theorem HasConstantIndicatorPolar.isAmbientOutwardPerimeterPolar {E : Set AmbientSpace}
    {μ : Measure AmbientSpace} [μ.Regular] {ν : AmbientSpace}
    (h : HasConstantIndicatorPolar E μ ν) (hE : NullMeasurableSet E volume)
    (hν : ‖ν‖ = 1) : IsAmbientOutwardPerimeterPolar E μ (fun _ => ν) := by
  refine ⟨inferInstance, inferInstance, measurable_const,
    Eventually.of_forall fun _ => hν, fun O hO => (h.perimeterIn_eq hE hν hO).symm, h, ?_⟩
  intro X hX hcX
  let e := Homeomorph.Set.univ AmbientSpace
  let ρ := Measure.map e.symm μ
  let : ρ.Regular := Measure.Regular.map e.symm
  have hp := h.univ_representation hν
  have hd := hp.integral_divergence_eq
    ((locallyIntegrable_indicator_one hE).locallyIntegrableOn univ) hX hcX (subset_univ _)
  rw [Measure.restrict_univ, e.symm.measurableEmbedding.integral_map] at hd
  have heq : (fun x => E.indicator (fun _ => (1 : ℝ)) x * divergenceN X x) =
      E.indicator (divergenceN X) := by
    funext x
    by_cases hx : x ∈ E <;> simp [hx]
  change -(∫ x, E.indicator (fun _ => (1 : ℝ)) x * divergenceN X x) =
    ∫ x, inner ℝ (X x) (-ν) ∂μ at hd
  simpa only [heq, integral_indicator₀ hE, inner_neg_right, integral_neg, neg_inj] using hd

/-- A regular constant unit polar forces local finite perimeter. -/
theorem HasConstantIndicatorPolar.hasLocallyFinitePerimeter {E : Set AmbientSpace}
    {μ : Measure AmbientSpace} [μ.Regular] {ν : AmbientSpace}
    (h : HasConstantIndicatorPolar E μ ν) (hE : NullMeasurableSet E volume)
    (hν : ‖ν‖ = 1) : HasLocallyFinitePerimeter E := by
  intro A hA hcA
  rw [h.perimeterIn_eq hE hν hA]
  exact (measure_mono subset_closure).trans_lt hcA.measure_lt_top

/-- The chosen canonical perimeter measure agrees with any regular constant unit polar. -/
theorem HasConstantIndicatorPolar.canonicalPerimeterMeasure_eq {E : Set AmbientSpace}
    {μ : Measure AmbientSpace} [μ.Regular] {ν : AmbientSpace}
    (h : HasConstantIndicatorPolar E μ ν) (hE : HasLocallyFinitePerimeter E)
    (hmE : NullMeasurableSet E volume) (hν : ‖ν‖ = 1) :
    canonicalPerimeterMeasure E hE hmE = μ := by
  let := (canonicalPerimeterPolar E hE hmE).regular
  apply Measure.OuterRegular.ext_isOpen
  intro O hO
  rw [canonicalPerimeterMeasure_open E hE hmE hO, h.perimeterIn_eq hmE hν hO]

end LiquidDrop

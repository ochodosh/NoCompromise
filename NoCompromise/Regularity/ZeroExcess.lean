import NoCompromise.Regularity.ZeroExcessThreshold
import NoCompromise.Regularity.ZeroExcessLocalPolar
import NoCompromise.Regularity.CylindersConvex
import NoCompromise.Regularity.Excess

/-! # Zero-excess classification, including the two constant phases -/

noncomputable section
open MeasureTheory Set Filter Metric
open scoped Topology ENNReal
namespace LiquidDrop

/-- The complete local constant-normal classification on any bounded convex
open region. The polar decomposition lives only on U, so no finite-perimeter
hypothesis outside U is imposed. The negative direction is the distributional
polar sign corresponding to the outward normal ν. -/
theorem zero_excess_classification
    {E U : Set AmbientSpace} (hmE : NullMeasurableSet E volume)
    (hU : IsOpen U) (hcU : Convex ℝ U) (hbU : Bornology.IsBounded U)
    {ν : AmbientSpace} (hν : ‖ν‖ = 1)
    {ρ : Measure U} {σ : U → AmbientSpace}
    (hp : IsDistributionalPolarRepresentation (E.indicator (fun _ => (1 : ℝ))) U ρ σ)
    (hσ : σ =ᵐ[ρ] fun _ => -ν) :
    E =ᵐ[volume.restrict U] (∅ : Set AmbientSpace) ∨
      E =ᵐ[volume.restrict U] (univ : Set AmbientSpace) ∨
      ∃ c : ℝ, E =ᵐ[volume.restrict U] {x : AmbientSpace | inner ℝ ν x < c} :=
  (hp.hasLocalConstantIndicatorPolar hσ).classification hmE hν hU hcU hbU

/-- A disjoint version of the three-case classification. The nonconstant
case explicitly excludes both pure phases, so the alternatives cannot overlap. -/
theorem zero_excess_classification_trichotomy
    {E U : Set AmbientSpace} (hmE : NullMeasurableSet E volume)
    (hU : IsOpen U) (hcU : Convex ℝ U) (hbU : Bornology.IsBounded U)
    {ν : AmbientSpace} (hν : ‖ν‖ = 1)
    {ρ : Measure U} {σ : U → AmbientSpace}
    (hp : IsDistributionalPolarRepresentation (E.indicator (fun _ => (1 : ℝ))) U ρ σ)
    (hσ : σ =ᵐ[ρ] fun _ => -ν) :
    E =ᵐ[volume.restrict U] (∅ : Set AmbientSpace) ∨
      (¬ E =ᵐ[volume.restrict U] (∅ : Set AmbientSpace)) ∧
        E =ᵐ[volume.restrict U] (univ : Set AmbientSpace) ∨
      (¬ E =ᵐ[volume.restrict U] (∅ : Set AmbientSpace)) ∧
        (¬ E =ᵐ[volume.restrict U] (univ : Set AmbientSpace)) ∧
        ∃ c : ℝ, E =ᵐ[volume.restrict U] {x : AmbientSpace | inner ℝ ν x < c} := by
  by_cases he : E =ᵐ[volume.restrict U] (∅ : Set AmbientSpace)
  · exact Or.inl he
  by_cases hf : E =ᵐ[volume.restrict U] (univ : Set AmbientSpace)
  · exact Or.inr (Or.inl ⟨he, hf⟩)
  have hc := zero_excess_classification hmE hU hcU hbU hν hp hσ
  exact Or.inr (Or.inr ⟨he, hf, (hc.resolve_left he).resolve_left hf⟩)

/-- The blueprint cylinder case with a genuine local polar decomposition. -/
theorem zero_excess_classification_cylinder
    {E : Set AmbientSpace} (hmE : NullMeasurableSet E volume)
    (x : AmbientSpace) (r : ℝ) {ν : AmbientSpace} (hν : ‖ν‖ = 1)
    {ρ : Measure (cylinder x r ν)} {σ : cylinder x r ν → AmbientSpace}
    (hp : IsDistributionalPolarRepresentation (E.indicator (fun _ => (1 : ℝ)))
      (cylinder x r ν) ρ σ) (hσ : σ =ᵐ[ρ] fun _ => -ν) :
    E =ᵐ[volume.restrict (cylinder x r ν)] (∅ : Set AmbientSpace) ∨
      E =ᵐ[volume.restrict (cylinder x r ν)] (univ : Set AmbientSpace) ∨
      ∃ c : ℝ, E =ᵐ[volume.restrict (cylinder x r ν)]
        {y : AmbientSpace | inner ℝ ν y < c} :=
  zero_excess_classification hmE (isOpen_cylinder x r ν) (convex_cylinder x r ν)
    (isBounded_cylinder x r hν) hν hp hσ

/-- The same classification directly for the genuine reduced outward normal. -/
theorem zero_excess_classification_reduced_normal
    {E U : Set AmbientSpace} (hE : HasLocallyFinitePerimeter E)
    (hmE : NullMeasurableSet E volume) (hU : IsOpen U) (hcU : Convex ℝ U)
    (hbU : Bornology.IsBounded U) {ν : AmbientSpace} (hν : ‖ν‖ = 1)
    (hσ : reducedNormal E hE hmE
      =ᵐ[((hausdorffMeasure2 3).restrict (reducedBoundary E hE hmE)).restrict U] fun _ => ν) :
    E =ᵐ[volume.restrict U] (∅ : Set AmbientSpace) ∨
      E =ᵐ[volume.restrict U] (univ : Set AmbientSpace) ∨
      ∃ c : ℝ, E =ᵐ[volume.restrict U] {x : AmbientSpace | inner ℝ ν x < c} :=
  ((reducedBoundary_outwardPerimeterPolar E hE hmE).hasLocalConstantIndicatorPolar
    hU.measurableSet hσ).classification hmE hν hU hcU hbU

lemma normal_ae_eq_of_cylindricalExcess_eq_zero
    {E : Set AmbientSpace} (hE : HasLocallyFinitePerimeter E)
    (hmE : NullMeasurableSet E volume) (x : AmbientSpace) {r : ℝ} (hr : 0 < r)
    {ν : AmbientSpace} (hν : ‖ν‖ = 1) (hz : cylindricalExcess E hE hmE x r ν = 0) :
    reducedNormal E hE hmE =ᵐ[
      ((hausdorffMeasure2 3).restrict (reducedBoundary E hE hmE)).restrict (cylinder x r ν)]
      fun _ => ν := by
  have he : normalExcessIntegral E hE hmE (cylinder x r ν) ν = 0 :=
    (div_eq_zero_iff.mp hz).resolve_right (pow_ne_zero 2 hr.ne')
  have hae := (integral_eq_zero_iff_of_nonneg_ae
    (Eventually.of_forall (fun y => sq_nonneg ‖reducedNormal E hE hmE y - ν‖))
    (integrableOn_normal_excess E hE hmE (isBounded_cylinder x r hν) ν)).mp he
  filter_upwards [hae] with y hy
  change ‖reducedNormal E hE hmE y - ν‖ ^ 2 = 0 at hy
  exact sub_eq_zero.mp (norm_eq_zero.mp (by nlinarith [hy]))

/-- Vanishing of the actual cylindrical excess gives the lower-halfspace
classification, with no phase-density assumption to exclude the constant cases. -/
theorem classification_of_cylindricalExcess_eq_zero
    {E : Set AmbientSpace} (hE : HasLocallyFinitePerimeter E)
    (hmE : NullMeasurableSet E volume) (x : AmbientSpace) {r : ℝ} (hr : 0 < r)
    {ν : AmbientSpace} (hν : ‖ν‖ = 1) (hz : cylindricalExcess E hE hmE x r ν = 0) :
    E =ᵐ[volume.restrict (cylinder x r ν)] (∅ : Set AmbientSpace) ∨
      E =ᵐ[volume.restrict (cylinder x r ν)] (univ : Set AmbientSpace) ∨
      ∃ c : ℝ, E =ᵐ[volume.restrict (cylinder x r ν)]
        {y : AmbientSpace | inner ℝ ν y < c} :=
  zero_excess_classification_reduced_normal hE hmE (isOpen_cylinder x r ν)
    (convex_cylinder x r ν) (isBounded_cylinder x r hν) hν
    (normal_ae_eq_of_cylindricalExcess_eq_zero hE hmE x hr hν hz)

end LiquidDrop

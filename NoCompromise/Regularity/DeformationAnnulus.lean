import NoCompromise.Regularity.DeformationColumn
import NoCompromise.Regularity.DeformationTransport
import NoCompromise.Regularity.DeformationCore

/-! # The uniform annular perimeter estimate for actual compression competitors -/

noncomputable section
open Set MeasureTheory Filter
open scoped ENNReal
namespace LiquidDrop

def horizontalAnnulus (σ τ : ℝ) : Set AmbientSpace :=
  {x | σ < ‖graphProjectionN 2 x‖ ∧ ‖graphProjectionN 2 x‖ < τ}

def cylindricalTransition (r σ τ : ℝ) : Set AmbientSpace :=
  horizontalAnnulus σ τ ∩ standardCylinder r

lemma isOpen_horizontalAnnulus (σ τ : ℝ) : IsOpen (horizontalAnnulus σ τ) :=
  (isOpen_lt continuous_const (graphProjectionN 2).continuous.norm).inter
    (isOpen_lt (graphProjectionN 2).continuous.norm continuous_const)

lemma isOpen_cylindricalTransition (r σ τ : ℝ) : IsOpen (cylindricalTransition r σ τ) :=
  (isOpen_horizontalAnnulus σ τ).inter (isOpen_standardCylinder r)

lemma verticalCompression_image_horizontalAnnulus
    (β : EuclideanSpace ℝ (Fin 2) → ℝ) (hβ : ContDiff ℝ 1 β)
    (hn : ∀ p, β p ≠ 0) (c σ τ : ℝ) :
    verticalCompression β c '' horizontalAnnulus σ τ = horizontalAnnulus σ τ := by
  let Φ := verticalCompressionHomeomorph β hβ hn c
  ext y
  constructor
  · rintro ⟨x, hx, rfl⟩
    simpa only [horizontalAnnulus, mem_ofPred_eq, verticalCompression_projection] using hx
  · intro hy
    refine ⟨Φ.symm y, ?_, Φ.apply_symm_apply y⟩
    simpa only [horizontalAnnulus, mem_ofPred_eq, Φ,
      verticalCompressionHomeomorph_symm_apply, verticalCompression_projection] using hy

lemma IsSlabCapConfiguration.extension_perimeter_annulus
    {E : Set AmbientSpace} {hE : HasLocallyFinitePerimeter E}
    {hmE : NullMeasurableSet E volume} {r c η : ℝ}
    (h : IsSlabCapConfiguration E hE hmE r c η)
    (hExt : HasLocallyFinitePerimeter (verticalPhaseExtension E r))
    (hmExt : NullMeasurableSet (verticalPhaseExtension E r) volume)
    {σ τ : ℝ} (hτr : τ ≤ r) :
    (canonicalPerimeterMeasure (verticalPhaseExtension E r) hExt hmExt).restrict
      (horizontalAnnulus σ τ) =
      (canonicalPerimeterMeasure E hE hmE).restrict (cylindricalTransition r σ τ) := by
  have hs : horizontalAnnulus σ τ ⊆ {x | ‖graphProjectionN 2 x‖ < τ} := fun _ hx => hx.2
  calc
    _ = ((canonicalPerimeterMeasure (verticalPhaseExtension E r) hExt hmExt).restrict
        {x | ‖graphProjectionN 2 x‖ < τ}).restrict (horizontalAnnulus σ τ) :=
      (Measure.restrict_restrict_of_subset hs).symm
    _ = ((canonicalPerimeterMeasure E hE hmE).restrict
        ({x | ‖graphProjectionN 2 x‖ < τ} ∩ standardCylinder r)).restrict
          (horizontalAnnulus σ τ) := by rw [h.extension_perimeter_column hExt hmExt hτr]
    _ = _ := by
      rw [Measure.restrict_restrict (isOpen_horizontalAnnulus σ τ).measurableSet,
        ← inter_assoc, inter_eq_self_of_subset_left hs]
      rfl

theorem IsSlabCapConfiguration.compression_annular_perimeter_bound
    {E : Set AmbientSpace} {hE : HasLocallyFinitePerimeter E}
    {hmE : NullMeasurableSet E volume} {r c η : ℝ}
    (h : IsSlabCapConfiguration E hE hmE r c η)
    {σ τ ε : ℝ} (hσ : 0 < σ) (hst : σ < τ) (hτr : τ ≤ r)
    (hε : 0 < ε) (hε1 : ε ≤ 1) :
    perimeterIn (compressionCompetitor E r σ τ ε c) (cylindricalTransition r σ τ) ≤
      perimeterIn E (cylindricalTransition r σ τ) +
        ENNReal.ofReal (Real.pi ^ 2 / (τ - σ) ^ 2) *
          ∫⁻ x in standardCylinder r, ENNReal.ofReal ((x 2 - c) ^ 2)
            ∂canonicalPerimeterMeasure E hE hmE := by
  let Ext := verticalPhaseExtension E r
  let G := verticalCompression (compressionBeta σ τ ε) c '' Ext
  have hExt := hasLocallyFinitePerimeter_verticalPhaseExtension hE hmE h.1.1.le
  have hmExt := nullMeasurableSet_verticalPhaseExtension hmE r
  have hG := hasLocallyFinitePerimeter_verticalCompression hσ hst hε hε1 c Ext hExt hmExt
  have hmG := nullMeasurableSet_image_of_differentiable
    ((contDiff_verticalCompression (contDiff_compressionBeta hσ hst ε) c).differentiable
      one_ne_zero)
    (verticalCompressionHomeomorph (compressionBeta σ τ ε)
      (contDiff_compressionBeta hσ hst ε) (compressionBeta_ne_zero hε hε1) c).injective hmExt
  have hrest := h.extension_perimeter_annulus hExt hmExt (σ := σ) hτr
  have hmass : canonicalPerimeterMeasure Ext hExt hmExt (horizontalAnnulus σ τ) =
      perimeterIn E (cylindricalTransition r σ τ) := by
    have hh := congrArg (fun μ : Measure AmbientSpace => μ univ) hrest
    simpa only [Measure.restrict_apply_univ,
      canonicalPerimeterMeasure_open E hE hmE (isOpen_cylindricalTransition r σ τ)] using hh
  have hbound := perimeter_verticalCompression_le_source_measure hσ hst hε hε1 c
    Ext hExt hmExt hG hmG (isOpen_horizontalAnnulus σ τ).measurableSet
  rw [verticalCompression_image_horizontalAnnulus _ (contDiff_compressionBeta hσ hst ε)
    (compressionBeta_ne_zero hε hε1), hmass] at hbound
  have hmom : (∫⁻ x in horizontalAnnulus σ τ, ENNReal.ofReal ((x 2 - c) ^ 2)
        ∂canonicalPerimeterMeasure Ext hExt hmExt) ≤
      ∫⁻ x in standardCylinder r, ENNReal.ofReal ((x 2 - c) ^ 2)
        ∂canonicalPerimeterMeasure E hE hmE := by
    rw [hrest]
    exact lintegral_mono_set inter_subset_right
  have hlocal : perimeterIn (compressionCompetitor E r σ τ ε c)
      (cylindricalTransition r σ τ) = perimeterIn G (cylindricalTransition r σ τ) := by
    apply variation_congr_ae
    apply (ae_restrict_iff' (isOpen_cylindricalTransition r σ τ).measurableSet).mpr
    exact Eventually.of_forall fun x hx => compressionCompetitor_indicator_between E r σ τ ε c
      ⟨(abs_lt.mp hx.2.2).1.le, (abs_lt.mp hx.2.2).2⟩
  rw [hlocal, ← canonicalPerimeterMeasure_open G hG hmG (isOpen_cylindricalTransition r σ τ)]
  exact (measure_mono inter_subset_left).trans (hbound.trans (by gcongr))

end LiquidDrop

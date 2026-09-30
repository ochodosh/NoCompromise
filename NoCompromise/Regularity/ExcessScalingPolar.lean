module

public import NoCompromise.DeGiorgi.AmbientPolar
public import NoCompromise.DeGiorgi.BlowupPolar
public import NoCompromise.DeGiorgi.Structure

@[expose] public section

/-!
# The genuine perimeter polar under positive blowup

The transformed field is identified through the distributional coordinate
pairing and uniqueness of the unit perimeter polar. No transformation rule for
the reduced normal is assumed.
-/

noncomputable section
open MeasureTheory Set Filter Metric
open scoped ENNReal Topology
namespace LiquidDrop

/-- Positive rescaling preserves regularity of the rescaled perimeter measure. -/
lemma blowupPolarMeasure_regular (μ : Measure AmbientSpace) [μ.Regular]
    (x : AmbientSpace) {r : ℝ} (hr : 0 < r) : (blowupPolarMeasure μ x r).Regular := by
  have he : (fun y : AmbientSpace => r⁻¹ • (y - x)) = (blowupHomeomorph x hr).symm :=
    (funext (blowupHomeomorph_symm_apply x · hr)).symm
  rw [blowupPolarMeasure, he]
  let := Measure.Regular.map (μ := μ) (blowupHomeomorph x hr).symm
  exact Measure.Regular.smul ENNReal.ofReal_ne_top

/-- The actual outward polar field pulls back under a positive blowup. -/
theorem IsAmbientOutwardPerimeterPolar.blowup_polar
    {E : Set AmbientSpace} {μ : Measure AmbientSpace} {σ : AmbientSpace → AmbientSpace}
    (h : IsAmbientOutwardPerimeterPolar E μ σ) (hmE : NullMeasurableSet E volume)
    (x : AmbientSpace) {r : ℝ} (hr : 0 < r) :
    IsAmbientOutwardPerimeterPolar (LiquidDrop.blowupSet E x r)
      (blowupPolarMeasure μ x r) (fun y => σ (x + r • y)) := by
  let := h.regular
  let := blowupPolarMeasure_regular μ x hr
  apply ambientOutwardPerimeterPolar_of_coordinate_pairing
    (nullMeasurableSet_blowupSet hmE x hr) (h.measurable.comp (by fun_prop))
  · unfold blowupPolarMeasure
    apply Measure.ae_smul_measure _ (ENNReal.ofReal (r⁻¹ ^ 2))
    have he : (fun y : AmbientSpace => r⁻¹ • (y - x)) = (blowupHomeomorph x hr).symm :=
      (funext (blowupHomeomorph_symm_apply x · hr)).symm
    rw [he, (blowupHomeomorph x hr).symm.measurableEmbedding.ae_map_iff]
    simpa only [Function.comp_def, ← blowupHomeomorph_apply x _ hr,
      Homeomorph.apply_symm_apply] using h.norm_ae
  · intro i φ hφ
    rw [h.blowup_coordinate_pairing x hr i φ hφ, integral_blowupPolarMeasure μ x hr]
    congr 1
    apply integral_congr_ae
    exact Eventually.of_forall fun y => by simp [smul_smul, hr.ne']

/-- The canonical perimeter measure itself has the exact quadratic covariance. -/
theorem canonicalPerimeterMeasure_blowupSet (E : Set AmbientSpace)
    (hE : HasLocallyFinitePerimeter E) (hmE : NullMeasurableSet E volume)
    (x : AmbientSpace) {r : ℝ} (hr : 0 < r) :
    canonicalPerimeterMeasure (blowupSet E x r) (hE.blowupSet (by norm_num) x hr)
      (nullMeasurableSet_blowupSet hmE x hr) =
        blowupPolarMeasure (canonicalPerimeterMeasure E hE hmE) x r :=
  ((canonicalPerimeterPolar E hE hmE).blowup_polar hmE x hr).canonicalPerimeterMeasure_eq _ _

/-- The actual reduced normal of the blowup equals the pulled-back reduced normal
almost everywhere. -/
theorem reducedNormal_blowupSet_ae (E : Set AmbientSpace)
    (hE : HasLocallyFinitePerimeter E) (hmE : NullMeasurableSet E volume)
    (x : AmbientSpace) {r : ℝ} (hr : 0 < r) :
    reducedNormal (blowupSet E x r) (hE.blowupSet (by norm_num) x hr)
      (nullMeasurableSet_blowupSet hmE x hr) =ᵐ[
        blowupPolarMeasure (canonicalPerimeterMeasure E hE hmE) x r]
          (fun y => reducedNormal E hE hmE (x + r • y)) := by
  have hp := (reducedBoundary_outwardPerimeterPolar E hE hmE).blowup_polar hmE x hr
  rw [← canonicalPerimeterMeasure_eq_reducedBoundary_area E hE hmE] at hp
  have hpol := hp.ae_eq_canonicalOutwardPolarDensity
    (hE.blowupSet (by norm_num) x hr) (nullMeasurableSet_blowupSet hmE x hr)
  have hn := reducedNormal_ae_eq_polarDensity (blowupSet E x r)
    (hE.blowupSet (by norm_num) x hr) (nullMeasurableSet_blowupSet hmE x hr)
  rw [canonicalPerimeterMeasure_blowupSet E hE hmE x hr] at hn
  exact hn.trans hpol.symm

/-- Exact change of variables for a real integral restricted to any rescaled region. -/
lemma setIntegral_blowupPolarMeasure (μ : Measure AmbientSpace) (x : AmbientSpace)
    {r : ℝ} (hr : 0 < r) (f : AmbientSpace → ℝ) (U : Set AmbientSpace) :
    (∫ y in U, f y ∂blowupPolarMeasure μ x r) =
      r⁻¹ ^ 2 * ∫ y in (fun z => x + r • z) '' U, f (r⁻¹ • (y - x)) ∂μ := by
  have he : (fun y : AmbientSpace => r⁻¹ • (y - x)) = (blowupHomeomorph x hr).symm :=
    (funext (blowupHomeomorph_symm_apply x · hr)).symm
  rw [blowupPolarMeasure, Measure.restrict_smul, integral_smul_measure,
    ENNReal.toReal_ofReal (sq_nonneg _), smul_eq_mul, he,
    (blowupHomeomorph x hr).symm.measurableEmbedding.setIntegral_map]
  have hs : (blowupHomeomorph x hr).symm ⁻¹' U = (fun z => x + r • z) '' U :=
    ((blowupHomeomorph x hr).toEquiv.image_eq_preimage_symm U).symm
  rw [hs]
  simp only [blowupHomeomorph_symm_apply]

end LiquidDrop

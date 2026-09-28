import NoCompromise.Regularity.FluxDefect
import NoCompromise.Regularity.DensityCutComparison

/-! # Complement orientation for reverse Poincaré -/

noncomputable section
open Set MeasureTheory Filter Metric
open scoped ENNReal Topology
namespace LiquidDrop
set_option maxSynthPendingDepth 8

lemma reducedBoundaryOfPolar_neg {n : ℕ}
    (μ : Measure (EuclideanSpace ℝ (Fin n)))
    (σ : EuclideanSpace ℝ (Fin n) → EuclideanSpace ℝ (Fin n)) :
    reducedBoundaryOfPolar μ (-σ) = reducedBoundaryOfPolar μ σ := by
  ext x
  constructor
  · rintro ⟨hx, z, hz, ht⟩
    refine ⟨hx, -z, by simpa only [norm_neg] using hz, ?_⟩
    simpa only [average_neg, neg_neg] using ht.neg
  · rintro ⟨hx, z, hz, ht⟩
    refine ⟨hx, -z, by simpa only [norm_neg] using hz, ?_⟩
    simpa only [average_neg] using ht.neg

lemma canonicalPerimeterMeasure_compl (E : Set AmbientSpace)
    (hE : HasLocallyFinitePerimeter E) (hmE : NullMeasurableSet E volume)
    (hEc : HasLocallyFinitePerimeter Eᶜ) (hmEc : NullMeasurableSet Eᶜ volume) :
    canonicalPerimeterMeasure Eᶜ hEc hmEc = canonicalPerimeterMeasure E hE hmE :=
  ((canonicalPerimeterPolar E hE hmE).compl hmE).canonicalPerimeterMeasure_eq hEc hmEc

lemma reducedBoundary_compl (E : Set AmbientSpace)
    (hE : HasLocallyFinitePerimeter E) (hmE : NullMeasurableSet E volume)
    (hEc : HasLocallyFinitePerimeter Eᶜ) (hmEc : NullMeasurableSet Eᶜ volume) :
    reducedBoundary Eᶜ hEc hmEc = reducedBoundary E hE hmE := by
  have hp := (canonicalPerimeterPolar E hE hmE).compl hmE
  have hν := hp.ae_eq_canonicalOutwardPolarDensity hEc hmEc
  rw [reducedBoundary, canonicalPerimeterMeasure_compl E hE hmE hEc hmEc]
  calc
    _ = reducedBoundaryOfPolar (canonicalPerimeterMeasure E hE hmE)
        (-(-canonicalOutwardPolarDensity E hE hmE)) :=
      reducedBoundaryOfPolar_congr_ae _ hν.symm.neg
    _ = _ := reducedBoundaryOfPolar_neg _ _

lemma reducedNormal_compl_ae (E : Set AmbientSpace)
    (hE : HasLocallyFinitePerimeter E) (hmE : NullMeasurableSet E volume)
    (hEc : HasLocallyFinitePerimeter Eᶜ) (hmEc : NullMeasurableSet Eᶜ volume) :
    reducedNormal Eᶜ hEc hmEc =ᵐ[canonicalPerimeterMeasure E hE hmE]
      -reducedNormal E hE hmE := by
  have hc := reducedNormal_ae_eq_polarDensity Eᶜ hEc hmEc
  rw [canonicalPerimeterMeasure_compl E hE hmE hEc hmEc] at hc
  have hp := (canonicalPerimeterPolar E hE hmE).compl hmE
  have hν := hp.ae_eq_canonicalOutwardPolarDensity hEc hmEc
  exact (hc.trans hν.symm).trans (reducedNormal_ae_eq_polarDensity E hE hmE).neg.symm

lemma normalExcessIntegral_compl (E : Set AmbientSpace)
    (hE : HasLocallyFinitePerimeter E) (hmE : NullMeasurableSet E volume)
    (hEc : HasLocallyFinitePerimeter Eᶜ) (hmEc : NullMeasurableSet Eᶜ volume)
    (U : Set AmbientSpace) (ν : AmbientSpace) :
    normalExcessIntegral Eᶜ hEc hmEc U (-ν) = normalExcessIntegral E hE hmE U ν := by
  rw [normalExcessIntegral, normalExcessIntegral,
    ← canonicalPerimeterMeasure_eq_reducedBoundary_area Eᶜ hEc hmEc,
    ← canonicalPerimeterMeasure_eq_reducedBoundary_area E hE hmE,
    canonicalPerimeterMeasure_compl E hE hmE hEc hmEc]
  apply integral_congr_ae
  filter_upwards [ae_restrict_of_ae (reducedNormal_compl_ae E hE hmE hEc hmEc)] with x hx
  rw [hx]
  change ‖-reducedNormal E hE hmE x - -ν‖ ^ 2 = _
  have he : -reducedNormal E hE hmE x - -ν = -(reducedNormal E hE hmE x - ν) := by abel
  rw [he, norm_neg]

lemma IsReversedSlabCapConfiguration.compl
    {E : Set AmbientSpace} {hE : HasLocallyFinitePerimeter E}
    {hmE : NullMeasurableSet E volume} {r c η : ℝ}
    (h : IsReversedSlabCapConfiguration E hE hmE r c η)
    (hEc : HasLocallyFinitePerimeter Eᶜ) (hmEc : NullMeasurableSet Eᶜ volume) :
    IsSlabCapConfiguration Eᶜ hEc hmEc r c η := by
  refine ⟨⟨h.1.1, h.1.2.1, h.1.2.2.1, h.1.2.2.2.1, ?_⟩, ?_, ?_⟩
  · intro x hx
    apply h.1.2.2.2.2 x
    rwa [reducedBoundary_compl E hE hmE hEc hmEc] at hx
  · simpa only [densityOne_compl hmE] using h.2.1
  · simpa only [← densityOne_compl hmE.compl, compl_compl] using h.2.2

end LiquidDrop

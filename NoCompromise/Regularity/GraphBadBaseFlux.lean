import NoCompromise.Regularity.GraphSlicesCapBridge
import NoCompromise.Regularity.GraphSlicesPolar
import NoCompromise.Regularity.Excess

/-! # Exact signed vertical flux localized over an arbitrary Borel base -/

noncomputable section
open Set MeasureTheory Filter Metric
open scoped ENNReal Topology
namespace LiquidDrop
set_option maxSynthPendingDepth 8

/-- The half-radius cylinder localized above a planar base set. -/
def graphBaseRegion (B : Set (EuclideanSpace ℝ (Fin 2))) : Set AmbientSpace :=
  standardCylinder (1 / 2) ∩ (graphProjectionN 2) ⁻¹' B

lemma measurableSet_graphBaseRegion {B : Set (EuclideanSpace ℝ (Fin 2))}
    (hB : MeasurableSet B) : MeasurableSet (graphBaseRegion B) :=
  (isOpen_standardCylinder _).measurableSet.inter ((graphProjectionN 2).measurable hB)

lemma isBounded_graphBaseRegion (B : Set (EuclideanSpace ℝ (Fin 2))) :
    Bornology.IsBounded (graphBaseRegion B) :=
  (isBounded_standardCylinder _).subset inter_subset_left

lemma graphBaseRegion_slice {B : Set (EuclideanSpace ℝ (Fin 2))}
    (hB : B ⊆ ball 0 (1 / 2)) (p : EuclideanSpace ℝ (Fin 2)) :
    {t : ℝ | graphAppendN p t ∈ graphBaseRegion B} =
      {t | p ∈ B ∧ t ∈ Ioo (-(1 / 2)) (1 / 2)} := by
  ext t
  simp only [graphBaseRegion, standardCylinder, mem_inter_iff, mem_preimage,
    mem_ofPred_eq, graphProjectionN_append, graphAppendN_height_three, abs_lt, mem_Ioo]
  constructor
  · intro ht
    exact ⟨ht.2, ht.1.2⟩
  · intro ht
    exact ⟨⟨mem_ball_zero_iff.mp (hB ht.1), ht.2⟩, ht.1⟩

/-- Actual signed slicing gives flux equal to base volume on every Borel part,
including exceptional base sets. No injectivity of the projection is assumed. -/
theorem HasGraphCapPhases.vertical_flux_on_base
    {E : Set AmbientSpace} (h : HasGraphCapPhases E)
    (hE : HasLocallyFinitePerimeter E) (hmE : NullMeasurableSet E volume)
    {B : Set (EuclideanSpace ℝ (Fin 2))} (hB : MeasurableSet B)
    (hBB : B ⊆ ball 0 (1 / 2)) :
    (∫ z in graphBaseRegion B, reducedNormal E hE hmE z 2
      ∂canonicalPerimeterMeasure E hE hmE) = volume.real B := by
  classical
  obtain ⟨τ, s, κ, σ, g, hd, hj⟩ := h.exists_oriented_slices hE hmE
  have hi := hd.setIntegral_eq (isBounded_standardCylinder (1 / 2)).isCompact_closure
    (measurableSet_graphBaseRegion hB)
    (show graphBaseRegion B ⊆ closure (standardCylinder (1 / 2)) from
      inter_subset_left.trans subset_closure)
  have hae : (fun p : EuclideanSpace ℝ (Fin 2) =>
      ∫ t in {t | graphAppendN p t ∈ graphBaseRegion B}, σ p t ∂κ p) =ᵐ[volume]
        B.indicator (fun _ => (-1 : ℝ)) := by
    filter_upwards [hj] with p hp
    rw [graphBaseRegion_slice hBB]
    by_cases hpB : p ∈ B
    · simp only [hpB, true_and, ofPred_mem_eq, indicator_of_mem hpB]
      exact (hp (ball_subset_ball (by norm_num : (1 / 2 : ℝ) ≤ 3 / 4) (hBB hpB))).2.2.1
    · simp only [hpB, false_and, ofPred_false, indicator_of_notMem hpB,
        Measure.restrict_empty, integral_zero_measure]
  have hmass : (∫ z in graphBaseRegion B, s z ∂τ) = -volume.real B := by
    rw [hi.2]
    change (∫ p, ∫ t in {t | graphAppendN p t ∈ graphBaseRegion B}, σ p t ∂κ p) = _
    rw [integral_congr_ae hae, integral_indicator hB]
    simp
  have he := hd.polar.setIntegral_vertical_eq hE hmE (measurableSet_graphBaseRegion hB)
    (fun _ => 1)
  simp only [one_mul, integral_neg] at he
  linarith

end LiquidDrop

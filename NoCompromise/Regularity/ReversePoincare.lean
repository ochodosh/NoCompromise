module

public import NoCompromise.Regularity.ReversePoincareEstimate
public import NoCompromise.Regularity.ReversePoincareComplement

@[expose] public section

/-! # Reverse Poincaré for both signed slab-and-cap configurations -/

noncomputable section
open Set MeasureTheory Filter Metric
open scoped ENNReal Topology
namespace LiquidDrop

/-- One universal constant controls the height and quasiminimality terms. -/
def reversePoincareConstant : ℝ := 128 * Real.pi ^ 2 + 256 * Real.pi / 3

lemma reversePoincareConstant_pos : 0 < reversePoincareConstant := by
  unfold reversePoincareConstant
  positivity

lemma cylinder_neg_axis (x : AmbientSpace) (r : ℝ) (ν : AmbientSpace) :
    cylinder x r (-ν) = cylinder x r ν := by
  have he (y : AmbientSpace) : cylinderProjection (-ν) y = cylinderProjection ν y := by
    simp [cylinderProjection_apply]
  simp only [cylinder, he, inner_neg_left, abs_neg]

lemma cylindricalExcess_compl (E : Set AmbientSpace)
    (hE : HasLocallyFinitePerimeter E) (hmE : NullMeasurableSet E volume)
    (hEc : HasLocallyFinitePerimeter Eᶜ) (hmEc : NullMeasurableSet Eᶜ volume)
    (x : AmbientSpace) (r : ℝ) (ν : AmbientSpace) :
    cylindricalExcess Eᶜ hEc hmEc x r (-ν) = cylindricalExcess E hE hmE x r ν := by
  rw [cylindricalExcess, cylindricalExcess, cylinder_neg_axis,
    normalExcessIntegral_compl E hE hmE hEc hmEc]

/-- Reverse Poincaré at every admissible original radius, with a fixed constant
and any genuine cleared slab width. -/
theorem IsOmegaMinimal.reverse_poincare
    {E : Set AmbientSpace} {ω r c η : ℝ} (hE : IsOmegaMinimal E ω)
    (h : IsSlabCapConfiguration E hE.locallyFinite hE.nullMeasurable r c η)
    (hr1 : r ≤ 1 / Real.sqrt 2) :
    cylindricalExcess E hE.locallyFinite hE.nullMeasurable 0 (r / 2)
      (EuclideanSpace.single 2 1) ≤
      (reversePoincareConstant / r ^ 4) *
        (∫ x in standardCylinder r ∩ reducedBoundary E hE.locallyFinite hE.nullMeasurable,
          (x 2 - c) ^ 2 ∂hausdorffMeasure2 3) + reversePoincareConstant * ω * r := by
  have hH : 0 ≤ ∫ x in standardCylinder r ∩
      reducedBoundary E hE.locallyFinite hE.nullMeasurable,
      (x 2 - c) ^ 2 ∂hausdorffMeasure2 3 := integral_nonneg fun _ => sq_nonneg _
  have hω := hE.nonneg
  have hr := h.1.1
  have hc1 : 128 * Real.pi ^ 2 ≤ reversePoincareConstant := by
    unfold reversePoincareConstant
    nlinarith [Real.pi_pos]
  have hc2 : 256 * Real.pi / 3 ≤ reversePoincareConstant := by
    unfold reversePoincareConstant
    nlinarith [sq_nonneg Real.pi]
  apply (hE.reverse_poincare_explicit h hr1).trans
  gcongr

/-- Exchanging the actual cap phases reverses the normal in the estimate. -/
theorem IsOmegaMinimal.reverse_poincare_reversed
    {E : Set AmbientSpace} {ω r c η : ℝ} (hE : IsOmegaMinimal E ω)
    (h : IsReversedSlabCapConfiguration E hE.locallyFinite hE.nullMeasurable r c η)
    (hr1 : r ≤ 1 / Real.sqrt 2) :
    cylindricalExcess E hE.locallyFinite hE.nullMeasurable 0 (r / 2)
      (-EuclideanSpace.single 2 1) ≤
      (reversePoincareConstant / r ^ 4) *
        (∫ x in standardCylinder r ∩ reducedBoundary E hE.locallyFinite hE.nullMeasurable,
          (x 2 - c) ^ 2 ∂hausdorffMeasure2 3) + reversePoincareConstant * ω * r := by
  have hc := hE.compl.reverse_poincare
    (h.compl hE.compl.locallyFinite hE.compl.nullMeasurable) hr1
  have hex := cylindricalExcess_compl E hE.locallyFinite hE.nullMeasurable
    hE.compl.locallyFinite hE.compl.nullMeasurable 0 (r / 2) (-EuclideanSpace.single 2 1)
  rw [neg_neg] at hex
  rw [hex, reducedBoundary_compl E hE.locallyFinite hE.nullMeasurable
    hE.compl.locallyFinite hE.compl.nullMeasurable] at hc
  exact hc

/-- Full blueprint `lem:reverse-poincare`, including the reversed-phase clause.
One may take η₀=1/4 and the displayed universal constant. -/
theorem reverse_poincare :
    ∃ η₀ : ℝ, η₀ ∈ Ioo 0 (1 / 2) ∧ ∃ C : ℝ, 0 < C ∧
      ∀ (E : Set AmbientSpace) (ω r c : ℝ) (hE : IsOmegaMinimal E ω),
        0 < r → r ≤ 1 / Real.sqrt 2 →
        (IsSlabCapConfiguration E hE.locallyFinite hE.nullMeasurable r c η₀ →
          cylindricalExcess E hE.locallyFinite hE.nullMeasurable 0 (r / 2)
            (EuclideanSpace.single 2 1) ≤
            (C / r ^ 4) *
              (∫ x in standardCylinder r ∩ reducedBoundary E hE.locallyFinite hE.nullMeasurable,
                (x 2 - c) ^ 2 ∂hausdorffMeasure2 3) + C * ω * r) ∧
        (IsReversedSlabCapConfiguration E hE.locallyFinite hE.nullMeasurable r c η₀ →
          cylindricalExcess E hE.locallyFinite hE.nullMeasurable 0 (r / 2)
            (-EuclideanSpace.single 2 1) ≤
            (C / r ^ 4) *
              (∫ x in standardCylinder r ∩ reducedBoundary E hE.locallyFinite hE.nullMeasurable,
                (x 2 - c) ^ 2 ∂hausdorffMeasure2 3) + C * ω * r) := by
  refine ⟨1 / 4, by norm_num, reversePoincareConstant, reversePoincareConstant_pos, ?_⟩
  intro E ω r c hE _ hr1
  exact ⟨fun h => hE.reverse_poincare h hr1, fun h => hE.reverse_poincare_reversed h hr1⟩

end LiquidDrop

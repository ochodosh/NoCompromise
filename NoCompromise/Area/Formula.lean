import NoCompromise.Area.RankDeficient
import NoCompromise.Area.PieceMeasure
import NoCompromise.Area.PieceFormula
import NoCompromise.Area.GoodPiecesCover

/-!
# The planar-source area formula with multiplicity

Countably many disjoint uniform pieces cover the nonzero-Jacobian locus up to
a Lebesgue-null set. The rank-deficient image theorem makes the entire omitted
image Hausdorff-null. Weighted one-piece area and Tonelli then give the exact
formula, including infinite nonnegative weights and unbounded Borel source sets.
-/

noncomputable section
open MeasureTheory Set Function
open scoped ENNReal NNReal Topology
namespace LiquidDrop
set_option maxSynthPendingDepth 8

/-- The source contribution vanishes if the nonzero-Jacobian portion is null. -/
lemma lintegral_weighted_jacobian_eq_zero_of_nonzero_null {m : ℕ}
    {f : EuclideanSpace ℝ (Fin 2) → EuclideanSpace ℝ (Fin m)}
    {A : Set (EuclideanSpace ℝ (Fin 2))} (hA : MeasurableSet A)
    (hnull : volume (A ∩ {x | jacobian2 f x ≠ 0}) = 0)
    (q : EuclideanSpace ℝ (Fin 2) → ℝ≥0∞) :
    (∫⁻ x in A, q x * ENNReal.ofReal (jacobian2 f x)) = 0 := by
  apply Eq.trans (lintegral_congr_ae ?_) (lintegral_zero (μ := volume.restrict A))
  have hn : ∀ᵐ x ∂volume, x ∉ A ∩ {x | jacobian2 f x ≠ 0} :=
    (measure_eq_zero_iff_ae_notMem).mp hnull
  filter_upwards [ae_restrict_mem hA, ae_restrict_of_ae hn] with x hx hn
  have hz : jacobian2 f x = 0 := by
    by_contra h
    exact hn ⟨hx, h⟩
  simp only [hz, ENNReal.ofReal_zero, mul_zero]

/-- A cover missing only a null part of the nonzero-Jacobian set has a null image remainder. -/
lemma hausdorffMeasure2_image_sdiff_null_of_rankTwo_cover {m : ℕ} {L : ℝ≥0}
    {f : EuclideanSpace ℝ (Fin 2) → EuclideanSpace ℝ (Fin m)} (hf : LipschitzWith L f)
    {C : Set (EuclideanSpace ℝ (Fin 2))}
    (hC : volume ({x | jacobian2 f x ≠ 0} \ C) = 0)
    (A : Set (EuclideanSpace ℝ (Fin 2))) :
    hausdorffMeasure2 m (f '' (A \ C)) = 0 := by
  have hs : A \ C ⊆ {x | jacobian2 f x = 0} ∪ ({x | jacobian2 f x ≠ 0} \ C) := by
    intro x hx
    by_cases h : jacobian2 f x = 0
    · exact Or.inl h
    · exact Or.inr ⟨h, hx.2⟩
  apply measure_mono_null (image_mono hs)
  rw [image_union]
  exact measure_union_null (hausdorffMeasure2_image_jacobian2_eq_zero hf)
    (hausdorffMeasure2_image_null hf hC)

/-- Discarding a null part of the nonzero-Jacobian set does not change weighted source area. -/
lemma lintegral_weighted_jacobian_inter_cover {m : ℕ}
    {f : EuclideanSpace ℝ (Fin 2) → EuclideanSpace ℝ (Fin m)}
    {A C : Set (EuclideanSpace ℝ (Fin 2))} (hA : MeasurableSet A) (hC : MeasurableSet C)
    (hnull : volume ({x | jacobian2 f x ≠ 0} \ C) = 0)
    (q : EuclideanSpace ℝ (Fin 2) → ℝ≥0∞) :
    (∫⁻ x in A, q x * ENNReal.ofReal (jacobian2 f x)) =
      ∫⁻ x in A ∩ C, q x * ENNReal.ofReal (jacobian2 f x) := by
  have hn : volume ((A \ C) ∩ {x | jacobian2 f x ≠ 0}) = 0 := by
    exact measure_mono_null (show ((A \ C) ∩ {x | jacobian2 f x ≠ 0}) ⊆
      {x | jacobian2 f x ≠ 0} \ C from fun x hx => ⟨hx.2, hx.1.2⟩) hnull
  have hi := lintegral_weighted_jacobian_eq_zero_of_nonzero_null (hA.diff hC) hn q
  have hsplit : A = (A ∩ C) ∪ (A \ C) := by
    ext x
    simp only [mem_union, mem_inter_iff, mem_sdiff]
    tauto
  conv_lhs => rw [hsplit]
  rw [lintegral_union (hA.diff hC) (Set.disjoint_left.mpr (fun x hx hy => hy.2 hx.2)), hi,
    add_zero]

/-- Outside the image of a removed source set, all weighted fibers are unchanged. -/
lemma areaMultiplicity_inter_of_notMem_image_sdiff {α β : Type*} {f : α → β}
    {A C : Set α} (q : α → ℝ≥0∞) {y : β} (hy : y ∉ f '' (A \ C)) :
    areaMultiplicity f A q y = areaMultiplicity f (A ∩ C) q y := by
  have he : A ∩ f ⁻¹' {y} = (A ∩ C) ∩ f ⁻¹' {y} := by
    ext x
    constructor
    · intro hx
      refine ⟨⟨hx.1, ?_⟩, hx.2⟩
      by_contra hnot
      exact hy ⟨x, ⟨hx.1, hnot⟩, hx.2⟩
    · exact fun hx => ⟨hx.1.1, hx.2⟩
  simp only [areaMultiplicity, he]

lemma areaMultiplicity_inter_ae_of_image_sdiff_null {m : ℕ}
    {f : EuclideanSpace ℝ (Fin 2) → EuclideanSpace ℝ (Fin m)}
    {A C : Set (EuclideanSpace ℝ (Fin 2))}
    (hnull : hausdorffMeasure2 m (f '' (A \ C)) = 0)
    (q : EuclideanSpace ℝ (Fin 2) → ℝ≥0∞) :
    areaMultiplicity f A q =ᵐ[hausdorffMeasure2 m] areaMultiplicity f (A ∩ C) q := by
  filter_upwards [(measure_eq_zero_iff_ae_notMem).mp hnull] with y hy
  exact areaMultiplicity_inter_of_notMem_image_sdiff q hy

/-- Blueprint `thm:area-formula-2d`, with arbitrary nonnegative Borel weights and multiplicities. -/
theorem area_formula_two_dimensional {m : ℕ} {L : ℝ≥0}
    {f : EuclideanSpace ℝ (Fin 2) → EuclideanSpace ℝ (Fin m)} (hf : LipschitzWith L f)
    {A : Set (EuclideanSpace ℝ (Fin 2))} (hA : MeasurableSet A)
    {q : EuclideanSpace ℝ (Fin 2) → ℝ≥0∞} (hq : Measurable q) :
    (∫⁻ x in A, q x * ENNReal.ofReal (jacobian2 f x)) =
      ∫⁻ y, areaMultiplicity f A q y ∂hausdorffMeasure2 m := by
  obtain ⟨G, hd, hG, _, hcover⟩ := exists_disjoint_uniform_differentiability_pieces hf
  let C := ⋃ j, G j
  have hmC : MeasurableSet C := MeasurableSet.iUnion fun j => (hG j).1
  have hbad : volume ({x | jacobian2 f x ≠ 0} \ C) = 0 := by
    simpa only [rankTwoDifferentiabilitySet_eq_jacobian_ne_zero, C] using hcover
  let B (j : ℕ) := A ∩ G j
  have hB (j) : IsUniformDifferentiabilityPiece f (B j) :=
    (hG j).mono (hA.inter (hG j).1) inter_subset_right
  have hBd : Pairwise (Disjoint on B) :=
    hd.mono fun _ _ h => h.mono inter_subset_right inter_subset_right
  have hBC : A ∩ C = ⋃ j, B j := inter_iUnion A G
  have hnull := hausdorffMeasure2_image_sdiff_null_of_rankTwo_cover hf hbad A
  calc
    _ = ∫⁻ x in A ∩ C, q x * ENNReal.ofReal (jacobian2 f x) :=
      lintegral_weighted_jacobian_inter_cover hA hmC hbad q
    _ = ∑' j, ∫⁻ x in B j, q x * ENNReal.ofReal (jacobian2 f x) := by
      rw [hBC]
      exact lintegral_iUnion (fun j => (hB j).1) hBd _
    _ = ∑' j, ∫⁻ y, areaMultiplicity f (B j) q y ∂hausdorffMeasure2 m :=
      tsum_congr fun j => area_formula_uniform_piece hf.continuous.measurable (hB j) hq
    _ = ∫⁻ y, ∑' j, areaMultiplicity f (B j) q y ∂hausdorffMeasure2 m :=
      (lintegral_tsum fun j =>
        (measurable_areaMultiplicity_of_uniform_piece (hB j) hq).aemeasurable).symm
    _ = ∫⁻ y, areaMultiplicity f (A ∩ C) q y ∂hausdorffMeasure2 m := by
      rw [hBC]
      apply lintegral_congr
      intro y
      exact (areaMultiplicity_iUnion f B hBd q y).symm
    _ = _ := (lintegral_congr_ae (areaMultiplicity_inter_ae_of_image_sdiff_null hnull q)).symm

/-- The area formula with the literal sum over the source fiber. -/
theorem area_formula_two_dimensional_fiber {m : ℕ} {L : ℝ≥0}
    {f : EuclideanSpace ℝ (Fin 2) → EuclideanSpace ℝ (Fin m)} (hf : LipschitzWith L f)
    {A : Set (EuclideanSpace ℝ (Fin 2))} (hA : MeasurableSet A)
    {q : EuclideanSpace ℝ (Fin 2) → ℝ≥0∞} (hq : Measurable q) :
    (∫⁻ x in A, q x * ENNReal.ofReal (jacobian2 f x)) =
      ∫⁻ y, ∑' x : ↥(A ∩ f ⁻¹' {y}), q x ∂hausdorffMeasure2 m := by
  simpa only [areaMultiplicity_eq_tsum_fiber] using area_formula_two_dimensional hf hA hq

/-- Every Borel source set has a Hausdorff-measurable Lipschitz image. -/
theorem nullMeasurableSet_image_lipschitz_planar {m : ℕ} {L : ℝ≥0}
    {f : EuclideanSpace ℝ (Fin 2) → EuclideanSpace ℝ (Fin m)} (hf : LipschitzWith L f)
    {A : Set (EuclideanSpace ℝ (Fin 2))} (hA : MeasurableSet A) :
    NullMeasurableSet (f '' A) (hausdorffMeasure2 m) := by
  obtain ⟨G, hd, hG, _, hcover⟩ := exists_disjoint_uniform_differentiability_pieces hf
  let C := ⋃ j, G j
  have hbad : volume ({x | jacobian2 f x ≠ 0} \ C) = 0 := by
    simpa only [rankTwoDifferentiabilitySet_eq_jacobian_ne_zero, C] using hcover
  have him : MeasurableSet (f '' (A ∩ C)) := by
    rw [show A ∩ C = ⋃ j, A ∩ G j from inter_iUnion A G, image_iUnion]
    exact MeasurableSet.iUnion fun j =>
      ((hG j).mono (hA.inter (hG j).1) inter_subset_right).measurableSet_image
  have hrem : NullMeasurableSet (f '' (A \ C)) (hausdorffMeasure2 m) :=
    .of_null (hausdorffMeasure2_image_sdiff_null_of_rankTwo_cover hf hbad A)
  have hs : f '' A = f '' (A ∩ C) ∪ f '' (A \ C) := by
    rw [← image_union, inter_union_sdiff]
  rw [hs]
  exact him.nullMeasurableSet.union hrem

/-- The full multiplicity integrand is measurable for completed Hausdorff area. -/
theorem aemeasurable_areaMultiplicity_lipschitz_planar {m : ℕ} {L : ℝ≥0}
    {f : EuclideanSpace ℝ (Fin 2) → EuclideanSpace ℝ (Fin m)} (hf : LipschitzWith L f)
    {A : Set (EuclideanSpace ℝ (Fin 2))} (hA : MeasurableSet A)
    {q : EuclideanSpace ℝ (Fin 2) → ℝ≥0∞} (hq : Measurable q) :
    AEMeasurable (areaMultiplicity f A q) (hausdorffMeasure2 m) := by
  obtain ⟨G, hd, hG, _, hcover⟩ := exists_disjoint_uniform_differentiability_pieces hf
  let C := ⋃ j, G j
  let B (j : ℕ) := A ∩ G j
  have hB (j) : IsUniformDifferentiabilityPiece f (B j) :=
    (hG j).mono (hA.inter (hG j).1) inter_subset_right
  have hBd : Pairwise (Disjoint on B) :=
    hd.mono fun _ _ h => h.mono inter_subset_right inter_subset_right
  have hbad : volume ({x | jacobian2 f x ≠ 0} \ C) = 0 := by
    simpa only [rankTwoDifferentiabilitySet_eq_jacobian_ne_zero, C] using hcover
  have hm : Measurable (areaMultiplicity f (A ∩ C) q) := by
    have he : areaMultiplicity f (A ∩ C) q = fun y => ∑' j, areaMultiplicity f (B j) q y := by
      rw [show A ∩ C = ⋃ j, B j from inter_iUnion A G]
      funext y
      exact areaMultiplicity_iUnion f B hBd q y
    rw [he]
    exact Measurable.tsum fun j => measurable_areaMultiplicity_of_uniform_piece (hB j) hq
  exact hm.aemeasurable.congr (areaMultiplicity_inter_ae_of_image_sdiff_null
    (hausdorffMeasure2_image_sdiff_null_of_rankTwo_cover hf hbad A) q).symm

/-- Unit weight on an injective fiber is the indicator of the image. -/
lemma areaMultiplicity_one_of_injOn {α β : Type*} {f : α → β} {A : Set α}
    (hinj : InjOn f A) : areaMultiplicity f A (fun _ => 1) = (f '' A).indicator (fun _ => 1) := by
  classical
  funext y
  by_cases hy : y ∈ f '' A
  · rw [indicator_of_mem hy]
    obtain ⟨x, hx, rfl⟩ := hy
    exact areaMultiplicity_apply_of_injOn hinj _ hx
  · rw [indicator_of_notMem hy]
    exact areaMultiplicity_eq_zero_of_notMem_image _ hy

/-- The injective form of the planar-source area formula. -/
theorem hausdorffMeasure2_image_eq_lintegral_jacobian_of_lipschitz {m : ℕ} {L : ℝ≥0}
    {f : EuclideanSpace ℝ (Fin 2) → EuclideanSpace ℝ (Fin m)} (hf : LipschitzWith L f)
    {A : Set (EuclideanSpace ℝ (Fin 2))} (hA : MeasurableSet A) (hinj : InjOn f A) :
    hausdorffMeasure2 m (f '' A) = ∫⁻ x in A, ENNReal.ofReal (jacobian2 f x) := by
  have h := area_formula_two_dimensional hf hA (measurable_const (a := (1 : ℝ≥0∞)))
  rw [areaMultiplicity_one_of_injOn hinj,
    lintegral_indicator_const₀ (nullMeasurableSet_image_lipschitz_planar hf hA) 1] at h
  simpa only [one_mul] using h.symm

end LiquidDrop

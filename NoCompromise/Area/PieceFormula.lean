import NoCompromise.Area.PieceMeasure
import Mathlib.MeasureTheory.Integral.Lebesgue.Map

/-!
# The weighted area formula on a uniform piece

`areaMultiplicity` is the sum of an extended nonnegative source weight over an
actual fiber. It agrees with the usual subtype sum and is additive over disjoint
source unions, including countable unions and infinite weights.

On an injective Borel carrier subset the map is a measurable embedding, so a Borel
source weight extends measurably to the target. The proved pushforward identity
then gives the weighted area formula. A finite injective Borel partition and
Tonelli's theorem yield the formula and Borel multiplicity on any uniform piece.
The final theorem also permits weights defined only on the Borel source subset.
-/

noncomputable section
open MeasureTheory Set Filter Function
open scoped ENNReal Topology
namespace LiquidDrop
set_option maxSynthPendingDepth 8

/-- The sum of a nonnegative source weight over the fiber inside `A`. -/
def areaMultiplicity {α β : Type*} (f : α → β) (A : Set α) (q : α → ℝ≥0∞)
    (y : β) : ℝ≥0∞ := ∑' x : α, (A ∩ f ⁻¹' {y}).indicator q x

lemma areaMultiplicity_eq_tsum_fiber {α β : Type*} (f : α → β) (A : Set α)
    (q : α → ℝ≥0∞) (y : β) :
    areaMultiplicity f A q y = ∑' x : ↥(A ∩ f ⁻¹' {y}), q x := by
  rw [areaMultiplicity, tsum_subtype]

lemma areaMultiplicity_apply_of_injOn {α β : Type*} {f : α → β} {A : Set α}
    (hf : InjOn f A) (q : α → ℝ≥0∞) {x : α} (hx : x ∈ A) :
    areaMultiplicity f A q (f x) = q x := by
  classical
  rw [areaMultiplicity, tsum_eq_single x]
  · simp [hx]
  · intro z hzx
    apply indicator_of_notMem
    intro hz
    exact hzx (hf hz.1 hx hz.2)

lemma areaMultiplicity_eq_zero_of_notMem_image {α β : Type*} {f : α → β} {A : Set α}
    (q : α → ℝ≥0∞) {y : β} (hy : y ∉ f '' A) : areaMultiplicity f A q y = 0 := by
  unfold areaMultiplicity
  apply ENNReal.tsum_eq_zero.mpr
  intro x
  apply indicator_of_notMem
  rintro ⟨hx, hxy⟩
  exact hy ⟨x, hx, hxy⟩

lemma areaMultiplicity_iUnion {α β ι : Type*} (f : α → β)
    (B : ι → Set α) (hd : Pairwise (Disjoint on B)) (q : α → ℝ≥0∞) (y : β) :
    areaMultiplicity f (⋃ i, B i) q y = ∑' i, areaMultiplicity f (B i) q y := by
  classical
  simp only [areaMultiplicity]
  rw [ENNReal.tsum_comm]
  apply tsum_congr
  intro x
  by_cases hxy : f x = y
  · by_cases hx : x ∈ ⋃ i, B i
    · obtain ⟨i, hi⟩ := mem_iUnion.mp hx
      rw [tsum_eq_single i]
      · simp [hx, hi, hxy]
      · intro j hji
        have hxj : x ∉ B j := fun hj => disjoint_left.mp (hd hji) hj hi
        simp [hxj]
    · have hxB (i) : x ∉ B i := fun hi => hx (mem_iUnion.mpr ⟨i, hi⟩)
      simp [hx, hxB]
  · simp [hxy]

lemma UniformDifferentiabilityCarrier.measurableEmbedding_restrict {m : ℕ}
    {f : EuclideanSpace ℝ (Fin 2) → EuclideanSpace ℝ (Fin m)}
    (d : UniformDifferentiabilityCarrier f) {A : Set (EuclideanSpace ℝ (Fin 2))}
    (hA : MeasurableSet A) (hAK : A ⊆ d.carrier) (hinj : InjOn f A) :
    MeasurableEmbedding (fun x : A => f x) := by
  refine ⟨fun x y hxy => Subtype.ext (hinj x.property y.property hxy),
    (d.continuousOn.mono hAK).domRestrict.measurable, ?_⟩
  intro T hT
  have himage : MeasurableSet (f '' ((↑) '' T : Set (EuclideanSpace ℝ (Fin 2)))) :=
    IsUniformDifferentiabilityPiece.measurableSet_image
      ⟨hA.subtype_image hT, d, by rintro _ ⟨x, hx, rfl⟩; exact hAK x.property⟩
  simpa only [image_image] using himage

lemma UniformDifferentiabilityCarrier.measurable_areaMultiplicity_of_injOn {m : ℕ}
    {f : EuclideanSpace ℝ (Fin 2) → EuclideanSpace ℝ (Fin m)}
    (d : UniformDifferentiabilityCarrier f) {A : Set (EuclideanSpace ℝ (Fin 2))}
    (hA : MeasurableSet A) (hAK : A ⊆ d.carrier) (hinj : InjOn f A)
    {q : EuclideanSpace ℝ (Fin 2) → ℝ≥0∞} (hq : Measurable q) :
    Measurable (areaMultiplicity f A q) := by
  have he := d.measurableEmbedding_restrict hA hAK hinj
  have heq : areaMultiplicity f A q =
      Function.extend (fun x : A => f x) (fun x : A => q x) (fun _ => 0) := by
    funext y
    by_cases hy : y ∈ f '' A
    · obtain ⟨x, hx, rfl⟩ := hy
      rw [areaMultiplicity_apply_of_injOn hinj q hx]
      exact (he.injective.extend_apply (fun x : A => q x) (fun _ => 0) ⟨x, hx⟩).symm
    · rw [areaMultiplicity_eq_zero_of_notMem_image q hy,
        Function.extend_apply']
      intro hy'
      obtain ⟨x, hx⟩ := hy'
      exact hy ⟨x, x.property, hx⟩
  rw [heq]
  exact he.measurable_extend (hq.comp measurable_subtype_coe) measurable_const

/-- The weighted area identity on an injective Borel subset of a uniform carrier. -/
theorem UniformDifferentiabilityCarrier.area_formula_of_injOn {m : ℕ}
    {f : EuclideanSpace ℝ (Fin 2) → EuclideanSpace ℝ (Fin m)}
    (d : UniformDifferentiabilityCarrier f) (hfm : Measurable f)
    {A : Set (EuclideanSpace ℝ (Fin 2))} (hA : MeasurableSet A)
    (hAK : A ⊆ d.carrier) (hinj : InjOn f A)
    {q : EuclideanSpace ℝ (Fin 2) → ℝ≥0∞} (hq : Measurable q) :
    (∫⁻ x in A, q x * ENNReal.ofReal (jacobian2 f x)) =
      ∫⁻ y, areaMultiplicity f A q y ∂hausdorffMeasure2 m := by
  have hm := d.measurable_areaMultiplicity_of_injOn hA hAK hinj hq
  have himage : MeasurableSet (f '' A) :=
    IsUniformDifferentiabilityPiece.measurableSet_image ⟨hA, d, hAK⟩
  have hind : (f '' A).indicator (areaMultiplicity f A q) = areaMultiplicity f A q := by
    funext y
    by_cases hy : y ∈ f '' A
    · exact indicator_of_mem hy _
    · rw [indicator_of_notMem hy, areaMultiplicity_eq_zero_of_notMem_image q hy]
  calc
    _ = ∫⁻ x in A, areaMultiplicity f A q (f x) * ENNReal.ofReal (jacobian2 f x) := by
      apply lintegral_congr_ae
      filter_upwards [ae_restrict_mem hA] with x hx
      rw [areaMultiplicity_apply_of_injOn hinj q hx]
    _ = ∫⁻ y in f '' A, areaMultiplicity f A q y ∂hausdorffMeasure2 m :=
      d.lintegral_comp_mul_jacobian hfm hA hAK hinj hm
    _ = _ := by rw [← lintegral_indicator himage, hind]

/-- Every Borel subset of a uniform carrier has a finite Borel injective partition. -/
lemma UniformDifferentiabilityCarrier.exists_finite_injective_partition {m : ℕ}
    {f : EuclideanSpace ℝ (Fin 2) → EuclideanSpace ℝ (Fin m)}
    (d : UniformDifferentiabilityCarrier f)
    {A : Set (EuclideanSpace ℝ (Fin 2))} (hA : MeasurableSet A) (hAK : A ⊆ d.carrier) :
    ∃ (k : ℕ) (B : Fin k → Set (EuclideanSpace ℝ (Fin 2))),
      (∀ i, MeasurableSet (B i)) ∧ Pairwise (Disjoint on B) ∧ (⋃ i, B i) = A ∧
      (∀ i, B i ⊆ A) ∧ ∀ i, InjOn f (B i) := by
  obtain ⟨r, hr, hsmall⟩ := d.exists_injective_scale
  obtain ⟨k, B, c, hm, hd, hu, hsub, hbase, hdiam⟩ :=
    exists_finite_measurable_partition_of_compact_subset d.isCompact hA hAK
      (show (0 : ℝ) < r by exact_mod_cast hr)
  refine ⟨k, B, hm, hd, hu, hsub, fun i => ?_⟩
  apply d.injOn_of_diameter_le ((hsub i).trans hAK) hsmall
  intro x hx y hy
  exact_mod_cast hdiam i x hx y hy

/-- Multiplicity with a Borel nonnegative weight is Borel on a uniform piece. -/
theorem measurable_areaMultiplicity_of_uniform_piece {m : ℕ}
    {f : EuclideanSpace ℝ (Fin 2) → EuclideanSpace ℝ (Fin m)}
    {G : Set (EuclideanSpace ℝ (Fin 2))} (hG : IsUniformDifferentiabilityPiece f G)
    {q : EuclideanSpace ℝ (Fin 2) → ℝ≥0∞} (hq : Measurable q) :
    Measurable (areaMultiplicity f G q) := by
  obtain ⟨hGm, d, hGK⟩ := hG
  obtain ⟨k, B, hm, hd, hu, hsub, hinj⟩ := d.exists_finite_injective_partition hGm hGK
  have heq : areaMultiplicity f G q = fun y => ∑' i, areaMultiplicity f (B i) q y := by
    funext y
    rw [← hu, areaMultiplicity_iUnion f B hd]
  rw [heq]
  exact Measurable.tsum fun i =>
    d.measurable_areaMultiplicity_of_injOn (hm i) ((hsub i).trans hGK) (hinj i) hq

/-- Blueprint `lem:area-one-piece`, for any Borel nonnegative source weight. -/
theorem area_formula_uniform_piece {m : ℕ}
    {f : EuclideanSpace ℝ (Fin 2) → EuclideanSpace ℝ (Fin m)} (hfm : Measurable f)
    {G : Set (EuclideanSpace ℝ (Fin 2))} (hG : IsUniformDifferentiabilityPiece f G)
    {q : EuclideanSpace ℝ (Fin 2) → ℝ≥0∞} (hq : Measurable q) :
    (∫⁻ x in G, q x * ENNReal.ofReal (jacobian2 f x)) =
      ∫⁻ y, areaMultiplicity f G q y ∂hausdorffMeasure2 m := by
  obtain ⟨hGm, d, hGK⟩ := hG
  obtain ⟨k, B, hm, hd, hu, hsub, hinj⟩ := d.exists_finite_injective_partition hGm hGK
  have hmi (i) := d.measurable_areaMultiplicity_of_injOn
    (hm i) ((hsub i).trans hGK) (hinj i) hq
  have heq : areaMultiplicity f G q = fun y => ∑' i, areaMultiplicity f (B i) q y := by
    funext y
    rw [← hu, areaMultiplicity_iUnion f B hd]
  calc
    _ = ∑' i, ∫⁻ x in B i, q x * ENNReal.ofReal (jacobian2 f x) := by
      rw [← hu, lintegral_iUnion hm hd]
    _ = ∑' i, ∫⁻ y, areaMultiplicity f (B i) q y ∂hausdorffMeasure2 m :=
      tsum_congr fun i => d.area_formula_of_injOn hfm
        (hm i) ((hsub i).trans hGK) (hinj i) hq
    _ = _ := by rw [heq, lintegral_tsum (fun i => (hmi i).aemeasurable)]

/-- The indicator-based multiplicity is the usual sum over the subtype fiber. -/
lemma areaMultiplicity_eq_tsum_subtype_fiber {α β : Type*} (f : α → β) (A : Set α)
    (q : α → ℝ≥0∞) (y : β) :
    areaMultiplicity f A q y = ∑' x : {x : A // f x = y}, q x.val := by
  let e : {x : A // f x = y} ≃ ↥(A ∩ f ⁻¹' {y}) :=
    { toFun := fun x => ⟨x.val.val, x.val.property, x.property⟩
      invFun := fun x => ⟨⟨x.val, x.property.1⟩, x.property.2⟩
      left_inv := fun _ => rfl
      right_inv := fun _ => rfl }
  rw [areaMultiplicity_eq_tsum_fiber]
  exact (e.tsum_eq (fun x => q x)).symm

/-- The area formula remains unchanged for a Borel subset of the given uniform piece. -/
theorem area_formula_uniform_piece_subset {m : ℕ}
    {f : EuclideanSpace ℝ (Fin 2) → EuclideanSpace ℝ (Fin m)} (hfm : Measurable f)
    {G A : Set (EuclideanSpace ℝ (Fin 2))} (hG : IsUniformDifferentiabilityPiece f G)
    (hA : MeasurableSet A) (hAG : A ⊆ G)
    {q : EuclideanSpace ℝ (Fin 2) → ℝ≥0∞} (hq : Measurable q) :
    (∫⁻ x in A, q x * ENNReal.ofReal (jacobian2 f x)) =
      ∫⁻ y, areaMultiplicity f A q y ∂hausdorffMeasure2 m :=
  area_formula_uniform_piece hfm (hG.mono hA hAG) hq

/-- The literal source-subtype version: a Borel weight need only be defined on
`A`, and the target integrand is the standard sum over `A ∩ f⁻¹({y})`. -/
theorem area_formula_uniform_piece_subtype {m : ℕ}
    {f : EuclideanSpace ℝ (Fin 2) → EuclideanSpace ℝ (Fin m)} (hfm : Measurable f)
    {G A : Set (EuclideanSpace ℝ (Fin 2))} (hG : IsUniformDifferentiabilityPiece f G)
    (hA : MeasurableSet A) (hAG : A ⊆ G) {q : A → ℝ≥0∞} (hq : Measurable q) :
    (∫⁻ x : A, q x * ENNReal.ofReal (jacobian2 f x)
      ∂volume.comap (Subtype.val : A → EuclideanSpace ℝ (Fin 2))) =
      ∫⁻ y, (∑' x : {x : A // f x = y}, q x.val) ∂hausdorffMeasure2 m := by
  let q' : EuclideanSpace ℝ (Fin 2) → ℝ≥0∞ := Function.extend (Subtype.val : A → _) q (fun _ => 0)
  have hq' : Measurable q' :=
    (MeasurableEmbedding.subtype_coe hA).measurable_extend hq measurable_const
  have heq (x : A) : q' x = q x := Subtype.coe_injective.extend_apply q (fun _ => 0) x
  calc
    _ = ∫⁻ x in A, q' x * ENNReal.ofReal (jacobian2 f x) := by
      rw [← lintegral_subtype_comap hA]
      apply lintegral_congr
      intro x
      rw [heq x]
    _ = ∫⁻ y, areaMultiplicity f A q' y ∂hausdorffMeasure2 m :=
      area_formula_uniform_piece_subset hfm hG hA hAG hq'
    _ = _ := by
      apply lintegral_congr
      intro y
      rw [areaMultiplicity_eq_tsum_subtype_fiber]
      apply tsum_congr
      intro x
      exact heq x.val

end LiquidDrop

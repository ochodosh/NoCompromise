module

public import NoCompromise.Area.Formula

@[expose] public section

/-!
# Injective chart pieces for countably rectifiable sets

This module constructs finite-area Borel chart pieces. It does not assume
existence of an intrinsic approximate tangent for a rectifiable set of
infinite local Hausdorff measure.
-/

noncomputable section
open MeasureTheory Set Function
open scoped ENNReal NNReal Topology
namespace LiquidDrop
set_option maxSynthPendingDepth 8

lemma IsUniformDifferentiabilityPiece.image_measure_lt_top {m : ℕ}
    {f : EuclideanSpace ℝ (Fin 2) → EuclideanSpace ℝ (Fin m)}
    {A : Set (EuclideanSpace ℝ (Fin 2))} (hA : IsUniformDifferentiabilityPiece f A) :
    hausdorffMeasure2 m (f '' A) < ∞ := by
  obtain ⟨_, d, hAd⟩ := hA
  exact d.image_subset_measure_lt_top hAd

/-- A Lipschitz planar map has countably many injective Borel uniform pieces,
with rank-two derivative on every piece and a null omitted image. -/
theorem exists_countable_injective_uniform_pieces {m : ℕ} {L : ℝ≥0}
    {f : EuclideanSpace ℝ (Fin 2) → EuclideanSpace ℝ (Fin m)}
    (hf : LipschitzWith L f) :
    ∃ A : ℕ → Set (EuclideanSpace ℝ (Fin 2)),
      (∀ i, IsUniformDifferentiabilityPiece f (A i)) ∧
      (∀ i, InjOn f (A i)) ∧
      (∀ i, A i ⊆ rankTwoDifferentiabilitySet f) ∧
      hausdorffMeasure2 m (f '' ((⋃ i, A i)ᶜ)) = 0 := by
  classical
  obtain ⟨G, _, hG, hGrank, hnull⟩ := exists_disjoint_uniform_differentiability_pieces hf
  have hex (j : ℕ) : ∃ (k : ℕ) (B : Fin k → Set (EuclideanSpace ℝ (Fin 2))),
      (∀ i, MeasurableSet (B i)) ∧ (⋃ i, B i) = G j ∧
      (∀ i, B i ⊆ G j) ∧ ∀ i, InjOn f (B i) := by
    obtain ⟨hm, d, hGd⟩ := hG j
    obtain ⟨k, B, hmB, _, hu, hsub, hinj⟩ := d.exists_finite_injective_partition hm hGd
    exact ⟨k, B, hmB, hu, hsub, hinj⟩
  choose k B hmB hu hsub hinj using hex
  let P (j i : ℕ) : Set (EuclideanSpace ℝ (Fin 2)) :=
    if h : i < k j then B j ⟨i, h⟩ else ∅
  have hP (j i : ℕ) : IsUniformDifferentiabilityPiece f (P j i) ∧
      InjOn f (P j i) ∧ P j i ⊆ G j := by
    dsimp only [P]
    split_ifs with h
    · exact ⟨(hG j).mono (hmB j ⟨i, h⟩) (hsub j ⟨i, h⟩),
        hinj j ⟨i, h⟩, hsub j ⟨i, h⟩⟩
    · exact ⟨(hG j).mono MeasurableSet.empty (empty_subset _), injOn_empty _, empty_subset _⟩
  have hPu (j : ℕ) : (⋃ i, P j i) = G j := by
    apply Subset.antisymm
    · exact iUnion_subset fun i => (hP j i).2.2
    · intro x hx
      rw [← hu j] at hx
      obtain ⟨i, hi⟩ := mem_iUnion.mp hx
      exact mem_iUnion.mpr ⟨i, by simpa only [P, dite_eq_left i.isLt] using hi⟩
  let A (i : ℕ) := P (Nat.unpair i).1 (Nat.unpair i).2
  have hAu : (⋃ i, A i) = ⋃ j, G j := by
    apply Subset.antisymm
    · exact iUnion_subset fun i => ((hP _ _).2.2).trans (subset_iUnion G _)
    · intro x hx
      obtain ⟨j, hj⟩ := mem_iUnion.mp hx
      rw [← hPu j] at hj
      obtain ⟨i, hi⟩ := mem_iUnion.mp hj
      exact mem_iUnion.mpr ⟨Nat.pair j i, by simpa only [A, Nat.unpair_pair] using hi⟩
  refine ⟨A, fun i => (hP _ _).1, fun i => (hP _ _).2.1,
    fun i => ((hP _ _).2.2).trans (hGrank _), ?_⟩
  have hn : volume ({x | jacobian2 f x ≠ 0} \ ⋃ i, A i) = 0 := by
    rw [hAu, ← rankTwoDifferentiabilitySet_eq_jacobian_ne_zero]
    exact hnull
  simpa only [compl_eq_univ_sdiff] using
    hausdorffMeasure2_image_sdiff_null_of_rankTwo_cover hf hn univ

/-- Countable two-dimensional rectifiability, with measurability in the
completion of normalized Hausdorff measure. No local finiteness is assumed. -/
def CountablyH2Rectifiable (S : Set (EuclideanSpace ℝ (Fin 3))) : Prop :=
  NullMeasurableSet S (hausdorffMeasure2 3) ∧
    ∃ (f : ℕ → EuclideanSpace ℝ (Fin 2) → EuclideanSpace ℝ (Fin 3)) (L : ℕ → ℝ≥0),
      (∀ j, LipschitzWith (L j) (f j)) ∧
      hausdorffMeasure2 3 (S \ ⋃ j, range (f j)) = 0

/-- Source restriction realizes successive differences of chart images. -/
lemma exists_disjoint_injective_chart_refinement {m : ℕ}
    (f : ℕ → EuclideanSpace ℝ (Fin 2) → EuclideanSpace ℝ (Fin m))
    (A : ℕ → Set (EuclideanSpace ℝ (Fin 2))) (hf : ∀ i, Measurable (f i))
    (hA : ∀ i, IsUniformDifferentiabilityPiece (f i) (A i))
    (hinj : ∀ i, InjOn (f i) (A i)) :
    ∃ B : ℕ → Set (EuclideanSpace ℝ (Fin 2)),
      (∀ i, B i ⊆ A i) ∧ (∀ i, IsUniformDifferentiabilityPiece (f i) (B i)) ∧
      (∀ i, InjOn (f i) (B i)) ∧ Pairwise (Disjoint on fun i => f i '' B i) ∧
      (⋃ i, f i '' B i) = ⋃ i, f i '' A i := by
  let T (i : ℕ) := f i '' A i
  let B (i : ℕ) := A i ∩ f i ⁻¹' disjointed T i
  have hT (i : ℕ) : MeasurableSet (T i) := (hA i).measurableSet_image
  have hsub (i : ℕ) : B i ⊆ A i := inter_subset_left
  have hB (i : ℕ) : IsUniformDifferentiabilityPiece (f i) (B i) :=
    (hA i).mono ((hA i).1.inter ((MeasurableSet.disjointed hT i).preimage (hf i)))
      (hsub i)
  have heq (i : ℕ) : f i '' B i = disjointed T i := by
    apply Subset.antisymm
    · rintro _ ⟨x, hx, rfl⟩
      exact hx.2
    · intro y hy
      obtain ⟨x, hx, rfl⟩ := disjointed_subset T i hy
      exact ⟨x, ⟨hx, hy⟩, rfl⟩
  refine ⟨B, hsub, hB, fun i => (hinj i).mono (hsub i), ?_, ?_⟩
  · simpa only [heq] using disjoint_disjointed T
  · simp only [heq, iUnion_disjointed, T]

/-- A countably rectifiable set has disjoint finite-area Borel injective chart
images covering it up to a Hausdorff-null set. The derivative has rank two
at every parameter point of the chosen pieces. -/
theorem CountablyH2Rectifiable.exists_injective_chart_pieces
    {S : Set (EuclideanSpace ℝ (Fin 3))} (hS : CountablyH2Rectifiable S) :
    ∃ (f : ℕ → EuclideanSpace ℝ (Fin 2) → EuclideanSpace ℝ (Fin 3)) (L : ℕ → ℝ≥0)
      (A : ℕ → Set (EuclideanSpace ℝ (Fin 2))),
      (∀ i, LipschitzWith (L i) (f i)) ∧
      (∀ i, IsUniformDifferentiabilityPiece (f i) (A i)) ∧
      (∀ i, InjOn (f i) (A i)) ∧
      (∀ i, A i ⊆ rankTwoDifferentiabilitySet (f i)) ∧
      (∀ i, f i '' A i ⊆ S) ∧
      Pairwise (Disjoint on fun i => f i '' A i) ∧
      hausdorffMeasure2 3 (S \ ⋃ i, f i '' A i) = 0 := by
  classical
  obtain ⟨hSm, f, L, hf, hcover⟩ := hS
  obtain ⟨S₀, hS₀S, hS₀, hS₀ae⟩ := hSm.exists_measurable_subset_ae_eq
  have hSnull : hausdorffMeasure2 3 (S \ S₀) = 0 := ae_le_set.mp hS₀ae.symm.le
  choose A hA hinj hrank hnull using fun j => exists_countable_injective_uniform_pieces (hf j)
  let g (i : ℕ) := f (Nat.unpair i).1
  let M (i : ℕ) := L (Nat.unpair i).1
  let B (i : ℕ) := A (Nat.unpair i).1 (Nat.unpair i).2 ∩ g i ⁻¹' S₀
  have hg (i : ℕ) : LipschitzWith (M i) (g i) := hf _
  have hBsub (i : ℕ) : B i ⊆ A (Nat.unpair i).1 (Nat.unpair i).2 := inter_subset_left
  have hB (i : ℕ) : IsUniformDifferentiabilityPiece (g i) (B i) :=
    (hA _ _).mono ((hA _ _).1.inter (hS₀.preimage (hg i).continuous.measurable)) (hBsub i)
  have hBinj (i : ℕ) : InjOn (g i) (B i) := (hinj _ _).mono (hBsub i)
  have hBrank (i : ℕ) : B i ⊆ rankTwoDifferentiabilitySet (g i) :=
    (hBsub i).trans (hrank _ _)
  have hBS (i : ℕ) : g i '' B i ⊆ S := by
    rintro _ ⟨x, hx, rfl⟩
    exact hS₀S hx.2
  have hBnull : hausdorffMeasure2 3 (S \ ⋃ i, g i '' B i) = 0 := by
    have hsub : S \ (⋃ i, g i '' B i) ⊆
        (S \ S₀) ∪ (S \ ⋃ j, range (f j)) ∪
          ⋃ j, f j '' ((⋃ k, A j k)ᶜ) := by
      intro y hy
      by_cases hy₀ : y ∈ S₀
      · by_cases hyr : y ∈ ⋃ j, range (f j)
        · obtain ⟨j, x, rfl⟩ := mem_iUnion.mp hyr
          apply Or.inr
          refine mem_iUnion.mpr ⟨j, x, ?_, rfl⟩
          intro hx
          obtain ⟨k, hk⟩ := mem_iUnion.mp hx
          apply hy.2
          refine mem_iUnion.mpr ⟨Nat.pair j k, x, ?_, ?_⟩
          · simpa only [B, g, Nat.unpair_pair, mem_inter_iff, mem_preimage] using
              And.intro hk hy₀
          · simp only [g, Nat.unpair_pair]
        · exact Or.inl (Or.inr ⟨hy.1, hyr⟩)
      · exact Or.inl (Or.inl ⟨hy.1, hy₀⟩)
    exact measure_mono_null hsub
      (measure_union_null (measure_union_null hSnull hcover) (measure_iUnion_null hnull))
  obtain ⟨C, hCB, hC, hCinj, hCdisj, hCu⟩ :=
    exists_disjoint_injective_chart_refinement g B (fun i => (hg i).continuous.measurable) hB hBinj
  refine ⟨g, M, C, hg, hC, hCinj, fun i => (hCB i).trans (hBrank i),
    fun i => (image_mono (hCB i)).trans (hBS i), hCdisj, ?_⟩
  rw [hCu]
  exact hBnull

/-- In particular, rectifiable sets admit disjoint finite-area Borel pieces
contained in the original representative, with a null remainder. -/
theorem CountablyH2Rectifiable.exists_finite_area_borel_pieces
    {S : Set (EuclideanSpace ℝ (Fin 3))} (hS : CountablyH2Rectifiable S) :
    ∃ T : ℕ → Set (EuclideanSpace ℝ (Fin 3)),
      (∀ i, MeasurableSet (T i)) ∧ (∀ i, hausdorffMeasure2 3 (T i) < ∞) ∧
      (∀ i, T i ⊆ S) ∧ Pairwise (Disjoint on T) ∧
      hausdorffMeasure2 3 (S \ ⋃ i, T i) = 0 := by
  obtain ⟨f, L, A, _, hA, _, _, hAS, hd, hn⟩ := hS.exists_injective_chart_pieces
  exact ⟨fun i => f i '' A i, fun i => (hA i).measurableSet_image,
    fun i => (hA i).image_measure_lt_top, hAS, hd, hn⟩

/-- Hausdorff measure on a countably rectifiable set is sigma-finite even
when its mass on every nonempty ambient ball is infinite. -/
theorem CountablyH2Rectifiable.sigmaFinite_restrict
    {S : Set (EuclideanSpace ℝ (Fin 3))} (hS : CountablyH2Rectifiable S) :
    SigmaFinite ((hausdorffMeasure2 3).restrict S) := by
  obtain ⟨T, hm, hfin, _, _, hn⟩ := hS.exists_finite_area_borel_pieces
  let μ := (hausdorffMeasure2 3).restrict S
  have hc : μ (⋃ i, T i)ᶜ = 0 := by
    rw [Measure.restrict_apply (MeasurableSet.iUnion hm).compl]
    convert hn using 1
    congr 1
    ext x
    simp only [mem_inter_iff, mem_compl_iff, mem_sdiff, and_comm]
  refine ⟨⟨⟨fun i => T i ∪ (⋃ j, T j)ᶜ, fun _ => trivial, fun i => ?_, ?_⟩⟩⟩
  · apply (measure_union_le _ _).trans_lt
    rw [hc, add_zero]
    exact (Measure.restrict_apply_le S (T i)).trans_lt (hfin i)
  · rw [← iUnion_union, union_compl_self]

/-- Lipschitz maps in any finite ambient dimensions preserve null area sets. -/
lemma hausdorffMeasure2_image_null_of_lipschitz {n m : ℕ} {K : ℝ≥0}
    {f : EuclideanSpace ℝ (Fin n) → EuclideanSpace ℝ (Fin m)}
    (hf : LipschitzWith K f) {A : Set (EuclideanSpace ℝ (Fin n))}
    (hA : hausdorffMeasure2 n A = 0) : hausdorffMeasure2 m (f '' A) = 0 := by
  have h :=
    hausdorffMeasure2_image_le_of_lipschitzOn (hf.lipschitzOnWith (s := A))
  rw [hA, mul_zero] at h
  exact le_antisymm h bot_le

/-- The Lipschitz image of a rectifiable set is measurable for completed
Hausdorff area, proved using the planar-source area formula on its charts. -/
theorem CountablyH2Rectifiable.nullMeasurableSet_image
    {S : Set (EuclideanSpace ℝ (Fin 3))} (hS : CountablyH2Rectifiable S)
    {Φ : EuclideanSpace ℝ (Fin 3) → EuclideanSpace ℝ (Fin 3)} {K : ℝ≥0}
    (hΦ : LipschitzWith K Φ) : NullMeasurableSet (Φ '' S) (hausdorffMeasure2 3) := by
  obtain ⟨f, L, A, hf, hA, _, _, hAS, _, hn⟩ := hS.exists_injective_chart_pieces
  let C := ⋃ i, f i '' A i
  have hCS : C ⊆ S := iUnion_subset hAS
  have heq : S = C ∪ (S \ C) := by
    ext x
    simp only [mem_union, mem_sdiff]
    constructor
    · intro hx
      by_cases hc : x ∈ C
      · exact Or.inl hc
      · exact Or.inr ⟨hx, hc⟩
    · rintro (hc | hx)
      · exact hCS hc
      · exact hx.1
  have hC : NullMeasurableSet (Φ '' C) (hausdorffMeasure2 3) := by
    rw [show Φ '' C = ⋃ i, (Φ ∘ f i) '' A i by
      simp only [C, image_iUnion, image_image, Function.comp_def]]
    exact NullMeasurableSet.iUnion fun i =>
      nullMeasurableSet_image_lipschitz_planar (hΦ.comp (hf i)) (hA i).1
  have hN : NullMeasurableSet (Φ '' (S \ C)) (hausdorffMeasure2 3) :=
    .of_null (hausdorffMeasure2_image_null_of_lipschitz hΦ hn)
  conv_lhs => rw [heq, image_union]
  exact hC.union hN

/-- Countable rectifiability is preserved by a globally Lipschitz map. -/
theorem CountablyH2Rectifiable.image
    {S : Set (EuclideanSpace ℝ (Fin 3))} (hS : CountablyH2Rectifiable S)
    {Φ : EuclideanSpace ℝ (Fin 3) → EuclideanSpace ℝ (Fin 3)} {K : ℝ≥0}
    (hΦ : LipschitzWith K Φ) : CountablyH2Rectifiable (Φ '' S) := by
  have hmes := hS.nullMeasurableSet_image hΦ
  obtain ⟨_, f, L, hf, hn⟩ := hS
  refine ⟨hmes, fun i => Φ ∘ f i, fun i => K * L i,
    fun i => hΦ.comp (hf i), ?_⟩
  apply measure_mono_null _ (hausdorffMeasure2_image_null_of_lipschitz hΦ hn)
  rintro y ⟨⟨x, hx, rfl⟩, hy⟩
  refine ⟨x, ⟨hx, ?_⟩, rfl⟩
  intro hxrange
  obtain ⟨i, z, hz⟩ := mem_iUnion.mp hxrange
  exact hy (mem_iUnion.mpr ⟨i, z, by simp only [Function.comp_apply, hz]⟩)

/-- Every Borel portion of a planar Lipschitz image is rectifiable. -/
theorem countablyH2Rectifiable_image {f : EuclideanSpace ℝ (Fin 2) →
    EuclideanSpace ℝ (Fin 3)} {L : ℝ≥0} (hf : LipschitzWith L f)
    {A : Set (EuclideanSpace ℝ (Fin 2))} (hA : MeasurableSet A) :
    CountablyH2Rectifiable (f '' A) := by
  refine ⟨nullMeasurableSet_image_lipschitz_planar hf hA,
    fun _ => f, fun _ => L, fun _ => hf, ?_⟩
  rw [iUnion_const, sdiff_eq_empty.mpr (image_subset_range _ _), measure_empty]

theorem CountablyH2Rectifiable.mono
    {S T : Set (EuclideanSpace ℝ (Fin 3))} (hS : CountablyH2Rectifiable S)
    (hT : NullMeasurableSet T (hausdorffMeasure2 3)) (hTS : T ⊆ S) :
    CountablyH2Rectifiable T := by
  obtain ⟨_, f, L, hf, hn⟩ := hS
  exact ⟨hT, f, L, hf, measure_mono_null (sdiff_subset_sdiff_left hTS) hn⟩

/-- The area measure is the sum of Jacobian-weighted chart pushforwards.
The pieces lie in the original set and may omit a Hausdorff-null remainder. -/
theorem hausdorffMeasure2_restrict_eq_sum_chart_maps
    {S : Set (EuclideanSpace ℝ (Fin 3))}
    (f : ℕ → EuclideanSpace ℝ (Fin 2) → EuclideanSpace ℝ (Fin 3))
    (A : ℕ → Set (EuclideanSpace ℝ (Fin 2))) (hf : ∀ i, Measurable (f i))
    (hA : ∀ i, IsUniformDifferentiabilityPiece (f i) (A i))
    (hinj : ∀ i, InjOn (f i) (A i)) (hAS : ∀ i, f i '' A i ⊆ S)
    (hd : Pairwise (Disjoint on fun i => f i '' A i))
    (hn : hausdorffMeasure2 3 (S \ ⋃ i, f i '' A i) = 0) :
    (hausdorffMeasure2 3).restrict S = Measure.sum (fun i =>
      Measure.map (f i) ((volume.restrict (A i)).withDensity
        (fun x => ENNReal.ofReal (jacobian2 (f i) x)))) := by
  have hCS : (⋃ i, f i '' A i) ⊆ S := iUnion_subset hAS
  have hae : S =ᵐ[hausdorffMeasure2 3] ⋃ i, f i '' A i := by
    apply ae_eq_set.mpr
    exact ⟨hn, by rw [sdiff_eq_empty.mpr hCS, measure_empty]⟩
  rw [Measure.restrict_congr_set hae,
    Measure.restrict_iUnion hd (fun i => (hA i).measurableSet_image)]
  congr 1
  funext i
  obtain ⟨hm, d, hAd⟩ := hA i
  exact (d.map_withDensity_jacobian_restrict (hf i) hm hAd (hinj i)).symm

end LiquidDrop

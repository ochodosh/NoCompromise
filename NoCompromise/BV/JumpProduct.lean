module

public import NoCompromise.BV.JumpKernel

@[expose] public section

/-!
# Integrating slice variation measures

Borel product sections have Lebesgue-measurable slice masses. Countable
additivity constructs the integrated measure and gives Tonelli and real Fubini
formulas. Strict approximation bounds its total mass for globally BV functions;
compact cutoffs prove local finiteness for locally BV functions. None of these
steps assumes the directional derivative or total-variation disintegration.
-/

noncomputable section
open MeasureTheory Filter Set Metric TopologicalSpace
open scoped ENNReal Topology
namespace LiquidDrop

/-- Almost-everywhere local finiteness and measurable Borel evaluations imply
measurability of all Borel product sections, without any assumed joint density. -/
theorem aemeasurable_measure_prod_section {α β : Type*} [MeasurableSpace α]
    {ν : Measure α} [MetricSpace β] [ProperSpace β] [SecondCountableTopology β]
    [MeasurableSpace β] [BorelSpace β] (c : β) {κ : α → Measure β}
    (hfin : ∀ᵐ x ∂ν, IsFiniteMeasureOnCompacts (κ x))
    (hκ : ∀ A : Set β, MeasurableSet A → AEMeasurable (fun x => κ x A) ν) :
    ∀ A : Set (α × β), MeasurableSet A →
      AEMeasurable (fun x => κ x (Prod.mk x ⁻¹' A)) ν := by
  have hrestrict (k : ℕ) : ∀ A : Set (α × β), MeasurableSet A →
      AEMeasurable (fun x => (κ x).restrict (ball c k) (Prod.mk x ⁻¹' A)) ν := by
    intro A hA
    induction A, hA using MeasurableSpace.induction_on_inter
      generateFrom_prod.symm isPiSystem_prod with
    | empty => simp
    | basic A hA =>
      obtain ⟨S, hS, T, hT, rfl⟩ := hA
      have hm : AEMeasurable (fun x => (κ x).restrict (ball c k) T) ν := by
        simpa only [Measure.restrict_apply hT] using hκ _ (hT.inter measurableSet_ball)
      classical
      have he : (fun x => (κ x).restrict (ball c k) (Prod.mk x ⁻¹' (S ×ˢ T))) =
          S.indicator (fun x => (κ x).restrict (ball c k) T) := by
        funext x
        by_cases hx : x ∈ S <;> simp [hx]
      rw [he]
      exact hm.indicator hS
    | compl A hA ih =>
      have hmass : AEMeasurable (fun x => (κ x).restrict (ball c k) univ) ν := by
        simpa only [Measure.restrict_apply_univ] using hκ _ measurableSet_ball
      apply (hmass.sub ih).congr
      filter_upwards [hfin] with x hx
      let := hx
      have htop : (κ x).restrict (ball c k) (Prod.mk x ⁻¹' A) ≠ ∞ := by
        apply ne_top_of_le_ne_top (measure_ball_lt_top (μ := κ x) (x := c) (r := k)).ne
        exact le_trans (measure_mono (subset_univ _)) (by simp)
      simpa only [preimage_compl, Pi.sub_apply] using
        (measure_compl (measurable_prodMk_left hA) htop).symm
    | iUnion A hd hA ih =>
      have he (x : α) : (κ x).restrict (ball c k) (Prod.mk x ⁻¹' ⋃ j, A j) =
          ∑' j : ℕ, (κ x).restrict (ball c k) (Prod.mk x ⁻¹' A j) := by
        rw [preimage_iUnion, measure_iUnion]
        exacts [hd.mono fun _ _ => Disjoint.preimage _,
          fun j => measurable_prodMk_left (hA j)]
      have hm : AEMeasurable (fun x => ∑' j : ℕ,
          (κ x).restrict (ball c k) (Prod.mk x ⁻¹' A j)) ν := AEMeasurable.tsum ih
      simpa only [he] using hm
  intro A hA
  have hm := AEMeasurable.iSup (fun k : ℕ => hrestrict k A hA)
  apply hm.congr
  exact ae_of_all _ fun x => by
    have hmono : Monotone (fun k : ℕ => (Prod.mk x ⁻¹' A) ∩ ball c (k : ℝ)) := by
      intro j k hjk
      exact inter_subset_inter_right _ (ball_subset_ball (Nat.cast_le.mpr hjk))
    have he := hmono.measure_iUnion (μ := κ x)
    simpa only [← inter_iUnion, iUnion_ball_nat, inter_univ,
      Measure.restrict_apply (measurable_prodMk_left hA)] using he.symm

/-- Integrating the actual slice measures defines a Borel measure on the product.
The construction uses the proved section measurability, not a postulated disintegration. -/
def sliceProductMeasure {α β : Type*} [MeasurableSpace α]
    (ν : Measure α) [MetricSpace β] [ProperSpace β] [SecondCountableTopology β]
    [MeasurableSpace β] [BorelSpace β] (c : β) (κ : α → Measure β)
    (hfin : ∀ᵐ x ∂ν, IsFiniteMeasureOnCompacts (κ x))
    (hκ : ∀ A : Set β, MeasurableSet A → AEMeasurable (fun x => κ x A) ν) :
    Measure (α × β) :=
  Measure.ofMeasurable (fun A _ => ∫⁻ x, κ x (Prod.mk x ⁻¹' A) ∂ν)
    (by simp)
    (by
      intro A hA hd
      have he (x : α) : κ x (Prod.mk x ⁻¹' ⋃ j, A j) =
          ∑' j : ℕ, κ x (Prod.mk x ⁻¹' A j) := by
        rw [preimage_iUnion, measure_iUnion]
        exacts [hd.mono fun _ _ => Disjoint.preimage _,
          fun j => measurable_prodMk_left (hA j)]
      simp only [he]
      exact lintegral_tsum (fun j => aemeasurable_measure_prod_section c hfin hκ _ (hA j)))

lemma sliceProductMeasure_apply {α β : Type*} [MeasurableSpace α]
    (ν : Measure α) [MetricSpace β] [ProperSpace β] [SecondCountableTopology β]
    [MeasurableSpace β] [BorelSpace β] (c : β) (κ : α → Measure β)
    (hfin : ∀ᵐ x ∂ν, IsFiniteMeasureOnCompacts (κ x))
    (hκ : ∀ A : Set β, MeasurableSet A → AEMeasurable (fun x => κ x A) ν)
    {A : Set (α × β)} (hA : MeasurableSet A) :
    sliceProductMeasure ν c κ hfin hκ A = ∫⁻ x, κ x (Prod.mk x ⁻¹' A) ∂ν :=
  Measure.ofMeasurable_apply A hA

/-- Nonnegative Borel weights have Lebesgue-measurable integrals against the
slice measures, even though only almost-everywhere local finiteness is assumed. -/
theorem aemeasurable_lintegral_sliceMeasure {α β : Type*} [MeasurableSpace α]
    {ν : Measure α} [MetricSpace β] [ProperSpace β] [SecondCountableTopology β]
    [MeasurableSpace β] [BorelSpace β] (c : β) {κ : α → Measure β}
    (hfin : ∀ᵐ x ∂ν, IsFiniteMeasureOnCompacts (κ x))
    (hκ : ∀ A : Set β, MeasurableSet A → AEMeasurable (fun x => κ x A) ν) :
    ∀ q : α × β → ℝ≥0∞, Measurable q →
      AEMeasurable (fun x => ∫⁻ t, q (x, t) ∂κ x) ν := by
  intro q hq
  refine Measurable.ennreal_induction
    (motive := fun q => AEMeasurable (fun x => ∫⁻ t, q (x, t) ∂κ x) ν) ?_ ?_ ?_ hq
  · intro b A hA
    simp only [← indicator_comp_right]
    suffices AEMeasurable (fun x => b * κ x (Prod.mk x ⁻¹' A)) ν by
      simpa [lintegral_indicator (measurable_prodMk_left hA)] using this
    exact (aemeasurable_measure_prod_section c hfin hκ A hA).const_mul b
  · intro f g _ hf _ hif hig
    simp only [Pi.add_apply]
    have he (x : α) : (∫⁻ t, f (x, t) + g (x, t) ∂κ x) =
        (∫⁻ t, f (x, t) ∂κ x) + ∫⁻ t, g (x, t) ∂κ x :=
      lintegral_add_left (hf.comp measurable_prodMk_left) _
    have hh := hif.add hig
    change AEMeasurable (fun x => (∫⁻ t, f (x, t) ∂κ x) +
      ∫⁻ t, g (x, t) ∂κ x) ν at hh
    simpa only [he] using hh
  · intro f hf hmono hi
    have he (x : α) : (∫⁻ t, ⨆ j, f j (x, t) ∂κ x) =
        ⨆ j, ∫⁻ t, f j (x, t) ∂κ x :=
      lintegral_iSup (fun j => (hf j).comp measurable_prodMk_left)
        (fun i j hij t => hmono hij (x, t))
    simpa only [iSup_apply, he] using AEMeasurable.iSup hi

/-- Tonelli's formula for the constructed integrated slice measure. -/
theorem lintegral_sliceProductMeasure {α β : Type*} [MeasurableSpace α]
    (ν : Measure α) [MetricSpace β] [ProperSpace β] [SecondCountableTopology β]
    [MeasurableSpace β] [BorelSpace β] (c : β) (κ : α → Measure β)
    (hfin : ∀ᵐ x ∂ν, IsFiniteMeasureOnCompacts (κ x))
    (hκ : ∀ A : Set β, MeasurableSet A → AEMeasurable (fun x => κ x A) ν) :
    ∀ q : α × β → ℝ≥0∞, Measurable q →
      (∫⁻ z, q z ∂sliceProductMeasure ν c κ hfin hκ) =
        ∫⁻ x, ∫⁻ t, q (x, t) ∂κ x ∂ν := by
  intro q hq
  refine Measurable.ennreal_induction
    (motive := fun q => (∫⁻ z, q z ∂sliceProductMeasure ν c κ hfin hκ) =
      ∫⁻ x, ∫⁻ t, q (x, t) ∂κ x ∂ν) ?_ ?_ ?_ hq
  · intro b A hA
    rw [lintegral_indicator hA]
    simp only [lintegral_const, Measure.restrict_apply_univ,
      ← indicator_comp_right, lintegral_indicator (measurable_prodMk_left hA),
      Function.comp_def]
    rw [sliceProductMeasure_apply ν c κ hfin hκ hA]
    exact (lintegral_const_mul'' b (aemeasurable_measure_prod_section c hfin hκ A hA)).symm
  · intro f g _ hf _ hif hig
    simp only [Pi.add_apply]
    rw [lintegral_add_left hf, hif, hig]
    have he (x : α) : (∫⁻ t, f (x, t) + g (x, t) ∂κ x) =
        (∫⁻ t, f (x, t) ∂κ x) + ∫⁻ t, g (x, t) ∂κ x :=
      lintegral_add_left (hf.comp measurable_prodMk_left) _
    simp only [he]
    exact (lintegral_add_left'
      (aemeasurable_lintegral_sliceMeasure c hfin hκ f hf) _).symm
  · intro f hf hmono hi
    rw [lintegral_iSup hf hmono]
    simp only [hi]
    have he (x : α) : (∫⁻ t, ⨆ j, f j (x, t) ∂κ x) =
        ⨆ j, ∫⁻ t, f j (x, t) ∂κ x :=
      lintegral_iSup (fun j => (hf j).comp measurable_prodMk_left)
        (fun i j hij t => hmono hij (x, t))
    simp only [he]
    exact (lintegral_iSup' (fun j => aemeasurable_lintegral_sliceMeasure c hfin hκ _ (hf j))
      (ae_of_all _ fun x i j hij => lintegral_mono fun t => hmono hij (x, t))).symm

/-- The real slice-polar kernel exists for arbitrary locally BV functions;
no binary-value assumption is needed for its measurability. -/
theorem IsLocallyBVOn.exists_measurable_real_line_polar {n : ℕ}
    {f : EuclideanSpace ℝ (Fin (n + 1)) → ℝ} (hf : IsLocallyBVOn f univ) :
    ∃ μ : EuclideanSpace ℝ (Fin n) → Measure ℝ,
    ∃ σ : EuclideanSpace ℝ (Fin n) → ℝ → ℝ,
      (∀ᵐ x, IsRealBVPolar (fun t => f (graphAppendN x t)) (μ x) (σ x)) ∧
      ∀ A : Set ℝ, MeasurableSet A → AEMeasurable (fun x => μ x A) volume := by
  classical
  have hex (x : EuclideanSpace ℝ (Fin n)) : ∃ μ : Measure ℝ, ∃ σ : ℝ → ℝ,
      IsLocallyBVOn (lineSlice f x) univ →
        IsRealBVPolar (fun t => f (graphAppendN x t)) μ σ := by
    by_cases hx : IsLocallyBVOn (lineSlice f x) univ
    · obtain ⟨μ, σ, hμ⟩ := exists_real_bv_polar
        (f := fun t => f (graphAppendN x t)) hx
      exact ⟨μ, σ, fun _ => hμ⟩
    · exact ⟨0, fun _ => 0, fun h => (hx h).elim⟩
  choose μ σ hμ using hex
  have hg := hf.ae_lineSlice.mono fun x hx => hμ x hx
  refine ⟨μ, σ, hg, ?_⟩
  have hp := (lineCoordinateEquiv_measurePreserving n).symm (lineCoordinateEquiv n)
  have hfm := (locallyIntegrableOn_univ.mp hf.1).aestronglyMeasurable
  apply aemeasurable_realSlicePolar_measure (f := lineSlice f)
  · exact hfm.comp_measurePreserving hp
  · exact hf.ae_lineSlice.mono fun _ h => locallyIntegrableOn_univ.mp h.1
  · filter_upwards [hg] with x hx
    simpa only [Function.comp_def, lineSlice, euclideanOneReal_symm_apply] using hx

/-- The constructed product of the slice variation measures has finite mass
for a globally BV function, with the bound supplied by strict approximation. -/
theorem IsBVOn.sliceProductMeasure_mass_le {n : ℕ}
    {f : EuclideanSpace ℝ (Fin (n + 1)) → ℝ} (hf : IsBVOn f univ)
    {κ : EuclideanSpace ℝ (Fin n) → Measure ℝ}
    {σ : EuclideanSpace ℝ (Fin n) → ℝ → ℝ}
    (hp : ∀ᵐ x, IsRealBVPolar (fun t => f (graphAppendN x t)) (κ x) (σ x))
    (hκ : ∀ A : Set ℝ, MeasurableSet A → AEMeasurable (fun x => κ x A) volume) :
    sliceProductMeasure volume 0 κ (hp.mono fun _ h => h.finiteOnCompacts) hκ univ ≤
      variation f univ := by
  rw [sliceProductMeasure_apply _ _ _ _ _ MeasurableSet.univ]
  simp only [preimage_univ]
  have he : (fun x => κ x univ) =ᵐ[volume] (fun x => variation (lineSlice f x) univ) := by
    filter_upwards [hp] with x hx
    change κ x univ = variation (fun t : EuclideanSpace ℝ (Fin 1) =>
      f (graphAppendN x (t 0))) univ
    simpa only [preimage_univ, Function.comp_def, euclideanOneReal_apply] using
      hx.open_eq univ isOpen_univ
  rw [lintegral_congr_ae he]
  exact hf.ae_lineSlice_and_lintegral_variation_le.2

lemma IsBVOn.isFiniteMeasure_sliceProductMeasure {n : ℕ}
    {f : EuclideanSpace ℝ (Fin (n + 1)) → ℝ} (hf : IsBVOn f univ)
    {κ : EuclideanSpace ℝ (Fin n) → Measure ℝ}
    {σ : EuclideanSpace ℝ (Fin n) → ℝ → ℝ}
    (hp : ∀ᵐ x, IsRealBVPolar (fun t => f (graphAppendN x t)) (κ x) (σ x))
    (hκ : ∀ A : Set ℝ, MeasurableSet A → AEMeasurable (fun x => κ x A) volume) :
    IsFiniteMeasure (sliceProductMeasure volume 0 κ
      (hp.mono fun _ h => h.finiteOnCompacts) hκ) :=
  ⟨(hf.sliceProductMeasure_mass_le hp hκ).trans_lt hf.2⟩

/-- Real integrable Borel weights satisfy Fubini for the constructed slice measure. -/
theorem integral_sliceProductMeasure {α β : Type*} [MeasurableSpace α]
    (ν : Measure α) [MetricSpace β] [ProperSpace β] [SecondCountableTopology β]
    [MeasurableSpace β] [BorelSpace β] (c : β) (κ : α → Measure β)
    (hfin : ∀ᵐ x ∂ν, IsFiniteMeasureOnCompacts (κ x))
    (hκ : ∀ A : Set β, MeasurableSet A → AEMeasurable (fun x => κ x A) ν)
    {q : α × β → ℝ} (hq : Measurable q)
    (hqi : Integrable q (sliceProductMeasure ν c κ hfin hκ)) :
    (∀ᵐ x ∂ν, Integrable (fun t => q (x, t)) (κ x)) ∧
    Integrable (fun x => ∫ t, q (x, t) ∂κ x) ν ∧
    (∫ z, q z ∂sliceProductMeasure ν c κ hfin hκ) =
      ∫ x, ∫ t, q (x, t) ∂κ x ∂ν := by
  let p : α → ℝ≥0∞ := fun x => ∫⁻ t, ENNReal.ofReal (q (x, t)) ∂κ x
  let m : α → ℝ≥0∞ := fun x => ∫⁻ t, ENNReal.ofReal (-q (x, t)) ∂κ x
  have hpm : AEMeasurable p ν :=
    aemeasurable_lintegral_sliceMeasure c hfin hκ _ hq.ennreal_ofReal
  have hmm : AEMeasurable m ν :=
    aemeasurable_lintegral_sliceMeasure c hfin hκ _ hq.neg.ennreal_ofReal
  have hpfin : (∫⁻ x, p x ∂ν) < ∞ := by
    rw [← lintegral_sliceProductMeasure ν c κ hfin hκ _ hq.ennreal_ofReal]
    exact (lintegral_ofReal_le_lintegral_enorm q).trans_lt hqi.2
  have hmfin : (∫⁻ x, m x ∂ν) < ∞ := by
    rw [← lintegral_sliceProductMeasure ν c κ hfin hκ
      (fun z => ENNReal.ofReal (-q z)) hq.neg.ennreal_ofReal]
    exact (lintegral_ofReal_le_lintegral_enorm (-q)).trans_lt hqi.neg.2
  have hnfin : (∫⁻ x, ∫⁻ t, ‖q (x, t)‖ₑ ∂κ x ∂ν) < ∞ := by
    rw [← lintegral_sliceProductMeasure ν c κ hfin hκ _ hq.enorm]
    exact hqi.2
  have hnmeas := aemeasurable_lintegral_sliceMeasure c hfin hκ _ hq.enorm
  have hline : ∀ᵐ x ∂ν, Integrable (fun t => q (x, t)) (κ x) := by
    filter_upwards [ae_lt_top' hnmeas hnfin.ne] with x hx
    exact ⟨(hq.comp measurable_prodMk_left).aestronglyMeasurable, hx⟩
  have hpi := integrable_toReal_of_lintegral_ne_top hpm hpfin.ne
  have hmi := integrable_toReal_of_lintegral_ne_top hmm hmfin.ne
  have he : (fun x => ∫ t, q (x, t) ∂κ x) =ᵐ[ν] (fun x => (p x).toReal - (m x).toReal) :=
    hline.mono fun x hx => integral_eq_lintegral_pos_part_sub_lintegral_neg_part hx
  refine ⟨hline, (hpi.sub hmi).congr he.symm, ?_⟩
  rw [integral_congr_ae he, integral_sub hpi hmi,
    integral_toReal hpm (ae_lt_top' hpm hpfin.ne),
    integral_toReal hmm (ae_lt_top' hmm hmfin.ne)]
  rw [← lintegral_sliceProductMeasure ν c κ hfin hκ _ hq.ennreal_ofReal,
    ← lintegral_sliceProductMeasure ν c κ hfin hκ
      (fun z => ENNReal.ofReal (-q z)) hq.neg.ennreal_ofReal]
  exact integral_eq_lintegral_pos_part_sub_lintegral_neg_part hqi

/-- The integrated slice variation is locally finite for every locally BV
function. Compact cutoffs reduce the bound to the proved global slicing estimate. -/
theorem IsLocallyBVOn.isFiniteMeasureOnCompacts_sliceProductMeasure {n : ℕ}
    {f : EuclideanSpace ℝ (Fin (n + 1)) → ℝ} (hf : IsLocallyBVOn f univ)
    {κ : EuclideanSpace ℝ (Fin n) → Measure ℝ}
    {σ : EuclideanSpace ℝ (Fin n) → ℝ → ℝ}
    (hp : ∀ᵐ x, IsRealBVPolar (fun t => f (graphAppendN x t)) (κ x) (σ x))
    (hκ : ∀ A : Set ℝ, MeasurableSet A → AEMeasurable (fun x => κ x A) volume) :
    IsFiniteMeasureOnCompacts (sliceProductMeasure volume 0 κ
      (hp.mono fun _ h => h.finiteOnCompacts) hκ) := by
  constructor
  intro K hK
  have hcont : Continuous (fun p : EuclideanSpace ℝ (Fin n) × ℝ =>
      graphAppendN p.1 p.2) :=
    ((graphBaseN n).continuous.comp continuous_fst).add
      (continuous_snd.smul continuous_const)
  obtain ⟨R, hR⟩ := (hK.image hcont).isBounded.subset_closedBall 0
  let b : ContDiffBump (0 : EuclideanSpace ℝ (Fin (n + 1))) :=
    ⟨max R 0 + 1, max R 0 + 2, by positivity, by linarith⟩
  let g : EuclideanSpace ℝ (Fin (n + 1)) → ℝ := fun z => b z * f z
  have hg : IsBVOn g univ := hf.isBVOn_mul_compact_factor isOpen_univ
    b.contDiff b.hasCompactSupport (subset_univ _)
  rw [sliceProductMeasure_apply _ _ _ _ _ hK.measurableSet]
  apply lt_of_le_of_lt _ hg.2
  apply le_trans _ hg.ae_lineSlice_and_lintegral_variation_le.2
  apply lintegral_mono_ae
  filter_upwards [hp] with x hx
  let O : Set ℝ := {t | graphAppendN x t ∈ ball 0 b.rIn}
  have hO : IsOpen O := isOpen_ball.preimage
    (continuous_const.add (continuous_id.smul continuous_const))
  have hKO : Prod.mk x ⁻¹' K ⊆ O := by
    intro t ht
    have hh := hR (mem_image_of_mem (fun p : EuclideanSpace ℝ (Fin n) × ℝ =>
      graphAppendN p.1 p.2) ht)
    exact closedBall_subset_ball (show R < b.rIn by dsimp [b]; linarith [le_max_left R 0]) hh
  apply (measure_mono hKO).trans
  rw [hx.open_eq O hO]
  have he : variation ((fun t => f (graphAppendN x t)) ∘ euclideanOneReal)
      (euclideanOneReal ⁻¹' O) = variation (lineSlice g x) (euclideanOneReal ⁻¹' O) := by
    apply variation_congr_ae
    filter_upwards [ae_restrict_mem (hO.preimage euclideanOneReal.continuous).measurableSet]
      with t ht
    change f (graphAppendN x (t 0)) = b (graphAppendN x (t 0)) * f (graphAppendN x (t 0))
    change graphAppendN x (t 0) ∈ ball 0 b.rIn at ht
    rw [b.one_of_mem_closedBall (ball_subset_closedBall ht), one_mul]
  rw [he]
  exact variation_mono MeasurableSet.univ (subset_univ _)

end LiquidDrop

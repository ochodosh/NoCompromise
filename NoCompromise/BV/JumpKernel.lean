module

public import NoCompromise.BV.JumpSlicing
public import Mathlib.Topology.ContinuousMap.SecondCountableSpace
public import Mathlib.Probability.Kernel.Defs

@[expose] public section

/-!
# Measurability of slice derivative measures

A fixed countable family of admissible divergence tests computes variation on
any region with compact closure. Fubini therefore gives measurability of
parameterized variation. Almost-everywhere local finiteness and measurable-set
induction extend measure evaluations from relatively compact open sets to all
Borel sets. Applied to the actual one-dimensional polar measures, this yields
Lebesgue-measurable slice measure evaluations and a genuine measure kernel on
the completed transverse Lebesgue space.

The full Borel-set disintegration identities are established separately.
-/

noncomputable section
open MeasureTheory Filter Set Metric TopologicalSpace
open scoped ENNReal Topology
namespace LiquidDrop

lemma continuous_integral_mul_continuousMap {K : Type*} [TopologicalSpace K]
    [CompactSpace K] [MeasurableSpace K] [BorelSpace K]
    {μ : Measure K} {f : K → ℝ} (hf : Integrable f μ) :
    Continuous (fun v : C(K, ℝ) => ∫ x, f x * v x ∂μ) := by
  apply continuous_iff_continuousAt.mpr
  intro v
  apply continuousAt_of_dominated (bound := fun x => ‖f x‖ * (‖v‖ + 1))
  · exact Eventually.of_forall fun w => hf.aestronglyMeasurable.mul
      w.continuous.aestronglyMeasurable
  · filter_upwards [(continuous_norm.tendsto v) (Iio_mem_nhds (lt_add_one ‖v‖))] with w hw
    exact ae_of_all _ fun x => by
      rw [norm_mul]
      exact mul_le_mul_of_nonneg_left ((ContinuousMap.norm_coe_le_norm w x).trans hw.le)
        (norm_nonneg _)
  · exact hf.norm.mul_const _
  · exact ae_of_all _ fun x => continuousAt_const.mul (continuous_eval_const x).continuousAt

/-- On a compact metrizable space one countable family of tests computes all the
integral suprema, simultaneously for every integrable density and every measure. -/
lemma exists_countable_integral_iSup {K ι : Type*} [TopologicalSpace K]
    [CompactSpace K] [T2Space K] [SecondCountableTopology K] [MeasurableSpace K] [BorelSpace K]
    (v : ι → C(K, ℝ)) :
    ∃ s : Set ι, s.Countable ∧ ∀ (μ : Measure K) (f : K → ℝ), Integrable f μ →
      (⨆ i, ENNReal.ofReal (∫ x, f x * v i x ∂μ)) =
        ⨆ i ∈ s, ENNReal.ofReal (∫ x, f x * v i x ∂μ) := by
  classical
  let A : Set C(K, ℝ) := range v
  obtain ⟨D, hDc, hDd⟩ := exists_countable_dense A
  have hpre (w : A) : ∃ i, v i = w.1 := w.2
  choose pick hpick using hpre
  let s : Set ι := pick '' D
  refine ⟨s, hDc.image pick, ?_⟩
  intro μ f hf
  apply le_antisymm
  · apply iSup_le
    intro i
    have hc : Continuous (fun w : A => ENNReal.ofReal (∫ x, f x * w.1 x ∂μ)) :=
      ENNReal.continuous_ofReal.comp ((continuous_integral_mul_continuousMap hf).comp
        continuous_subtype_val)
    have hbound : ∀ w : A, ENNReal.ofReal (∫ x, f x * w.1 x ∂μ) ≤
        ⨆ j ∈ s, ENNReal.ofReal (∫ x, f x * v j x ∂μ) := by
      have hsub : D ⊆ {w : A | ENNReal.ofReal (∫ x, f x * w.1 x ∂μ) ≤
          ⨆ j ∈ s, ENNReal.ofReal (∫ x, f x * v j x ∂μ)} := by
        intro w hw
        change ENNReal.ofReal (∫ x, f x * w.1 x ∂μ) ≤ _
        rw [← hpick w]
        exact le_iSup_of_le (pick w) (le_iSup_of_le (mem_image_of_mem pick hw) le_rfl)
      exact fun w => closure_minimal hsub (isClosed_le hc continuous_const) (hDd w)
    exact hbound ⟨v i, mem_range_self i⟩
  · exact iSup₂_le fun i _ => le_iSup (fun j => ENNReal.ofReal (∫ x, f x * v j x ∂μ)) i

/-- Variation on a relatively compact region is a countable supremum of its
original admissible divergence pairings. The family is independent of the function. -/
lemma exists_countable_variation_tests {n : ℕ}
    {U : Set (EuclideanSpace ℝ (Fin n))} (hK : IsCompact (closure U)) :
    ∃ S : Set {X : EuclideanSpace ℝ (Fin n) → EuclideanSpace ℝ (Fin n) //
        IsVariationTestField U X}, S.Countable ∧
      ∀ f : EuclideanSpace ℝ (Fin n) → ℝ, IntegrableOn f U →
        variation f U = ⨆ X ∈ S, ENNReal.ofReal (∫ x in U, f x * divergenceN X.1 x) := by
  let K := closure U
  let : CompactSpace K := isCompact_iff_compactSpace.mp hK
  let T := {X : EuclideanSpace ℝ (Fin n) → EuclideanSpace ℝ (Fin n) //
    IsVariationTestField U X}
  let v : T → C(K, ℝ) := fun X =>
    ⟨fun x => divergenceN X.1 x, (continuous_divergenceN X.2.1).comp continuous_subtype_val⟩
  obtain ⟨S, hSc, hS⟩ := exists_countable_integral_iSup v
  refine ⟨S, hSc, ?_⟩
  intro f hf
  let μ : Measure K := Measure.comap Subtype.val (volume.restrict U)
  have hfi : Integrable (fun x : K => f x) μ := by
    exact (integrableOn_iff_comap_subtypeVal hK.measurableSet).mp hf.integrableOn
  have he (X : T) : (∫ x : K, f x * v X x ∂μ) =
      ∫ x in U, f x * divergenceN X.1 x := by
    change (∫ x : K, (fun z => f z * divergenceN X.1 z) x
      ∂Measure.comap Subtype.val (volume.restrict U)) = _
    have he0 := integral_subtype_comap (μ := volume.restrict U) (s := K)
      hK.measurableSet (fun z => f z * divergenceN X.1 z)
    rw [Measure.restrict_restrict hK.measurableSet,
      inter_eq_right.mpr (show U ⊆ K from subset_closure)] at he0
    exact he0
  have hh := hS μ (fun x : K => f x) hfi
  simp only [he] at hh
  simpa only [T, variation, iSup_subtype] using hh

/-- Parameterized locally integrable functions have measurable variation on each
relatively compact region. Product almost-everywhere measurability suffices. -/
theorem aemeasurable_variation_of_prod {α : Type*} [MeasurableSpace α]
    {ν : Measure α} {n : ℕ} {U : Set (EuclideanSpace ℝ (Fin n))}
    (hK : IsCompact (closure U)) {f : α → EuclideanSpace ℝ (Fin n) → ℝ}
    (hf : AEStronglyMeasurable (Function.uncurry f) (ν.prod (volume.restrict U)))
    (hfi : ∀ᵐ x ∂ν, IntegrableOn (f x) U) :
    AEMeasurable (fun x => variation (f x) U) ν := by
  classical
  obtain ⟨S, hSc, hS⟩ := exists_countable_variation_tests hK
  have htest (X : {X : EuclideanSpace ℝ (Fin n) → EuclideanSpace ℝ (Fin n) //
      IsVariationTestField U X}) :
      AEMeasurable (fun x => ENNReal.ofReal (∫ t in U, f x t * divergenceN X.1 t)) ν := by
    have hh := hf.mul ((continuous_divergenceN X.2.1).measurable.comp
      measurable_snd).aestronglyMeasurable
    exact ENNReal.continuous_ofReal.measurable.comp_aemeasurable
      hh.integral_prod_right'.aemeasurable
  have hm : AEMeasurable
      (fun x => ⨆ X ∈ S, ENNReal.ofReal (∫ t in U, f x t * divergenceN X.1 t)) ν :=
    AEMeasurable.biSup S hSc fun X _ => htest X
  apply hm.congr
  filter_upwards [hfi] with x hx
  exact (hS (f x) hx).symm

/-- For locally finite measures, measurability on relatively compact open sets
extends to every Borel set. This version requires local finiteness only almost everywhere. -/
lemma aemeasurable_measure_of_relativelyCompact_open
    {α β : Type*} [MeasurableSpace α] {ν : Measure α}
    [MetricSpace β] [ProperSpace β] [SecondCountableTopology β]
    [MeasurableSpace β] [BorelSpace β] (c : β) {κ : α → Measure β}
    (hfin : ∀ᵐ x ∂ν, IsFiniteMeasureOnCompacts (κ x))
    (hopen : ∀ U : Set β, IsOpen U → IsCompact (closure U) →
      AEMeasurable (fun x => κ x U) ν) :
    ∀ A : Set β, MeasurableSet A → AEMeasurable (fun x => κ x A) ν := by
  have hrestrict (k : ℕ) : ∀ A : Set β, MeasurableSet A →
      AEMeasurable (fun x => (κ x).restrict (ball c k) A) ν := by
    apply MeasurableSet.induction_on_open
    · intro U hU
      simp only [Measure.restrict_apply hU.measurableSet]
      exact hopen _ (hU.inter isOpen_ball)
        (isBounded_ball.subset inter_subset_right).isCompact_closure
    · intro A hA ih
      have hmass : AEMeasurable (fun x => (κ x).restrict (ball c k) univ) ν := by
        simp only [Measure.restrict_apply_univ]
        exact hopen _ isOpen_ball isBounded_ball.isCompact_closure
      apply (hmass.sub ih).congr
      filter_upwards [hfin] with x hx
      let := hx
      have htop : (κ x).restrict (ball c k) A ≠ ∞ := by
        apply ne_top_of_le_ne_top (measure_ball_lt_top (μ := κ x) (x := c) (r := k)).ne
        exact le_trans (measure_mono (subset_univ _)) (by simp)
      exact (measure_compl hA htop).symm
    · intro A hd hA ih
      have hh : AEMeasurable
          (fun x => ∑' j : ℕ, (κ x).restrict (ball c k) (A j)) ν :=
        AEMeasurable.tsum ih
      simpa only [measure_iUnion hd hA] using hh
  intro A hA
  have hm := AEMeasurable.iSup (fun k : ℕ => hrestrict k A hA)
  apply hm.congr
  exact ae_of_all _ fun x => by
    have hmono : Monotone (fun k : ℕ => A ∩ ball c (k : ℝ)) := by
      intro j k hjk
      exact inter_subset_inter_right _ (ball_subset_ball (Nat.cast_le.mpr hjk))
    have he := hmono.measure_iUnion (μ := κ x)
    simpa only [← inter_iUnion, iUnion_ball_nat, inter_univ,
      Measure.restrict_apply hA] using he.symm

/-- Every Borel evaluation of the genuine real slice variation measure is
Lebesgue measurable. No measurability of a chosen family of polar densities is assumed. -/
theorem aemeasurable_realSlicePolar_measure {α : Type*} [MeasurableSpace α]
    {ν : Measure α} [SFinite ν]
    {f : α → EuclideanSpace ℝ (Fin 1) → ℝ}
    {κ : α → Measure ℝ} {σ : α → ℝ → ℝ}
    (hf : AEStronglyMeasurable (Function.uncurry f) (ν.prod volume))
    (hi : ∀ᵐ x ∂ν, LocallyIntegrable (f x) volume)
    (hκ : ∀ᵐ x ∂ν, IsRealBVPolar (f x ∘ euclideanOneReal.symm) (κ x) (σ x)) :
    ∀ A : Set ℝ, MeasurableSet A → AEMeasurable (fun x => κ x A) ν := by
  apply aemeasurable_measure_of_relativelyCompact_open (0 : ℝ)
    (hκ.mono fun _ h => h.finiteOnCompacts)
  intro U hU hUc
  let V : Set (EuclideanSpace ℝ (Fin 1)) := euclideanOneReal ⁻¹' U
  have hVc : IsCompact (closure V) := by
    change IsCompact (closure (euclideanOneReal.toHomeomorph ⁻¹' U))
    rw [← euclideanOneReal.toHomeomorph.preimage_closure]
    exact euclideanOneReal.toHomeomorph.isCompact_preimage.mpr hUc
  have hfV : AEStronglyMeasurable (Function.uncurry f) (ν.prod (volume.restrict V)) := by
    have hh := hf.restrict (s := univ ×ˢ V)
    simpa only [← Measure.prod_restrict, Measure.restrict_univ] using hh
  have hm := aemeasurable_variation_of_prod hVc hfV
    (hi.mono fun _ h => (h.integrableOn_isCompact hVc).mono_set subset_closure)
  apply hm.congr
  filter_upwards [hκ] with x hx
  simpa only [Function.comp_def, euclideanOneReal.symm_apply_apply] using (hx.open_eq U hU).symm

/-- Binary BV slices have actual polar derivative measures whose evaluations on
all Borel sets are Lebesgue measurable in the transverse variable. -/
theorem IsLocallyBVOn.exists_measurable_binary_line_measures {n : ℕ}
    {f : EuclideanSpace ℝ (Fin (n + 1)) → ℝ} (hf : IsLocallyBVOn f univ)
    (hb : ∀ z, f z ∈ ({0, 1} : Set ℝ)) :
    ∃ μ : EuclideanSpace ℝ (Fin n) → Measure ℝ,
    ∃ σ : EuclideanSpace ℝ (Fin n) → ℝ → ℝ,
    ∃ g : EuclideanSpace ℝ (Fin n) → ℝ → ℝ → ℝ → ℝ,
      (∀ᵐ x, IsRealBVPolar (fun t => f (graphAppendN x t)) (μ x) (σ x) ∧
        ∀ a b, IsBinaryBVRepresentativeOn (fun t => f (graphAppendN x t)) (g x a b) a b) ∧
      ∀ A : Set ℝ, MeasurableSet A → AEMeasurable (fun x => μ x A) volume := by
  obtain ⟨μ, σ, g, hg⟩ := hf.exists_binary_line_representatives hb
  refine ⟨μ, σ, g, hg, ?_⟩
  have hp := (lineCoordinateEquiv_measurePreserving n).symm (lineCoordinateEquiv n)
  have hfm := (locallyIntegrableOn_univ.mp hf.1).aestronglyMeasurable
  have hprod := hfm.comp_measurePreserving hp
  apply aemeasurable_realSlicePolar_measure (f := lineSlice f)
  · exact hprod
  · exact hf.ae_lineSlice.mono fun _ h => locallyIntegrableOn_univ.mp h.1
  · filter_upwards [hg] with x hx
    simpa only [Function.comp_def, lineSlice, euclideanOneReal_symm_apply] using hx.1

/-- A family with Lebesgue-measurable evaluations is an actual measure kernel on
the completed transverse measurable space; no modification of its measures is needed. -/
def completedMeasureKernel {α β : Type*} [MeasurableSpace α] [MeasurableSpace β]
    {ν : Measure α} (κ : α → Measure β)
    (hκ : ∀ A : Set β, MeasurableSet A → AEMeasurable (fun x => κ x A) ν) :
    ProbabilityTheory.Kernel (NullMeasurableSpace α ν) β where
  toFun := κ
  measurable' := Measure.measurable_of_measurable_coe _ fun A hA =>
    (hκ A hA).nullMeasurable

@[simp] lemma completedMeasureKernel_apply {α β : Type*}
    [MeasurableSpace α] [MeasurableSpace β] {ν : Measure α}
    (κ : α → Measure β)
    (hκ : ∀ A : Set β, MeasurableSet A → AEMeasurable (fun x => κ x A) ν)
    (x : NullMeasurableSpace α ν) : completedMeasureKernel κ hκ x = κ x := rfl

end LiquidDrop

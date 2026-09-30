module

public import NoCompromise.Regularity.PerimeterConvergenceMeasures

@[expose] public section

/-! # Every positive weak limit dominates the genuine limiting perimeter measure -/

noncomputable section
open MeasureTheory Set Filter Metric
open scoped ENNReal Topology CompactlySupported
namespace LiquidDrop
set_option maxSynthPendingDepth 8

lemma measure_le_ofReal_integral_of_cutoff {X : Type*} [TopologicalSpace X]
    [MeasurableSpace X] [BorelSpace X] (μ : Measure X) [IsFiniteMeasureOnCompacts μ]
    (φ : C_c(X, ℝ)) {K : Set X} (hK : MeasurableSet K)
    (hn : ∀ x, 0 ≤ φ x) (hφ : EqOn φ 1 K) :
    μ K ≤ ENNReal.ofReal (∫ x, φ x ∂μ) := by
  have hi : Integrable (fun x => φ x) μ :=
    φ.continuous.integrable_of_hasCompactSupport φ.hasCompactSupport
  rw [ofReal_integral_eq_lintegral_ofReal hi (Eventually.of_forall hn)]
  calc
    μ K = ∫⁻ x, K.indicator (fun _ => (1 : ℝ≥0∞)) x ∂μ := by
      simp only [lintegral_indicator hK, lintegral_const, Measure.restrict_apply_univ, one_mul]
    _ ≤ _ := lintegral_mono fun x => by
      by_cases hx : x ∈ K
      · rw [indicator_of_mem hx, hφ hx]
        simp
      · rw [indicator_of_notMem hx]
        exact bot_le

lemma ofReal_integral_le_measure_of_cutoff {X : Type*} [TopologicalSpace X]
    [MeasurableSpace X] [BorelSpace X] (μ : Measure X) [IsFiniteMeasureOnCompacts μ]
    (φ : C_c(X, ℝ)) {V : Set X} (hV : MeasurableSet V)
    (hn : ∀ x, 0 ≤ φ x) (hb : ∀ x, φ x ≤ 1) (hs : tsupport φ ⊆ V) :
    ENNReal.ofReal (∫ x, φ x ∂μ) ≤ μ V := by
  have hi : Integrable (fun x => φ x) μ :=
    φ.continuous.integrable_of_hasCompactSupport φ.hasCompactSupport
  rw [ofReal_integral_eq_lintegral_ofReal hi (Eventually.of_forall hn)]
  calc
    _ ≤ ∫⁻ x, V.indicator (fun _ => (1 : ℝ≥0∞)) x ∂μ := lintegral_mono fun x => by
      by_cases hx : x ∈ V
      · rw [indicator_of_mem hx]
        simpa only [ENNReal.ofReal_one] using ENNReal.ofReal_le_ofReal (hb x)
      · rw [indicator_of_notMem hx, image_eq_zero_of_notMem_tsupport (fun h => hx (hs h))]
        simp
    _ = μ V := by
      simp only [lintegral_indicator hV, lintegral_const, Measure.restrict_apply_univ, one_mul]

/-- Local L¹ convergence, together with actual positive weak convergence, forces
the limiting perimeter measure to be no larger than the positive weak limit. -/
theorem localPerimeterMeasure_le_of_weak_limit {n : ℕ}
    {U F : Set (EuclideanSpace ℝ (Fin n))} (hU : IsOpen U)
    {E : ℕ → Set (EuclideanSpace ℝ (Fin n))}
    (hf : ∀ j, IsLocallyBVOn ((E j).indicator (fun _ => (1 : ℝ))) U)
    (hF : IsLocallyBVOn (F.indicator (fun _ => (1 : ℝ))) U)
    (τ : Measure U) [τ.Regular]
    (hweak : ∀ φ : C_c(U, ℝ),
      Tendsto (fun j => ∫ z : U, φ z ∂localPerimeterMeasure hU (hf j))
        atTop (𝓝 (∫ z : U, φ z ∂τ)))
    (hlim : ∀ K : Set (EuclideanSpace ℝ (Fin n)), IsCompact K → K ⊆ U →
      Tendsto (fun j => ∫ z in K,
        |(E j).indicator (fun _ => (1 : ℝ)) z - F.indicator (fun _ => (1 : ℝ)) z|)
        atTop (𝓝 0)) : localPerimeterMeasure hU hF ≤ τ := by
  let : LocallyCompactSpace U := hU.locallyCompactSpace
  let : ∀ j, IsFiniteMeasureOnCompacts (localPerimeterMeasure hU (hf j)) :=
    fun j => (localPerimeterMeasure_data hU (hf j)).2.1
  have hvar (O : Set (EuclideanSpace ℝ (Fin n))) (hO : IsOpen O) (hOU : O ⊆ U) :
      perimeterIn F O ≤ τ (Subtype.val ⁻¹' O) := by
    apply iSup_le
    intro X
    apply iSup_le
    intro hX
    have hsX : tsupport X ⊆ U := hX.2.2.1.trans hOU
    have hXU : IsVariationTestField U X := ⟨hX.1, hX.2.1, hsX, hX.2.2.2⟩
    obtain ⟨φ, hφK, hcφ, hsφ, hbφ⟩ :=
      exists_continuousMap_one_of_isCompact_subset_isOpen hX.2.1 hO hX.2.2.1
    let ψ : C_c(EuclideanSpace ℝ (Fin n), ℝ) := ⟨φ, hcφ⟩
    let Φ : C_c(U, ℝ) := restrictSupportedCC ⟨ψ, hsφ.trans hOU⟩
    have hΦ (z : U) : Φ z = φ z := rfl
    have hK : IsCompact ((Subtype.val : U → EuclideanSpace ℝ (Fin n)) ⁻¹' tsupport X) :=
      Topology.IsInducing.subtypeVal.isCompact_preimage' hX.2.1 (by simpa using hsX)
    have hΦs : tsupport Φ ⊆ (Subtype.val : U → EuclideanSpace ℝ (Fin n)) ⁻¹' O := by
      apply (continuous_subtype_val.closure_preimage_subset (Function.support ψ)).trans
      exact preimage_mono hsφ
    have hsupport (g : EuclideanSpace ℝ (Fin n) → ℝ) :
        (∫ z in U, g z * divergenceN X z) = ∫ z in tsupport X, g z * divergenceN X z := by
      apply setIntegral_eq_of_subset_of_forall_sdiff_eq_zero hU.measurableSet hsX
      intro z hz
      rw [divergenceN_eq_zero_of_notMem_tsupport hz.2, mul_zero]
    have hOeq (g : EuclideanSpace ℝ (Fin n) → ℝ) :
        (∫ z in O, g z * divergenceN X z) = ∫ z in U, g z * divergenceN X z := by
      symm
      apply setIntegral_eq_of_subset_of_forall_sdiff_eq_zero hU.measurableSet hOU
      intro z hz
      rw [divergenceN_eq_zero_of_notMem_tsupport (fun h => hz.2 (hX.2.2.1 h)), mul_zero]
    have ht := tendsto_integral_mul_of_l1_on_compact hX.2.1
      (fun j => (hf j).1.integrableOn_compact_subset hsX hX.2.1)
      (hF.1.integrableOn_compact_subset hsX hX.2.1)
      (continuous_divergenceN hX.1).continuousOn (hlim _ hX.2.1 hsX)
    simp only [← hsupport] at ht
    have hbound (j : ℕ) :
        ENNReal.ofReal (∫ z in U, (E j).indicator (fun _ => (1 : ℝ)) z * divergenceN X z) ≤
          ENNReal.ofReal (∫ z : U, Φ z ∂localPerimeterMeasure hU (hf j)) := by
      apply ((localPerimeterMeasure_data hU (hf j)).2.2.test_integral_le_support_measure
        (hf j).1 hXU).trans
      exact measure_le_ofReal_integral_of_cutoff _ Φ hK.measurableSet
        (fun z => (hbφ z).1) (fun z hz => hφK hz)
    have hle := le_of_tendsto_of_tendsto
      (ENNReal.continuous_ofReal.continuousAt.tendsto.comp ht)
      (ENNReal.continuous_ofReal.continuousAt.tendsto.comp (hweak Φ))
      (Eventually.of_forall hbound)
    rw [hOeq]
    exact hle.trans (ofReal_integral_le_measure_of_cutoff τ Φ
      (hO.measurableSet.preimage measurable_subtype_coe)
      (fun z => (hbφ z).1) (fun z => (hbφ z).2) hΦs)
  have hopen (V : Set U) (hV : IsOpen V) : localPerimeterMeasure hU hF V ≤ τ V := by
    let O := (Subtype.val : U → EuclideanSpace ℝ (Fin n)) '' V
    have hO : IsOpen O := hU.isOpenEmbedding_subtypeVal.isOpenMap _ hV
    have hOU : O ⊆ U := by rintro _ ⟨z, _, rfl⟩; exact z.property
    have hp : (Subtype.val : U → EuclideanSpace ℝ (Fin n)) ⁻¹' O = V :=
      preimage_image_eq _ Subtype.val_injective
    rw [← hp, localPerimeterMeasure_open hU hF hO hOU]
    exact hvar O hO hOU
  apply Measure.le_iff.mpr
  intro S _
  rw [S.measure_eq_iInf_isOpen τ]
  exact le_iInf fun O => le_iInf fun hSO => le_iInf fun hO =>
    (measure_mono hSO).trans (hopen O hO)

end LiquidDrop

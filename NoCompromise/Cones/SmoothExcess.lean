import NoCompromise.Cones.TangentHalfspaceMain
import NoCompromise.Regularity.FixedNormalExcess
import NoCompromise.Regularity.ExcessScaling
import NoCompromise.DeGiorgi.HalfspacePerimeter
import NoCompromise.DeGiorgi.AmbientPolar

/-!
# Vanishing cylindrical excess at nonzero boundary points of minimizing cones

The local perimeter measures in tangent compactness are identified with the
ambient perimeter polar measures before applying fixed-normal convergence.
-/

noncomputable section
open MeasureTheory Set Filter Metric
open scoped Topology ENNReal CompactlySupported
namespace LiquidDrop
set_option maxSynthPendingDepth 8

/-- On the whole space the local perimeter measure is the pullback of any
ambient outward perimeter polar measure. -/
lemma localPerimeterMeasure_univ_eq_of_ambientPolar
    {E : Set AmbientSpace}
    (hf : IsLocallyBVOn (E.indicator (fun _ => (1 : ℝ))) univ)
    {μ : Measure AmbientSpace} {ν : AmbientSpace → AmbientSpace}
    (hp : IsAmbientOutwardPerimeterPolar E μ ν) :
    localPerimeterMeasure isOpen_univ hf =
      Measure.map (Homeomorph.Set.univ AmbientSpace).symm μ := by
  let e := Homeomorph.Set.univ AmbientSpace
  let := hp.regular
  let : (Measure.map e.symm μ).Regular := Measure.Regular.map e.symm
  apply localPerimeterMeasure_unique isOpen_univ hf
  intro O hO _
  rw [Measure.map_apply e.symm.continuous.measurable
    (hO.measurableSet.preimage measurable_subtype_coe)]
  exact hp.open_eq O hO

/-- Weak convergence of the genuine local measures gives weak convergence of
any chosen ambient perimeter polar measures. -/
lemma tendsto_ambientPerimeterMeasure_of_local
    {E : ℕ → Set AmbientSpace} {F : Set AmbientSpace}
    (hf : ∀ j, IsLocallyBVOn ((E j).indicator (fun _ => (1 : ℝ))) univ)
    (hg : IsLocallyBVOn (F.indicator (fun _ => (1 : ℝ))) univ)
    {μs : ℕ → Measure AmbientSpace} {μ : Measure AmbientSpace}
    {νs : ℕ → AmbientSpace → AmbientSpace} {ν : AmbientSpace → AmbientSpace}
    (hps : ∀ j, IsAmbientOutwardPerimeterPolar (E j) (μs j) (νs j))
    (hp : IsAmbientOutwardPerimeterPolar F μ ν)
    (hweak : ∀ φ : C_c((univ : Set AmbientSpace), ℝ),
      Tendsto (fun j => ∫ x, φ x ∂localPerimeterMeasure isOpen_univ (hf j)) atTop
        (𝓝 (∫ x, φ x ∂localPerimeterMeasure isOpen_univ hg)))
    (φ : C_c(AmbientSpace, ℝ)) :
    Tendsto (fun j => ∫ x, φ x ∂μs j) atTop (𝓝 (∫ x, φ x ∂μ)) := by
  let e := Homeomorph.Set.univ AmbientSpace
  let ψ : C_c((univ : Set AmbientSpace), ℝ) :=
    ⟨⟨fun x => φ (e x), φ.continuous.comp e.continuous⟩,
      φ.hasCompactSupport.comp_homeomorph e⟩
  have ht := hweak ψ
  simp_rw [localPerimeterMeasure_univ_eq_of_ambientPolar _ (hps _),
    localPerimeterMeasure_univ_eq_of_ambientPolar _ hp,
    (Homeomorph.Set.univ AmbientSpace).symm.measurableEmbedding.integral_map] at ht
  exact ht

/-- A set equal almost everywhere to a halfspace has its constant outward polar. -/
lemma ambientPolar_of_ae_negativeHalfspace {F : Set AmbientSpace}
    (hmF : NullMeasurableSet F volume) {ν : AmbientSpace} (hν : ‖ν‖ = 1)
    (hF : F =ᵐ[volume] negativeHalfspace ν) :
    IsAmbientOutwardPerimeterPolar F (halfspacePlaneMeasure ν) (fun _ => ν) := by
  let := halfspacePlaneMeasure_regular hν
  exact HasConstantIndicatorPolar.isAmbientOutwardPerimeterPolar
    ((negativeHalfspace_hasConstantIndicatorPolar hν).congr_set_ae hF.symm) hmF hν

/-- Mapping the whole-space pullback back to ambient space recovers the measure. -/
lemma map_univ_map_symm (μ : Measure AmbientSpace) :
    Measure.map (Homeomorph.Set.univ AmbientSpace)
      (Measure.map (Homeomorph.Set.univ AmbientSpace).symm μ) = μ := by
  rw [Measure.map_map (Homeomorph.Set.univ AmbientSpace).continuous.measurable
    (Homeomorph.Set.univ AmbientSpace).symm.continuous.measurable]
  simp only [Function.comp_def, Homeomorph.apply_symm_apply, Measure.map_id']

/-- Strict local perimeter convergence to a halfspace forces normal excess to
vanish on every bounded measurable region. The normal is the outward one. -/
theorem tendsto_normalExcessIntegral_of_local_halfspace
    {E : ℕ → Set AmbientSpace} {F : Set AmbientSpace}
    (hE : ∀ j, HasLocallyFinitePerimeter (E j))
    (hmE : ∀ j, NullMeasurableSet (E j) volume)
    (hg : IsLocallyBVOn (F.indicator (fun _ => (1 : ℝ))) univ)
    (hmF : NullMeasurableSet F volume)
    (hconv : ∀ K : Set AmbientSpace, IsCompact K →
      Tendsto (fun j => ∫ x in K,
        |(E j).indicator (fun _ => (1 : ℝ)) x - F.indicator (fun _ => (1 : ℝ)) x|)
        atTop (𝓝 0))
    (hweak : ∀ φ : C_c((univ : Set AmbientSpace), ℝ),
      Tendsto (fun j => ∫ x, φ x ∂localPerimeterMeasure isOpen_univ
        ((hE j).isLocallyBVOn_indicator (hmE j) univ)) atTop
        (𝓝 (∫ x, φ x ∂localPerimeterMeasure isOpen_univ hg)))
    {ν : AmbientSpace} (hν : ‖ν‖ = 1)
    (hF : F =ᵐ[volume] negativeHalfspace ν)
    {V : Set AmbientSpace} (hbV : Bornology.IsBounded V) (hmV : MeasurableSet V) :
    Tendsto (fun j => normalExcessIntegral (E j) (hE j) (hmE j) V ν) atTop (𝓝 0) := by
  let μs := fun j => (hausdorffMeasure2 3).restrict (reducedBoundary (E j) (hE j) (hmE j))
  let ns := fun j => reducedNormal (E j) (hE j) (hmE j)
  have hps (j) : IsAmbientOutwardPerimeterPolar (E j) (μs j) (ns j) :=
    reducedBoundary_outwardPerimeterPolar (E j) (hE j) (hmE j)
  have hp := ambientPolar_of_ae_negativeHalfspace hmF hν hF
  let e := Homeomorph.Set.univ AmbientSpace
  let ρs := fun j => Measure.map e.symm (μs j)
  let ρ := Measure.map e.symm (halfspacePlaneMeasure ν)
  let : ∀ j, IsFiniteMeasureOnCompacts (μs j) := fun j => (hps j).finiteOnCompacts
  let : IsFiniteMeasureOnCompacts (halfspacePlaneMeasure ν) := hp.finiteOnCompacts
  let : ∀ j, IsFiniteMeasureOnCompacts (ρs j) :=
    fun j => Measure.IsFiniteMeasureOnCompacts.map (μs j) e.symm
  let : IsFiniteMeasureOnCompacts ρ :=
    Measure.IsFiniteMeasureOnCompacts.map (halfspacePlaneMeasure ν) e.symm
  obtain ⟨φ₀, hone, hc, _, hb⟩ := exists_continuousMap_one_of_isCompact_subset_isOpen
    hbV.isCompact_closure isOpen_univ (subset_univ _)
  let φ : C_c(AmbientSpace, ℝ) := ⟨φ₀, hc⟩
  have ht := fixed_normal_excess_convergence isOpen_univ E F ρs ρ
    (fun j x => -ns j x.val) (fun _ => -ν)
    (fun j => univ_indicator_polar_of_coordinate_pairing
      (hps j).measurable (hps j).norm_ae (hps j).coordinate_eq)
    (univ_indicator_polar_of_coordinate_pairing hp.measurable hp.norm_ae hp.coordinate_eq)
    (fun j => ((hE j).isLocallyBVOn_indicator (hmE j) univ).1) hg.1
    (fun K hK _ => hconv K hK) (fun ψ _ => ?_) hν
    (Eventually.of_forall fun _ => neg_neg ν) φ (subset_univ _)
  · have ht' : Tendsto (fun j => ∫ x, φ x * ‖ns j x - ν‖ ^ 2 ∂μs j)
        atTop (𝓝 0) := by
      have hv (x : AmbientSpace) : (e.symm x).val = x := rfl
      simpa only [ρs, e.symm.measurableEmbedding.integral_map, neg_neg, hv] using ht
    apply squeeze_zero (fun j => normalExcessIntegral_nonneg _ _ _ _ _) (fun j => ?_) ht'
    have hi : Integrable (fun x => φ x * ‖ns j x - ν‖ ^ 2) (μs j) := by
      apply integrable_of_finite_support_bound (isClosed_tsupport φ).measurableSet
        φ.hasCompactSupport.measure_lt_top
        (φ.continuous.measurable.mul
          (((hps j).measurable.sub measurable_const).norm.pow_const 2)).aestronglyMeasurable
        (fun x hx => by
          change φ x * ‖ns j x - ν‖ ^ 2 = 0
          rw [image_eq_zero_of_notMem_tsupport hx, zero_mul]) 4
      filter_upwards [ae_restrict_of_ae (hps j).norm_ae] with x hx
      have hn : ‖ns j x - ν‖ ≤ 2 := by
        simpa only [hx, hν, one_add_one_eq_two] using norm_sub_le (ns j x) ν
      have hn0 := norm_nonneg (ns j x - ν)
      have hφ0 : 0 ≤ φ x := (hb x).1
      have hφ1 : φ x ≤ 1 := (hb x).2
      change ‖φ x * ‖ns j x - ν‖ ^ 2‖ ≤ 4
      rw [Real.norm_eq_abs, abs_of_nonneg (mul_nonneg hφ0 (sq_nonneg _))]
      nlinarith [sq_nonneg (‖ns j x - ν‖),
        mul_le_mul_of_nonneg_right hφ1 (sq_nonneg ‖ns j x - ν‖)]
    change (∫ x in V, ‖ns j x - ν‖ ^ 2 ∂μs j) ≤ _
    calc
      _ = ∫ x in V, φ x * ‖ns j x - ν‖ ^ 2 ∂μs j := by
        apply setIntegral_congr_fun hmV
        intro x hx
        dsimp only
        rw [show φ x = 1 from hone (subset_closure hx), one_mul]
      _ ≤ _ := setIntegral_le_integral hi
        (Eventually.of_forall fun x => mul_nonneg (hb x).1 (sq_nonneg _))
  · simp only [ρs, ρ, show (Subtype.val : ↥(univ : Set AmbientSpace) → AmbientSpace) = e from rfl,
      show e = Homeomorph.Set.univ AmbientSpace from rfl, map_univ_map_symm]
    exact tendsto_ambientPerimeterMeasure_of_local
      (fun j => (hE j).isLocallyBVOn_indicator (hmE j) univ) hg hps hp hweak ψ

/-- At every nonzero boundary point of a nontrivial minimizing cone, the
cylindrical excess tends to zero along positive scales, with an axis orthogonal
to the boundary point. -/
theorem cone_tendsto_cylindricalExcess_of_ne_zero {C : Set AmbientSpace}
    (hC : IsNontrivialMinimizingCone C) {p : AmbientSpace}
    (hp : p ∈ frontier (densityOne C)) (hp0 : p ≠ 0) :
    ∃ ν : AmbientSpace, ‖ν‖ = 1 ∧ inner ℝ ν p = 0 ∧
      ∃ r : ℕ → ℝ, (∀ j, 0 < r j) ∧ Tendsto r atTop (𝓝 0) ∧
        Tendsto (fun j => cylindricalExcess C hC.minimizing.isOmegaMinimal.locallyFinite
          hC.minimizing.isOmegaMinimal.nullMeasurable p (r j) ν) atTop (𝓝 0) := by
  obtain ⟨θ, _, _, htangent⟩ := hC.minimizing.isOmegaMinimal.exists_tangent_limit hp
  let r : ℕ → ℝ := fun j => 1 / ((j : ℝ) + 1)
  have hr (j) : 0 < r j := by dsimp [r]; positivity
  have ht : Tendsto r atTop (𝓝 0) := tendsto_one_div_add_atTop_nhds_zero_nat
  obtain ⟨F, hmF, hlocal, hmin, hb, σ, hσ, hl1, hweak, hd, _⟩ := htangent r hr ht
  have he : (0 : AmbientSpace) ∈ essentialBoundary F := by
    rwa [hmin.isOmegaMinimal.frontier_densityOne] at hb
  have hec : (0 : AmbientSpace) ∈ essentialBoundary Fᶜ := by
    rwa [essentialBoundary_compl hmF.nullMeasurableSet]
  have hFpos : 0 < volume F := by
    have hv := radialVolume_pos_at_essentialBoundary he (r := 1) (by norm_num)
    exact ((ENNReal.toReal_pos_iff.mp hv).1).trans_le
      (measure_mono (inter_subset_left : F ∩ ball 0 1 ⊆ F))
  have hFcpos : 0 < volume Fᶜ := by
    have hv := radialVolume_pos_at_essentialBoundary hec (r := 1) (by norm_num)
    exact ((ENNReal.toReal_pos_iff.mp hv).1).trans_le
      (measure_mono (inter_subset_left : Fᶜ ∩ ball 0 1 ⊆ Fᶜ))
  have htan : IsConeTangentLimit C p F :=
    ⟨hmF, hmin, ⟨θ, hd⟩,
      ⟨fun j => r (σ j), fun j => hr (σ j), ht.comp hσ.tendsto_atTop, hl1⟩⟩
  obtain ⟨ν, hν, hνp, hhalf⟩ :=
    cone_tangent_halfspace_of_ne_zero hC hp hp0 htan ⟨hFpos, hFcpos⟩
  have hn : ‖-ν‖ = 1 := by simpa only [norm_neg] using hν
  have hhalf' : F =ᵐ[volume] negativeHalfspace (-ν) := by
    have hae := (densityOne_ae_eq (by norm_num : 0 < 3) hmF.nullMeasurableSet).symm
    rw [hhalf] at hae
    simpa only [negativeHalfspace, inner_neg_left, neg_lt_zero] using hae
  refine ⟨-ν, hn, by simp only [inner_neg_left, hνp, neg_zero],
    fun j => r (σ j), fun j => hr (σ j), ht.comp hσ.tendsto_atTop, ?_⟩
  have hex := tendsto_normalExcessIntegral_of_local_halfspace
    (fun j => (hC.minimizing.isOmegaMinimal.blowupSet p (hr (σ j))).locallyFinite)
    (fun j => (hC.minimizing.isOmegaMinimal.blowupSet p (hr (σ j))).nullMeasurable)
    hlocal.locallyBV hmF.nullMeasurableSet hl1 hweak hn hhalf'
    (isBounded_cylinder 0 1 hn) (isOpen_cylinder 0 1 (-ν)).measurableSet
  have heq (j) : normalExcessIntegral (blowupSet C p (r (σ j)))
      (hC.minimizing.isOmegaMinimal.blowupSet p (hr (σ j))).locallyFinite
      (hC.minimizing.isOmegaMinimal.blowupSet p (hr (σ j))).nullMeasurable
      (cylinder 0 1 (-ν)) (-ν) =
      cylindricalExcess C hC.minimizing.isOmegaMinimal.locallyFinite
        hC.minimizing.isOmegaMinimal.nullMeasurable p (r (σ j)) (-ν) := by
    simpa only [cylindricalExcess, one_pow, div_one] using
      cylindricalExcess_blowupSet_unit C hC.minimizing.isOmegaMinimal.locallyFinite
        hC.minimizing.isOmegaMinimal.nullMeasurable p (hr (σ j)) (-ν)
  simpa only [heq] using hex

end LiquidDrop

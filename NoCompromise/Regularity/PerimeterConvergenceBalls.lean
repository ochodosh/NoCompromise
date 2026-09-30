module

public import NoCompromise.Regularity.PerimeterConvergenceVague
public import NoCompromise.Regularity.PerimeterConvergenceInner
public import NoCompromise.Regularity.PerimeterConvergenceLower

@[expose] public section

/-! # Interior continuity balls and the upper bound for positive perimeter limits -/

noncomputable section
open MeasureTheory Set Filter Metric
open scoped ENNReal Topology CompactlySupported symmDiff
namespace LiquidDrop
set_option maxSynthPendingDepth 8

lemma ae_local_measure_sphere_eq_zero {n : ℕ}
    {U : Set (EuclideanSpace ℝ (Fin n))} (μ : Measure U) [SFinite μ]
    (x : EuclideanSpace ℝ (Fin n)) :
    ∀ᵐ r : ℝ, μ (Subtype.val ⁻¹' sphere x r) = 0 := by
  have hc := Measure.countable_meas_level_set_pos (μ := μ)
    (g := fun z : U => dist (z : EuclideanSpace ℝ (Fin n)) x) (by fun_prop)
  have hn := hc.measure_zero (μ := (volume : Measure ℝ))
  have hae : ∀ᵐ r : ℝ, ¬0 < μ {z : U | dist (z : EuclideanSpace ℝ (Fin n)) x = r} := by
    apply ae_iff.mpr
    simpa only [not_not] using hn
  filter_upwards [hae] with r hr
  exact nonpos_iff_eq_zero.mp (le_of_not_gt hr)

/-- Interior ball masses are continuous in the radius at every null sphere. -/
theorem tendsto_local_ball_of_null_sphere {n : ℕ}
    {U : Set (EuclideanSpace ℝ (Fin n))} (μ : Measure U)
    [IsFiniteMeasureOnCompacts μ] (x : EuclideanSpace ℝ (Fin n)) {r R : ℝ}
    (hrR : r < R) (hRU : closedBall x R ⊆ U)
    (hnull : μ (Subtype.val ⁻¹' sphere x r) = 0) :
    Tendsto (fun b : ℝ => μ (Subtype.val ⁻¹' ball x b)) (𝓝 r)
      (𝓝 (μ (Subtype.val ⁻¹' ball x r))) := by
  let K : Set U := Subtype.val ⁻¹' closedBall x R
  have hK : IsCompact K := Topology.IsInducing.subtypeVal.isCompact_preimage'
    (isCompact_closedBall x R) (by simpa using hRU)
  have hmK : MeasurableSet K := measurableSet_closedBall.preimage measurable_subtype_coe
  have hm (b : ℝ) : MeasurableSet ((Subtype.val : U → EuclideanSpace ℝ (Fin n)) ⁻¹'
      ball x b) := measurableSet_ball.preimage measurable_subtype_coe
  have hfin {b : ℝ} (hb : b ≤ R) : μ (Subtype.val ⁻¹' ball x b) ≠ ∞ :=
    ((measure_mono (preimage_mono ((ball_subset_ball hb).trans ball_subset_closedBall))).trans_lt
      hK.measure_lt_top).ne
  have hi : Integrable (K.indicator (fun _ => (1 : ℝ))) μ :=
    (integrable_indicator_iff hmK).mpr (integrableOn_const hK.measure_lt_top.ne)
  have ht : Tendsto (fun b : ℝ => ∫ z : U,
      (Subtype.val ⁻¹' ball x b).indicator (fun _ => (1 : ℝ)) z ∂μ) (𝓝 r)
      (𝓝 (∫ z : U, (Subtype.val ⁻¹' ball x r).indicator (fun _ => (1 : ℝ)) z ∂μ)) := by
    apply tendsto_integral_filter_of_dominated_convergence (K.indicator (fun _ => (1 : ℝ)))
    · exact Eventually.of_forall fun b =>
        (measurable_const.indicator (hm b)).aestronglyMeasurable
    · filter_upwards [eventually_lt_nhds hrR] with b hb
      apply Eventually.of_forall
      intro z
      by_cases hz : z ∈ (Subtype.val : U → EuclideanSpace ℝ (Fin n)) ⁻¹' ball x b
      · have hzK : z ∈ K := by
          change dist (z : EuclideanSpace ℝ (Fin n)) x ≤ R
          exact le_trans (le_of_lt hz) hb.le
        rw [indicator_of_mem hz, indicator_of_mem hzK]
        norm_num
      · rw [indicator_of_notMem hz, norm_zero]
        exact indicator_nonneg (fun _ _ => zero_le_one) _
    · exact hi
    · filter_upwards [measure_eq_zero_iff_ae_notMem.mp hnull] with z hz
      have hd : dist (z : EuclideanSpace ℝ (Fin n)) x ≠ r := hz
      rcases lt_or_gt_of_ne hd with hlt | hgt
      · have he : ∀ᶠ b : ℝ in 𝓝 r,
            (Subtype.val ⁻¹' ball x b).indicator (fun _ => (1 : ℝ)) z = 1 := by
          filter_upwards [eventually_gt_nhds hlt] with b hb
          exact indicator_of_mem (show z ∈ Subtype.val ⁻¹' ball x b from hb) _
        rw [indicator_of_mem (show z ∈ Subtype.val ⁻¹' ball x r from hlt)]
        exact tendsto_const_nhds.congr' (he.mono fun _ h => h.symm)
      · have he : ∀ᶠ b : ℝ in 𝓝 r,
            (Subtype.val ⁻¹' ball x b).indicator (fun _ => (1 : ℝ)) z = 0 := by
          filter_upwards [eventually_lt_nhds hgt] with b hb
          exact indicator_of_notMem
            (show z ∉ Subtype.val ⁻¹' ball x b from not_lt.mpr hb.le) _
        rw [indicator_of_notMem
          (show z ∉ Subtype.val ⁻¹' ball x r from not_lt.mpr hgt.le)]
        exact tendsto_const_nhds.congr' (he.mono fun _ h => h.symm)
  simp only [integral_indicator_const _ (hm _), smul_eq_mul, mul_one, measureReal_def] at ht
  have ht' := ENNReal.continuous_ofReal.continuousAt.tendsto.comp ht
  rw [ENNReal.ofReal_toReal (hfin hrR.le)] at ht'
  apply ht'.congr'
  filter_upwards [eventually_lt_nhds hrR] with b hb
  exact ENNReal.ofReal_toReal (hfin hb.le)

/-- Genuine gluing gives an upper bound for every interior ball whose sphere
is null for both the positive weak limit and the limiting perimeter measure. -/
theorem weak_limit_local_ball_le_perimeter
    {U F : Set AmbientSpace} (hU : IsOpen U)
    {E : ℕ → Set AmbientSpace} {ω : ℕ → ℝ} {s : ℕ → ℝ≥0∞}
    (hE : ∀ j, IsOmegaMinimalAtScales (E j) (ω j) (s j))
    (hf : ∀ j, IsLocallyBVOn ((E j).indicator (fun _ => (1 : ℝ))) U)
    (hmF : NullMeasurableSet F volume)
    (hF : IsLocallyBVOn (F.indicator (fun _ => (1 : ℝ))) U)
    {ω₀ : ℝ} (hω : Tendsto ω atTop (𝓝 ω₀))
    (hlim : ∀ K : Set AmbientSpace, IsCompact K → K ⊆ U →
      Tendsto (fun j => ∫ z in K,
        |(E j).indicator (fun _ => (1 : ℝ)) z - F.indicator (fun _ => (1 : ℝ)) z|)
        atTop (𝓝 0))
    (τ : Measure U) [τ.Regular]
    (hweak : ∀ φ : C_c(U, ℝ),
      Tendsto (fun j => ∫ z : U, φ z ∂localPerimeterMeasure hU (hf j))
        atTop (𝓝 (∫ z : U, φ z ∂τ)))
    (x : AmbientSpace) {a R : ℝ} (ha : 0 < a) (haR : a < R)
    (hRU : closedBall x R ⊆ U)
    (hscale : ∀ᶠ j in atTop, ENNReal.ofReal R ≤ s j)
    (hτ : τ (Subtype.val ⁻¹' sphere x a) = 0)
    (hρ : localPerimeterMeasure hU hF (Subtype.val ⁻¹' sphere x a) = 0) :
    τ (Subtype.val ⁻¹' ball x a) ≤ localPerimeterMeasure hU hF (Subtype.val ⁻¹' ball x a) := by
  let : ∀ j, IsFiniteMeasureOnCompacts (localPerimeterMeasure hU (hf j)) :=
    fun j => (localPerimeterMeasure_data hU (hf j)).2.1
  let : IsFiniteMeasureOnCompacts (localPerimeterMeasure hU hF) :=
    (localPerimeterMeasure_data hU hF).2.1
  have haU : closedBall x a ⊆ U := (closedBall_subset_closedBall haR.le).trans hRU
  have hconv := tendsto_local_ball_of_compact_test_convergence hU
    (fun j => localPerimeterMeasure hU (hf j)) τ hweak x ha haU hτ
  simp only [localPerimeterMeasure_open hU _ isOpen_ball
    (ball_subset_closedBall.trans haU)] at hconv
  obtain ⟨G, hmG, _, hpG, heG⟩ :=
    hF.exists_finitePerimeter_eq_near_compact hU (isCompact_closedBall x R) hRU
  have heq := heG.self_of_nhdsSet
  have hb (b : ℝ) (hab : a < b) (hbR : b < R) :
      τ (Subtype.val ⁻¹' ball x a) ≤ localPerimeterMeasure hU hF (Subtype.val ⁻¹' ball x b) := by
    have hbb : ball x b ⊆ closedBall x R :=
      (ball_subset_ball hbR.le).trans ball_subset_closedBall
    have hGF : G =ᵐ[volume.restrict (ball x b)] F := by
      filter_upwards [ae_restrict_mem measurableSet_ball] with z hz
      exact (heq (hbb hz)).symm
    have hGF' : G =ᵐ[volume.restrict (ball x b \ closedBall x a)] F :=
      ae_mono (Measure.restrict_mono_set _ sdiff_subset) hGF
    have hvol : (F ∆ G) ∩ ball x b = ∅ := by
      ext z
      have hz : z ∈ ball x b → (z ∈ F) = (z ∈ G) := fun hz => heq (hbb hz)
      simp only [mem_inter_iff, mem_symmDiff, mem_empty_iff_false]
      tauto
    have h := limsup_perimeter_inner_ball_le hE hmF hmG hpG hω x ha.le hab hbR
      hscale hGF' (hlim _ (isCompact_closedBall x b)
        ((closedBall_subset_closedBall hbR.le).trans hRU))
    rw [hconv.limsup_eq, perimeterIn_congr_ae (ball x b) hGF, hvol, measure_empty, mul_zero,
      add_zero] at h
    rw [localPerimeterMeasure_open hU hF isOpen_ball (hbb.trans hRU)]
    exact h
  have ht := (tendsto_local_ball_of_null_sphere (localPerimeterMeasure hU hF)
    x haR hRU hρ).mono_left (nhdsWithin_le_nhds (s := Ioi a))
  apply ge_of_tendsto ht
  filter_upwards [self_mem_nhdsWithin,
    (eventually_lt_nhds haR).filter_mono nhdsWithin_le_nhds] with b hab hbR
  exact hb b hab hbR

end LiquidDrop

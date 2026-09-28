import NoCompromise.Regularity.DensityAhlfors
import NoCompromise.DeGiorgi.BlowupCompactness

/-!
# Compactness of quasiminimal blow-ups at arbitrary centers

The quasiminimal upper perimeter estimate applies at every center. Thus the
compactness conclusion does not require a reduced-boundary hypothesis. The
limiting set below is obtained from actual BV compactness of the indicators.
-/

noncomputable section
open MeasureTheory Set Filter Metric
open scoped Topology ENNReal
namespace LiquidDrop
set_option maxSynthPendingDepth 8

lemma IsOmegaMinimal.eventually_perimeterIn_blowupSet_ball_le
    {E : Set AmbientSpace} {ω : ℝ} (hE : IsOmegaMinimal E ω) (x : AmbientSpace)
    {r : ℕ → ℝ} (hr : ∀ j, 0 < r j) (ht : Tendsto r atTop (𝓝 0))
    {R : ℝ} (hR : 0 < R) :
    ∀ᶠ j in atTop, (perimeterIn (blowupSet E x (r j)) (ball 0 R)).toReal ≤
      (4 * (4 * Real.pi + ω * (4 * Real.pi / 3))) * R ^ 2 := by
  have hs : ∀ᶠ j in atTop, r j * R < 1 / 2 := by
    simpa only [zero_mul] using
      (ht.mul_const R).eventually (Iio_mem_nhds (by norm_num : (0 : ℝ) * R < 1 / 2))
  filter_upwards [hs] with j hj
  rw [perimeterIn_blowupSet_ball_real E hE.locallyFinite hE.nullMeasurable x (hr j)]
  rw [measureReal_def,
    canonicalPerimeterMeasure_open E hE.locallyFinite hE.nullMeasurable isOpen_ball]
  calc
    _ ≤ (r j)⁻¹ ^ 2 *
        ((4 * (4 * Real.pi + ω * (4 * Real.pi / 3))) * (r j * R) ^ 2) :=
      mul_le_mul_of_nonneg_left
        (hE.perimeterIn_ball_upper x (mul_pos (hr j) hR) hj.le) (sq_nonneg _)
    _ = _ := by field_simp [(hr j).ne']

/-- Uniform actual perimeter bounds on every precompact region, including the
finitely many initial scales before the asymptotic upper bound applies. -/
theorem IsOmegaMinimal.bounded_perimeterIn_blowupSet
    {E : Set AmbientSpace} {ω : ℝ} (hE : IsOmegaMinimal E ω) (x : AmbientSpace)
    {r : ℕ → ℝ} (hr : ∀ j, 0 < r j) (ht : Tendsto r atTop (𝓝 0))
    {A : Set AmbientSpace} (hcA : IsCompact (closure A)) :
    ∃ C : ℝ, ∀ j, (perimeterIn (blowupSet E x (r j)) A).toReal ≤ C := by
  obtain ⟨R, hR, hAR⟩ := hcA.isBounded.subset_ball_lt 0 (0 : AmbientSpace)
  have hAB : A ⊆ ball (0 : AmbientSpace) R := subset_closure.trans hAR
  have hle (j) : (perimeterIn (blowupSet E x (r j)) A).toReal ≤
      (perimeterIn (blowupSet E x (r j)) (ball 0 R)).toReal := by
    apply ENNReal.toReal_mono
      ((hE.locallyFinite.blowupSet (by norm_num) x (hr j)) _ isOpen_ball
        isBounded_ball.isCompact_closure).ne
    exact variation_mono isOpen_ball.measurableSet hAB
  have hb : atTop.IsBoundedUnder (· ≤ ·)
      (fun j => (perimeterIn (blowupSet E x (r j)) A).toReal) := by
    refine ⟨(4 * (4 * Real.pi + ω * (4 * Real.pi / 3))) * R ^ 2, ?_⟩
    change ∀ᶠ j in atTop, (perimeterIn (blowupSet E x (r j)) A).toReal ≤ _
    filter_upwards [hE.eventually_perimeterIn_blowupSet_ball_le x hr ht hR] with j hj
    exact (hle j).trans hj
  obtain ⟨C, hC⟩ := hb.bddAbove_range
  exact ⟨C, fun j => hC (mem_range_self j)⟩

lemma IsOmegaMinimal.bounded_perimeterIn_blowupSet_ennreal
    {E : Set AmbientSpace} {ω : ℝ} (hE : IsOmegaMinimal E ω) (x : AmbientSpace)
    {r : ℕ → ℝ} (hr : ∀ j, 0 < r j) (ht : Tendsto r atTop (𝓝 0))
    {A : Set AmbientSpace} (hA : IsOpen A) (hcA : IsCompact (closure A)) :
    ∃ C : ℝ≥0∞, C < ∞ ∧ ∀ j, perimeterIn (blowupSet E x (r j)) A ≤ C := by
  obtain ⟨C, hC⟩ := hE.bounded_perimeterIn_blowupSet x hr ht hcA
  refine ⟨ENNReal.ofReal C, ENNReal.ofReal_lt_top, ?_⟩
  intro j
  have hp := hE.locallyFinite.blowupSet (by norm_num) x (hr j) A hA hcA
  rw [← ENNReal.ofReal_toReal hp.ne]
  exact ENNReal.ofReal_le_ofReal (hC j)

/-- Every vanishing sequence of positive scales at a quasiminimal set has an
actual locally L¹-convergent subsequence with a measurable locally BV limit. -/
theorem IsOmegaMinimal.exists_blowup_subsequence
    {E : Set AmbientSpace} {ω : ℝ} (hE : IsOmegaMinimal E ω) (x : AmbientSpace)
    {r : ℕ → ℝ} (hr : ∀ j, 0 < r j) (ht : Tendsto r atTop (𝓝 0)) :
    ∃ F : Set AmbientSpace, MeasurableSet F ∧ HasLocallyFinitePerimeter F ∧
      ∃ σ : ℕ → ℕ, StrictMono σ ∧ ∀ K : Set AmbientSpace, IsCompact K →
        Tendsto (fun j => ∫ y in K,
          |(blowupSet E x (r (σ j))).indicator (fun _ => (1 : ℝ)) y -
            F.indicator (fun _ => (1 : ℝ)) y|) atTop (𝓝 0) := by
  apply bv_compactness_indicators_univ (fun j => blowupSet E x (r j))
    (fun j => hE.locallyFinite.blowupSet (by norm_num) x (hr j))
    (fun j => nullMeasurableSet_blowupSet hE.nullMeasurable x (hr j))
  intro A _ hcA
  obtain ⟨C, hC⟩ := hE.bounded_perimeterIn_blowupSet x hr ht hcA
  refine ⟨volume.real A + C, fun j => ?_⟩
  exact add_le_add (integral_abs_indicator_one_le_volume
    (nullMeasurableSet_blowupSet hE.nullMeasurable x (hr j)) hcA) (hC j)

end LiquidDrop

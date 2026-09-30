module

public import NoCompromise.Regularity.PerimeterConvergenceL1
public import NoCompromise.Regularity.RepresentativeBoundary

@[expose] public section

/-! # Uniform phase density and local L1 limits

The error parameter can be enlarged to obtain one density constant for an
entire compactness sequence. Local indicator convergence then excludes moving
boundary points from any region occupied by a single limiting phase.
-/

noncomputable section
open Set MeasureTheory Filter Metric
open scoped ENNReal Topology symmDiff
namespace LiquidDrop

lemma IsOmegaMinimalAtScales.mono_error {n : ℕ}
    {E : Set (EuclideanSpace ℝ (Fin n))} {ω ω' : ℝ} {r₀ : ℝ≥0∞}
    (hE : IsOmegaMinimalAtScales E ω r₀) (hω : ω ≤ ω') :
    IsOmegaMinimalAtScales E ω' r₀ := by
  refine ⟨hE.nonneg.trans hω, hE.scale_pos, hE.nullMeasurable, hE.locallyFinite, ?_⟩
  intro x r hr hrr F hmF hF hc hs
  exact (hE.comparison x r hr hrr F hmF hF hc hs).trans
    (add_le_add le_rfl (mul_le_mul' (ENNReal.ofReal_le_ofReal hω) le_rfl))

lemma IsOmegaMinimal.uniform_radialVolume_lower_bound
    {E : Set AmbientSpace} {ω : ℝ} (hE : IsOmegaMinimal E ω) (hω : ω ≤ 1)
    {x : AmbientSpace} (hx : x ∈ frontier (densityOne E))
    {r : ℝ} (hr : 0 ≤ r) (hr1 : r ≤ 1) :
    quasiminimalDensityConstant 1 * r ^ 3 ≤ radialVolume E x r ∧
      quasiminimalDensityConstant 1 * r ^ 3 ≤ radialVolume Eᶜ x r := by
  have hE1 : IsOmegaMinimal E 1 := hE.mono_error hω
  have hx' : x ∈ essentialBoundary E := by rwa [hE.frontier_densityOne] at hx
  refine ⟨hE1.radialVolume_lower_bound hx' hr hr1, ?_⟩
  apply hE1.compl.radialVolume_lower_bound _ hr hr1
  rwa [essentialBoundary_compl hE.nullMeasurable]

lemma volume_inter_le_symmDiff_inter_add {E F A : Set AmbientSpace} :
    volume (E ∩ A) ≤ volume ((E ∆ F) ∩ A) + volume (F ∩ A) := by
  apply (measure_mono (show E ∩ A ⊆ ((E ∆ F) ∩ A) ∪ (F ∩ A) from ?_)).trans
    (measure_union_le _ _)
  intro x hx
  by_cases hF : x ∈ F
  · exact Or.inr ⟨hF, hx.2⟩
  · exact Or.inl ⟨Or.inl ⟨hx.1, hF⟩, hx.2⟩

lemma tendsto_volume_inter_of_l1_zero_phase
    {E : ℕ → Set AmbientSpace} {F K : Set AmbientSpace}
    (hmE : ∀ j, NullMeasurableSet (E j) volume) (hmF : NullMeasurableSet F volume)
    (hK : IsCompact K)
    (hl1 : Tendsto (fun j => ∫ x in K,
      |(E j).indicator (fun _ => (1 : ℝ)) x - F.indicator (fun _ => (1 : ℝ)) x|)
      atTop (𝓝 0)) (hF : volume (F ∩ K) = 0) :
    Tendsto (fun j => volume (E j ∩ K)) atTop (𝓝 0) := by
  have ht := tendsto_volume_symmDiff_inter_of_l1 hmE hmF
    (fun j => (locallyIntegrable_indicator_one (hmE j)).integrableOn_isCompact hK)
    ((locallyIntegrable_indicator_one hmF).integrableOn_isCompact hK) hl1
  apply tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds ht
    (fun _ => zero_le) _
  intro j
  simpa only [hF, add_zero] using
    (volume_inter_le_symmDiff_inter_add (E := E j) (F := F) (A := K))

/-- Positive phase density prevents a moving sequence of boundary points from
entering a region in which the local L1 limit has zero volume. -/
lemma IsOmegaMinimal.limit_phase_volume_pos
    {E : ℕ → Set AmbientSpace} {ω : ℕ → ℝ}
    (hE : ∀ j, IsOmegaMinimal (E j) (ω j)) (hω : ∀ j, ω j ≤ 1)
    {x : ℕ → AmbientSpace} {a : AmbientSpace}
    (hx : ∀ j, x j ∈ frontier (densityOne (E j))) (ht : Tendsto x atTop (𝓝 a))
    {F : Set AmbientSpace} (hmF : NullMeasurableSet F volume)
    {ρ : ℝ} (hρ : 0 < ρ) (hρ1 : ρ ≤ 1)
    (hl1 : Tendsto (fun j => ∫ y in closedBall a (2 * ρ),
      |(E j).indicator (fun _ => (1 : ℝ)) y - F.indicator (fun _ => (1 : ℝ)) y|)
      atTop (𝓝 0)) :
    0 < volume (F ∩ closedBall a (2 * ρ)) := by
  by_contra hp
  have hz : volume (F ∩ closedBall a (2 * ρ)) = 0 := le_antisymm (not_lt.mp hp) zero_le
  have hv := tendsto_volume_inter_of_l1_zero_phase (fun j => (hE j).nullMeasurable)
    hmF (isCompact_closedBall a (2 * ρ)) hl1 hz
  have he : ∀ᶠ j in atTop,
      ENNReal.ofReal (quasiminimalDensityConstant 1 * ρ ^ 3) ≤
        volume (E j ∩ closedBall a (2 * ρ)) := by
    filter_upwards [ht.eventually (ball_mem_nhds a hρ)] with j hj
    have hsub : ball (x j) ρ ⊆ closedBall a (2 * ρ) := by
      intro y hy
      rw [mem_closedBall]
      calc
        dist y a ≤ dist y (x j) + dist (x j) a := dist_triangle _ _ _
        _ ≤ 2 * ρ := by have := mem_ball.mp hy; have := mem_ball.mp hj; linarith
    have hd := ((hE j).uniform_radialVolume_lower_bound (hω j) (hx j) hρ.le hρ1).1
    calc
      ENNReal.ofReal (quasiminimalDensityConstant 1 * ρ ^ 3) ≤
          ENNReal.ofReal (radialVolume (E j) (x j) ρ) := ENNReal.ofReal_le_ofReal hd
      _ = volume (E j ∩ ball (x j) ρ) := by
        unfold radialVolume
        exact ENNReal.ofReal_toReal
          ((measure_mono inter_subset_right).trans_lt (measure_ball_lt_top)).ne
      _ ≤ _ := measure_mono (inter_subset_inter_right _ hsub)
  have hz' : ENNReal.ofReal (quasiminimalDensityConstant 1 * ρ ^ 3) ≤ 0 :=
    le_of_tendsto_of_tendsto tendsto_const_nhds hv he
  exact (not_le_of_gt (ENNReal.ofReal_pos.mpr
    (mul_pos (quasiminimalDensityConstant_pos (by norm_num)) (pow_pos hρ 3)))) hz'

end LiquidDrop

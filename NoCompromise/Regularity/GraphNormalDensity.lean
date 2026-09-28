import NoCompromise.Area.GraphDensity
import NoCompromise.Regularity.DensitySimilarity
import NoCompromise.DeGiorgi.Structure

/-!
# Positive base mass near a graph density point

At a density-one point, every translated ball at a fixed relative scale retains
at least half its area in the base set at sufficiently small radii. Graph area
then bounds this base area from below, and reduced-boundary graph pieces are
measured by the actual canonical perimeter.
-/

noncomputable section
open MeasureTheory Set Filter Metric
open scoped Topology ENNReal NNReal Gradient
namespace LiquidDrop

/-- Density one controls off-center balls whose displacement is proportional
to their radius. No graph or perimeter premise is involved. -/
lemma graphNormal_eventually_base_mass_lower
    {G : Set (EuclideanSpace ℝ (Fin 2))} (hG : MeasurableSet G)
    {x : EuclideanSpace ℝ (Fin 2)} (hx : x ∈ densityOne G)
    (v : EuclideanSpace ℝ (Fin 2)) {δ : ℝ} (hδ : 0 < δ) :
    ∀ᶠ r in 𝓝[>] (0 : ℝ),
      Real.pi * δ ^ 2 / 2 * r ^ 2 ≤
        volume.real (G ∩ ball (x + r • v) (r * δ)) := by
  let M := ‖v‖ + δ
  have hM : 0 < M := by dsimp [M]; positivity
  have hxc : x ∈ densityZero Gᶜ := by
    rw [← densityOne_compl hG.compl.nullMeasurableSet, compl_compl]
    exact hx
  have ht : Tendsto (fun r : ℝ => densityRatio Gᶜ x (r * M)) (𝓝[>] 0) (𝓝 0) := by
    simpa only [Function.comp_def, mul_comm M] using
      hxc.comp (tangent_pos_mul_tendsto_zero hM)
  have he := ht.eventually (Iio_mem_nhds (show 0 < δ ^ 2 / (2 * M ^ 2) by positivity))
  filter_upwards [self_mem_nhdsWithin, he] with r hr hb
  change 0 < r at hr
  let B := ball (x + r • v) (r * δ)
  have hsub : B ⊆ ball x (r * M) := by
    intro y hy
    have htri := dist_triangle y (x + r • v) x
    have heq : dist (x + r • v) x = r * ‖v‖ := by
      simp [dist_eq_norm, norm_smul, Real.norm_of_nonneg hr.le]
    rw [heq] at htri
    change dist y (x + r • v) < r * δ at hy
    change dist y x < r * M
    dsimp [M]
    nlinarith
  have hbad : volume.real (Gᶜ ∩ ball x (r * M)) <
      Real.pi * δ ^ 2 / 2 * r ^ 2 := by
    change volume.real (Gᶜ ∩ ball x (r * M)) /
      volume.real (ball x (r * M)) < δ ^ 2 / (2 * M ^ 2) at hb
    rw [volume_real_ball_plane x (by positivity)] at hb
    have hh := (div_lt_iff₀ (by positivity : 0 < Real.pi * (r * M) ^ 2)).mp hb
    convert hh using 1 <;> first | rfl | (field_simp [hM.ne'])
  have hbad' : volume.real (B \ G) ≤ volume.real (Gᶜ ∩ ball x (r * M)) := by
    apply measureReal_mono _ (measure_ne_top_of_subset inter_subset_right measure_ball_lt_top.ne)
    intro y hy
    exact ⟨hy.2, hsub hy.1⟩
  have hsum := measureReal_inter_add_sdiff (μ := volume) (s := B) hG
    (show volume B ≠ ∞ from measure_ball_lt_top.ne)
  have hball : volume.real B = Real.pi * (r * δ) ^ 2 :=
    volume_real_ball_plane _ (by positivity)
  rw [inter_comm B G, hball] at hsum
  change Real.pi * δ ^ 2 / 2 * r ^ 2 ≤ volume.real (G ∩ B)
  nlinarith

/-- Graph area dominates base area, including extended values. -/
lemma volume_le_hausdorffMeasure2_graphMap_image
    {f : EuclideanSpace ℝ (Fin 2) → ℝ} {K : ℝ≥0} (hf : LipschitzWith K f)
    {G : Set (EuclideanSpace ℝ (Fin 2))} (hG : MeasurableSet G) :
    volume G ≤ hausdorffMeasure2 3 (graphMap f '' G) := by
  rw [hausdorffMeasure2_graphMap_image hf hG]
  calc
    volume G = ∫⁻ _ in G, (1 : ℝ≥0∞) := by simp
    _ ≤ _ := lintegral_mono fun x => by
      rw [← ENNReal.ofReal_one]
      apply ENNReal.ofReal_le_ofReal
      exact (Real.le_sqrt (by norm_num) (by positivity)).mpr
        (by nlinarith [sq_nonneg ‖gradient f x‖])

/-- A Borel graph piece in the reduced boundary has its actual area bounded by
canonical perimeter on every ambient Borel set containing it. -/
lemma graphNormal_base_area_le_perimeter (E : Set AmbientSpace)
    (hE : HasLocallyFinitePerimeter E) (hmE : NullMeasurableSet E volume)
    {f : EuclideanSpace ℝ (Fin 2) → ℝ} {K : ℝ≥0} (hf : LipschitzWith K f)
    {G : Set (EuclideanSpace ℝ (Fin 2))} (hG : MeasurableSet G)
    (hred : graphMap f '' G ⊆ reducedBoundary E hE hmE)
    {A : Set AmbientSpace} (hA : MeasurableSet A) (hGA : graphMap f '' G ⊆ A) :
    volume G ≤ canonicalPerimeterMeasure E hE hmE A := by
  rw [canonicalPerimeterMeasure_eq_reducedBoundary_area, Measure.restrict_apply hA]
  exact (volume_le_hausdorffMeasure2_graphMap_image hf hG).trans
    (measure_mono fun y hy => ⟨hGA hy, hred hy⟩)

end LiquidDrop

import NoCompromise.Area.GraphDensityGeometry
import NoCompromise.Measure.BallDifferentiation

/-!
# Density one on Borel pieces of Lipschitz graphs

The graph-area weight has Lebesgue points almost everywhere. Tangent ellipses
and differentiability squeeze the area of a graph piece in shrinking balls,
with the exact linear Jacobian canceling the ellipse-area denominator.
-/

noncomputable section
open MeasureTheory Set Filter Metric Function InnerProductSpace
open scoped Topology ENNReal NNReal Gradient
namespace LiquidDrop

/-- The area weight of a Borel graph piece, extended by zero off its base. -/
def graphPieceWeight (f : EuclideanSpace ℝ (Fin 2) → ℝ)
    (G : Set (EuclideanSpace ℝ (Fin 2))) : EuclideanSpace ℝ (Fin 2) → ℝ :=
  G.indicator (fun x => Real.sqrt (1 + ‖gradient f x‖ ^ 2))

lemma graphPieceWeight_nonneg (f : EuclideanSpace ℝ (Fin 2) → ℝ)
    (G : Set (EuclideanSpace ℝ (Fin 2))) (x) : 0 ≤ graphPieceWeight f G x := by
  by_cases hx : x ∈ G
  · simp only [graphPieceWeight, indicator_of_mem hx]; positivity
  · simp only [graphPieceWeight, indicator_of_notMem hx, le_refl]

lemma measurable_graphPieceWeight (f : EuclideanSpace ℝ (Fin 2) → ℝ)
    {G : Set (EuclideanSpace ℝ (Fin 2))} (hG : MeasurableSet G) :
    Measurable (graphPieceWeight f G) := by
  have hw : Measurable (fun x => Real.sqrt (1 + ‖gradient f x‖ ^ 2)) := by
    simpa only [ENNReal.toReal_ofReal (Real.sqrt_nonneg _)] using
      (measurable_graphAreaDensity f).ennreal_toReal
  exact hw.indicator hG

lemma norm_graphPieceWeight_le {f : EuclideanSpace ℝ (Fin 2) → ℝ} {K : ℝ≥0}
    (hf : LipschitzWith K f) (G : Set (EuclideanSpace ℝ (Fin 2))) (x) :
    ‖graphPieceWeight f G x‖ ≤ 1 + (K : ℝ) := by
  by_cases hx : x ∈ G
  · rw [graphPieceWeight, indicator_of_mem hx, Real.norm_of_nonneg (Real.sqrt_nonneg _)]
    have hh := ENNReal.toReal_mono (ENNReal.ofReal_ne_top)
      (graphAreaDensity_le_of_lipschitz hf x)
    simpa only [ENNReal.toReal_ofReal (Real.sqrt_nonneg _),
      ENNReal.toReal_ofReal (show 0 ≤ 1 + (K : ℝ) by positivity)] using hh
  · simp only [graphPieceWeight, indicator_of_notMem hx, norm_zero]
    positivity

lemma locallyIntegrable_graphPieceWeight {f : EuclideanSpace ℝ (Fin 2) → ℝ} {K : ℝ≥0}
    (hf : LipschitzWith K f) {G : Set (EuclideanSpace ℝ (Fin 2))} (hG : MeasurableSet G) :
    LocallyIntegrable (graphPieceWeight f G) volume :=
  locallyIntegrable_of_ae_norm_le volume (measurable_graphPieceWeight f hG).aestronglyMeasurable
    (Eventually.of_forall (norm_graphPieceWeight_le hf G))

lemma graph_ball_preimage_subset_ball (f : EuclideanSpace ℝ (Fin 2) → ℝ)
    (x : EuclideanSpace ℝ (Fin 2)) (r : ℝ) :
    graphMap f ⁻¹' ball (graphMap f x) r ⊆ ball x r := by
  intro y hy
  have hh := (antilipschitzWith_graphMap f).le_mul_dist y x
  simp only [NNReal.coe_one, one_mul] at hh
  exact hh.trans_lt hy

/-- Graph area in a ball is exactly the integral of the zero-extended base weight
on that ball's graph preimage. -/
lemma real_graph_piece_ball_eq_integral {f : EuclideanSpace ℝ (Fin 2) → ℝ} {K : ℝ≥0}
    (hf : LipschitzWith K f) {G : Set (EuclideanSpace ℝ (Fin 2))} (hG : MeasurableSet G)
    (x : EuclideanSpace ℝ (Fin 2)) (r : ℝ) :
    (hausdorffMeasure2 3).real (ball (graphMap f x) r ∩ graphMap f '' G) =
      ∫ y in graphMap f ⁻¹' ball (graphMap f x) r, graphPieceWeight f G y := by
  let A := graphMap f ⁻¹' ball (graphMap f x) r
  have hA : MeasurableSet A := (lipschitzWith_graphMap hf).continuous.measurable measurableSet_ball
  have harea := hausdorffMeasure2_graphMap_image hf (hA.inter hG)
  rw [Set.image_preimage_inter] at harea
  rw [Measure.real, harea]
  rw [graphPieceWeight, setIntegral_indicator hG]
  have hw : Measurable (fun y => Real.sqrt (1 + ‖gradient f y‖ ^ 2)) := by
    simpa only [ENNReal.toReal_ofReal (Real.sqrt_nonneg _)] using
      (measurable_graphAreaDensity f).ennreal_toReal
  exact (integral_eq_lintegral_of_nonneg_ae
    (Eventually.of_forall fun y => Real.sqrt_nonneg _) hw.aestronglyMeasurable.restrict).symm

lemma volume_real_ball_plane (x : EuclideanSpace ℝ (Fin 2)) {r : ℝ} (hr : 0 ≤ r) :
    volume.real (ball x r) = Real.pi * r ^ 2 := by
  simp only [Measure.real, EuclideanSpace.volume_ball_fin_two, ENNReal.toReal_mul,
    ENNReal.toReal_pow, ENNReal.toReal_ofReal hr, ENNReal.toReal_ofReal Real.pi_pos.le]
  ring

/-- A norm Lebesgue point has the expected weighted mass on every family of
homothetically shrinking tangent ellipses. -/
lemma tendsto_integral_graphTangentEllipse_div_sq
    {w : EuclideanSpace ℝ (Fin 2) → ℝ} (hw : LocallyIntegrable w volume)
    (p x : EuclideanSpace ℝ (Fin 2))
    (hx : Tendsto (fun r => ⨍ y in ball x r, ‖w y - w x‖) (𝓝[>] 0) (𝓝 0))
    {a : ℝ} (ha : 0 < a) :
    Tendsto (fun r : ℝ => (∫ y in graphTangentEllipse p x (a * r), w y) /
      (Real.pi * r ^ 2)) (𝓝[>] 0) (𝓝 (w x * a ^ 2 / Real.sqrt (1 + ‖p‖ ^ 2))) := by
  have hscale : Tendsto (fun r : ℝ => a * r) (𝓝[>] 0) (𝓝[>] 0) := by
    apply tendsto_nhdsWithin_iff.mpr
    constructor
    · have ht : Tendsto (fun r : ℝ => a * r) (𝓝 0) (𝓝 0) := by
        simpa only [id_eq, mul_zero] using
          (tendsto_id : Tendsto (fun r : ℝ => r) (𝓝 0) (𝓝 0)).const_mul a
      exact ht.mono_left nhdsWithin_le_nhds
    · filter_upwards [self_mem_nhdsWithin] with r hr
      exact mul_pos ha hr
  have hlim := (hx.comp hscale).const_mul (a ^ 2)
  simp only [mul_zero] at hlim
  rw [tendsto_iff_norm_sub_tendsto_zero]
  apply squeeze_zero' (Eventually.of_forall fun _ => norm_nonneg _) ?_ hlim
  filter_upwards [self_mem_nhdsWithin] with r hr
  have hr0 : 0 < r := hr
  have har : 0 < a * r := mul_pos ha hr0
  have hBfin : volume (ball x (a * r)) ≠ ∞ :=
    ne_top_of_le_ne_top (isCompact_closedBall x (a * r)).measure_lt_top.ne
      (measure_mono ball_subset_closedBall)
  have hiB := (hw.integrableOn_isCompact (isCompact_closedBall x (a * r))).mono_set
    ball_subset_closedBall
  have hiE := hiB.mono_set (graphTangentEllipse_subset_ball p x (a * r))
  have hcB : IntegrableOn (fun _ => w x) (ball x (a * r)) volume := integrableOn_const hBfin
  have hcE := hcB.mono_set (graphTangentEllipse_subset_ball p x (a * r))
  have hJ : Real.sqrt (1 + ‖p‖ ^ 2) ≠ 0 := (Real.sqrt_pos.mpr (by positivity)).ne'
  have heq : (∫ y in graphTangentEllipse p x (a * r), w y) / (Real.pi * r ^ 2) -
      w x * a ^ 2 / Real.sqrt (1 + ‖p‖ ^ 2) =
      (∫ y in graphTangentEllipse p x (a * r), (w y - w x)) / (Real.pi * r ^ 2) := by
    rw [integral_sub hiE hcE, setIntegral_const, smul_eq_mul,
      volume_real_graphTangentEllipse p x har.le]
    field_simp [hJ, Real.pi_ne_zero, hr0.ne']
  rw [heq, norm_div, Real.norm_of_nonneg (mul_nonneg Real.pi_pos.le (sq_nonneg r))]
  have hnorm : ‖∫ y in graphTangentEllipse p x (a * r), (w y - w x)‖ ≤
      ∫ y in ball x (a * r), ‖w y - w x‖ := by
    apply (norm_integral_le_integral_norm _).trans
    exact setIntegral_mono_set (hiB.sub hcB).norm
      (Eventually.of_forall fun _ => norm_nonneg _)
      (Eventually.of_forall fun _ hy => graphTangentEllipse_subset_ball p x (a * r) hy)
  apply (div_le_div_of_nonneg_right hnorm (by positivity)).trans_eq
  dsimp only [Function.comp_apply]
  rw [setAverage_eq, smul_eq_mul, volume_real_ball_plane x har.le]
  field_simp [ha.ne', hr0.ne', Real.pi_ne_zero]

/-- Differentiability of the height and the norm Lebesgue-point property of the
piece weight give density one at the corresponding graph point. -/
theorem tendsto_graph_piece_density_of_lebesgue_point
    {f : EuclideanSpace ℝ (Fin 2) → ℝ} {K : ℝ≥0} (hf : LipschitzWith K f)
    {G : Set (EuclideanSpace ℝ (Fin 2))} (hG : MeasurableSet G)
    {x : EuclideanSpace ℝ (Fin 2)} (hxG : x ∈ G) (hdf : DifferentiableAt ℝ f x)
    (hx : Tendsto (fun r => ⨍ y in ball x r,
      ‖graphPieceWeight f G y - graphPieceWeight f G x‖) (𝓝[>] 0) (𝓝 0)) :
    Tendsto (fun r : ℝ => (hausdorffMeasure2 3).real
      (ball (graphMap f x) r ∩ graphMap f '' G) / (Real.pi * r ^ 2))
      (𝓝[>] 0) (𝓝 1) := by
  let w := graphPieceWeight f G
  let p := gradient f x
  let I (a r : ℝ) := (∫ y in graphTangentEllipse p x (a * r), w y) / (Real.pi * r ^ 2)
  let M (r : ℝ) := (hausdorffMeasure2 3).real
    (ball (graphMap f x) r ∩ graphMap f '' G) / (Real.pi * r ^ 2)
  have hw : LocallyIntegrable w volume := locallyIntegrable_graphPieceWeight hf hG
  have hwx : w x = Real.sqrt (1 + ‖p‖ ^ 2) := indicator_of_mem hxG _
  have hJ : Real.sqrt (1 + ‖p‖ ^ 2) ≠ 0 := (Real.sqrt_pos.mpr (by positivity)).ne'
  have hI (a : ℝ) (ha : 0 < a) : Tendsto (I a) (𝓝[>] 0) (𝓝 (a ^ 2)) := by
    have ht := tendsto_integral_graphTangentEllipse_div_sq hw p x hx ha
    rw [hwx] at ht
    simpa only [mul_div_cancel_left₀ _ hJ] using ht
  have hbounds (ε : ℝ) (hε : 0 < ε) (hε1 : ε < 1) :
      ∀ᶠ r in 𝓝[>] (0 : ℝ), I (1 / (1 + ε)) r ≤ M r ∧ M r ≤ I (1 / (1 - ε)) r := by
    filter_upwards [self_mem_nhdsWithin,
      eventually_graph_ball_between_tangent_ellipses hdf hε hε1] with r hr hb
    have hlo : graphTangentEllipse p x ((1 / (1 + ε)) * r) ⊆
        graphMap f ⁻¹' ball (graphMap f x) r := by
      simpa only [div_eq_mul_inv, one_mul, mul_comm] using hb.1
    have hup : graphMap f ⁻¹' ball (graphMap f x) r ⊆
        graphTangentEllipse p x ((1 / (1 - ε)) * r) := by
      simpa only [div_eq_mul_inv, one_mul, mul_comm] using hb.2
    have hiBall := (hw.integrableOn_isCompact (isCompact_closedBall x r)).mono_set
      ball_subset_closedBall
    have hiA : IntegrableOn w (graphMap f ⁻¹' ball (graphMap f x) r) volume :=
      hiBall.mono_set (graph_ball_preimage_subset_ball f x r)
    have hiUp : IntegrableOn w
        (graphTangentEllipse p x ((1 / (1 - ε)) * r)) volume :=
      ((hw.integrableOn_isCompact (isCompact_closedBall x ((1 / (1 - ε)) * r))).mono_set
        ball_subset_closedBall).mono_set (graphTangentEllipse_subset_ball _ _ _)
    dsimp only [I, M]
    rw [real_graph_piece_ball_eq_integral hf hG]
    constructor
    · apply div_le_div_of_nonneg_right _ (by positivity)
      exact setIntegral_mono_set hiA (Eventually.of_forall (graphPieceWeight_nonneg f G))
        (Eventually.of_forall fun _ hy => hlo hy)
    · apply div_le_div_of_nonneg_right _ (by positivity)
      exact setIntegral_mono_set hiUp (Eventually.of_forall (graphPieceWeight_nonneg f G))
        (Eventually.of_forall fun _ hy => hup hy)
  let ε (j : ℕ) : ℝ := (1 / 2) ^ (j + 1)
  have hεpos (j) : 0 < ε j := pow_pos (by norm_num) _
  have hεlt (j) : ε j < 1 := by
    have hp : (1 / 2 : ℝ) ^ j ≤ 1 := pow_le_one₀ (by norm_num) (by norm_num)
    dsimp only [ε]
    rw [pow_succ]
    nlinarith
  have hε : Tendsto ε atTop (𝓝 0) := by
    have ht := (tendsto_pow_atTop_nhds_zero_of_lt_one
      (by norm_num : (0 : ℝ) ≤ 1 / 2) (by norm_num : (1 / 2 : ℝ) < 1)).mul_const (1 / 2)
    simpa only [ε, pow_succ, zero_mul] using ht
  have hlow : Tendsto (fun j => (1 / (1 + ε j)) ^ 2) atTop (𝓝 (1 : ℝ)) := by
    have ht := ((tendsto_const_nhds (x := (1 : ℝ))).div
      ((tendsto_const_nhds (x := (1 : ℝ))).add hε) (by norm_num)).pow 2
    simpa using ht
  have hupp : Tendsto (fun j => (1 / (1 - ε j)) ^ 2) atTop (𝓝 (1 : ℝ)) := by
    have ht := ((tendsto_const_nhds (x := (1 : ℝ))).div
      ((tendsto_const_nhds (x := (1 : ℝ))).sub hε) (by norm_num)).pow 2
    simpa using ht
  apply tendsto_order.mpr
  constructor
  · intro b hb
    obtain ⟨j, hj⟩ := (hlow.eventually (Ioi_mem_nhds hb)).exists
    have hpos : 0 < 1 / (1 + ε j) := by have := hεpos j; positivity
    filter_upwards [(hI _ hpos).eventually (Ioi_mem_nhds hj),
      hbounds (ε j) (hεpos j) (hεlt j)] with r hr hbound
    exact hr.trans_le hbound.1
  · intro b hb
    obtain ⟨j, hj⟩ := (hupp.eventually (Iio_mem_nhds hb)).exists
    have hpos : 0 < 1 / (1 - ε j) := one_div_pos.mpr (sub_pos.mpr (hεlt j))
    filter_upwards [(hI _ hpos).eventually (Iio_mem_nhds hj),
      hbounds (ε j) (hεpos j) (hεlt j)] with r hr hbound
    exact hbound.2.trans_lt hr

/-- Density one at almost every base point of a Borel Lipschitz graph piece. -/
theorem ae_graph_piece_density_base
    {f : EuclideanSpace ℝ (Fin 2) → ℝ} {K : ℝ≥0} (hf : LipschitzWith K f)
    {G : Set (EuclideanSpace ℝ (Fin 2))} (hG : MeasurableSet G) :
    ∀ᵐ x ∂volume.restrict G, Tendsto (fun r : ℝ => (hausdorffMeasure2 3).real
      (ball (graphMap f x) r ∩ graphMap f '' G) / (Real.pi * r ^ 2))
      (𝓝[>] 0) (𝓝 1) := by
  have hLeb := ae_tendsto_average_norm_sub_ball volume (locallyIntegrable_graphPieceWeight hf hG)
  filter_upwards [ae_restrict_mem hG, ae_restrict_of_ae hf.ae_differentiableAt,
    ae_restrict_of_ae hLeb] with x hx hdf hpoint
  exact tendsto_graph_piece_density_of_lebesgue_point hf hG hx hdf hpoint

/-- The normalized two-dimensional density of every Borel Lipschitz graph piece
is one at Hausdorff-almost every point of that piece. -/
theorem ae_graph_piece_density
    {f : EuclideanSpace ℝ (Fin 2) → ℝ} {K : ℝ≥0} (hf : LipschitzWith K f)
    {G : Set (EuclideanSpace ℝ (Fin 2))} (hG : MeasurableSet G) :
    ∀ᵐ y ∂(hausdorffMeasure2 3).restrict (graphMap f '' G),
      Tendsto (fun r : ℝ => (hausdorffMeasure2 3).real
        (ball y r ∩ graphMap f '' G) / (Real.pi * r ^ 2)) (𝓝[>] 0) (𝓝 1) := by
  rw [hausdorffMeasure2_restrict_graphMap_image hf hG,
    (measurableEmbedding_graphMap hf).ae_map_iff]
  exact (withDensity_absolutelyContinuous (volume.restrict G)
    (fun x => ENNReal.ofReal (Real.sqrt (1 + ‖gradient f x‖ ^ 2)))).ae_le
      (ae_graph_piece_density_base hf hG)

end LiquidDrop

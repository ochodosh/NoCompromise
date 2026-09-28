import NoCompromise.Regularity.GraphNormal
import NoCompromise.Regularity.Excess

/-!
# Graph Dirichlet energy from genuine reduced-normal excess

For a graph of Lipschitz constant at most one, the base gradient energy is at
most twice the actual quadratic normal excess on any bounded Borel region
containing the graph piece. The normal comparison is derived in `GraphNormal`;
it is not an input. The constant two is independent of all graph parameters.
-/

noncomputable section
open MeasureTheory Set Filter Metric InnerProductSpace
open scoped Topology ENNReal NNReal Gradient
namespace LiquidDrop

/-- Either orientation of a unit graph normal controls the slope by the
quadratic deviation from the vertical direction. -/
lemma graphDirichlet_slope_bound (p : EuclideanSpace ℝ (Fin 2)) {ν : AmbientSpace}
    (hν : ν = graphUnitNormal p ∨ ν = -graphUnitNormal p) (hp : ‖p‖ ≤ 1) :
    ‖p‖ ^ 2 ≤ 2 * ‖ν - EuclideanSpace.single 2 1‖ ^ 2 := by
  let J := Real.sqrt (1 + ‖p‖ ^ 2)
  have hJ : 0 < J := Real.sqrt_pos.mpr (by positivity)
  have hJsq : J ^ 2 = 1 + ‖p‖ ^ 2 := Real.sq_sqrt (by positivity)
  have hsq : ‖p‖ ^ 2 ≤ 1 := by nlinarith [norm_nonneg p]
  have hrough : ‖p‖ ^ 2 ≤ (1 + ‖p‖ ^ 2) *
      ‖ν - EuclideanSpace.single 2 1‖ ^ 2 := by
    rcases hν with rfl | rfl
    · rw [norm_sub_sq_real, norm_graphUnitNormal]
      simp only [PiLp.norm_single, norm_one, EuclideanSpace.inner_single_right,
        graphUnitNormal, PiLp.smul_apply, graphNormalVector_apply_two, smul_eq_mul,
        mul_one, starRingEnd_apply, star_trivial, one_mul]
      change ‖p‖ ^ 2 ≤ (1 + ‖p‖ ^ 2) * (1 ^ 2 - 2 * J⁻¹ + 1 ^ 2)
      rw [← hJsq]
      have he : J ^ 2 * (1 ^ 2 - 2 * J⁻¹ + 1 ^ 2) = 2 * J ^ 2 - 2 * J := by
        field_simp [hJ.ne']; ring
      rw [he]
      nlinarith [sq_nonneg (J - 1)]
    · rw [norm_sub_sq_real, norm_neg, norm_graphUnitNormal]
      simp only [PiLp.norm_single, norm_one, inner_neg_left,
        EuclideanSpace.inner_single_right, graphUnitNormal, PiLp.smul_apply,
        graphNormalVector_apply_two, smul_eq_mul, mul_one, starRingEnd_apply, star_trivial, one_mul]
      change ‖p‖ ^ 2 ≤ (1 + ‖p‖ ^ 2) * (1 ^ 2 - 2 * -J⁻¹ + 1 ^ 2)
      have hn : 0 ≤ J⁻¹ := inv_nonneg.mpr hJ.le
      nlinarith [sq_nonneg ‖p‖]
  have ht := mul_le_mul_of_nonneg_right (show 1 + ‖p‖ ^ 2 ≤ 2 by linarith)
    (sq_nonneg ‖ν - EuclideanSpace.single 2 1‖)
  exact hrough.trans ht

/-- The nonnegative graph-energy inequality, with no finiteness assumption. -/
theorem lintegral_graph_gradient_sq_le (E : Set AmbientSpace)
    (hE : HasLocallyFinitePerimeter E) (hmE : NullMeasurableSet E volume)
    {f : EuclideanSpace ℝ (Fin 2) → ℝ} {K : ℝ≥0} (hf : LipschitzWith K f)
    (hK : (K : ℝ) ≤ 1) {G : Set (EuclideanSpace ℝ (Fin 2))} (hG : MeasurableSet G)
    (hred : graphMap f '' G ⊆ reducedBoundary E hE hmE) :
    (∫⁻ x in G, ENNReal.ofReal (‖gradient f x‖ ^ 2)) ≤
      2 * ∫⁻ y in graphMap f '' G,
        ENNReal.ofReal (‖reducedNormal E hE hmE y - EuclideanSpace.single 2 1‖ ^ 2)
          ∂hausdorffMeasure2 3 := by
  have hq : Measurable (fun y => ENNReal.ofReal
      (‖reducedNormal E hE hmE y - EuclideanSpace.single 2 1‖ ^ 2)) :=
    (((measurable_reducedNormal E hE hmE).sub measurable_const).norm.pow_const 2).ennreal_ofReal
  rw [lintegral_graphMap_image hf hG hq, ← lintegral_const_mul' _ _ (by norm_num)]
  apply lintegral_mono_ae
  filter_upwards [ae_reducedNormal_eq_graphUnitNormal_or_neg_base E hE hmE hf hG hred]
    with x hx
  have hp := (norm_gradient_le_of_lipschitz hf x).trans hK
  have hb := graphDirichlet_slope_bound (gradient f x) hx hp
  have hJ : 1 ≤ Real.sqrt (1 + ‖gradient f x‖ ^ 2) :=
    (Real.le_sqrt (by norm_num) (by positivity)).mpr (by nlinarith [sq_nonneg ‖gradient f x‖])
  have hb' := hb.trans (le_mul_of_one_le_right (by positivity) hJ)
  simpa only [ENNReal.ofReal_mul (by norm_num : (0 : ℝ) ≤ 2),
    ENNReal.ofReal_mul (sq_nonneg _), ENNReal.ofReal_ofNat, mul_assoc] using
      ENNReal.ofReal_le_ofReal hb'

/-- Genuine Dirichlet energy of a Borel graph piece is bounded by actual
reduced-normal excess in any bounded Borel containing region. -/
theorem graph_dirichlet_le_normalExcess (E : Set AmbientSpace)
    (hE : HasLocallyFinitePerimeter E) (hmE : NullMeasurableSet E volume)
    {f : EuclideanSpace ℝ (Fin 2) → ℝ} {K : ℝ≥0} (hf : LipschitzWith K f)
    (hK : (K : ℝ) ≤ 1) {G : Set (EuclideanSpace ℝ (Fin 2))} (hG : MeasurableSet G)
    (hred : graphMap f '' G ⊆ reducedBoundary E hE hmE)
    {U : Set AmbientSpace} (hU : MeasurableSet U) (hbU : Bornology.IsBounded U)
    (hGU : graphMap f '' G ⊆ U) :
    IntegrableOn (fun x => ‖gradient f x‖ ^ 2) G volume ∧
      (∫ x in G, ‖gradient f x‖ ^ 2) ≤
        2 * normalExcessIntegral E hE hmE U (EuclideanSpace.single 2 1) := by
  let μ := (hausdorffMeasure2 3).restrict (reducedBoundary E hE hmE)
  let := (reducedBoundary_outwardPerimeterPolar E hE hmE).finiteOnCompacts
  have hfin : volume G < ∞ :=
    (graphNormal_base_area_le_perimeter E hE hmE hf hG hred hU hGU).trans_lt (by
      rw [canonicalPerimeterMeasure_eq_reducedBoundary_area]
      exact hbU.measure_lt_top)
  let : IsFiniteMeasure (volume.restrict G) := ⟨by simpa using hfin⟩
  have hi : IntegrableOn (fun x => ‖gradient f x‖ ^ 2) G volume := by
    apply (integrable_const (1 : ℝ)).mono'
      ((measurable_gradient f).norm.pow_const 2).aestronglyMeasurable
    filter_upwards [] with x
    rw [Real.norm_eq_abs, abs_of_nonneg (sq_nonneg _)]
    have hp := (norm_gradient_le_of_lipschitz hf x).trans hK
    nlinarith [norm_nonneg (gradient f x)]
  refine ⟨hi, ?_⟩
  have hraw := lintegral_graph_gradient_sq_le E hE hmE hf hK hG hred
  have hmono : (hausdorffMeasure2 3).restrict (graphMap f '' G) ≤ μ.restrict U := by
    dsimp [μ]
    rw [Measure.restrict_restrict hU]
    exact Measure.restrict_mono_set _ fun y hy => ⟨hGU hy, hred hy⟩
  have hb := hraw.trans (mul_le_mul' le_rfl (lintegral_mono' hmono le_rfl))
  have hiν := integrableOn_normal_excess E hE hmE hbU (EuclideanSpace.single 2 1)
  rw [← ofReal_integral_eq_lintegral_ofReal hi (Eventually.of_forall fun _ => sq_nonneg _),
    ← ofReal_integral_eq_lintegral_ofReal hiν
      (Eventually.of_forall fun _ => sq_nonneg _)] at hb
  apply (ENNReal.ofReal_le_ofReal_iff (by
    exact mul_nonneg (by norm_num) (normalExcessIntegral_nonneg E hE hmE U _))).mp
  simpa only [ENNReal.ofReal_mul (by norm_num : (0 : ℝ) ≤ 2),
    ENNReal.ofReal_ofNat, normalExcessIntegral] using hb

end LiquidDrop

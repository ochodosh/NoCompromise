import NoCompromise.Area.Graph
import NoCompromise.Area.PlaneSections
import NoCompromise.BV.CoareaCoordinates

/-!
# Tangent ellipses for graph density

Linear area and the exact central disk area determine the volume of tangent
ellipses. At a differentiability point, graph-ball preimages are squeezed
between slightly dilated tangent ellipses.
-/

noncomputable section
open MeasureTheory Set Filter Metric Function InnerProductSpace
open scoped Topology ENNReal Gradient
namespace LiquidDrop

lemma norm_le_graphTangentMap (p v : EuclideanSpace ℝ (Fin 2)) :
    ‖v‖ ≤ ‖graphTangentMap p v‖ := by
  have hs : ‖graphTangentMap p v‖ ^ 2 = ‖v‖ ^ 2 + (inner ℝ p v) ^ 2 := by
    simp [EuclideanSpace.real_norm_sq_eq, Fin.sum_univ_three, Fin.sum_univ_two]
  nlinarith [norm_nonneg v, norm_nonneg (graphTangentMap p v), sq_nonneg (inner ℝ p v)]

lemma graphTangentMap_projection_of_inner_eq_zero (p : EuclideanSpace ℝ (Fin 2))
    {y : EuclideanSpace ℝ (Fin 3)} (hy : inner ℝ (graphUnitNormal p) y = 0) :
    graphTangentMap p (graphProjectionN 2 y) = y := by
  have hd : (Real.sqrt (1 + ‖p‖ ^ 2))⁻¹ ≠ 0 :=
    inv_ne_zero (Real.sqrt_pos.mpr (by positivity)).ne'
  rw [graphUnitNormal, real_inner_smul_left] at hy
  have hh := (mul_eq_zero.mp hy).resolve_left hd
  simp only [PiLp.inner_apply, Fin.sum_univ_three, RCLike.inner_apply,
    graphNormalVector_apply_zero, graphNormalVector_apply_one,
    graphNormalVector_apply_two, starRingEnd_apply, star_trivial] at hh
  apply PiLp.ext
  intro i
  fin_cases i
  · simp
  · simp
  · change graphTangentMap p (graphProjectionN 2 y) 2 = y 2
    simp only [graphTangentMap_apply_two, PiLp.inner_apply, Fin.sum_univ_two,
      RCLike.inner_apply, starRingEnd_apply, star_trivial, graphProjectionN_apply]
    norm_num at hh ⊢
    linarith

/-- The tangent ellipse of a graph slope, with center `x` and ambient radius `r`. -/
def graphTangentEllipse (p x : EuclideanSpace ℝ (Fin 2)) (r : ℝ) :
    Set (EuclideanSpace ℝ (Fin 2)) := {y | ‖graphTangentMap p (y - x)‖ < r}

lemma isOpen_graphTangentEllipse (p x : EuclideanSpace ℝ (Fin 2)) (r : ℝ) :
    IsOpen (graphTangentEllipse p x r) := isOpen_lt (by fun_prop) continuous_const

lemma graphTangentEllipse_subset_ball (p x : EuclideanSpace ℝ (Fin 2)) (r : ℝ) :
    graphTangentEllipse p x r ⊆ ball x r := by
  intro y hy
  exact (norm_le_graphTangentMap p (y - x)).trans_lt hy

lemma image_graphTangentEllipse_zero (p : EuclideanSpace ℝ (Fin 2)) (r : ℝ) :
    graphTangentMap p '' graphTangentEllipse p 0 r =
      ball (0 : EuclideanSpace ℝ (Fin 3)) r ∩ {y | inner ℝ y (graphUnitNormal p) = 0} := by
  ext y
  constructor
  · rintro ⟨v, hv, rfl⟩
    refine ⟨?_, ?_⟩
    · simpa only [graphTangentEllipse, mem_ofPred_eq, sub_zero, mem_ball,
        dist_zero_right] using hv
    · simpa only [mem_ofPred_eq, real_inner_comm] using inner_graphUnitNormal_graphTangentMap p v
  · intro hy
    have hp : inner ℝ (graphUnitNormal p) y = 0 := by
      simpa only [mem_ofPred_eq, real_inner_comm] using hy.2
    have he := graphTangentMap_projection_of_inner_eq_zero p hp
    refine ⟨graphProjectionN 2 y, ?_, he⟩
    change ‖graphTangentMap p (graphProjectionN 2 y - 0)‖ < r
    simpa only [sub_zero, he, mem_ball, dist_zero_right] using hy.1

/-- The exact real area of a tangent ellipse. -/
lemma volume_real_graphTangentEllipse (p x : EuclideanSpace ℝ (Fin 2)) {r : ℝ}
    (hr : 0 ≤ r) :
    volume.real (graphTangentEllipse p x r) = Real.pi * r ^ 2 / Real.sqrt (1 + ‖p‖ ^ 2) := by
  have htrans : volume (graphTangentEllipse p x r) = volume (graphTangentEllipse p 0 r) := by
    change volume ((fun y => y - x) ⁻¹' {v | ‖graphTangentMap p v‖ < r}) = _
    simpa only [sub_eq_add_neg, graphTangentEllipse, neg_zero, add_zero] using
      measure_preimage_add_right volume (-x) {v | ‖graphTangentMap p v‖ < r}
  rw [Measure.real, htrans]
  have harea := hausdorffMeasure2_image_linear (graphTangentMap p) (graphTangentMap_injective p)
    (graphTangentEllipse p 0 r)
  rw [image_graphTangentEllipse_zero,
    hausdorffMeasure2_central_plane_ball (norm_graphUnitNormal p) hr,
    jacobian2Linear_graphTangentMap] at harea
  have heq := congrArg ENNReal.toReal harea
  rw [ENNReal.toReal_mul, ENNReal.toReal_ofReal (by positivity),
    ENNReal.toReal_ofReal (Real.sqrt_nonneg _)] at heq
  apply (eq_div_iff (Real.sqrt_pos.mpr (by positivity)).ne').mpr
  nlinarith

/-- At a differentiability point, graph-ball preimages lie between the tangent
ellipses with radii `r/(1+ε)` and `r/(1-ε)`. -/
lemma eventually_graph_ball_between_tangent_ellipses
    {f : EuclideanSpace ℝ (Fin 2) → ℝ} {x : EuclideanSpace ℝ (Fin 2)}
    (hf : DifferentiableAt ℝ f x) {ε : ℝ} (hε : 0 < ε) (hεone : ε < 1) :
    ∀ᶠ r in 𝓝[>] (0 : ℝ),
      graphTangentEllipse (gradient f x) x (r / (1 + ε)) ⊆
        graphMap f ⁻¹' ball (graphMap f x) r ∧
      graphMap f ⁻¹' ball (graphMap f x) r ⊆
        graphTangentEllipse (gradient f x) x (r / (1 - ε)) := by
  obtain ⟨δ, hδ, hbound⟩ := Metric.mem_nhds_iff.mp
    ((hasFDerivAt_graphMap hf).isLittleO.def hε)
  filter_upwards [Ioo_mem_nhdsGT hδ] with r hr
  constructor
  · intro y hy
    have hrdiv : r / (1 + ε) ≤ r := (div_le_self hr.1.le (by linarith))
    have hnear : y ∈ ball x δ :=
      ((graphTangentEllipse_subset_ball _ _ _ hy).trans_le hrdiv).trans hr.2
    have hb := hbound hnear
    change ‖graphMap f y - graphMap f x - graphTangentMap (gradient f x) (y - x)‖ ≤
      ε * ‖y - x‖ at hb
    have hlow := norm_le_graphTangentMap (gradient f x) (y - x)
    have htri := norm_add_le
      (graphMap f y - graphMap f x - graphTangentMap (gradient f x) (y - x))
      (graphTangentMap (gradient f x) (y - x))
    simp only [sub_add_cancel] at htri
    change ‖graphTangentMap (gradient f x) (y - x)‖ < r / (1 + ε) at hy
    have hys := (lt_div_iff₀ (by linarith : 0 < 1 + ε)).mp hy
    change ‖graphMap f y - graphMap f x‖ < r
    nlinarith
  · intro y hy
    have hd : dist y x ≤ dist (graphMap f y) (graphMap f x) := by
      simpa only [NNReal.coe_one, one_mul] using (antilipschitzWith_graphMap f).le_mul_dist y x
    have hnear : y ∈ ball x δ := hd.trans_lt (hy.trans hr.2)
    have hb := hbound hnear
    change ‖graphMap f y - graphMap f x - graphTangentMap (gradient f x) (y - x)‖ ≤
      ε * ‖y - x‖ at hb
    have hlow := norm_le_graphTangentMap (gradient f x) (y - x)
    have htri := norm_sub_le (graphMap f y - graphMap f x)
      ((graphMap f y - graphMap f x) - graphTangentMap (gradient f x) (y - x))
    simp only [sub_sub_cancel] at htri
    change ‖graphMap f y - graphMap f x‖ < r at hy
    change ‖graphTangentMap (gradient f x) (y - x)‖ < r / (1 - ε)
    apply (lt_div_iff₀ (by linarith : 0 < 1 - ε)).mpr
    nlinarith

end LiquidDrop

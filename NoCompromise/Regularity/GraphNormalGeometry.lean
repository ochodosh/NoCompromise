import NoCompromise.Area.GraphDensityGeometry
import NoCompromise.DeGiorgi.ConeConcentration

/-!
# Graph tangents and exterior normal cones

The algebraic normal is determined up to sign by orthogonality to the graph
plane. At a differentiability point, any tangent direction outside another
plane produces an entire scaled open base ball outside a fixed cone about
that plane. These statements contain no geometric tangent identification.
-/

noncomputable section
open MeasureTheory Set Filter Metric InnerProductSpace
open scoped Topology ENNReal Gradient
namespace LiquidDrop

/-- The only unit vectors orthogonal to a graph plane are its two unit normals. -/
theorem graphNormal_eq_or_neg_of_orthogonal (p : EuclideanSpace ℝ (Fin 2))
    {ν : AmbientSpace} (hν : ‖ν‖ = 1)
    (horth : ∀ v, inner ℝ ν (graphTangentMap p v) = 0) :
    ν = graphUnitNormal p ∨ ν = -graphUnitNormal p := by
  let n := graphUnitNormal p
  let c := inner ℝ n ν
  let w := ν - c • n
  have hn : ‖n‖ = 1 := norm_graphUnitNormal p
  have hnw : inner ℝ n w = 0 := by simp [w, c, inner_sub_right, real_inner_smul_right, hn]
  have hνw : inner ℝ ν w = 0 := by
    rw [← graphTangentMap_projection_of_inner_eq_zero p hnw]
    exact horth _
  have hww : inner ℝ w w = 0 := by
    rw [show w = ν - c • n from rfl, inner_sub_left, real_inner_smul_left, hνw, hnw]
    ring
  have hw : w = 0 := inner_self_eq_zero.mp hww
  have he : ν = c • n := sub_eq_zero.mp hw
  have hc : |c| = 1 := by simpa [he, norm_smul, hn] using hν
  rcases (abs_eq (by norm_num : (0 : ℝ) ≤ 1)).mp hc with hc | hc
  · left; simpa [hc] using he
  · right; simpa [hc] using he

/-- A derivative controls every rescaled increment uniformly on a bounded set. -/
lemma graphNormal_eventually_rescaled_error
    {f : EuclideanSpace ℝ (Fin 2) → ℝ} {x : EuclideanSpace ℝ (Fin 2)}
    (hf : DifferentiableAt ℝ f x) {M ε : ℝ} (hM : 0 < M) (hε : 0 < ε) :
    ∀ᶠ r in 𝓝[>] (0 : ℝ), ∀ w : EuclideanSpace ℝ (Fin 2), ‖w‖ < M →
      ‖r⁻¹ • (graphMap f (x + r • w) - graphMap f x) -
        graphTangentMap (gradient f x) w‖ ≤ ε := by
  obtain ⟨δ, hδ, hb⟩ := Metric.mem_nhds_iff.mp
    ((hasFDerivAt_graphMap hf).isLittleO.def (div_pos hε hM))
  filter_upwards [Ioo_mem_nhdsGT (div_pos hδ hM)] with r hr
  have hr0 : 0 < r := hr.1
  intro w hw
  have hnear : x + r • w ∈ ball x δ := by
    simp only [mem_ball, dist_eq_norm, add_sub_cancel_left, norm_smul,
      Real.norm_of_nonneg hr.1.le]
    exact (mul_lt_mul_of_pos_left hw hr.1).trans ((lt_div_iff₀ hM).mp hr.2)
  have hh := hb hnear
  change ‖graphMap f (x + r • w) - graphMap f x -
    graphTangentMap (gradient f x) (x + r • w - x)‖ ≤
      ε / M * ‖x + r • w - x‖ at hh
  simp only [add_sub_cancel_left, map_smul, norm_smul, Real.norm_of_nonneg hr.1.le] at hh
  have heq : r⁻¹ • (graphMap f (x + r • w) - graphMap f x) -
      graphTangentMap (gradient f x) w =
      r⁻¹ • (graphMap f (x + r • w) - graphMap f x -
        r • graphTangentMap (gradient f x) w) := by
    simp only [smul_sub, smul_smul, inv_mul_cancel₀ hr.1.ne', one_smul]
  rw [heq, norm_smul, Real.norm_of_nonneg (inv_nonneg.mpr hr.1.le)]
  calc
    _ ≤ r⁻¹ * (ε / M * (r * ‖w‖)) := mul_le_mul_of_nonneg_left hh (by positivity)
    _ = ε / M * ‖w‖ := by field_simp [hr0.ne']
    _ ≤ ε / M * M := mul_le_mul_of_nonneg_left hw.le (by positivity)
    _ = ε := div_mul_cancel₀ _ hM.ne'

/-- A nonorthogonal graph tangent forces a fixed positive-radius base patch
into the exterior of a normal cone at all sufficiently small scales. -/
theorem graphNormal_exists_off_cone_patch
    {f : EuclideanSpace ℝ (Fin 2) → ℝ} {x : EuclideanSpace ℝ (Fin 2)}
    (hf : DifferentiableAt ℝ f x) (ν : AmbientSpace)
    {v : EuclideanSpace ℝ (Fin 2)}
    (hv : inner ℝ ν (graphTangentMap (gradient f x) v) ≠ 0) :
    ∃ δ ε R : ℝ, 0 < δ ∧ 0 < ε ∧ 0 < R ∧
      ∀ᶠ r in 𝓝[>] (0 : ℝ), ∀ w ∈ ball v δ,
        graphMap f (x + r • w) ∈ ball (graphMap f x) (r * R) \
          normalPlaneCone (graphMap f x) ν ε := by
  let z := graphTangentMap (gradient f x) v
  let R := ‖z‖ + 1
  let ε := |inner ℝ ν z| / (2 * R)
  have hR : 0 < R := by dsimp [R]; positivity
  have hε : 0 < ε := div_pos (abs_pos.mpr hv) (by positivity)
  let U : Set AmbientSpace := {y | ‖y‖ < R ∧ ε * ‖y‖ < |inner ℝ ν y|}
  have hU : IsOpen U := by
    change IsOpen ({y : AmbientSpace | ‖y‖ < R} ∩
      {y : AmbientSpace | ε * ‖y‖ < |inner ℝ ν y|})
    exact (isOpen_lt (by fun_prop) continuous_const).inter
      (isOpen_lt (by fun_prop) (by fun_prop))
  have hz : z ∈ U := by
    refine ⟨by dsimp [R]; linarith, ?_⟩
    have he : ε * (2 * R) = |inner ℝ ν z| := div_mul_cancel₀ _ (by positivity)
    have hr : ‖z‖ < 2 * R := by dsimp [R]; nlinarith [norm_nonneg z]
    nlinarith
  obtain ⟨a, ha, hball⟩ := Metric.mem_nhds_iff.mp (hU.mem_nhds hz)
  have hpre : graphTangentMap (gradient f x) ⁻¹' ball z (a / 2) ∈ 𝓝 v :=
    (graphTangentMap (gradient f x)).continuous.continuousAt
      (ball_mem_nhds _ (by positivity))
  obtain ⟨δ, hδ, hδball⟩ := Metric.mem_nhds_iff.mp hpre
  refine ⟨δ, ε, R, hδ, hε, hR, ?_⟩
  have hM : 0 < ‖v‖ + δ := by positivity
  filter_upwards [self_mem_nhdsWithin,
    graphNormal_eventually_rescaled_error hf hM (show 0 < a / 2 by positivity)] with r hr he
  change 0 < r at hr
  intro w hw
  have hwm : ‖w‖ < ‖v‖ + δ := by
    have ht' := norm_add_le (w - v) v
    rw [sub_add_cancel] at ht'
    have hw' : ‖w - v‖ < δ := hw
    linarith
  have hew := he w hwm
  have htw := hδball hw
  have hnear : r⁻¹ • (graphMap f (x + r • w) - graphMap f x) ∈ ball z a := by
    have ht := dist_triangle (r⁻¹ • (graphMap f (x + r • w) - graphMap f x))
      (graphTangentMap (gradient f x) w) z
    simp only [dist_eq_norm] at ht
    change dist (graphTangentMap (gradient f x) w) z < a / 2 at htw
    simp only [dist_eq_norm] at htw
    change ‖r⁻¹ • (graphMap f (x + r • w) - graphMap f x) - z‖ < a
    linarith
  have hh := hball hnear
  change ‖r⁻¹ • (graphMap f (x + r • w) - graphMap f x)‖ < R ∧
    ε * ‖r⁻¹ • (graphMap f (x + r • w) - graphMap f x)‖ <
      |inner ℝ ν (r⁻¹ • (graphMap f (x + r • w) - graphMap f x))| at hh
  simp only [norm_smul, Real.norm_of_nonneg (inv_nonneg.mpr hr.le),
    real_inner_smul_right, abs_mul, abs_of_nonneg (inv_nonneg.mpr hr.le)] at hh
  constructor
  · change ‖graphMap f (x + r • w) - graphMap f x‖ < r * R
    have ht := mul_lt_mul_of_pos_left hh.1 hr
    simpa [← mul_assoc, hr.ne'] using ht
  · change ¬ |inner ℝ ν (graphMap f (x + r • w) - graphMap f x)| <
      ε * ‖graphMap f (x + r • w) - graphMap f x‖
    have ht := mul_lt_mul_of_pos_left hh.2 hr
    have hc : ε * ‖graphMap f (x + r • w) - graphMap f x‖ <
        |inner ℝ ν (graphMap f (x + r • w) - graphMap f x)| := by
      convert ht using 1 <;> first | rfl | (field_simp [hr.ne'])
    exact not_lt.mpr hc.le

end LiquidDrop

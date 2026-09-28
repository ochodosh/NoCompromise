import NoCompromise.DeGiorgi.ExactDensity
import NoCompromise.Measure.WeakStarNull
import Mathlib.Topology.MetricSpace.HausdorffDistance

/-!
# Perimeter concentration in tangent-plane cones

At every reduced point, the rescaled perimeter measures converge to plane area.
The closed complement of a positive-aperture plane cone in a bounded ball is
compact and meets that plane only at the origin. Compact-null-set convergence
therefore gives concentration, including the boundary of the cone.
-/

noncomputable section
open MeasureTheory Set Filter Metric
open scoped Topology ENNReal
namespace LiquidDrop

/-- Distance to the plane perpendicular to a unit vector is its absolute normal coordinate. -/
lemma infDist_normal_plane {ν : AmbientSpace} (hν : ‖ν‖ = 1) (y : AmbientSpace) :
    infDist y {z : AmbientSpace | inner ℝ ν z = 0} = |inner ℝ ν y| := by
  apply le_antisymm
  · have hp : y - (inner ℝ ν y) • ν ∈ {z : AmbientSpace | inner ℝ ν z = 0} := by
      simp [inner_sub_right, inner_smul_right, hν]
    have hb := infDist_le_dist_of_mem (x := y) hp
    simpa [dist_eq_norm, norm_smul, hν] using hb
  · apply (le_infDist (show ({z : AmbientSpace | inner ℝ ν z = 0}).Nonempty from
      ⟨0, by simp⟩)).mpr
    intro z hz
    change inner ℝ ν z = 0 at hz
    have hb := abs_real_inner_le_norm ν (y - z)
    simpa [inner_sub_right, hz, hν, dist_eq_norm] using hb

/-- The open cone around the plane normal to `ν`, with vertex `x`. -/
def normalPlaneCone (x ν : AmbientSpace) (ε : ℝ) : Set AmbientSpace :=
  {y | |inner ℝ ν (y - x)| < ε * ‖y - x‖}

lemma isOpen_normalPlaneCone (x ν : AmbientSpace) (ε : ℝ) :
    IsOpen (normalPlaneCone x ν ε) :=
  isOpen_lt (by fun_prop) (by fun_prop)

lemma normalPlaneCone_eq_distance_cone (x : AmbientSpace) {ν : AmbientSpace}
    (hν : ‖ν‖ = 1) (ε : ℝ) :
    normalPlaneCone x ν ε =
      {y | infDist (y - x) {z : AmbientSpace | inner ℝ ν z = 0} < ε * ‖y - x‖} := by
  ext y
  simp only [normalPlaneCone, mem_ofPred_eq, infDist_normal_plane hν]

/-- The compact complement of an open cone inside a closed central ball. -/
def closedConeComplement (ν : AmbientSpace) (ε R : ℝ) : Set AmbientSpace :=
  closedBall 0 R \ normalPlaneCone 0 ν ε

lemma isCompact_closedConeComplement (ν : AmbientSpace) (ε R : ℝ) :
    IsCompact (closedConeComplement ν ε R) :=
  (isCompact_closedBall 0 R).diff (isOpen_normalPlaneCone 0 ν ε)

/-- The closed cone complement meets its limiting plane only at the null origin. -/
lemma halfspacePlaneMeasure_closedConeComplement {ν : AmbientSpace} (hν : ‖ν‖ = 1)
    {ε : ℝ} (hε : 0 < ε) (R : ℝ) :
    halfspacePlaneMeasure ν (closedConeComplement ν ε R) = 0 := by
  have hnull := halfspacePlaneMeasure_sphere hν 0
  rw [halfspacePlaneMeasure, Measure.restrict_apply isClosed_sphere.measurableSet] at hnull
  rw [halfspacePlaneMeasure,
    Measure.restrict_apply (isCompact_closedConeComplement ν ε R).measurableSet]
  apply measure_mono_null ?_ hnull
  intro y hy
  have hc := hy.1.2
  have hp := hy.2
  change inner ℝ ν y = 0 at hp
  change ¬ |inner ℝ ν (y - 0)| < ε * ‖y - 0‖ at hc
  simp only [sub_zero, hp, abs_zero, not_lt] at hc
  have hy0 : y = 0 := norm_eq_zero.mp (by nlinarith [norm_nonneg y])
  exact ⟨by simp [hy0], hy.2⟩

/-- The full rescaled perimeter mass outside a fixed plane cone tends to zero,
even when the cone boundary and the outer sphere are included. -/
theorem tendsto_blowupPolarMeasure_closedConeComplement (E : Set AmbientSpace)
    (hE : HasLocallyFinitePerimeter E) (hmE : NullMeasurableSet E volume)
    {x : AmbientSpace} (hx : x ∈ reducedBoundary E hE hmE)
    {ε : ℝ} (hε : 0 < ε) (R : ℝ) :
    Tendsto (fun r : ℝ => (blowupPolarMeasure (canonicalPerimeterMeasure E hE hmE) x r).real
      (closedConeComplement (reducedNormal E hE hmE x) ε R)) (𝓝[>] 0) (𝓝 0) := by
  let μ := canonicalPerimeterMeasure E hE hmE
  let ν := reducedNormal E hE hmE x
  have hν : ‖ν‖ = 1 := norm_reducedNormal E hE hmE hx
  let := (canonicalPerimeterPolar E hE hmE).finiteOnCompacts
  let := halfspacePlaneMeasure_regular hν
  apply tendsto_real_compact_null_of_compact_test_convergence
    (fun r => blowupPolarMeasure μ x r) (halfspacePlaneMeasure ν)
  · filter_upwards [self_mem_nhdsWithin] with r hr
    exact blowupPolarMeasure_finiteOnCompacts μ x hr
  · exact tendsto_integral_blowupPolarMeasure E hE hmE hx
  · exact isCompact_closedConeComplement ν ε R
  · exact halfspacePlaneMeasure_closedConeComplement hν hε R

/-- Positive dilations preserve the aperture of the normal-plane cone. -/
lemma mem_normalPlaneCone_translate_smul (x ν y : AmbientSpace) (ε : ℝ)
    {r : ℝ} (hr : 0 < r) :
    x + r • y ∈ normalPlaneCone x ν ε ↔ y ∈ normalPlaneCone 0 ν ε := by
  simp only [normalPlaneCone, mem_ofPred_eq, add_sub_cancel_left, sub_zero,
    inner_smul_right, norm_smul, Real.norm_eq_abs, abs_mul, abs_of_pos hr]
  rw [show ε * (r * ‖y‖) = r * (ε * ‖y‖) by ring]
  exact mul_lt_mul_iff_right₀ hr

lemma image_normalPlaneCone_translate_smul (x ν : AmbientSpace) (ε : ℝ)
    {r : ℝ} (hr : 0 < r) :
    (fun y => x + r • y) '' normalPlaneCone 0 ν ε = normalPlaneCone x ν ε := by
  ext y
  constructor
  · rintro ⟨z, hz, rfl⟩
    exact (mem_normalPlaneCone_translate_smul x ν z ε hr).mpr hz
  · intro hy
    obtain ⟨z, rfl⟩ := (blowupHomeomorph x hr).surjective y
    exact ⟨z, (mem_normalPlaneCone_translate_smul x ν z ε hr).mp hy, rfl⟩

lemma blowupPolarMeasure_real_ball_sdiff_cone (μ : Measure AmbientSpace)
    (x ν : AmbientSpace) (ε R : ℝ) {r : ℝ} (hr : 0 < r) :
    (blowupPolarMeasure μ x r).real (ball 0 R \ normalPlaneCone 0 ν ε) =
      r⁻¹ ^ 2 * μ.real (ball x (r * R) \ normalPlaneCone x ν ε) := by
  rw [Measure.real, blowupPolarMeasure_apply μ x hr
    (measurableSet_ball.diff (isOpen_normalPlaneCone 0 ν ε).measurableSet),
    Set.image_sdiff (show Function.Injective (fun y : AmbientSpace => x + r • y) from
      (blowupHomeomorph x hr).injective), image_ball_translate_pos_smul x hr R,
    image_normalPlaneCone_translate_smul x ν ε hr, ENNReal.toReal_mul,
    ENNReal.toReal_ofReal (sq_nonneg _)]
  rfl

/-- Rescaled mass in the open ball outside the strict plane cone tends to zero. -/
theorem tendsto_blowupPolarMeasure_ball_sdiff_cone (E : Set AmbientSpace)
    (hE : HasLocallyFinitePerimeter E) (hmE : NullMeasurableSet E volume)
    {x : AmbientSpace} (hx : x ∈ reducedBoundary E hE hmE)
    {ε : ℝ} (hε : 0 < ε) (R : ℝ) :
    Tendsto (fun r : ℝ => (blowupPolarMeasure (canonicalPerimeterMeasure E hE hmE) x r).real
      (ball 0 R \ normalPlaneCone 0 (reducedNormal E hE hmE x) ε)) (𝓝[>] 0) (𝓝 0) := by
  let μ := canonicalPerimeterMeasure E hE hmE
  let ν := reducedNormal E hE hmE x
  let := (canonicalPerimeterPolar E hE hmE).finiteOnCompacts
  apply squeeze_zero' (Eventually.of_forall fun _ => ENNReal.toReal_nonneg) ?_
    (tendsto_blowupPolarMeasure_closedConeComplement E hE hmE hx hε R)
  filter_upwards [self_mem_nhdsWithin] with r hr
  let := blowupPolarMeasure_finiteOnCompacts μ x hr
  exact ENNReal.toReal_mono (isCompact_closedConeComplement ν ε R).measure_lt_top.ne
    (measure_mono (sdiff_subset_sdiff_left ball_subset_closedBall))

/-- Blueprint cone concentration, as a ratio to the actual perimeter of the ball. -/
theorem cone_concentration (E : Set AmbientSpace)
    (hE : HasLocallyFinitePerimeter E) (hmE : NullMeasurableSet E volume)
    {x : AmbientSpace} (hx : x ∈ reducedBoundary E hE hmE)
    {ε : ℝ} (hε : 0 < ε) :
    Tendsto (fun r : ℝ =>
      (canonicalPerimeterMeasure E hE hmE).real
        (ball x r \ normalPlaneCone x (reducedNormal E hE hmE x) ε) /
      (canonicalPerimeterMeasure E hE hmE).real (ball x r)) (𝓝[>] 0) (𝓝 0) := by
  have ht := (tendsto_blowupPolarMeasure_ball_sdiff_cone E hE hmE hx hε 1).div
    (tendsto_blowupPolarMeasure_real_ball E hE hmE hx (R := 1) zero_lt_one)
    (by simp [Real.pi_ne_zero])
  simp only [zero_div] at ht
  apply ht.congr'
  filter_upwards [self_mem_nhdsWithin] with r hr
  dsimp only [Pi.div_apply]
  rw [blowupPolarMeasure_real_ball_sdiff_cone _ _ _ _ _ hr,
    blowupPolarMeasure_real_ball _ _ hr, mul_one]
  exact mul_div_mul_left _ _ (pow_ne_zero 2 (inv_ne_zero hr.ne'))

/-- Cone concentration in the blueprint's literal distance-to-plane notation. -/
theorem cone_concentration_distance (E : Set AmbientSpace)
    (hE : HasLocallyFinitePerimeter E) (hmE : NullMeasurableSet E volume)
    {x : AmbientSpace} (hx : x ∈ reducedBoundary E hE hmE)
    {ε : ℝ} (hε : 0 < ε) :
    Tendsto (fun r : ℝ =>
      (canonicalPerimeterMeasure E hE hmE).real
        (ball x r \ {y | infDist (y - x)
          {z : AmbientSpace | inner ℝ (reducedNormal E hE hmE x) z = 0} < ε * ‖y - x‖}) /
      (canonicalPerimeterMeasure E hE hmE).real (ball x r)) (𝓝[>] 0) (𝓝 0) := by
  simpa only [normalPlaneCone_eq_distance_cone x (norm_reducedNormal E hE hmE hx) ε] using
    cone_concentration E hE hmE hx hε

/-- The stronger closed-complement mass limit also holds in extended nonnegative reals. -/
theorem tendsto_blowupPolarMeasure_closedConeComplement_ennreal (E : Set AmbientSpace)
    (hE : HasLocallyFinitePerimeter E) (hmE : NullMeasurableSet E volume)
    {x : AmbientSpace} (hx : x ∈ reducedBoundary E hE hmE)
    {ε : ℝ} (hε : 0 < ε) (R : ℝ) :
    Tendsto (fun r : ℝ => blowupPolarMeasure (canonicalPerimeterMeasure E hE hmE) x r
      (closedConeComplement (reducedNormal E hE hmE x) ε R)) (𝓝[>] 0) (𝓝 0) := by
  have ht := ENNReal.tendsto_ofReal
    (tendsto_blowupPolarMeasure_closedConeComplement E hE hmE hx hε R)
  simp only [ENNReal.ofReal_zero] at ht
  apply ht.congr'
  filter_upwards [self_mem_nhdsWithin] with r hr
  let := (canonicalPerimeterPolar E hE hmE).finiteOnCompacts
  let := blowupPolarMeasure_finiteOnCompacts (canonicalPerimeterMeasure E hE hmE) x hr
  exact ENNReal.ofReal_toReal
    (isCompact_closedConeComplement (reducedNormal E hE hmE x) ε R).measure_lt_top.ne

/-- Blueprint `lem:cone-concentration`: the rescaled mass of the strict exterior
cone in the unit ball tends to zero. -/
theorem cone_concentration_rescaled (E : Set AmbientSpace)
    (hE : HasLocallyFinitePerimeter E) (hmE : NullMeasurableSet E volume)
    {x : AmbientSpace} (hx : x ∈ reducedBoundary E hE hmE)
    {ε : ℝ} (hε : 0 < ε) :
    Tendsto (fun r : ℝ => blowupPolarMeasure (canonicalPerimeterMeasure E hE hmE) x r
      {y ∈ ball (0 : AmbientSpace) 1 | ε * ‖y‖ < infDist y
        {z : AmbientSpace | inner ℝ (reducedNormal E hE hmE x) z = 0}})
      (𝓝[>] 0) (𝓝 0) := by
  apply ENNReal.tendsto_nhds_zero.mpr
  intro δ hδ
  filter_upwards [ENNReal.tendsto_nhds_zero.mp
    (tendsto_blowupPolarMeasure_closedConeComplement_ennreal E hE hmE hx hε 1) δ hδ]
    with r hr
  apply le_trans (measure_mono ?_) hr
  intro y hy
  refine ⟨ball_subset_closedBall hy.1, ?_⟩
  change ¬ |inner ℝ (reducedNormal E hE hmE x) (y - 0)| < ε * ‖y - 0‖
  have hb := hy.2
  rw [infDist_normal_plane (norm_reducedNormal E hE hmE hx)] at hb
  simpa only [sub_zero] using not_lt.mpr hb.le

end LiquidDrop

import NoCompromise.Regularity.Cylinders
import NoCompromise.DeGiorgi.Structure

/-! # Spherical and cylindrical normal excess -/

noncomputable section
open MeasureTheory Set Metric Filter
open scoped ENNReal Topology
namespace LiquidDrop

/-- The unnormalized squared normal deviation on a region, integrated with
respect to actual reduced-boundary Hausdorff area. -/
def normalExcessIntegral (E : Set AmbientSpace) (hE : HasLocallyFinitePerimeter E)
    (hmE : NullMeasurableSet E volume) (U : Set AmbientSpace) (ν : AmbientSpace) : ℝ :=
  ∫ y in U, ‖reducedNormal E hE hmE y - ν‖ ^ 2
    ∂(hausdorffMeasure2 3).restrict (reducedBoundary E hE hmE)

/-- Blueprint spherical excess, with normalization r⁻². -/
def sphericalExcess (E : Set AmbientSpace) (hE : HasLocallyFinitePerimeter E)
    (hmE : NullMeasurableSet E volume) (x : AmbientSpace) (r : ℝ) (ν : AmbientSpace) : ℝ :=
  normalExcessIntegral E hE hmE (ball x r) ν / r ^ 2

/-- Blueprint cylindrical excess, about the specified unit axis. -/
def cylindricalExcess (E : Set AmbientSpace) (hE : HasLocallyFinitePerimeter E)
    (hmE : NullMeasurableSet E volume) (x : AmbientSpace) (r : ℝ) (ν : AmbientSpace) : ℝ :=
  normalExcessIntegral E hE hmE (cylinder x r ν) ν / r ^ 2

lemma normalExcessIntegral_eq_area (E : Set AmbientSpace) (hE : HasLocallyFinitePerimeter E)
    (hmE : NullMeasurableSet E volume) {U : Set AmbientSpace} (hU : MeasurableSet U)
    (ν : AmbientSpace) :
    normalExcessIntegral E hE hmE U ν =
      ∫ y in reducedBoundary E hE hmE ∩ U,
        ‖reducedNormal E hE hmE y - ν‖ ^ 2 ∂hausdorffMeasure2 3 := by
  rw [normalExcessIntegral, Measure.restrict_restrict hU, inter_comm]

lemma integrableOn_normal_excess (E : Set AmbientSpace) (hE : HasLocallyFinitePerimeter E)
    (hmE : NullMeasurableSet E volume) {U : Set AmbientSpace}
    (hbU : Bornology.IsBounded U) (ν : AmbientSpace) :
    IntegrableOn (fun y => ‖reducedNormal E hE hmE y - ν‖ ^ 2) U
      ((hausdorffMeasure2 3).restrict (reducedBoundary E hE hmE)) := by
  let μ := (hausdorffMeasure2 3).restrict (reducedBoundary E hE hmE)
  have hp := reducedBoundary_outwardPerimeterPolar E hE hmE
  let := hp.finiteOnCompacts
  have hfin : μ U < ∞ := hbU.measure_lt_top
  let : IsFiniteMeasure (μ.restrict U) := ⟨by simpa only [Measure.restrict_apply_univ] using hfin⟩
  have hm : Measurable (fun y => ‖reducedNormal E hE hmE y - ν‖ ^ 2) :=
    ((measurable_reducedNormal E hE hmE).sub measurable_const).norm.pow_const 2
  apply (integrable_const ((1 + ‖ν‖) ^ 2 : ℝ)).mono' hm.aestronglyMeasurable
  filter_upwards [ae_restrict_of_ae hp.norm_ae] with y hy
  rw [Real.norm_eq_abs, abs_of_nonneg (sq_nonneg _)]
  apply (sq_le_sq₀ (norm_nonneg _) (by positivity)).mpr
  exact (norm_sub_le _ _).trans (by rw [hy])

lemma normalExcessIntegral_nonneg (E : Set AmbientSpace) (hE : HasLocallyFinitePerimeter E)
    (hmE : NullMeasurableSet E volume) (U : Set AmbientSpace) (ν : AmbientSpace) :
    0 ≤ normalExcessIntegral E hE hmE U ν :=
  integral_nonneg (fun _ => sq_nonneg _)

lemma normalExcessIntegral_mono (E : Set AmbientSpace) (hE : HasLocallyFinitePerimeter E)
    (hmE : NullMeasurableSet E volume) {U V : Set AmbientSpace}
    (hbV : Bornology.IsBounded V) (hUV : U ⊆ V) (ν : AmbientSpace) :
    normalExcessIntegral E hE hmE U ν ≤ normalExcessIntegral E hE hmE V ν := by
  apply setIntegral_mono_set (integrableOn_normal_excess E hE hmE hbV ν)
    (Eventually.of_forall (fun _ => sq_nonneg _))
  exact Eventually.of_forall hUV

/-- Blueprint `lem:excess-ball-cyl`, with its exact normalization factor two. -/
theorem excess_ball_cylinder_comparison (E : Set AmbientSpace)
    (hE : HasLocallyFinitePerimeter E) (hmE : NullMeasurableSet E volume)
    (x : AmbientSpace) {r : ℝ} (hr : 0 < r) {ν : AmbientSpace} (hν : ‖ν‖ = 1) :
    sphericalExcess E hE hmE x r ν ≤ cylindricalExcess E hE hmE x r ν ∧
      cylindricalExcess E hE hmE x r ν ≤
        2 * sphericalExcess E hE hmE x (Real.sqrt 2 * r) ν := by
  constructor
  · exact div_le_div_of_nonneg_right
      (normalExcessIntegral_mono E hE hmE (isBounded_cylinder x r hν)
        (ball_subset_cylinder x r hν) ν) (sq_nonneg r)
  · have hi := normalExcessIntegral_mono E hE hmE isBounded_ball
      (cylinder_subset_ball x hr.le hν) ν
    have he : 2 * sphericalExcess E hE hmE x (Real.sqrt 2 * r) ν =
        normalExcessIntegral E hE hmE (ball x (Real.sqrt 2 * r)) ν / r ^ 2 := by
      rw [sphericalExcess, mul_pow, Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 2)]
      ring
    rw [he]
    exact div_le_div_of_nonneg_right hi (sq_nonneg r)

/-- Blueprint `lem:excess-center`, at the exact radius and factor used by the
uniform-center iteration. -/
theorem excess_change_center (E : Set AmbientSpace)
    (hE : HasLocallyFinitePerimeter E) (hmE : NullMeasurableSet E volume)
    {x z ν : AmbientSpace} {r : ℝ} (hr : 0 < r) (hν : ‖ν‖ = 1)
    (hz : z ∈ cylinder x (r / 8) ν) :
    cylindricalExcess E hE hmE z (r / 8) ν ≤ 64 * cylindricalExcess E hE hmE x r ν := by
  have hi := normalExcessIntegral_mono E hE hmE (isBounded_cylinder x r hν)
    (cylinder_eighth_subset hr.le hz) ν
  have hd := div_le_div_of_nonneg_right hi (sq_nonneg (r / 8))
  change normalExcessIntegral E hE hmE (cylinder z (r / 8) ν) ν / (r / 8) ^ 2 ≤
    64 * (normalExcessIntegral E hE hmE (cylinder x r ν) ν / r ^ 2)
  calc
    _ ≤ normalExcessIntegral E hE hmE (cylinder x r ν) ν / (r / 8) ^ 2 := hd
    _ = _ := by ring


end LiquidDrop

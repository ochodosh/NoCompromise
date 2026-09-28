import NoCompromise.DeGiorgi.Blowup
import NoCompromise.DeGiorgi.HalfspacePerimeter
import NoCompromise.Measure.WeakStarBalls

/-!
# Exact perimeter density at every reduced point

Every subsequential rescaled perimeter limit is the boundary-plane area measure.
Its central spheres are null, so compact-test convergence gives convergence of
ball masses. Sequential extraction yields the full positive-radius density limit.
-/

noncomputable section
open MeasureTheory Set Filter Metric
open scoped Topology ENNReal
namespace LiquidDrop

lemma blowupPolarMeasure_real_ball (μ : Measure AmbientSpace) (x : AmbientSpace)
    {r : ℝ} (hr : 0 < r) (R : ℝ) :
    (blowupPolarMeasure μ x r).real (ball (0 : AmbientSpace) R) =
      r⁻¹ ^ 2 * μ.real (ball x (r * R)) := by
  rw [Measure.real, blowupPolarMeasure_apply μ x hr measurableSet_ball,
    image_ball_translate_pos_smul x hr R, ENNReal.toReal_mul,
    ENNReal.toReal_ofReal (sq_nonneg _)]
  rfl

/-- Every positive scale sequence has a subsequence converging on all compact
continuous tests to the actual boundary-plane area of the normal halfspace. -/
theorem exists_subseq_blowupPolarMeasure_tendsto (E : Set AmbientSpace)
    (hE : HasLocallyFinitePerimeter E) (hmE : NullMeasurableSet E volume)
    {x : AmbientSpace} (hx : x ∈ reducedBoundary E hE hmE)
    {r : ℕ → ℝ} (hr : ∀ j, 0 < r j) (ht : Tendsto r atTop (𝓝 0)) :
    ∃ τ : ℕ → ℕ, StrictMono τ ∧
      ∀ φ : CompactlySupportedContinuousMap AmbientSpace ℝ,
        Tendsto (fun j => ∫ y, φ y ∂blowupPolarMeasure
          (canonicalPerimeterMeasure E hE hmE) x (r (τ j))) atTop
          (𝓝 (∫ y, φ y ∂halfspacePlaneMeasure (reducedNormal E hE hmE x))) := by
  obtain ⟨μ, τ, hτ, hμ, hμfin, hpolar, htest⟩ :=
    exists_halfspace_blowup_measure_limit E hE hmE hx hr ht
  let := hμ
  have heq := halfspacePlaneMeasure_eq_of_constantPolar (norm_reducedNormal E hE hmE hx)
    hpolar
  exact ⟨τ, hτ, fun φ => heq ▸ htest φ⟩

/-- The full family of rescaled perimeter measures converges on every compact
continuous test to the area measure on the normal boundary plane. -/
theorem tendsto_integral_blowupPolarMeasure (E : Set AmbientSpace)
    (hE : HasLocallyFinitePerimeter E) (hmE : NullMeasurableSet E volume)
    {x : AmbientSpace} (hx : x ∈ reducedBoundary E hE hmE)
    (φ : CompactlySupportedContinuousMap AmbientSpace ℝ) :
    Tendsto (fun r : ℝ => ∫ y, φ y ∂blowupPolarMeasure
      (canonicalPerimeterMeasure E hE hmE) x r) (𝓝[>] 0)
      (𝓝 (∫ y, φ y ∂halfspacePlaneMeasure (reducedNormal E hE hmE x))) := by
  apply tendsto_nhdsGT_of_positive_sequences_subseq
  intro r hr ht
  obtain ⟨τ, hτ, htest⟩ := exists_subseq_blowupPolarMeasure_tendsto E hE hmE hx hr ht
  exact ⟨τ, htest φ⟩

/-- Rescaled perimeter mass converges to the central planar disk area for every
fixed positive radius, at every reduced point. -/
theorem tendsto_blowupPolarMeasure_real_ball (E : Set AmbientSpace)
    (hE : HasLocallyFinitePerimeter E) (hmE : NullMeasurableSet E volume)
    {x : AmbientSpace} (hx : x ∈ reducedBoundary E hE hmE)
    {R : ℝ} (hR : 0 < R) :
    Tendsto (fun r : ℝ => (blowupPolarMeasure (canonicalPerimeterMeasure E hE hmE) x r).real
      (ball (0 : AmbientSpace) R)) (𝓝[>] 0) (𝓝 (Real.pi * R ^ 2)) := by
  apply tendsto_nhdsGT_of_positive_sequences_subseq
  intro r hr ht
  obtain ⟨τ, hτ, htest⟩ := exists_subseq_blowupPolarMeasure_tendsto E hE hmE hx hr ht
  let μ := canonicalPerimeterMeasure E hE hmE
  let ν := reducedNormal E hE hmE x
  have hν : ‖ν‖ = 1 := norm_reducedNormal E hE hmE hx
  let := (canonicalPerimeterPolar E hE hmE).finiteOnCompacts
  let : ∀ j, IsFiniteMeasureOnCompacts (blowupPolarMeasure μ x (r (τ j))) :=
    fun j => blowupPolarMeasure_finiteOnCompacts μ x (hr (τ j))
  let := halfspacePlaneMeasure_regular hν
  refine ⟨τ, ?_⟩
  have hb := tendsto_real_ball_of_compact_test_convergence
    (fun j => blowupPolarMeasure μ x (r (τ j))) (halfspacePlaneMeasure ν) htest 0 hR
    (halfspacePlaneMeasure_sphere hν R)
  simpa only [Measure.real, halfspacePlaneMeasure_ball hν hR.le,
    ENNReal.toReal_ofReal (mul_nonneg Real.pi_pos.le (sq_nonneg R))] using hb

/-- The unnormalized real perimeter-to-square-radius ratio tends to `π`. -/
theorem tendsto_perimeter_div_radius_sq (E : Set AmbientSpace)
    (hE : HasLocallyFinitePerimeter E) (hmE : NullMeasurableSet E volume)
    {x : AmbientSpace} (hx : x ∈ reducedBoundary E hE hmE) :
    Tendsto (fun r : ℝ => (canonicalPerimeterMeasure E hE hmE).real (ball x r) / r ^ 2)
      (𝓝[>] 0) (𝓝 Real.pi) := by
  have ht := tendsto_blowupPolarMeasure_real_ball E hE hmE hx (R := 1) zero_lt_one
  simp only [one_pow, mul_one] at ht
  apply ht.congr'
  filter_upwards [self_mem_nhdsWithin] with r hr
  rw [blowupPolarMeasure_real_ball _ _ hr, mul_one]
  simp only [div_eq_mul_inv, inv_pow, mul_comm]

/-- Blueprint `thm:exact-density`: the normalized perimeter density equals one
at every point of the reduced boundary. -/
theorem exact_perimeter_density (E : Set AmbientSpace)
    (hE : HasLocallyFinitePerimeter E) (hmE : NullMeasurableSet E volume)
    {x : AmbientSpace} (hx : x ∈ reducedBoundary E hE hmE) :
    Tendsto (fun r : ℝ => (canonicalPerimeterMeasure E hE hmE).real (ball x r) /
      (Real.pi * r ^ 2)) (𝓝[>] 0) (𝓝 (1 : ℝ)) := by
  have ht := (tendsto_perimeter_div_radius_sq E hE hmE hx).div_const Real.pi
  simpa only [div_div, mul_comm (Real.pi), div_self Real.pi_ne_zero] using ht

end LiquidDrop

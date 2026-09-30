module

public import NoCompromise.CapacitaryK.EndpointBoundary
public import NoCompromise.Stationary.GraphCurvature

@[expose] public section

/-!
# The mean curvature in `thm:capacitary-inequalities` is the chart mean curvature of `∂K`

`capacitary_inequalities_boundary_of_C2_extension` states the second inequality with
`H = meanCurv g`, the mean curvature of the level set of the `C²` extension `g` through a
point of `∂K`. At every `p ∈ ∂K` and for every `C²` boundary chart `c` of `int K` at `p`, this is
the intrinsic mean curvature `meanCurvature (frontier K) c.outwardNormal p` of
`Surface/Geometry.lean` (the form in which `cor:EL-pointwise` / `IsStationaryDomain` state
`H + v = λ`): both unit normal fields agree on `∂K` near `p`, and each mean curvature is the
full trace of the derivative of a unit normal field whose normal line is `(T_p ∂K)ᗮ`.
-/

noncomputable section
open Real Set Filter Metric MeasureTheory InnerProductSpace
open scoped Topology Gradient RealInnerProductSpace ENNReal

namespace LiquidDrop.CapacitaryK

/-- For a unit normal field `ν = unitNormal u`, `H = div_Σ ν` is the full trace of `Dν`. -/
lemma meanCurv_eq_trace_fderiv_unitNormal {u : E3 → ℝ} {x : E3}
    (hd : DifferentiableAt ℝ (unitNormal u) x) (hunit : ∀ᶠ z in 𝓝 x, ‖unitNormal u z‖ = 1) :
    meanCurv u x =
      LinearMap.trace ℝ E3 ((fderiv ℝ (unitNormal u) x : E3 →L[ℝ] E3) : E3 →ₗ[ℝ] E3) := by
  have htrace : LinearMap.trace ℝ E3 (fderiv ℝ (unitNormal u) x).toLinearMap =
      ∑ i, secondFF u x (basisVec i) (basisVec i) := by
    rw [LinearMap.trace_eq_sum_inner _ (EuclideanSpace.basisFun (Fin 3) ℝ)]
    apply Finset.sum_congr rfl
    intro i _
    simp only [EuclideanSpace.basisFun_apply, secondFF]
    exact real_inner_comm _ _
  have hνν : secondFF u x (unitNormal u x) (unitNormal u x) = 0 := by
    rw [secondFF, real_inner_comm]
    exact inner_fderiv_self_eq_zero_of_unit hd hunit _
  rw [meanCurv, hνν, sub_zero, ← htrace]

/-- The chart normal of a `C²` boundary chart is differentiable. -/
lemma chart_differentiableAt_outwardNormal_of_contDiff_two (c : C1BoundaryChart)
    (hf : ContDiff ℝ 2 c.height) (p : E3) : DifferentiableAt ℝ c.outwardNormal p := by
  have h1 : ContDiff ℝ 1 (smoothSubgraphNormal c.height) :=
    (contDiff_smoothGraphUnitNormal_two.of_le (by simp)).comp
      ((contDiff_gradient_of_contDiff_two hf).comp (graphProjectionN 2).contDiff)
  have h2 : ContDiff ℝ 1 c.outwardNormal :=
    c.placement.linearIsometryEquiv.contDiff.comp
      (h1.comp c.placement.symm.toAffineIsometry.toContinuousAffineMap.contDiff)
  exact h2.differentiable one_ne_zero p

/-- At `p ∈ ∂K`, the level-set mean curvature of the extension `g` equals the intrinsic mean
curvature of `∂K` for the outward normal of any `C²` chart of `int K` at `p`. -/
theorem meanCurv_extension_eq_meanCurvature_chart {K : Set E3} (hK : IsCompact K)
    (hreg : K = closure (interior K)) (hC1 : HasC1Boundary (interior K))
    {g : E3 → ℝ} (hg : ContDiff ℝ 2 g)
    (hbd : ∀ q ∈ frontier K,
      gradient g q = -‖gradient g q‖ • hC1.outwardNormal q ∧ 0 < ‖gradient g q‖)
    {p : E3} (hp : p ∈ frontier K) {c : C1BoundaryChart} (hc : c.IsChartFor (interior K))
    (hpc : p ∈ c.region) (hc2 : ContDiff ℝ 2 c.height) :
    meanCurv g p = meanCurvature (frontier K) c.outwardNormal p := by
  have hfr : frontier (interior K) = frontier K := capacity_frontier_interior hK hreg
  have hpi : p ∈ frontier (interior K) := by rwa [hfr]
  have hν : ∀ q ∈ frontier K, unitNormal g q = hC1.outwardNormal q := by
    intro q hq
    obtain ⟨hgq, hpos⟩ := hbd q hq
    rw [unitNormal, hgq]
    change -((‖gradient g q‖)⁻¹ • (-‖gradient g q‖ • hC1.outwardNormal q)) = _
    rw [smul_smul, mul_neg, inv_mul_cancel₀ hpos.ne', neg_smul, one_smul, neg_neg]
  have hνp : unitNormal g p = c.outwardNormal p := by
    rw [hν p hp, hC1.outwardNormal_eq_chart hc hpi hpc]
  have hG : Continuous (gradient g) :=
    (contDiff_gradient_of_contDiff_succ (r := 1) hg).continuous
  have hne : ∀ᶠ z in 𝓝 p, gradient g z ≠ 0 :=
    hG.continuousAt.eventually_ne (norm_pos_iff.mp (hbd p hp).2)
  have hunit : ∀ᶠ z in 𝓝 p, ‖unitNormal g z‖ = 1 := by
    filter_upwards [hne] with z hz
    have hw : 0 < gradNorm g z := norm_pos_iff.mpr hz
    rw [unitNormal, norm_neg, norm_smul, norm_inv, Real.norm_eq_abs,
      abs_of_nonneg (gradNorm_nonneg g z)]
    exact inv_mul_cancel₀ hw.ne'
  have hw : 0 < gradNorm g p := (hbd p hp).2
  have hd : DifferentiableAt ℝ (unitNormal g) p :=
    (((differentiableAt_gradNorm hg.contDiffAt hw).inv hw.ne').smul
      (differentiableAt_gradient_of_contDiffAt hg.contDiffAt)).neg
  have hcd := chart_differentiableAt_outwardNormal_of_contDiff_two c hc2 p
  have hT : tangentPlane (frontier K) p = (ℝ ∙ unitNormal g p)ᗮ := by
    rw [hνp, ← hfr]
    exact hc.tangentPlane_frontier_eq hc2 hpi hpc
  have heq : unitNormal g =ᶠ[𝓝[frontier K] p] c.outwardNormal := by
    filter_upwards [self_mem_nhdsWithin,
      mem_nhdsWithin_of_mem_nhds (c.isOpen_region.mem_nhds hpc)] with z hz hzr
    rw [hν z hz, hC1.outwardNormal_eq_chart hc (by rwa [hfr]) hzr]
  rw [meanCurv_eq_trace_fderiv_unitNormal hd hunit,
    ← meanCurvature_eq_trace_fderiv hT hd hunit]
  unfold meanCurvature
  rw [tangentShapeOperator_congr hd hcd heq]

/-- `thm:capacitary-inequalities` (`eq:capacitary-inequalities`) with `H` the intrinsic mean
curvature of `∂K` in the charts of `int K` (the form of `cor:EL-pointwise`), modulo only
`thm:total-curvature-bound` and the `C²` extension `g` of `u` across `∂K`:
`∫_{∂K} |∇u|² ≥ 4π` and `∫_{∂K} H|∇u| ≥ 4 ∫_{∂K} |∇u|² - 8π`, where `|∇u| = |∇g|` on `∂K`. -/
theorem capacitary_inequalities_boundary_chart_of_C2_extension
    {K : Set E3} (hK : IsCompact K) (hKconn : IsConnected K) (hcompl : IsPreconnected Kᶜ)
    (hreg : K = closure (interior K)) (hC1 : HasC1Boundary (interior K))
    (hC2 : HasC2Boundary (interior K))
    {R₀ : ℝ} (hR₀ : 0 < R₀) (hKR : K ⊆ closedBall 0 R₀)
    (hzero : (0 : E3) ∈ interior K)
    {u : E3 → ℝ} (hu : Continuous u)
    (hh : HasDistributionalLaplacianOn u (fun _ => 0) Kᶜ)
    (hb : ∀ x ∈ K, u x = 1) (hinf : Tendsto u (cocompact E3) (𝓝 0))
    {g : E3 → ℝ} (hg : ContDiff ℝ 2 g) (hug : EqOn u g (closure Kᶜ))
    {μ : Measure E3} (hμU : μ Kᶜᶜ = 0)
    (hμK : ∀ L : Set E3, IsCompact L → L ⊆ Kᶜ → μ L < ⊤)
    (hμ : ∀ φ : E3 → ℝ, ContDiff ℝ (⊤ : ℕ∞) φ → HasCompactSupport φ → tsupport φ ⊆ Kᶜ →
        ∫ x, gradNorm u x * laplacianN φ x = ∫ x, φ x ∂μ)
    (h_of_total_curvature_bound : ∀ (S : Set E3) (n : E3 → E3), IsCompact S → IsConnected S →
      IsSmoothEmbeddedSurface S → IsUnitNormalField S n →
      ∫ x in S, gaussCurvature S n x ∂(Measure.euclideanHausdorffMeasure 2) ≤ 4 * Real.pi)
    {t₀ : ℝ} (ht₀ : t₀ ∈ Ioo (0 : ℝ) 1)
    (ht₀R : ∀ x ∈ Kᶜ, u x = t₀ → gradient u x ≠ 0)
    {H : E3 → ℝ} (hH : ∀ p ∈ frontier K, ∀ c : C1BoundaryChart, c.IsChartFor (interior K) →
      p ∈ c.region → ContDiff ℝ 2 c.height → H p = meanCurvature (frontier K) c.outwardNormal p) :
    4 * π ≤ ∫ x in frontier K, ‖gradient g x‖ ^ 2 ∂hausdorffMeasure2 3 ∧
      4 * (∫ x in frontier K, ‖gradient g x‖ ^ 2 ∂hausdorffMeasure2 3) - 8 * π ≤
        ∫ x in frontier K, H x * ‖gradient g x‖ ∂hausdorffMeasure2 3 := by
  have h := capacitary_inequalities_boundary_of_C2_extension hK hKconn hcompl hreg hC1 hC2 hR₀
    hKR hzero hu hh hb hinf hg hug hμU hμK hμ h_of_total_curvature_bound ht₀ ht₀R
  have hbd := gradient_eq_neg_norm_smul_normal hK hreg hC1 hR₀ hKR hzero hu hh hb hinf hg hug
    hC2 hcompl
  have hint : (∫ x in frontier K, meanCurv g x * gradNorm g x ∂hausdorffMeasure2 3) =
      ∫ x in frontier K, H x * ‖gradient g x‖ ∂hausdorffMeasure2 3 := by
    refine setIntegral_congr_fun isClosed_frontier.measurableSet fun x hx => ?_
    have hxi : x ∈ frontier (interior K) := by rwa [capacity_frontier_interior hK hreg]
    obtain ⟨c, hc, hxc, hc2⟩ := hC2 x hxi
    change meanCurv g x * gradNorm g x = H x * gradNorm g x
    rw [hH x hx c hc hxc hc2,
      meanCurv_extension_eq_meanCurvature_chart hK hreg hC1 hg hbd hx hc hxc hc2]
  rw [hint] at h
  exact h

end LiquidDrop.CapacitaryK

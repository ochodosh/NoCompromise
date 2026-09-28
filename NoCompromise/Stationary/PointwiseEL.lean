import NoCompromise.Stationary.GraphCurvature
import NoCompromise.Stationary.Connected
import NoCompromise.Stationary.ScalingIdentity
import NoCompromise.Energy.PotentialHolder
import Mathlib.Analysis.Distribution.AEEqOfIntegralContDiff
import Mathlib.Analysis.Calculus.LineDeriv.IntegrationByParts

/-!
# The pointwise Euler--Lagrange equation in a `C²` chart

Blueprint `cor:EL-pointwise`: in every boundary chart whose height is `C²`, the
weak graph equation of `lem:graph-PMC` expands pointwise to `H + v_Ω = λ`, with
`H` the mean curvature for the outward normal (`conv:curvature`).
-/

noncomputable section
open Set Filter InnerProductSpace MeasureTheory Metric
open scoped Topology Gradient RealInnerProductSpace ContDiff
namespace LiquidDrop
set_option maxSynthPendingDepth 8

local notation "E2" => EuclideanSpace ℝ (Fin 2)

/-- Integration by parts for the divergence of a `C¹` planar field. -/
theorem integral_inner_gradient_eq_neg_trace {F : E2 → E2} (hF : ContDiff ℝ 1 F)
    {ζ : E2 → ℝ} (hζ : ContDiff ℝ 1 ζ) (hcζ : HasCompactSupport ζ) :
    (∫ y, inner ℝ (F y) (gradient ζ y)) =
      -∫ y, LinearMap.trace ℝ E2 ((fderiv ℝ F y : E2 →L[ℝ] E2) : E2 →ₗ[ℝ] E2) * ζ y := by
  let b := EuclideanSpace.basisFun (Fin 2) ℝ
  have hFi (i : Fin 2) : ContDiff ℝ 1 (fun y => inner ℝ (F y) (b i)) :=
    hF.inner ℝ contDiff_const
  have hdFi (i : Fin 2) (y : E2) :
      fderiv ℝ (fun y => inner ℝ (F y) (b i)) y (b i) =
        inner ℝ (b i) (fderiv ℝ F y (b i)) := by
    have hd := ((hF.differentiable one_ne_zero y).hasFDerivAt).inner ℝ
      (hasFDerivAt_const (b i) y)
    rw [hd.fderiv]
    simp [real_inner_comm]
  have hcont_dζ : Continuous (fun y => fderiv ℝ ζ y) := hζ.continuous_fderiv one_ne_zero
  have hcont_dF : Continuous (fun y => fderiv ℝ F y) := hF.continuous_fderiv one_ne_zero
  have hterm (i : Fin 2) :
      (∫ y, inner ℝ (F y) (b i) * fderiv ℝ ζ y (b i)) =
        -∫ y, inner ℝ (b i) (fderiv ℝ F y (b i)) * ζ y := by
    have hcd : HasCompactSupport (fun y => fderiv ℝ ζ y (b i)) := hcζ.fderiv_apply ℝ (b i)
    have h1 : Integrable (fun y => fderiv ℝ (fun y => inner ℝ (F y) (b i)) y (b i) * ζ y) := by
      simp_rw [hdFi]
      exact ((continuous_const.inner ((hcont_dF.clm_apply continuous_const))).mul
        hζ.continuous).integrable_of_hasCompactSupport hcζ.mul_left
    have h2 : Integrable (fun y => inner ℝ (F y) (b i) * fderiv ℝ ζ y (b i)) :=
      (((hFi i).continuous).mul (hcont_dζ.clm_apply continuous_const)
        ).integrable_of_hasCompactSupport hcd.mul_left
    have h3 : Integrable (fun y => inner ℝ (F y) (b i) * ζ y) :=
      ((hFi i).continuous.mul hζ.continuous).integrable_of_hasCompactSupport hcζ.mul_left
    have := integral_mul_fderiv_eq_neg_fderiv_mul_of_integrable h1 h2 h3
      (fun y _ => (hFi i).differentiable one_ne_zero y)
      (fun y _ => hζ.differentiable one_ne_zero y)
    simpa only [hdFi] using this
  have hsplit : (fun y => inner ℝ (F y) (gradient ζ y)) =
      fun y => ∑ i, inner ℝ (F y) (b i) * fderiv ℝ ζ y (b i) := by
    funext y
    rw [← b.sum_inner_mul_inner (F y) (gradient ζ y)]
    congr 1
    funext i
    rw [real_inner_comm (gradient ζ y) (b i), inner_gradient_left]
  have htr : (fun y => LinearMap.trace ℝ E2 ((fderiv ℝ F y : E2 →L[ℝ] E2) : E2 →ₗ[ℝ] E2) * ζ y) =
      fun y => ∑ i, inner ℝ (b i) (fderiv ℝ F y (b i)) * ζ y := by
    funext y
    rw [LinearMap.trace_eq_sum_inner _ b, Finset.sum_mul]
    rfl
  rw [hsplit, htr, integral_finsetSum, integral_finsetSum, ← Finset.sum_neg_distrib]
  · exact Finset.sum_congr rfl fun i _ => hterm i
  · intro i _
    exact ((continuous_const.inner ((hcont_dF.clm_apply continuous_const))).mul
        hζ.continuous).integrable_of_hasCompactSupport hcζ.mul_left
  · intro i _
    exact ((hFi i).continuous.mul (hcont_dζ.clm_apply continuous_const)
      ).integrable_of_hasCompactSupport (hcζ.fderiv_apply ℝ (b i)).mul_left

/-- Blueprint `cor:EL-pointwise`, in every `C²` boundary chart: the weak graph
equation of `lem:graph-PMC` holds pointwise as `H + v_Ω = λ`, where `H` is the
mean curvature of `∂Ω` for the outward normal (`conv:curvature`). -/
theorem MinimizerRep.eulerLagrange_pointwise {V : ℝ} {Ω : Set AmbientSpace}
    (h : MinimizerRep V Ω) {c : C1BoundaryChart} (hc : c.IsChartFor Ω)
    (hf : ContDiff ℝ 2 c.height) {p : AmbientSpace} (hp : p ∈ frontier Ω)
    (hpc : p ∈ c.region) :
    meanCurvature (frontier Ω) c.outwardNormal p + (coulombPotential Ω p).toReal =
      minimizerMultiplier V Ω := by
  obtain ⟨y1, hy1⟩ : ∃ y, c.placement (graphMapN c.height y) = p := by
    have hmem : p ∈ c.graphSurface ∩ c.region := by
      rw [← hc.frontier_inter_eq]
      exact ⟨hp, hpc⟩
    obtain ⟨⟨w, ⟨y, hy⟩, hw⟩, _⟩ := hmem
    exact ⟨y, by rw [hy]; exact hw⟩
  have hy0 : graphProjectionN 2 (c.placement.symm p) = y1 := by
    rw [← hy1, c.placement.symm_apply_apply]
    change graphProjectionN 2 (graphAppendN y1 (c.height y1)) = y1
    simp
  have hH := hc.meanCurvature_eq_neg_div hf hp hpc
  rw [hy0] at hH
  -- the slab around the chart point
  let Φ : E2 × ℝ → AmbientSpace := fun q =>
    c.placement (graphBaseN 2 q.1 + q.2 • EuclideanSpace.single (Fin.last 2) (1 : ℝ))
  have hΦ : Continuous Φ :=
    c.placement.continuous.comp (((graphBaseN 2).continuous.comp continuous_fst).add
      (continuous_snd.smul continuous_const))
  have hΦp : Φ (y1, c.height y1) = p := hy1
  obtain ⟨ε, hε, hball⟩ := Metric.isOpen_iff.mp (c.isOpen_region.preimage hΦ) (y1, c.height y1)
    (by change Φ (y1, c.height y1) ∈ c.region; rw [hΦp]; exact hpc)
  obtain ⟨r, hr, hfr⟩ := Metric.continuousAt_iff.mp
    (c.height_contDiff.continuous.continuousAt (x := y1)) (ε / 2) (half_pos hε)
  set U : Set E2 := ball y1 (min r ε)
  have hU : IsOpen U := isOpen_ball
  have hy1U : y1 ∈ U := mem_ball_self (lt_min hr hε)
  have hslab : ∀ ζ : E2 → ℝ, tsupport ζ ⊆ U → ∀ y ∈ tsupport ζ, ∀ t : ℝ,
      |t - c.height y| ≤ ε / 2 →
      c.placement (graphBaseN 2 y + t • EuclideanSpace.single (Fin.last 2) 1) ∈ c.region := by
    intro ζ hζU y hy t ht
    have hyU := hζU hy
    have hyr : dist y y1 < r := lt_of_lt_of_le hyU (min_le_left _ _)
    have hyε : dist y y1 < ε := lt_of_lt_of_le hyU (min_le_right _ _)
    have hfy := hfr hyr
    rw [Real.dist_eq] at hfy
    have htε : dist t (c.height y1) < ε := by
      rw [Real.dist_eq]
      calc |t - c.height y1| ≤ |t - c.height y| + |c.height y - c.height y1| := abs_sub_le _ _ _
        _ < ε / 2 + ε / 2 := by linarith
        _ = ε := by ring
    have hmem : (y, t) ∈ ball (y1, c.height y1) ε := by
      rw [mem_ball, Prod.dist_eq]
      exact max_lt hyε htε
    have hΦmem : Φ (y, t) ∈ c.region := hball hmem
    exact hΦmem
  -- the flux and the forcing
  let F := graphFlux c.height
  have hF : ContDiff ℝ 1 F :=
    (contDiff_graphFluxMap.of_le (by simp)).comp (contDiff_gradient_of_contDiff_two hf)
  let b := EuclideanSpace.basisFun (Fin 2) ℝ
  have hcont_dF : Continuous (fun y => fderiv ℝ F y) := hF.continuous_fderiv one_ne_zero
  have htr : (fun y => LinearMap.trace ℝ E2 ((fderiv ℝ F y : E2 →L[ℝ] E2) : E2 →ₗ[ℝ] E2)) =
      fun y => ∑ i, inner ℝ (b i) (fderiv ℝ F y (b i)) := by
    funext y
    rw [LinearMap.trace_eq_sum_inner _ b]
    rfl
  have htrc : Continuous
      (fun y => LinearMap.trace ℝ E2 ((fderiv ℝ F y : E2 →L[ℝ] E2) : E2 →ₗ[ℝ] E2)) := by
    rw [htr]
    exact continuous_finsetSum _ fun i _ =>
      continuous_const.inner (hcont_dF.clm_apply continuous_const)
  have hvc : Continuous (fun x => (coulombPotential Ω x).toReal) :=
    (coulombPotential_contDiff_one_and_holder (β := 1 / 2) (by norm_num) (by norm_num)
      h.bounded).1.continuous
  have hgc : Continuous (graphMapN c.height) :=
    (graphBaseN 2).continuous.add
      (c.height_contDiff.continuous.smul continuous_const)
  let G : E2 → ℝ := fun y =>
    minimizerMultiplier V Ω - (coulombPotential Ω (c.placement (graphMapN c.height y))).toReal
  have hGc : Continuous G := continuous_const.sub (hvc.comp (c.placement.continuous.comp hgc))
  let k : E2 → ℝ := fun y =>
    LinearMap.trace ℝ E2 ((fderiv ℝ F y : E2 →L[ℝ] E2) : E2 →ₗ[ℝ] E2) + G y
  have hkc : Continuous k := htrc.add hGc
  have hk : ∀ᵐ y ∂(volume : Measure E2), y ∈ U → k y = 0 := by
    apply hU.ae_eq_zero_of_integral_contDiff_smul_eq_zero
      (hkc.locallyIntegrable.locallyIntegrableOn U)
    intro ζ hζ hcζ hζU
    have hw := h.graph_prescribed_mean_curvature c hc hζ hcζ (half_pos hε) (hslab ζ hζU)
    have hibp := integral_inner_gradient_eq_neg_trace hF (hζ.of_le (by simp)) hcζ
    have hlhs : (fun y => inner ℝ (gradient c.height y) (gradient ζ y) /
        Real.sqrt (1 + ‖gradient c.height y‖ ^ 2)) = fun y => inner ℝ (F y) (gradient ζ y) := by
      funext y
      simp only [F, graphFlux, graphFluxMap, real_inner_smul_left]
      rw [div_eq_inv_mul]
    rw [hlhs, hibp] at hw
    have hi1 : Integrable (fun y =>
        LinearMap.trace ℝ E2 ((fderiv ℝ F y : E2 →L[ℝ] E2) : E2 →ₗ[ℝ] E2) * ζ y) :=
      (htrc.mul hζ.continuous).integrable_of_hasCompactSupport hcζ.mul_left
    have hi2 : Integrable (fun y => G y * ζ y) :=
      (hGc.mul hζ.continuous).integrable_of_hasCompactSupport hcζ.mul_left
    have hsum : (fun y => ζ y • k y) = fun y =>
        LinearMap.trace ℝ E2 ((fderiv ℝ F y : E2 →L[ℝ] E2) : E2 →ₗ[ℝ] E2) * ζ y +
          G y * ζ y := by
      funext y
      simp only [k, smul_eq_mul]
      ring
    rw [hsum, integral_add hi1 hi2]
    change -(∫ y, LinearMap.trace ℝ E2 ((fderiv ℝ F y : E2 →L[ℝ] E2) : E2 →ₗ[ℝ] E2) * ζ y) =
      ∫ y, G y * ζ y at hw
    linarith
  have hkU : EqOn k 0 U := by
    apply Measure.eqOn_open_of_ae_eq (μ := volume) _ hU hkc.continuousOn continuousOn_const
    rw [EventuallyEq, ae_restrict_iff' measurableSet_ball]
    exact hk
  have hk1 := hkU hy1U
  simp only [k, G, Pi.zero_apply, hy1] at hk1
  change meanCurvature (frontier Ω) c.outwardNormal p = -LinearMap.trace ℝ E2
    ((fderiv ℝ F y1 : E2 →L[ℝ] E2) : E2 →ₗ[ℝ] E2) at hH
  linarith

/-- Reduction of blueprint `cor:minimizer-stationary` to the `C³` boundary
regularity of `prop:bootstrap-C3`: a minimiser representative with `C³` boundary
is a stationary domain with multiplier `minimizerMultiplier V Ω`. -/
theorem MinimizerRep.isStationaryDomain_of_hasCkBoundary {V : ℝ} {Ω : Set AmbientSpace}
    (h : MinimizerRep V Ω) (hC3 : HasCkBoundary 3 Ω) :
    IsStationaryDomain V (minimizerMultiplier V Ω) Ω where
  isOpen := h.isOpen
  isConnected := h.isConnected
  isBounded := h.bounded
  volume_eq := h.volume_eq
  boundary_C3 := hC3
  eulerLagrange := fun _ hp _ hc hpc hf => h.eulerLagrange_pointwise hc hf hp hpc

/-- Blueprint `cor:minimizer-stationary`, conditional on the `C³` boundary of
`prop:bootstrap-C3`: the representative is a stationary domain and its
multiplier satisfies the scaling identity `eq:scaling-identity`. -/
theorem MinimizerRep.stationary_and_scaling_of_hasCkBoundary {V : ℝ}
    {Ω : Set AmbientSpace} (h : MinimizerRep V Ω) (hC3 : HasCkBoundary 3 Ω) :
    IsStationaryDomain V (minimizerMultiplier V Ω) Ω ∧
      3 * V * minimizerMultiplier V Ω =
        2 * (perimeter Ω).toReal + 5 * (coulombEnergy Ω).toReal ∧
      3 * V * minimizerMultiplier V Ω =
        5 * (energy Ω).toReal - 3 * (perimeter Ω).toReal :=
  ⟨h.isStationaryDomain_of_hasCkBoundary hC3,
    scaling_identity_minimizerMultiplier h.volume_pos h.minimizer h.bounded
      h.hasLocallyFinitePerimeter⟩

end LiquidDrop

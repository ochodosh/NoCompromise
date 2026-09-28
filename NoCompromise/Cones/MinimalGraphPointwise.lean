import NoCompromise.Stationary.BootstrapC2
import NoCompromise.Stationary.PointwiseEL

/-! The classical minimal-surface equation for a locally `C²` weak solution. -/

noncomputable section
open Set Filter InnerProductSpace MeasureTheory Metric
open scoped Topology Gradient RealInnerProductSpace ContDiff

namespace LiquidDrop

local notation "E2" => EuclideanSpace ℝ (Fin 2)

/-- A `C²` weak minimal graph has pointwise zero divergence of its flux. -/
theorem minimal_graph_pointwise_of_weak {U : Set (EuclideanSpace ℝ (Fin 2))} (hU : IsOpen U)
    {f : EuclideanSpace ℝ (Fin 2) → ℝ} (hf : ContDiffOn ℝ 2 f U)
    (he : ∀ φ : EuclideanSpace ℝ (Fin 2) → ℝ, ContDiff ℝ 1 φ → HasCompactSupport φ →
      tsupport φ ⊆ U →
      ∫ y, inner ℝ (gradient f y) (gradient φ y) / Real.sqrt (1 + ‖gradient f y‖ ^ 2) = 0) :
    ∀ x ∈ U, LinearMap.trace ℝ (EuclideanSpace ℝ (Fin 2))
      ((fderiv ℝ (fun y => mcFlux (gradient f y)) x :
        EuclideanSpace ℝ (Fin 2) →L[ℝ] EuclideanSpace ℝ (Fin 2)) :
        EuclideanSpace ℝ (Fin 2) →ₗ[ℝ] EuclideanSpace ℝ (Fin 2)) = 0 := by
  intro x hx
  have hg : ContDiffOn ℝ 1 (gradient f) U :=
    (toDual ℝ E2).symm.contDiff.comp_contDiffOn
      (hf.fderiv_of_isOpen hU (by norm_num))
  have hflux : ContDiffOn ℝ 1 (fun y => mcFlux (gradient f y)) U :=
    (contDiff_mcFlux.of_le (by simp)).comp_contDiffOn hg
  obtain ⟨r, hr, hrU⟩ := Metric.nhds_basis_closedBall.mem_iff.mp (hU.mem_nhds hx)
  let χ : ContDiffBump x :=
    { rIn := r / 2
      rOut := r
      rIn_pos := half_pos hr
      rIn_lt_rOut := half_lt_self hr }
  let F : E2 → E2 := fun y => χ y • mcFlux (gradient f y)
  have hχU : tsupport χ ⊆ U := by
    rw [χ.tsupport_eq]
    exact hrU
  have hF : ContDiff ℝ 1 F := by
    rw [contDiff_iff_contDiffAt]
    intro y
    by_cases hy : y ∈ tsupport χ
    · exact χ.contDiffAt.smul (hflux.contDiffAt (hU.mem_nhds (hχU hy)))
    · apply (contDiffAt_const (c := (0 : E2))).congr_of_eventuallyEq
      filter_upwards [notMem_tsupport_iff_eventuallyEq.mp hy] with z hz
      simp [F, hz]
  have hFeq {y : E2} (hy : y ∈ ball x (r / 2)) :
      F =ᶠ[𝓝 y] (fun z => mcFlux (gradient f z)) := by
    filter_upwards [χ.eventuallyEq_one_of_mem_ball hy] with z hz
    simp [F, hz]
  let t : E2 → ℝ := fun y =>
    LinearMap.trace ℝ E2 ((fderiv ℝ F y : E2 →L[ℝ] E2) : E2 →ₗ[ℝ] E2)
  have htc : Continuous t := by
    have hd := hF.continuous_fderiv one_ne_zero
    have ht : t = fun y => ∑ i, inner ℝ ((EuclideanSpace.basisFun (Fin 2) ℝ) i)
        (fderiv ℝ F y ((EuclideanSpace.basisFun (Fin 2) ℝ) i)) := by
      funext y
      exact LinearMap.trace_eq_sum_inner _ (EuclideanSpace.basisFun (Fin 2) ℝ)
    rw [ht]
    exact continuous_finsetSum _ fun i _ =>
      continuous_const.inner (hd.clm_apply continuous_const)
  have hballU : ball x (r / 2) ⊆ U :=
    (ball_subset_closedBall.trans (closedBall_subset_closedBall (half_le_self hr.le))).trans hrU
  have htzero : ∀ᵐ y ∂(volume : Measure E2), y ∈ ball x (r / 2) → t y = 0 := by
    apply isOpen_ball.ae_eq_zero_of_integral_contDiff_smul_eq_zero
      (htc.locallyIntegrable.locallyIntegrableOn (ball x (r / 2)))
    intro φ hφ hcφ hφball
    have hw := he φ (hφ.of_le (by simp)) hcφ (hφball.trans hballU)
    have hi : (fun y => inner ℝ (gradient f y) (gradient φ y) /
        Real.sqrt (1 + ‖gradient f y‖ ^ 2)) =
        fun y => inner ℝ (F y) (gradient φ y) := by
      funext y
      by_cases hy : y ∈ tsupport φ
      · rw [(hFeq (hφball hy)).self_of_nhds]
        simp only [mcFlux, real_inner_smul_left]
        exact div_eq_inv_mul _ _
      · have hz : gradient φ y = 0 := by
          rw [gradient, fderiv_of_notMem_tsupport ℝ hy, map_zero]
        simp [hz]
    rw [hi, integral_inner_gradient_eq_neg_trace hF (hφ.of_le (by simp)) hcφ] at hw
    simpa only [smul_eq_mul, mul_comm, neg_eq_zero] using hw
  have htOn : EqOn t 0 (ball x (r / 2)) := by
    apply Measure.eqOn_open_of_ae_eq (μ := volume) _ isOpen_ball
      htc.continuousOn continuousOn_const
    rw [EventuallyEq, ae_restrict_iff' measurableSet_ball]
    exact htzero
  have hxball : x ∈ ball x (r / 2) := mem_ball_self (half_pos hr)
  have hxzero := htOn hxball
  change LinearMap.trace ℝ E2 ((fderiv ℝ F x : E2 →L[ℝ] E2) : E2 →ₗ[ℝ] E2) = 0 at hxzero
  rwa [(hFeq hxball).fderiv_eq] at hxzero

end LiquidDrop

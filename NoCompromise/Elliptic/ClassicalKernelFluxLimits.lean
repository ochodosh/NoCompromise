module

public import NoCompromise.Elliptic.ClassicalKernelW11
public import NoCompromise.Elliptic.ClassicalBoundaryMeasure

@[expose] public section

/-! # Actual volume and boundary limits for the reciprocal-kernel flux -/

noncomputable section
open MeasureTheory Set Filter Metric InnerProductSpace
open scoped ENNReal Topology Gradient
namespace LiquidDrop
set_option maxSynthPendingDepth 8

lemma regularizedNewtonKernel_le_inv_norm {ε : ℝ} (hε : 0 < ε)
    {z : AmbientSpace} (hz : z ≠ 0) : ‖regularizedNewtonKernel ε z‖ ≤ ‖z‖⁻¹ := by
  have hs := regularizedNewton_sqrt_bounds hε z
  rw [regularizedNewtonKernel, Real.norm_eq_abs, abs_of_pos (inv_pos.mpr hs.1)]
  exact inv_anti₀ (norm_pos_iff.mpr hz) hs.2.1

lemma tendsto_gradient_regularizedNewtonKernel_sub {ε : ℕ → ℝ}
    (hε : Tendsto ε atTop (𝓝 0)) (hp : ∀ j, 0 < ε j) (x y : AmbientSpace) :
    Tendsto (fun j => gradient (fun z => regularizedNewtonKernel (ε j) (z - y)) x)
      atTop (𝓝 (classicalNewtonGradient (x - y))) := by
  have h := ((toDual ℝ AmbientSpace).symm.continuous.tendsto
    (newtonDerivativeKernel (x - y))).comp (tendsto_regularizedNewtonDerivative hε (x - y))
  have he : (toDual ℝ AmbientSpace).symm (newtonDerivativeKernel (x - y)) =
      classicalNewtonGradient (x - y) := by
    rw [← toDual_classicalNewtonGradient, LinearIsometryEquiv.symm_apply_apply]
  simpa only [gradient_regularizedNewtonKernel_sub (hp _), he, Function.comp_def] using h

theorem tendsto_integral_regularized_newton_divergence {D : Set AmbientSpace}
    (hD : volume D < ∞) {X : AmbientSpace → AmbientSpace}
    (hX : ContDiff ℝ 1 X) (hcX : HasCompactSupport X)
    {ε : ℕ → ℝ} (hε : Tendsto ε atTop (𝓝 0)) (hp : ∀ j, 0 < ε j)
    (y : AmbientSpace) :
    Tendsto (fun j => ∫ x in D,
      regularizedNewtonKernel (ε j) (x - y) * divergenceN X x +
        inner ℝ (gradient (fun z => regularizedNewtonKernel (ε j) (z - y)) x) (X x))
      atTop (𝓝 (∫ x in D, ‖x - y‖⁻¹ * divergenceN X x +
        inner ℝ (classicalNewtonGradient (x - y)) (X x))) := by
  obtain ⟨B, hB⟩ := hcX.exists_bound_of_continuous hX.continuous
  have hsdiv : tsupport (divergenceN X) ⊆ tsupport X := by
    apply closure_minimal _ (isClosed_tsupport X)
    intro x hx
    by_contra hnot
    exact hx (divergenceN_eq_zero_of_notMem_tsupport hnot)
  have hcdiv : HasCompactSupport (divergenceN X) :=
    hcX.of_isClosed_subset (isClosed_tsupport _) hsdiv
  obtain ⟨A, hA⟩ := hcdiv.exists_bound_of_continuous (continuous_divergenceN hX)
  have hu : IntegrableOn (fun x => ‖x - y‖⁻¹) D := by
    simpa only [norm_sub_rev] using integrableOn_coulombKernel D hD y
  have hq : IntegrableOn (fun x => (‖x - y‖ ^ 2)⁻¹) D := by
    simpa only [norm_sub_rev] using integrableOn_inv_norm_sub_sq D hD y
  have hne : ∀ᵐ x ∂volume.restrict D, x - y ≠ 0 := by
    have h : ∀ᵐ x : AmbientSpace ∂volume, x ≠ y := by simp [ae_iff]
    exact (ae_restrict_of_ae h).mono fun _ hx => sub_ne_zero.mpr hx
  apply tendsto_integral_of_dominated_convergence
    (fun x => ‖x - y‖⁻¹ * A + (‖x - y‖ ^ 2)⁻¹ * B)
  · intro j
    have hc : ContDiff ℝ 1 (fun z : AmbientSpace => regularizedNewtonKernel (ε j) (z - y)) :=
      ((contDiff_regularizedNewtonKernel (hp j)).of_le (by simp)).comp
        (contDiff_id.sub contDiff_const)
    exact ((hc.continuous.mul (continuous_divergenceN hX)).add
      ((continuous_gradient_of_contDiff hc).inner hX.continuous)).aestronglyMeasurable
  · exact (hu.mul_const A).add (hq.mul_const B)
  · intro j
    filter_upwards [hne] with x hx
    apply (norm_add_le _ _).trans
    apply add_le_add
    · rw [norm_mul]
      exact mul_le_mul (regularizedNewtonKernel_le_inv_norm (hp j) hx) (hA x)
        (norm_nonneg _) (inv_nonneg.mpr (norm_nonneg _))
    · apply (norm_inner_le_norm _ _).trans
      have hg : ‖gradient (fun z => regularizedNewtonKernel (ε j) (z - y)) x‖ ≤
          (‖x - y‖ ^ 2)⁻¹ := by
        rw [gradient_regularizedNewtonKernel_sub (hp j), LinearIsometryEquiv.norm_map]
        exact (norm_regularizedNewtonDerivative_le (hp j) (x - y)).2
      exact mul_le_mul hg (hB x) (norm_nonneg _) (inv_nonneg.mpr (sq_nonneg _))
  · filter_upwards [hne] with x hx
    exact ((tendsto_regularizedNewtonKernel hε hx).mul_const _).add
      ((tendsto_gradient_regularizedNewtonKernel_sub hε hp x y).inner tendsto_const_nhds)

theorem tendsto_integral_regularized_newton_boundary {D : Set AmbientSpace}
    (hD : IsOpen D) (hbD : Bornology.IsBounded D) (hC1 : HasC1Boundary D)
    {X : AmbientSpace → AmbientSpace} (hX : Continuous X) (hcX : HasCompactSupport X)
    {ε : ℕ → ℝ} (hε : Tendsto ε atTop (𝓝 0)) (hp : ∀ j, 0 < ε j)
    {y : AmbientSpace} (hy : y ∈ D) :
    Tendsto (fun j => ∫ x, regularizedNewtonKernel (ε j) (x - y) *
      inner ℝ (X x) (hC1.outwardNormal x) ∂(hausdorffMeasure2 3).restrict (frontier D))
      atTop (𝓝 (∫ x, ‖x - y‖⁻¹ * inner ℝ (X x) (hC1.outwardNormal x)
        ∂(hausdorffMeasure2 3).restrict (frontier D))) := by
  let μ := (hausdorffMeasure2 3).restrict (frontier D)
  let : IsFiniteMeasure μ := finite_boundary_area hD hbD hC1
  obtain ⟨δ, hδ, hd⟩ := exists_pos_boundary_distance hD hy
  obtain ⟨B, hB⟩ := hcX.exists_bound_of_continuous hX
  have hn := hC1.aestronglyMeasurable_outwardNormal μ
  apply tendsto_integral_of_dominated_convergence (fun _ => δ⁻¹ * B)
  · intro j
    exact (((continuous_regularizedNewtonKernel (hp j)).comp
      (continuous_id.sub continuous_const)).aestronglyMeasurable).mul
        (hX.aestronglyMeasurable.inner hn)
  · exact integrable_const _
  · intro j
    filter_upwards [ae_restrict_mem isClosed_frontier.measurableSet] with x hx
    have hpos : 0 < ‖x - y‖ := hδ.trans_le (hd x hx)
    rw [norm_mul]
    apply mul_le_mul
    · exact (regularizedNewtonKernel_le_inv_norm (hp j) (norm_pos_iff.mp hpos)).trans
        (inv_anti₀ hδ (hd x hx))
    · exact (norm_inner_le_norm _ _).trans (by rw [hC1.norm_outwardNormal hx, mul_one]; exact hB x)
    · exact norm_nonneg _
    · exact inv_nonneg.mpr hδ.le
  · filter_upwards [ae_restrict_mem isClosed_frontier.measurableSet] with x hx
    have hpos : 0 < ‖x - y‖ := hδ.trans_le (hd x hx)
    exact (tendsto_regularizedNewtonKernel hε (norm_pos_iff.mp hpos)).mul_const _

end LiquidDrop

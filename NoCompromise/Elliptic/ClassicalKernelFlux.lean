import NoCompromise.Elliptic.ClassicalKernelField
import NoCompromise.Elliptic.ClassicalKernelFluxLimits

/-!
# Gauss–Green for a compact field divided by distance

The singular field has an actual integrable weak derivative, and smooth
regularizations converge in both the volume and boundary flux integrals.
-/

noncomputable section
open MeasureTheory Set Filter Metric InnerProductSpace
open scoped ENNReal Topology Gradient
namespace LiquidDrop

lemma w11Divergence_classicalNewtonFieldDerivative (X : AmbientSpace → AmbientSpace)
    (y x : AmbientSpace) :
    w11Divergence (classicalNewtonFieldDerivative X y) x =
      ‖x - y‖⁻¹ * divergenceN X x + inner ℝ (classicalNewtonGradient (x - y)) (X x) := by
  simp only [w11Divergence, classicalNewtonFieldDerivative, add_apply, smul_apply,
    ContinuousLinearMap.smulRight_apply, PiLp.add_apply, PiLp.smul_apply, smul_eq_mul,
    innerSL_apply_apply,
    Finset.sum_add_distrib, ← Finset.mul_sum, divergenceN, PiLp.inner_apply, Real.inner_apply]
  rw [add_comm]
  congr 1
  apply Finset.sum_congr rfl
  intro i _
  simp [mul_comm]

theorem newton_field_gauss_green {D : Set AmbientSpace}
    (hD : IsOpen D) (hbD : Bornology.IsBounded D) (hC1 : HasC1Boundary D)
    {X : AmbientSpace → AmbientSpace} (hX : ContDiff ℝ 1 X) (hcX : HasCompactSupport X)
    {y : AmbientSpace} (hy : y ∈ D) :
    HasW11VectorGradientOn (fun x => ‖x - y‖⁻¹ • X x)
      (classicalNewtonFieldDerivative X y) D ∧
      (∫ x in D, w11Divergence (classicalNewtonFieldDerivative X y) x) =
        ∫ x, ‖x - y‖⁻¹ * inner ℝ (X x) (hC1.outwardNormal x)
          ∂(hausdorffMeasure2 3).restrict (frontier D) := by
  refine ⟨(hasW11VectorGradientOn_newton_field hX hcX y).mono (subset_univ D), ?_⟩
  let ε (j : ℕ) : ℝ := 1 / ((j : ℝ) + 1)
  have hp : ∀ j, 0 < ε j := fun j => by dsimp [ε]; positivity
  have hε : Tendsto ε atTop (𝓝 0) := tendsto_one_div_add_atTop_nhds_zero_nat
  have hv := tendsto_integral_regularized_newton_divergence hbD.measure_lt_top hX hcX hε hp y
  have hs := tendsto_integral_regularized_newton_boundary hD hbD hC1 hX.continuous hcX hε hp hy
  have heq (j : ℕ) :
      (∫ x in D, regularizedNewtonKernel (ε j) (x - y) * divergenceN X x +
        inner ℝ (gradient (fun z => regularizedNewtonKernel (ε j) (z - y)) x) (X x)) =
      ∫ x, regularizedNewtonKernel (ε j) (x - y) * inner ℝ (X x) (hC1.outwardNormal x)
        ∂(hausdorffMeasure2 3).restrict (frontier D) := by
    have hc : ContDiff ℝ 1 (fun z : AmbientSpace => regularizedNewtonKernel (ε j) (z - y)) :=
      ((contDiff_regularizedNewtonKernel (hp j)).of_le (by simp)).comp
        (contDiff_id.sub contDiff_const)
    have h := classical_gauss_green hD hbD hC1 (hc.smul hX)
    change (∫ x in D, divergenceN
      (fun z => regularizedNewtonKernel (ε j) (z - y) • X z) x) =
        ∫ x, inner ℝ (regularizedNewtonKernel (ε j) (x - y) • X x)
          (hC1.outwardNormal x) ∂(hausdorffMeasure2 3).restrict (frontier D) at h
    simpa only [divergenceN_smul hc hX, real_inner_smul_left] using h
  have hlim := tendsto_nhds_unique (hv.congr' (Eventually.of_forall heq)) hs
  simpa only [w11Divergence_classicalNewtonFieldDerivative] using hlim

/-- Both consequences of classical W¹,¹ Gauss–Green used later in the blueprint. -/
theorem w11_gauss_green_consequences {D : Set AmbientSpace}
    (hD : IsOpen D) (hbD : Bornology.IsBounded D) (hC1 : HasC1Boundary D) :
    (∫ x, inner ℝ x (hC1.outwardNormal x)
      ∂(hausdorffMeasure2 3).restrict (frontier D)) = 3 * volume.real D ∧
      ∀ X : AmbientSpace → AmbientSpace, ContDiff ℝ 1 X → HasCompactSupport X →
        ∀ y ∈ D,
          HasW11VectorGradientOn (fun x => ‖x - y‖⁻¹ • X x)
            (classicalNewtonFieldDerivative X y) D ∧
          (∫ x in D, w11Divergence (classicalNewtonFieldDerivative X y) x) =
            ∫ x, ‖x - y‖⁻¹ * inner ℝ (X x) (hC1.outwardNormal x)
              ∂(hausdorffMeasure2 3).restrict (frontier D) :=
  ⟨integral_position_normal_eq_three_volume hD hbD hC1,
    fun _ hX hcX _ hy => newton_field_gauss_green hD hbD hC1 hX hcX hy⟩

end LiquidDrop

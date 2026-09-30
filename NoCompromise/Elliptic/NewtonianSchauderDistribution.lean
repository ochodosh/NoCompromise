module

public import NoCompromise.Elliptic.NewtonianSchauderRegularized
public import NoCompromise.Elliptic.NewtonianSchauderSplit

@[expose] public section

/-!
# Distributional Hessian of the signed Newtonian kernel

Radial symmetry computes the regularized Hessian moments. Subtracting the test
value at the origin makes the singular Hessian absolutely integrable, and the
actual regularized mixed integration-by-parts identity passes to the limit.
-/

noncomputable section
open MeasureTheory Filter Metric Set InnerProductSpace
open scoped NNReal ENNReal Topology Gradient RealInnerProductSpace
namespace LiquidDrop
set_option maxSynthPendingDepth 8
local notation "E₃" => EuclideanSpace ℝ (Fin 3)

lemma schauderRegularized_integral_radial_offDiagonal (ε : ℝ) {ψ : E₃ → ℝ}
    (hψ : ∀ (e : E₃ ≃ₗᵢ[ℝ] E₃) x, ψ (e x) = ψ x)
    {i j : Fin 3} (hij : i ≠ j) :
    (∫ x, schauderRegularizedHessianEntry ε i j x * ψ x) = 0 := by
  have he (x : E₃) : schauderRegularizedHessianEntry ε i j (coordinateReflection i x) *
      ψ (coordinateReflection i x) = -(schauderRegularizedHessianEntry ε i j x * ψ x) := by
    simp [schauderRegularizedHessianEntry_eq, hij, hij.symm, hψ,
      (coordinateReflection i).norm_map, coordinateReflection_apply]
  have h := (coordinateReflection i).measurePreserving.integral_comp
    (coordinateReflection i).toHomeomorph.measurableEmbedding
    (fun x => schauderRegularizedHessianEntry ε i j x * ψ x)
  simp_rw [he, integral_neg] at h
  linarith

lemma schauderRegularized_integral_radial_diagonal (ε : ℝ) {ψ : E₃ → ℝ}
    (hψ : ∀ (e : E₃ ≃ₗᵢ[ℝ] E₃) x, ψ (e x) = ψ x) (i j : Fin 3) :
    (∫ x, schauderRegularizedHessianEntry ε i i x * ψ x) =
      ∫ x, schauderRegularizedHessianEntry ε j j x * ψ x := by
  let e : E₃ ≃ₗᵢ[ℝ] E₃ := LinearIsometryEquiv.piLpCongrLeft 2 ℝ ℝ (Equiv.swap i j)
  have he (x : E₃) : schauderRegularizedHessianEntry ε i i (e x) * ψ (e x) =
      schauderRegularizedHessianEntry ε j j x * ψ x := by
    have hx : e x i = x j := by
      change x ((Equiv.swap i j).symm i) = x j
      simp
    simp only [schauderRegularizedHessianEntry_eq, ite_true, e.norm_map, hx, hψ]
  have h := e.measurePreserving.integral_comp e.toHomeomorph.measurableEmbedding
    (fun x => schauderRegularizedHessianEntry ε i i x * ψ x)
  simpa only [he] using h.symm

lemma schauderRegularized_integral_radial {ε : ℝ} (hε : 0 < ε) {ψ : E₃ → ℝ}
    (hcψ : Continuous ψ) (hkψ : HasCompactSupport ψ)
    (hψ : ∀ (e : E₃ ≃ₗᵢ[ℝ] E₃) x, ψ (e x) = ψ x) (i j : Fin 3) :
    (∫ x, schauderRegularizedHessianEntry ε i j x * ψ x) =
      (if i = j then (1 / 3 : ℝ) else 0) * (4 * Real.pi)⁻¹ *
        ∫ x, newtonApproximationDensity ε x * ψ x := by
  by_cases hij : i = j
  · subst j
    have hi (j : Fin 3) : Integrable (fun x =>
        schauderRegularizedHessianEntry ε j j x * ψ x) :=
      ((continuous_schauderRegularizedHessianEntry hε j j).mul hcψ).integrable_of_hasCompactSupport
        hkψ.mul_left
    have he := fun j => schauderRegularized_integral_radial_diagonal ε hψ j i
    have hs : (∑ j : Fin 3, ∫ x, schauderRegularizedHessianEntry ε j j x * ψ x) =
        (4 * Real.pi)⁻¹ * ∫ x, newtonApproximationDensity ε x * ψ x := by
      rw [← integral_finsetSum _ (fun j _ => hi j)]
      simp_rw [← Finset.sum_mul, schauderRegularizedHessianEntry_trace hε, mul_assoc]
      rw [integral_const_mul]
    simp only [Fin.sum_univ_three, he] at hs
    simp only [ite_true]
    linarith
  · simp only [hij, ite_false, zero_mul,
      schauderRegularized_integral_radial_offDiagonal ε hψ hij]

lemma tendsto_integral_schauderRegularized_radialBump {ε : ℕ → ℝ}
    (hε : Tendsto ε atTop (𝓝 0)) (hεpos : ∀ j, 0 < ε j) (i j : Fin 3) :
    Tendsto (fun k => ∫ x, schauderRegularizedHessianEntry (ε k) i j x *
      schauderRadialBump x) atTop (𝓝 (if i = j then (1 / 3 : ℝ) else 0)) := by
  simp_rw [schauderRegularized_integral_radial (hεpos _) contDiff_schauderRadialBump.continuous
    schauderRadialBump_hasCompactSupport schauderRadialBump_isometry]
  have h := (tendsto_integral_newtonApproximationDensity_mul hε hεpos
    contDiff_schauderRadialBump.continuous schauderRadialBump_hasCompactSupport).const_mul
      ((if i = j then (1 / 3 : ℝ) else 0) * (4 * Real.pi)⁻¹)
  have he : ((if i = j then (1 / 3 : ℝ) else 0) * (4 * Real.pi)⁻¹) *
      (4 * Real.pi * schauderRadialBump 0) = (if i = j then (1 / 3 : ℝ) else 0) := by
    rw [schauderRadialBump_one (by simp)]
    field_simp
  rwa [he] at h

lemma tendsto_integral_schauderRegularizedKernel_mul {ε : ℕ → ℝ}
    (hε : Tendsto ε atTop (𝓝 0)) (hεpos : ∀ j, 0 < ε j)
    {φ : E₃ → ℝ} (hφ : Continuous φ) (hcφ : HasCompactSupport φ) :
    Tendsto (fun j => ∫ x, schauderRegularizedKernel (ε j) x * φ x) atTop
      (𝓝 (∫ x, schauderNewtonKernel x * φ x)) := by
  simp only [schauderRegularizedKernel, schauderNewtonKernel, mul_assoc, integral_const_mul]
  exact (tendsto_integral_regularizedNewtonKernel_mul hε hεpos hφ hcφ).const_mul _

/-- A compact C¹ test vanishing at the origin supplies one integrable majorant
for every inverse-cubic kernel with the fixed Newtonian size bound. -/
lemma schauder_vanishing_test_majorant {g : E₃ → ℝ} (hg : ContDiff ℝ 1 g)
    (hcg : HasCompactSupport g) (hg0 : g 0 = 0) :
    ∃ b : E₃ → ℝ, Integrable b ∧
      ∀ k : E₃ → ℝ, (∀ x ≠ 0, ‖k x‖ ≤ Real.pi⁻¹ * (‖x‖ ^ 3)⁻¹) →
        ∀ x, ‖k x * g x‖ ≤ b x := by
  obtain ⟨B, hB⟩ := (hcg.fderiv ℝ).exists_bound_of_continuous
    (hg.fderiv_right (m := 0) (by norm_num)).continuous
  have hb : ∀ x ∈ (univ : Set E₃), ‖fderiv ℝ g x‖ ≤ max B 0 :=
    fun x _ => (hB x).trans (le_max_left _ _)
  have hlin (x : E₃) : ‖g x‖ ≤ max B 0 * ‖x‖ := by
    have h := (convex_univ : Convex ℝ (univ : Set E₃)).norm_image_sub_le_of_norm_fderiv_le
      (fun y _ => hg.differentiable one_ne_zero y) hb (mem_univ 0) (mem_univ x)
    simpa only [hg0, sub_zero] using h
  let b : E₃ → ℝ := (tsupport g).indicator
    (fun x => (Real.pi⁻¹ * max B 0) * (‖x‖ ^ 2)⁻¹)
  have hi : IntegrableOn (fun x : E₃ => (‖x‖ ^ 2)⁻¹) (tsupport g) := by
    simpa only [zero_sub, norm_neg] using
      integrableOn_inv_norm_sub_sq (tsupport g) hcg.measure_lt_top 0
  refine ⟨b, (integrable_indicator_iff (isClosed_tsupport g).measurableSet).mpr
    (hi.const_mul (Real.pi⁻¹ * max B 0)), ?_⟩
  intro k hk x
  by_cases hxs : x ∈ tsupport g
  · rw [show b x = (Real.pi⁻¹ * max B 0) * (‖x‖ ^ 2)⁻¹ by
      exact indicator_of_mem hxs _]
    by_cases hx : x = 0
    · simp [hx, hg0]
    have hn := norm_ne_zero_iff.mpr hx
    calc
      _ ≤ (Real.pi⁻¹ * (‖x‖ ^ 3)⁻¹) * (max B 0 * ‖x‖) := by
        rw [norm_mul]
        exact mul_le_mul (hk x hx) (hlin x) (norm_nonneg _) (by positivity)
      _ = _ := by field_simp
  · simp [b, hxs, image_eq_zero_of_notMem_tsupport hxs]

lemma integrable_schauderNewtonHessian_mul_zero {g : E₃ → ℝ} (hg : ContDiff ℝ 1 g)
    (hcg : HasCompactSupport g) (hg0 : g 0 = 0) (i j : Fin 3) :
    Integrable (fun x => schauderNewtonHessianEntry i j x * g x) := by
  obtain ⟨b, hb, hbound⟩ := schauder_vanishing_test_majorant hg hcg hg0
  exact hb.mono' ((measurable_schauderNewtonHessianEntry i j).mul
    hg.continuous.measurable).aestronglyMeasurable
    (Eventually.of_forall (hbound _ (fun x _ => norm_schauderNewtonHessianEntry_le i j x)))

lemma tendsto_integral_schauderRegularizedHessian_mul_zero {ε : ℕ → ℝ}
    (hε : Tendsto ε atTop (𝓝 0)) (hεpos : ∀ j, 0 < ε j)
    {g : E₃ → ℝ} (hg : ContDiff ℝ 1 g) (hcg : HasCompactSupport g)
    (hg0 : g 0 = 0) (i j : Fin 3) :
    Tendsto (fun k => ∫ x, schauderRegularizedHessianEntry (ε k) i j x * g x) atTop
      (𝓝 (∫ x, schauderNewtonHessianEntry i j x * g x)) := by
  obtain ⟨b, hb, hbound⟩ := schauder_vanishing_test_majorant hg hcg hg0
  apply tendsto_integral_of_dominated_convergence b
  · intro k
    exact ((continuous_schauderRegularizedHessianEntry (hεpos k) i j).mul
      hg.continuous).aestronglyMeasurable
  · exact hb
  · intro k
    exact Eventually.of_forall (hbound _ (fun x hx =>
      norm_schauderRegularizedHessianEntry_le (hεpos k) i j hx))
  · filter_upwards [] with x
    by_cases hx : x = 0
    · simp only [hx, hg0, mul_zero]
      exact tendsto_const_nhds
    · have hc : Continuous (fun L : E₃ →L[ℝ] E₃ →L[ℝ] ℝ =>
          L (EuclideanSpace.single i 1) (EuclideanSpace.single j 1)) :=
        (continuous_id.clm_apply continuous_const).clm_apply continuous_const
      exact ((hc.tendsto (schauderNewtonHessian x)).comp
        (tendsto_schauderRegularizedHessian hε hx)).mul_const (g x)

/-- The exact distributional Hessian identity, with an absolutely convergent
subtracted integral and the explicit diagonal correction. No principal value
identity is an assumption of this theorem. -/
theorem integral_schauderNewtonKernel_mixed_derivative {φ : E₃ → ℝ}
    (hφ : ContDiff ℝ 2 φ) (hcφ : HasCompactSupport φ) (i j : Fin 3) :
    Integrable (fun x => schauderNewtonHessianEntry i j x *
      (φ x - φ 0 * schauderRadialBump x)) ∧
    (∫ x, schauderNewtonKernel x *
      poissonCoordinateDerivative i (poissonCoordinateDerivative j φ) x) =
      (∫ x, schauderNewtonHessianEntry i j x * (φ x - φ 0 * schauderRadialBump x)) +
        (if i = j then (1 / 3 : ℝ) else 0) * φ 0 := by
  let g : E₃ → ℝ := fun x => φ x - φ 0 * schauderRadialBump x
  have hg : ContDiff ℝ 1 g := (hφ.of_le (by norm_num)).sub
    (contDiff_const.mul (contDiff_schauderRadialBump.of_le (by simp)))
  have hcg : HasCompactSupport g := hcφ.sub schauderRadialBump_hasCompactSupport.mul_left
  have hg0 : g 0 = 0 := by simp [g, schauderRadialBump_one (x := 0) (by simp)]
  refine ⟨integrable_schauderNewtonHessian_mul_zero hg hcg hg0 i j, ?_⟩
  let ε : ℕ → ℝ := fun k => ((k : ℝ) + 1)⁻¹
  have hε : Tendsto ε atTop (𝓝 0) := by
    simpa only [one_div] using (tendsto_one_div_add_atTop_nhds_zero_nat (𝕜 := ℝ))
  have hεpos (k : ℕ) : 0 < ε k := by dsimp [ε]; positivity
  have hDφ : Continuous (poissonCoordinateDerivative i (poissonCoordinateDerivative j φ)) :=
    (ContDiff.poissonCoordinateDerivative (r := 0)
      (ContDiff.poissonCoordinateDerivative (r := 1) hφ j) i).continuous
  have hcDφ := HasCompactSupport.poissonCoordinateDerivative
    (HasCompactSupport.poissonCoordinateDerivative hcφ j) i
  have hleft := tendsto_integral_schauderRegularizedKernel_mul hε hεpos hDφ hcDφ
  have hright := (tendsto_integral_schauderRegularizedHessian_mul_zero
    hε hεpos hg hcg hg0 i j).add
      ((tendsto_integral_schauderRegularized_radialBump hε hεpos i j).mul_const (φ 0))
  have he (k : ℕ) : (∫ x, schauderRegularizedKernel (ε k) x *
      poissonCoordinateDerivative i (poissonCoordinateDerivative j φ) x) =
      (∫ x, schauderRegularizedHessianEntry (ε k) i j x * g x) +
        (∫ x, schauderRegularizedHessianEntry (ε k) i j x * schauderRadialBump x) * φ 0 := by
    rw [integral_schauderRegularizedHessianEntry_test (hεpos k) hφ hcφ]
    have hki := continuous_schauderRegularizedHessianEntry (hεpos k) i j
    have hi0 : Integrable (fun x => schauderRegularizedHessianEntry (ε k) i j x * g x) :=
      (hki.mul hg.continuous).integrable_of_hasCompactSupport hcg.mul_left
    have hi1 : Integrable (fun x => schauderRegularizedHessianEntry (ε k) i j x *
        schauderRadialBump x) :=
      (hki.mul contDiff_schauderRadialBump.continuous).integrable_of_hasCompactSupport
        schauderRadialBump_hasCompactSupport.mul_left
    rw [← integral_mul_const, ← integral_add hi0 (hi1.mul_const _)]
    apply integral_congr_ae
    filter_upwards [] with x
    dsimp [g]
    ring
  simp_rw [he] at hleft
  exact tendsto_nhds_unique hleft hright

end LiquidDrop

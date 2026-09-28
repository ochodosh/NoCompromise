import NoCompromise.Elliptic.HarmonicMeanValue

/-!
# Shrinking cutoff estimates for point removability

In three dimensions, the L¹ norms of a rescaled smooth bump and its first and
second derivatives decay as radius cubed, radius squared, and radius. The
Laplacian of its product with any compact smooth test therefore tends to zero
in L¹. Subtracting this product removes a neighborhood of the origin from the
test's support.
-/

noncomputable section
open MeasureTheory Filter Metric Set InnerProductSpace
open scoped ENNReal NNReal Topology Gradient RealInnerProductSpace
namespace LiquidDrop
set_option maxSynthPendingDepth 8

lemma kelvin_poissonCoordinateDerivative_comp_smul {n : ℕ}
    {u : EuclideanSpace ℝ (Fin n) → ℝ} (hu : ContDiff ℝ 1 u) (c : ℝ) (i : Fin n) :
    poissonCoordinateDerivative i (fun x => u (c • x)) =
      fun x => c * poissonCoordinateDerivative i u (c • x) := by
  funext x
  simpa only [poissonCoordinateDerivative_eq_gradient, PiLp.smul_apply, smul_eq_mul] using
    congrArg (fun v : EuclideanSpace ℝ (Fin n) => v i) (gradient_comp_const_smul hu c x)

lemma kelvin_laplacianN_comp_smul {n : ℕ} {u : EuclideanSpace ℝ (Fin n) → ℝ}
    (hu : ContDiff ℝ 2 u) (c : ℝ) (x : EuclideanSpace ℝ (Fin n)) :
    laplacianN (fun y => u (c • y)) x = c ^ 2 * laplacianN u (c • x) := by
  have hd (i : Fin n) : ContDiff ℝ 1 (poissonCoordinateDerivative i u) :=
    ContDiff.poissonCoordinateDerivative (r := 1) hu i
  simp only [laplacianN, kelvin_poissonCoordinateDerivative_comp_smul
    (hu.of_le (by norm_num : (1 : WithTop ℕ∞) ≤ 2)), Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro i _
  have hf : DifferentiableAt ℝ (fun y => poissonCoordinateDerivative i u (c • y)) x :=
    ((hd i).comp (contDiff_id.const_smul c)).differentiable one_ne_zero x
  change fderiv ℝ (fun y => c * poissonCoordinateDerivative i u (c • y)) x
    (EuclideanSpace.single i 1) = _
  rw [(hf.hasFDerivAt.const_mul c).fderiv]
  change c * poissonCoordinateDerivative i (fun y => poissonCoordinateDerivative i u (c • y)) x = _
  rw [kelvin_poissonCoordinateDerivative_comp_smul (hd i)]
  ring

lemma kelvin_integral_norm_comp_smul (u : EuclideanSpace ℝ (Fin 3) → ℝ)
    {c : ℝ} (hc : 0 < c) :
    (∫ x, ‖u (c • x)‖) = c⁻¹ ^ 3 * ∫ x, ‖u x‖ := by
  rw [Measure.integral_comp_smul_of_nonneg volume (fun x => ‖u x‖) c (hR := hc.le)]
  simp only [finrank_euclideanSpace_fin, smul_eq_mul, inv_pow]

lemma kelvin_integral_norm_gradient_comp_smul {u : EuclideanSpace ℝ (Fin 3) → ℝ}
    (hu : ContDiff ℝ 1 u) {c : ℝ} (hc : 0 < c) :
    (∫ x, ‖gradient (fun y => u (c • y)) x‖) = c⁻¹ ^ 2 * ∫ x, ‖gradient u x‖ := by
  simp_rw [gradient_comp_const_smul hu, norm_smul, Real.norm_of_nonneg hc.le]
  rw [integral_const_mul, Measure.integral_comp_smul_of_nonneg volume
    (fun x => ‖gradient u x‖) c (hR := hc.le)]
  simp only [finrank_euclideanSpace_fin, smul_eq_mul]
  field_simp

lemma kelvin_integral_norm_laplacianN_comp_smul {u : EuclideanSpace ℝ (Fin 3) → ℝ}
    (hu : ContDiff ℝ 2 u) {c : ℝ} (hc : 0 < c) :
    (∫ x, ‖laplacianN (fun y => u (c • y)) x‖) = c⁻¹ * ∫ x, ‖laplacianN u x‖ := by
  simp_rw [kelvin_laplacianN_comp_smul hu, norm_mul, Real.norm_of_nonneg (sq_nonneg c)]
  rw [integral_const_mul, kelvin_integral_norm_comp_smul _ hc]
  field_simp

/-- A fixed smooth bump rescaled to shrink to the origin. -/
def kelvinCutoff (j : ℕ) : EuclideanSpace ℝ (Fin 3) → ℝ :=
  let χ : ContDiffBump (0 : EuclideanSpace ℝ (Fin 3)) := ⟨1, 2, zero_lt_one, one_lt_two⟩
  fun x => χ (((j : ℝ) + 1) • x)

lemma kelvinCutoff_contDiff (j : ℕ) : ContDiff ℝ (⊤ : ℕ∞) (kelvinCutoff j) :=
  (ContDiffBump.contDiff _).comp (contDiff_id.const_smul _)

lemma kelvinCutoff_hasCompactSupport (j : ℕ) : HasCompactSupport (kelvinCutoff j) := by
  let χ : ContDiffBump (0 : EuclideanSpace ℝ (Fin 3)) := ⟨1, 2, zero_lt_one, one_lt_two⟩
  exact χ.hasCompactSupport.comp_homeomorph
    (Homeomorph.smulOfNeZero _ (by positivity : (j : ℝ) + 1 ≠ 0))

lemma kelvinCutoff_eventuallyEq_one (j : ℕ) : kelvinCutoff j =ᶠ[𝓝 0] 1 := by
  let χ : ContDiffBump (0 : EuclideanSpace ℝ (Fin 3)) := ⟨1, 2, zero_lt_one, one_lt_two⟩
  have ht : Continuous (fun x : EuclideanSpace ℝ (Fin 3) => ((j : ℝ) + 1) • x) := by
    fun_prop
  exact χ.eventuallyEq_one.comp_tendsto (by simpa using ht.tendsto 0)

lemma tendsto_kelvinCutoff_integrals :
    Tendsto (fun j => ∫ x, ‖kelvinCutoff j x‖) atTop (𝓝 0) ∧
    Tendsto (fun j => ∫ x, ‖gradient (kelvinCutoff j) x‖) atTop (𝓝 0) ∧
    Tendsto (fun j => ∫ x, ‖laplacianN (kelvinCutoff j) x‖) atTop (𝓝 0) := by
  let χ : ContDiffBump (0 : EuclideanSpace ℝ (Fin 3)) := ⟨1, 2, zero_lt_one, one_lt_two⟩
  have ht : Tendsto (fun j : ℕ => ((j : ℝ) + 1)⁻¹) atTop (𝓝 0) := by
    simpa only [one_div] using (tendsto_one_div_add_atTop_nhds_zero_nat (𝕜 := ℝ))
  have h0 (j : ℕ) : (∫ x, ‖kelvinCutoff j x‖) =
      ((j : ℝ) + 1)⁻¹ ^ 3 * ∫ x, ‖χ x‖ :=
    kelvin_integral_norm_comp_smul χ (c := (j : ℝ) + 1) (by positivity)
  have h1 (j : ℕ) : (∫ x, ‖gradient (kelvinCutoff j) x‖) =
      ((j : ℝ) + 1)⁻¹ ^ 2 * ∫ x, ‖gradient χ x‖ :=
    kelvin_integral_norm_gradient_comp_smul χ.contDiff (by positivity)
  have h2 (j : ℕ) : (∫ x, ‖laplacianN (kelvinCutoff j) x‖) =
      ((j : ℝ) + 1)⁻¹ * ∫ x, ‖laplacianN χ x‖ :=
    kelvin_integral_norm_laplacianN_comp_smul χ.contDiff (by positivity)
  simp_rw [h0, h1, h2]
  exact ⟨by simpa using (ht.pow 3).mul_const (∫ x, ‖χ x‖),
    by simpa using (ht.pow 2).mul_const (∫ x, ‖gradient χ x‖),
    by simpa using ht.mul_const (∫ x, ‖laplacianN χ x‖)⟩

/-- Multiplying a compact test by the shrinking cutoff has vanishing L¹
Laplacian. This is the three-dimensional point-capacity estimate used below. -/
theorem tendsto_integral_norm_laplacianN_kelvinCutoff_mul
    {φ : EuclideanSpace ℝ (Fin 3) → ℝ} (hφ : ContDiff ℝ (⊤ : ℕ∞) φ)
    (hcφ : HasCompactSupport φ) :
    Tendsto (fun j => ∫ x, ‖laplacianN (fun y => kelvinCutoff j y * φ y) x‖)
      atTop (𝓝 0) := by
  have hcG : HasCompactSupport (gradient φ) :=
    hcφ.of_isClosed_subset (isClosed_tsupport _) (tsupport_gradient_subset φ)
  have hcL : HasCompactSupport (laplacianN φ) :=
    hcφ.of_isClosed_subset (isClosed_tsupport _) (tsupport_laplacianN_subset φ)
  obtain ⟨B₀, hb₀⟩ := hcφ.exists_bound_of_continuous hφ.continuous
  obtain ⟨B₁, hb₁⟩ := hcG.exists_bound_of_continuous
    (continuous_gradient_of_contDiff (hφ.of_le (by simp)))
  obtain ⟨B₂, hb₂⟩ := hcL.exists_bound_of_continuous
    (continuous_laplacianN (hφ.of_le (by simp)))
  have hbound (j : ℕ) :
      (∫ x, ‖laplacianN (fun y => kelvinCutoff j y * φ y) x‖) ≤
        B₂ * (∫ x, ‖kelvinCutoff j x‖) +
          B₀ * (∫ x, ‖laplacianN (kelvinCutoff j) x‖) +
          2 * B₁ * (∫ x, ‖gradient (kelvinCutoff j) x‖) := by
    have hj := kelvinCutoff_contDiff j
    have hcj := kelvinCutoff_hasCompactSupport j
    have hi0 := hj.continuous.integrable_of_hasCompactSupport (μ := volume) hcj
    have hi1 := (continuous_gradient_of_contDiff (hj.of_le (by simp)))
      |>.integrable_of_hasCompactSupport (μ := volume)
        (hcj.of_isClosed_subset (isClosed_tsupport _) (tsupport_gradient_subset _))
    have hi2 := (continuous_laplacianN (hj.of_le (by simp)))
      |>.integrable_of_hasCompactSupport (μ := volume)
        (hcj.of_isClosed_subset (isClosed_tsupport _) (tsupport_laplacianN_subset _))
    have hiP := (continuous_laplacianN ((hj.mul hφ).of_le (by simp)))
      |>.integrable_of_hasCompactSupport (μ := volume)
        ((hcj.mul_right (f' := φ)).of_isClosed_subset (isClosed_tsupport _)
          (tsupport_laplacianN_subset _))
    calc
      _ ≤ ∫ x, B₂ * ‖kelvinCutoff j x‖ + B₀ * ‖laplacianN (kelvinCutoff j) x‖ +
          2 * B₁ * ‖gradient (kelvinCutoff j) x‖ := by
        apply integral_mono hiP.norm
          (((hi0.norm.const_mul B₂).add (hi2.norm.const_mul B₀)).add
            (hi1.norm.const_mul (2 * B₁)))
        intro x
        change ‖laplacianN (fun y => kelvinCutoff j y * φ y) x‖ ≤
          B₂ * ‖kelvinCutoff j x‖ + B₀ * ‖laplacianN (kelvinCutoff j) x‖ +
            2 * B₁ * ‖gradient (kelvinCutoff j) x‖
        rw [laplacianN_mul (hφ.of_le (by simp)) (hj.of_le (by simp))]
        calc
          _ ≤ ‖kelvinCutoff j x * laplacianN φ x‖ +
              ‖φ x * laplacianN (kelvinCutoff j) x‖ +
              ‖2 * inner ℝ (gradient (kelvinCutoff j) x) (gradient φ x)‖ :=
            (norm_add_le _ _).trans (add_le_add (norm_add_le _ _) le_rfl)
          _ ≤ B₂ * ‖kelvinCutoff j x‖ + B₀ * ‖laplacianN (kelvinCutoff j) x‖ +
              2 * B₁ * ‖gradient (kelvinCutoff j) x‖ := by
            simp only [norm_mul, Real.norm_ofNat]
            have h0 := mul_le_mul_of_nonneg_left (hb₂ x) (norm_nonneg (kelvinCutoff j x))
            have h1 := mul_le_mul_of_nonneg_right (hb₀ x)
              (norm_nonneg (laplacianN (kelvinCutoff j) x))
            have h2 : ‖inner ℝ (gradient (kelvinCutoff j) x) (gradient φ x)‖ ≤
                ‖gradient (kelvinCutoff j) x‖ * B₁ :=
              (norm_inner_le_norm (gradient (kelvinCutoff j) x) (gradient φ x)).trans
              (mul_le_mul_of_nonneg_left (hb₁ x) (norm_nonneg (gradient (kelvinCutoff j) x)))
            nlinarith
      _ = _ := by
        have hi01 : Integrable (fun x => B₂ * ‖kelvinCutoff j x‖ +
            B₀ * ‖laplacianN (kelvinCutoff j) x‖) volume :=
          (hi0.norm.const_mul B₂).add (hi2.norm.const_mul B₀)
        rw [integral_add hi01 (hi1.norm.const_mul (2 * B₁)),
          integral_add (hi0.norm.const_mul B₂) (hi2.norm.const_mul B₀)]
        simp only [integral_const_mul]
  have ht := tendsto_kelvinCutoff_integrals
  have hlim := ((ht.1.const_mul B₂).add (ht.2.2.const_mul B₀)).add
    (ht.2.1.const_mul (2 * B₁))
  apply squeeze_zero (fun j => integral_nonneg (fun x => norm_nonneg _)) hbound
  simpa only [mul_zero, add_zero] using hlim

lemma kelvin_test_away_zero {φ : EuclideanSpace ℝ (Fin 3) → ℝ} (j : ℕ) :
    tsupport (fun x => φ x - kelvinCutoff j x * φ x) ⊆ tsupport φ \ {0} := by
  have hs : tsupport (fun x => φ x - kelvinCutoff j x * φ x) ⊆ tsupport φ := by
    apply closure_minimal _ (isClosed_tsupport φ)
    intro x hx
    by_contra hn
    exact hx (by simp [image_eq_zero_of_notMem_tsupport hn])
  have hz : (0 : EuclideanSpace ℝ (Fin 3)) ∉
      tsupport (fun x => φ x - kelvinCutoff j x * φ x) := by
    rw [notMem_tsupport_iff_eventuallyEq]
    filter_upwards [kelvinCutoff_eventuallyEq_one j] with x hx
    simp only [hx, Pi.one_apply, one_mul, sub_self, Pi.zero_apply]
  intro x hx
  exact ⟨hs hx, fun he => hz (by simpa only [mem_singleton_iff.mp he] using hx)⟩

end LiquidDrop

module

public import NoCompromise.Regularity.CompressionScalar
public import Mathlib.Analysis.InnerProductSpace.Calculus
public import Mathlib.Analysis.Calculus.Gradient.Basic
public import Mathlib.Analysis.SpecialFunctions.Pow.Deriv

@[expose] public section

/-! # The planar compression profile and its exact gradient estimate -/

noncomputable section
open Set Filter Metric InnerProductSpace
open scoped Topology Gradient
namespace LiquidDrop

def compressionProfile (σ τ : ℝ) (x : EuclideanSpace ℝ (Fin 2)) : ℝ :=
  compressionRadialProfile σ τ ‖x‖

def compressionBeta (σ τ ε : ℝ) (x : EuclideanSpace ℝ (Fin 2)) : ℝ :=
  ε + (1 - ε) * compressionProfile σ τ x

lemma compressionProfile_eq_zero_near_zero {σ τ : ℝ} (hσ : 0 < σ) (h : σ < τ) :
    compressionProfile σ τ =ᶠ[𝓝 (0 : EuclideanSpace ℝ (Fin 2))] fun _ => 0 := by
  filter_upwards [Metric.ball_mem_nhds (0 : EuclideanSpace ℝ (Fin 2)) hσ] with x hx
  have hx' : ‖x‖ < σ := by simpa only [mem_ball, dist_zero_right] using hx
  exact compressionRadialProfile_zero h hx'.le

lemma contDiff_compressionProfile {σ τ : ℝ} (hσ : 0 < σ) (h : σ < τ) :
    ContDiff ℝ 1 (compressionProfile σ τ) := by
  apply contDiff_iff_contDiffAt.mpr
  intro x
  by_cases hx : x = 0
  · subst x
    exact contDiffAt_const.congr_of_eventuallyEq (compressionProfile_eq_zero_near_zero hσ h)
  · exact (contDiff_compressionRadialProfile h).contDiffAt.comp x (contDiffAt_norm ℝ hx)

lemma lipschitzWith_compressionProfile {σ τ : ℝ} (h : σ < τ) :
    LipschitzWith ⟨Real.pi / (τ - σ), (div_pos Real.pi_pos (sub_pos.mpr h)).le⟩
      (compressionProfile σ τ) := by
  apply LipschitzWith.of_dist_le_mul
  intro x y
  have ht := (lipschitzWith_compressionRadialProfile h).dist_le_mul ‖x‖ ‖y‖
  have hn : dist ‖x‖ ‖y‖ ≤ dist x y := by
    simpa only [dist_eq_norm] using dist_norm_norm_le x y
  exact ht.trans (mul_le_mul_of_nonneg_left hn (div_pos Real.pi_pos (sub_pos.mpr h)).le)

lemma hasGradientAt_compressionProfile {σ τ : ℝ} (hσ : 0 < σ) (h : σ < τ)
    (x : EuclideanSpace ℝ (Fin 2)) :
    HasGradientAt (compressionProfile σ τ)
      ((compressionRadialDerivative σ τ ‖x‖ / ‖x‖) • x) x := by
  by_cases hx : x = 0
  · subst x
    simp only [smul_zero]
    rw [hasGradientAt_iff_hasFDerivAt, map_zero]
    exact (hasFDerivAt_const (𝕜 := ℝ) (0 : ℝ)
      (x := (0 : EuclideanSpace ℝ (Fin 2)))).congr_of_eventuallyEq
        (compressionProfile_eq_zero_near_zero hσ h)
  · have hn : ‖x‖ ≠ 0 := norm_ne_zero_iff.mpr hx
    have hnorm : HasFDerivAt (fun y : EuclideanSpace ℝ (Fin 2) => ‖y‖)
        (‖x‖⁻¹ • innerSL ℝ x) x := by
      have hh := (hasStrictFDerivAt_norm_sq x).hasFDerivAt.sqrt (pow_ne_zero 2 hn)
      convert! hh using 1
      · ext y
        simp only [Real.sqrt_sq (norm_nonneg y)]
      · ext y
        simp only [smul_apply, innerSL_apply_apply, smul_eq_mul,
          Real.sqrt_sq (norm_nonneg x)]
        field_simp
        ring
    rw [hasGradientAt_iff_hasFDerivAt]
    convert! (hasDerivAt_compressionRadialProfile h ‖x‖).comp_hasFDerivAt x hnorm using 1
    ext y
    simp only [toDual_apply_apply, inner_smul_left, RCLike.conj_to_real, smul_apply,
      innerSL_apply_apply, smul_eq_mul]
    simp only [div_eq_mul_inv, mul_assoc]

lemma compressionProfile_gradient_sq {σ τ : ℝ} (hσ : 0 < σ) (h : σ < τ)
    (x : EuclideanSpace ℝ (Fin 2)) :
    ‖gradient (compressionProfile σ τ) x‖ ^ 2 = Real.pi ^ 2 / (τ - σ) ^ 2 *
      compressionProfile σ τ x * (1 - compressionProfile σ τ x) := by
  rw [(hasGradientAt_compressionProfile hσ h x).gradient]
  by_cases hx : x = 0
  · subst x
    simp only [smul_zero, norm_zero, zero_pow (by decide : 2 ≠ 0)]
    have he : compressionProfile σ τ 0 = 0 :=
      compressionRadialProfile_zero h (by simpa only [norm_zero] using hσ.le)
    rw [he]
    ring
  · have hn : ‖x‖ ^ 2 ≠ 0 := pow_ne_zero 2 (norm_ne_zero_iff.mpr hx)
    rw [norm_smul, Real.norm_eq_abs, mul_pow, sq_abs, div_pow, div_mul_cancel₀ _ hn]
    exact compressionRadialDerivative_sq h ‖x‖

lemma compressionProfile_gradient_bound {σ τ : ℝ} (hσ : 0 < σ) (h : σ < τ)
    (x : EuclideanSpace ℝ (Fin 2)) :
    ‖gradient (compressionProfile σ τ) x‖ ^ 2 ≤
      Real.pi ^ 2 / (τ - σ) ^ 2 * (1 - compressionProfile σ τ x ^ 2) := by
  rw [compressionProfile_gradient_sq hσ h x]
  have ha := compressionRadialProfile_mem_Icc σ τ ‖x‖
  have hh : compressionProfile σ τ x * (1 - compressionProfile σ τ x) ≤
      1 - compressionProfile σ τ x ^ 2 := by dsimp [compressionProfile]; nlinarith [ha.2]
  simpa only [mul_assoc] using mul_le_mul_of_nonneg_left hh
    (div_nonneg (sq_nonneg Real.pi) (sq_nonneg (τ - σ)))

lemma contDiff_compressionBeta {σ τ : ℝ} (hσ : 0 < σ) (h : σ < τ) (ε : ℝ) :
    ContDiff ℝ 1 (compressionBeta σ τ ε) :=
  contDiff_const.add (contDiff_const.mul (contDiff_compressionProfile hσ h))

lemma compressionBeta_bounds (σ τ : ℝ) {ε : ℝ} (_hε : 0 ≤ ε) (hε1 : ε ≤ 1)
    (x : EuclideanSpace ℝ (Fin 2)) :
    ε ≤ compressionBeta σ τ ε x ∧ compressionBeta σ τ ε x ≤ 1 := by
  have ha := compressionRadialProfile_mem_Icc σ τ ‖x‖
  dsimp [compressionBeta, compressionProfile]
  constructor <;> nlinarith [ha.1, ha.2]

lemma compressionBeta_gradient {σ τ : ℝ} (hσ : 0 < σ) (h : σ < τ) (ε : ℝ)
    (x : EuclideanSpace ℝ (Fin 2)) :
    gradient (compressionBeta σ τ ε) x = (1 - ε) • gradient (compressionProfile σ τ) x := by
  apply HasGradientAt.gradient
  rw [hasGradientAt_iff_hasFDerivAt]
  have hg := ((contDiff_compressionProfile hσ h).differentiable (by norm_num) x).hasGradientAt
  convert! (hg.hasFDerivAt.const_mul (1 - ε)).const_add ε using 1
  ext y
  simp

lemma compressionBeta_gradient_bound {σ τ : ℝ} (hσ : 0 < σ) (h : σ < τ)
    {ε : ℝ} (hε : 0 ≤ ε) (hε1 : ε ≤ 1) (x : EuclideanSpace ℝ (Fin 2)) :
    ‖gradient (compressionBeta σ τ ε) x‖ ^ 2 ≤
      Real.pi ^ 2 / (τ - σ) ^ 2 * (1 - compressionBeta σ τ ε x ^ 2) := by
  rw [compressionBeta_gradient hσ h ε x, norm_smul, Real.norm_eq_abs, mul_pow, sq_abs,
    compressionProfile_gradient_sq hσ h x]
  have ha := compressionRadialProfile_mem_Icc σ τ ‖x‖
  have hb := compressionBeta_bounds σ τ hε hε1 x
  have hh : (1 - ε) ^ 2 * compressionProfile σ τ x * (1 - compressionProfile σ τ x) ≤
      1 - compressionBeta σ τ ε x ^ 2 := by
    have hnn : 0 ≤ ε * (1 - ε) * (1 - compressionProfile σ τ x) := by
      exact mul_nonneg (mul_nonneg hε (sub_nonneg.mpr hε1)) (sub_nonneg.mpr ha.2)
    dsimp [compressionBeta] at hb ⊢
    nlinarith
  have hk := mul_le_mul_of_nonneg_left hh
    (div_nonneg (sq_nonneg Real.pi) (sq_nonneg (τ - σ)))
  nlinarith only [hk]

end LiquidDrop

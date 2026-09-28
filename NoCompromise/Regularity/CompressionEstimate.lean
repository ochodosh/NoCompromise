import NoCompromise.Regularity.CompressionLinear

/-! # The quadratic area estimate for the compression cofactor -/

noncomputable section
open Set InnerProductSpace
namespace LiquidDrop

lemma compression_normal_sq_le {F : Type*} [NormedAddCommGroup F] [InnerProductSpace ℝ F]
    {u p : F} {β t s K : ℝ} (hβ : 0 ≤ β) (hβ1 : β ≤ 1) (hK : 0 ≤ K)
    (hp : ‖p‖ ^ 2 ≤ K * (1 - β ^ 2)) (hu : ‖u‖ ^ 2 + s ^ 2 = 1) :
    ‖β • u - (t * s) • p‖ ^ 2 + s ^ 2 ≤ 1 + K * t ^ 2 := by
  by_cases he : β = 1
  · subst β
    have hp0 : p = 0 := norm_eq_zero.mp (by nlinarith [norm_nonneg p])
    simp only [hp0, smul_zero, one_smul, sub_zero, hu]
    linarith [mul_nonneg hK (sq_nonneg t)]
  · have hlt : β < 1 := lt_of_le_of_ne hβ1 he
    have hq : 0 < 1 - β ^ 2 := by
      nlinarith [mul_pos (sub_pos.mpr hlt) (by linarith : 0 < 1 + β)]
    have hsq := sq_nonneg ‖(1 - β ^ 2) • u + (β * t * s) • p‖
    rw [norm_add_sq_real, norm_smul, norm_smul, Real.norm_eq_abs, Real.norm_eq_abs,
      mul_pow, mul_pow, sq_abs, sq_abs, inner_smul_left, inner_smul_right] at hsq
    simp only [RCLike.conj_to_real] at hsq
    have hnorm := norm_sub_sq_real (β • u) ((t * s) • p)
    rw [norm_smul, norm_smul, Real.norm_eq_abs, Real.norm_eq_abs,
      mul_pow, mul_pow, sq_abs, sq_abs, inner_smul_left, inner_smul_right] at hnorm
    simp only [RCLike.conj_to_real] at hnorm
    have herr : 0 ≤ t ^ 2 * s ^ 2 * (K * (1 - β ^ 2) - ‖p‖ ^ 2) :=
      mul_nonneg (mul_nonneg (sq_nonneg t) (sq_nonneg s)) (sub_nonneg.mpr hp)
    have hother : 0 ≤ K * t ^ 2 * (1 - β ^ 2) * ‖u‖ ^ 2 := by positivity
    have hm := congrArg (fun z : ℝ => K * t ^ 2 * (1 - β ^ 2) * z) hu
    have hm' := congrArg (fun z : ℝ => (1 - β ^ 2) * z) hu
    have hm'' := congrArg (fun z : ℝ => (1 - β ^ 2) * z) hnorm
    have hprod : (1 - β ^ 2) * (‖β • u - (t * s) • p‖ ^ 2 + s ^ 2 -
        (1 + K * t ^ 2)) ≤ 0 := by
      nlinarith only [hsq, herr, hother, hm, hm', hm'']
    apply sub_nonpos.mp
    exact le_of_not_gt (fun hh => (mul_pos hq hh).not_ge hprod)

theorem compression_jacobian_bound {β K : ℝ} (hβ : 0 ≤ β) (hβ1 : β ≤ 1) (hK : 0 ≤ K)
    (t : ℝ) {p : EuclideanSpace ℝ (Fin 2)} (hp : ‖p‖ ^ 2 ≤ K * (1 - β ^ 2))
    {ν : EuclideanSpace ℝ (Fin 3)} (hν : ‖ν‖ = 1)
    (e : EuclideanSpace ℝ (Fin 2) ≃ₗᵢ[ℝ] (ℝ ∙ ν)ᗮ) :
    jacobian2Linear ((compressionLinear β t p).comp
      (normalPlaneInclusion ν e).toContinuousLinearMap) ≤ 1 + K * t ^ 2 := by
  have hu : ‖graphProjectionN 2 ν‖ ^ 2 + (ν 2) ^ 2 = 1 := by
    simpa only [hν, one_pow, show (Fin.last 2 : Fin 3) = 2 from rfl] using
      (norm_sq_graphProjectionN ν).symm
  have hb := compression_normal_sq_le (t := t) hβ hβ1 hK hp hu
  rw [← compression_jacobian_sq β t p hν e] at hb
  have hpos : 0 ≤ K * t ^ 2 := mul_nonneg hK (sq_nonneg t)
  nlinarith [sq_nonneg (jacobian2Linear ((compressionLinear β t p).comp
    (normalPlaneInclusion ν e).toContinuousLinearMap) - (1 + K * t ^ 2))]

end LiquidDrop

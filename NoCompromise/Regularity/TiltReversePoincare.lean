import NoCompromise.Regularity.ReversePoincareRotated

/-! # Converting the actual tilted height moment into improved excess -/

noncomputable section
open Set MeasureTheory Metric
namespace LiquidDrop

lemma tilt_reverse_poincare_arithmetic {R K e ω θ : ℝ}
    (hR : 0 ≤ R) (hK : 0 ≤ K) (he : 0 ≤ e) (hω : 0 ≤ ω)
    (hθ : 0 < θ) (hθ1 : θ ≤ 1) :
    (R / (2 * θ) ^ 4) * (K * (e + ω) * θ ^ 6) + R * ω * (2 * θ) ≤
      (R * (K + 2)) * θ ^ 2 * e + (R * (K + 2)) * θ * ω := by
  have hid : (R / (2 * θ) ^ 4) * (K * (e + ω) * θ ^ 6) =
      (R * K / 16) * θ ^ 2 * (e + ω) := by
    field_simp
    ring
  rw [hid]
  have hc : R * K / 16 ≤ R * K := by nlinarith [mul_nonneg hR hK]
  have ht : θ ^ 2 ≤ θ := by nlinarith
  have h1 := mul_le_mul_of_nonneg_right hc (mul_nonneg (sq_nonneg θ) he)
  have h2 := mul_le_mul_of_nonneg_right hc (mul_nonneg (sq_nonneg θ) hω)
  have h3 := mul_le_mul_of_nonneg_left
    (mul_le_mul_of_nonneg_right ht hω) (mul_nonneg hR hK)
  have h4 := mul_nonneg hR (mul_nonneg (sq_nonneg θ) he)
  nlinarith

theorem IsOmegaMinimal.tilt_excess_of_height_bound
    {E : Set AmbientSpace} {ω θ c η K : ℝ} (hE : IsOmegaMinimal E ω)
    (Q : AmbientSpace ≃ₗᵢ[ℝ] AmbientSpace) (hθ : 0 < θ) (hθ32 : θ < 1 / 32)
    (hK : 0 ≤ K)
    (hconfig : IsSlabCapConfiguration (Q.toAffineIsometryEquiv ⁻¹' E)
      (hE.preimage_affineIsometry Q.toAffineIsometryEquiv).locallyFinite
      (hE.preimage_affineIsometry Q.toAffineIsometryEquiv).nullMeasurable (2 * θ) c η)
    (hmoment : (∫ y in cylinder 0 (2 * θ) (Q (EuclideanSpace.single 2 1)) ∩
        reducedBoundary E hE.locallyFinite hE.nullMeasurable,
        (inner ℝ (Q (EuclideanSpace.single 2 1)) y - c) ^ 2 ∂hausdorffMeasure2 3) ≤
      K * (cylindricalExcess E hE.locallyFinite hE.nullMeasurable 0 1
        (EuclideanSpace.single 2 1) + ω) * θ ^ 6) :
    cylindricalExcess E hE.locallyFinite hE.nullMeasurable 0 θ
      (Q (EuclideanSpace.single 2 1)) ≤
      (reversePoincareConstant * (K + 2)) * θ ^ 2 *
        cylindricalExcess E hE.locallyFinite hE.nullMeasurable 0 1
          (EuclideanSpace.single 2 1) +
      (reversePoincareConstant * (K + 2)) * θ * ω := by
  have hr : 2 * θ ≤ 1 / Real.sqrt 2 := by
    apply (le_div_iff₀ (Real.sqrt_pos.mpr (by norm_num : (0 : ℝ) < 2))).mpr
    have hs : Real.sqrt 2 ≤ 2 :=
      Real.sqrt_le_iff.mpr ⟨by norm_num, by norm_num⟩
    nlinarith [Real.sqrt_nonneg (2 : ℝ)]
  have hp := hE.reverse_poincare_rotated Q hconfig hr
  rw [show 2 * θ / 2 = θ by ring] at hp
  have he : 0 ≤ cylindricalExcess E hE.locallyFinite hE.nullMeasurable 0 1
      (EuclideanSpace.single 2 1) := by
    simpa only [cylindricalExcess, one_pow, div_one] using
      normalExcessIntegral_nonneg E hE.locallyFinite hE.nullMeasurable
        (cylinder 0 1 (EuclideanSpace.single 2 1)) (EuclideanSpace.single 2 1)
  apply hp.trans
  have hn : 0 ≤ reversePoincareConstant / (2 * θ) ^ 4 := by
    exact div_nonneg reversePoincareConstant_pos.le (by positivity)
  have hm := mul_le_mul_of_nonneg_left hmoment hn
  apply (add_le_add hm (le_refl (reversePoincareConstant * ω * (2 * θ)))).trans
  exact tilt_reverse_poincare_arithmetic reversePoincareConstant_pos.le hK he hE.nonneg
    hθ (by linarith)

end LiquidDrop

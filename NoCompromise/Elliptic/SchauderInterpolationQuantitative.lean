import NoCompromise.Elliptic.SchauderInterpolationQuantitativeScales
import NoCompromise.Elliptic.NondivSchauderNorm

/-! Same-ball interpolation with a polynomial cost in the small parameter.
The exponent and constant are fixed before every radius at least one half,
every ε in (0,1], and every actual C²,α function. -/

noncomputable section
open MeasureTheory Filter Metric Set
open scoped ENNReal NNReal Topology
namespace LiquidDrop

lemma schauder_derivative_interpolation_polynomial {n k : ℕ} {a ε R : ℝ}
    (ha : 0 < a) (ha1 : a < 1) (hk : 1 ≤ (k : ℝ) * (1 - a))
    (hε : 0 < ε) (hε1 : ε ≤ 1) (hR : (1 / 2 : ℝ) ≤ R)
    (c : EuclideanSpace ℝ (Fin n)) {u : EuclideanSpace ℝ (Fin n) → ℝ}
    (hu : HasC2HolderOn a u (ball c R)) :
    holderNorm a (fderiv ℝ u) (ball c R) ≤
      ε * holderNorm a (fderiv ℝ (fderiv ℝ u)) (ball c R) +
        (288 * (4 : ℝ) ^ (2 * k)) * (ε⁻¹) ^ (2 * k + 1) *
          lpNorm u ∞ (volume.restrict (ball c R)) := by
  obtain ⟨s, t, hs, hsR, ht, hsmall, hcost⟩ :=
    schauder_quantitative_interpolation_scales ha ha1 hk hε hε1 hR
  let Z := lpNorm u ∞ (volume.restrict (ball c R))
  let M := holderUniformNorm (fderiv ℝ (fderiv ℝ u)) (ball c R)
  have hZ : 0 ≤ Z := lpNorm_nonneg
  have hM : 0 ≤ M := holderUniformNorm_nonneg hu.hessian_holder.uniform_bounded
  have hval : ∀ x ∈ ball c R, ‖u x‖ ≤ Z :=
    holderInterpolation_norm_le_lpNorm_top isOpen_ball hu.contDiff.continuousOn
      (hu.memLp_top isOpen_ball)
  have hHbound : ∀ x ∈ ball c R, ‖fderiv ℝ (fderiv ℝ u) x‖ ≤ M :=
    fun _ hx => norm_le_holderUniformNorm hu.hessian_holder.uniform_bounded hx
  let A := (4 / s) * Z + (2 * s) * M
  have hA : 0 ≤ A := by dsimp [A]; positivity
  have hfirst : ∀ x ∈ ball c R, ‖fderiv ℝ u x‖ ≤ A :=
    fun _ hx => holderInterpolation_fderiv_le hu.contDiff hs hsR hM hZ hval hHbound hx
  let D := M * t ^ (1 - a) + 2 * A / t ^ a
  have hD : 0 ≤ D := by dsimp [D]; positivity
  have hquot : ∀ x ∈ ball c R, ∀ y ∈ ball c R,
      ‖fderiv ℝ u x - fderiv ℝ u y‖ / ‖x - y‖ ^ a ≤ D := by
    intro x hx y hy
    exact holderInterpolation_quotient_le ha ha1 ht hA hM hfirst
      (fun _ hx _ hy => holderInterpolation_fderiv_sub_le hu.contDiff hHbound hy hx) hx hy
  calc
    _ ≤ A + D := holderNorm_le hA hD hfirst hquot
    _ = (2 * s * (1 + 2 / t ^ a) + t ^ (1 - a)) * M +
        ((4 / s) * (1 + 2 / t ^ a)) * Z := by dsimp [A, D]; ring
    _ ≤ ε * M + ((288 * (4 : ℝ) ^ (2 * k)) * (ε⁻¹) ^ (2 * k + 1)) * Z :=
      add_le_add (mul_le_mul_of_nonneg_right hsmall hM)
        (mul_le_mul_of_nonneg_right hcost hZ)
    _ ≤ _ := add_le_add
      (mul_le_mul_of_nonneg_left hu.hessian_holder.uniformNorm_le hε.le) le_rfl

/-- Uniform polynomial interpolation for the actual sum C¹,α norm. In particular
this is uniform on all radii in [1/2,1]. -/
theorem schauder_interpolation_polynomial {n : ℕ} {a : ℝ} (ha : 0 < a) (ha1 : a < 1) :
    ∃ p : ℕ, 0 < p ∧ ∃ C : ℝ, 0 < C ∧
      ∀ (c : EuclideanSpace ℝ (Fin n)) (R ε : ℝ), (1 / 2 : ℝ) ≤ R →
        0 < ε → ε ≤ 1 → ∀ u : EuclideanSpace ℝ (Fin n) → ℝ,
        HasC2HolderOn a u (ball c R) →
        nondivC1HolderNorm a u (ball c R) ≤ ε * schauderC2HolderNorm a u (ball c R) +
          C * (ε⁻¹) ^ p * lpNorm u ∞ (volume.restrict (ball c R)) := by
  obtain ⟨k, hk⟩ := exists_nat_gt ((1 - a)⁻¹)
  have hka : 1 ≤ (k : ℝ) * (1 - a) := by
    have ht := mul_le_mul_of_nonneg_right hk.le (sub_pos.mpr ha1).le
    rwa [inv_mul_cancel₀ (sub_pos.mpr ha1).ne'] at ht
  let p := 2 * k + 1
  let C₀ : ℝ := 288 * 4 ^ (2 * k)
  let C := 3 + 2 * C₀ * 2 ^ p
  have hC₀ : 0 < C₀ := by dsimp [C₀]; positivity
  refine ⟨p, by dsimp [p]; omega, C, by dsimp [C]; positivity, ?_⟩
  intro c R ε hR hε hε1 u hu
  let Z := lpNorm u ∞ (volume.restrict (ball c R))
  let D := holderNorm a (fderiv ℝ u) (ball c R)
  let H := holderNorm a (fderiv ℝ (fderiv ℝ u)) (ball c R)
  have hZ : 0 ≤ Z := lpNorm_nonneg
  have hD : 0 ≤ D := hu.derivative_holder.norm_nonneg
  have hH : 0 ≤ H := hu.hessian_holder.norm_nonneg
  have hv : ∀ x ∈ ball c R, ‖u x‖ ≤ Z :=
    holderInterpolation_norm_le_lpNorm_top isOpen_ball hu.contDiff.continuousOn
      (hu.memLp_top isOpen_ball)
  have hd : ∀ x ∈ ball c R, ‖fderiv ℝ u x‖ ≤ D :=
    fun _ hx => hu.derivative_holder.nondiv_norm_le hx
  have hlip : ∀ x ∈ ball c R, ∀ y ∈ ball c R, ‖u x - u y‖ ≤ D * ‖x - y‖ := by
    intro x hx y hy
    exact (convex_ball c R).norm_image_sub_le_of_norm_fderiv_le
      (fun z hz => (hu.contDiff.contDiffAt (isOpen_ball.mem_nhds hz)).differentiableAt
        (by norm_num)) hd hy hx
  have hquot (x) (hx : x ∈ ball c R) (y) (hy : y ∈ ball c R) :
      ‖u x - u y‖ / ‖x - y‖ ^ a ≤ D + 2 * Z := by
    simpa only [Real.one_rpow, mul_one, div_one] using
      holderInterpolation_quotient_le ha ha1 (by norm_num : (0 : ℝ) < 1) hZ hD hv hlip hx hy
  have huN : holderNorm a u (ball c R) ≤ 3 * Z + D :=
    (holderNorm_le hZ (by positivity) hv hquot).trans_eq (by ring)
  have hder := schauder_derivative_interpolation_polynomial ha ha1 hka
    (half_pos hε) (by linarith : ε / 2 ≤ 1) hR c hu
  have hεpow : 1 ≤ (ε⁻¹) ^ p := one_le_pow₀ ((one_le_inv₀ hε).mpr hε1)
  have hder' : D ≤ (ε / 2) * H + C₀ * 2 ^ p * (ε⁻¹) ^ p * Z := by
    convert hder using 1
    dsimp only [p, C₀, H, Z]
    simp only [div_eq_mul_inv]
    ring
  have hfull : H ≤ schauderC2HolderNorm a u (ball c R) := by
    exact le_add_of_nonneg_left (add_nonneg hu.function_holder.norm_nonneg hD)
  have he : ε * H ≤ ε * schauderC2HolderNorm a u (ball c R) :=
    mul_le_mul_of_nonneg_left hfull hε.le
  change holderNorm a u (ball c R) + D ≤ _
  dsimp only [C]
  have hz := mul_le_mul_of_nonneg_right hεpow hZ
  nlinarith only [huN, hder', he, hz]

end LiquidDrop

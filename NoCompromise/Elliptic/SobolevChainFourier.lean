module

public import NoCompromise.Sobolev.SpatialGN
public import Mathlib.Analysis.Fourier.FourierTransformDeriv
public import Mathlib.Analysis.Fourier.Inversion
public import Mathlib.Analysis.SpecialFunctions.JapaneseBracket

@[expose] public section

/-!
# Weighted Fourier estimates for the Sobolev chain

The transform uses mathlib's phase `exp (-2π i ⟪x, ξ⟫)`. Polynomially weighted
L² control supplies integrable Fourier moments and hence classical derivatives
of the inverse transform. No continuity of the initial function is assumed.
-/

noncomputable section

open MeasureTheory Real
open scoped ENNReal Topology FourierTransform

namespace LiquidDrop

/-- The reciprocal polynomial weight is square integrable above half the dimension. -/
lemma sobolevChain_memLp_weight {n : ℕ} {s : ℝ} (hs : (n : ℝ) < 2 * s) :
    MemLp (fun x : EuclideanSpace ℝ (Fin n) => (1 + ‖x‖) ^ (-s)) 2 volume := by
  have hi : Integrable (fun x : EuclideanSpace ℝ (Fin n) =>
      (1 + ‖x‖) ^ (-(2 * s))) :=
    integrable_one_add_norm (by simpa using hs)
  have hc : Continuous (fun x : EuclideanSpace ℝ (Fin n) => (1 + ‖x‖) ^ (-s)) :=
    (continuous_const.add continuous_norm).rpow_const
      (fun x => Or.inl (ne_of_gt (by positivity : 0 < 1 + ‖x‖)))
  apply (memLp_two_iff_integrable_sq (μ := volume) hc.aestronglyMeasurable).mpr
  apply hi.congr
  filter_upwards with x
  rw [← Real.rpow_natCast, ← Real.rpow_mul (by positivity)]
  congr 1
  ring

/-- Hölder turns a weighted L² norm into an integrable Fourier moment. -/
lemma sobolevChain_integrable_moment {n j : ℕ} {m : ℝ}
    {F : EuclideanSpace ℝ (Fin n) → ℂ} (hF : AEStronglyMeasurable F volume)
    (hW : MemLp (fun x => (1 + ‖x‖) ^ m * ‖F x‖) 2 volume)
    (hm : (j : ℝ) + n / 2 < m) :
    Integrable (fun x => ‖x‖ ^ j * ‖F x‖) := by
  have hw := sobolevChain_memLp_weight (n := n) (s := m - j) (by linarith)
  have hi := hw.integrable_mul hW
  apply hi.mono' ((continuous_norm.pow j).aestronglyMeasurable.mul hF.norm)
  filter_upwards with x
  change ‖‖x‖ ^ j * ‖F x‖‖ ≤
    (1 + ‖x‖) ^ (-(m - j)) * ((1 + ‖x‖) ^ m * ‖F x‖)
  rw [Real.norm_of_nonneg (mul_nonneg (pow_nonneg (norm_nonneg _) _) (norm_nonneg _))]
  calc
    ‖x‖ ^ j * ‖F x‖ ≤ (1 + ‖x‖) ^ j * ‖F x‖ := by gcongr; linarith [norm_nonneg x]
    _ = (1 + ‖x‖) ^ (-(m - j)) * ((1 + ‖x‖) ^ m * ‖F x‖) := by
      rw [← mul_assoc, ← Real.rpow_add (by positivity)]
      congr 1
      rw [show -(m - (j : ℝ)) + m = j by ring, Real.rpow_natCast]

/-- Quantitative Hölder estimate for an individual Fourier moment. -/
lemma sobolevChain_integral_moment_le {n j : ℕ} {m : ℝ}
    {F : EuclideanSpace ℝ (Fin n) → ℂ} (hF : AEStronglyMeasurable F volume)
    (hW : MemLp (fun x => (1 + ‖x‖) ^ m * ‖F x‖) 2 volume)
    (hm : (j : ℝ) + n / 2 < m) :
    (∫ x, ‖x‖ ^ j * ‖F x‖) ≤
      lpNorm (fun x : EuclideanSpace ℝ (Fin n) => (1 + ‖x‖) ^ (-(m - j))) 2 volume *
        lpNorm (fun x => (1 + ‖x‖) ^ m * ‖F x‖) 2 volume := by
  have hw := sobolevChain_memLp_weight (n := n) (s := m - j) (by linarith)
  have hi := hw.integrable_mul hW
  apply (integral_mono (sobolevChain_integrable_moment hF hW hm) hi ?_).trans
  · have hn (x : EuclideanSpace ℝ (Fin n)) :
        ‖(1 + ‖x‖) ^ (-(m - j)) * ((1 + ‖x‖) ^ m * ‖F x‖)‖ =
          (1 + ‖x‖) ^ (-(m - j)) * ((1 + ‖x‖) ^ m * ‖F x‖) :=
      Real.norm_of_nonneg (by positivity)
    simpa only [smul_eq_mul, hn, Pi.mul_apply] using
      integral_norm_smul_le_lpNorm_two_mul hw hW
  · intro x
    calc
      ‖x‖ ^ j * ‖F x‖ ≤ (1 + ‖x‖) ^ j * ‖F x‖ := by
        gcongr; linarith [norm_nonneg x]
      _ = (1 + ‖x‖) ^ (-(m - j)) * ((1 + ‖x‖) ^ m * ‖F x‖) := by
        rw [← mul_assoc, ← Real.rpow_add (by positivity)]
        congr 1
        rw [show -(m - (j : ℝ)) + m = j by ring, Real.rpow_natCast]

/-- The inverse transform is the Fourier integral for the negative inner product. -/
lemma sobolevChain_fourierInv_eq {n : ℕ} (F : EuclideanSpace ℝ (Fin n) → ℂ) :
    𝓕⁻ F = VectorFourier.fourierIntegral Real.fourierChar volume
      (-(innerSL ℝ : EuclideanSpace ℝ (Fin n) →L[ℝ]
        EuclideanSpace ℝ (Fin n) →L[ℝ] ℝ)).toLinearMap₁₂ F := by
  ext x
  rw [Real.fourierInv_eq, VectorFourier.fourierIntegral]
  congr 1
  funext v
  change Real.fourierChar (inner ℝ v x) • F v =
    Real.fourierChar (-(-inner ℝ v x)) • F v
  rw [neg_neg]

/-- Weighted L² Fourier data have a classical Cᵏ inverse transform. -/
theorem sobolevChain_contDiff_fourierInv {n k : ℕ} {m : ℝ}
    {F : EuclideanSpace ℝ (Fin n) → ℂ} (hF : AEStronglyMeasurable F volume)
    (hW : MemLp (fun x => (1 + ‖x‖) ^ m * ‖F x‖) 2 volume)
    (hm : (k : ℝ) + n / 2 < m) : ContDiff ℝ k (𝓕⁻ F) := by
  rw [sobolevChain_fourierInv_eq]
  apply VectorFourier.contDiff_fourierIntegral (N := (k : ℕ∞))
  intro j hj
  have hjk : j ≤ k := by exact_mod_cast hj
  apply sobolevChain_integrable_moment hF hW
  have : (j : ℝ) ≤ k := by exact_mod_cast hjk
  linarith

/-- Every classical derivative of the inverse transform has a uniform quantitative bound. -/
theorem sobolevChain_norm_iteratedFDeriv_fourierInv_le {n k j : ℕ} {m : ℝ}
    {F : EuclideanSpace ℝ (Fin n) → ℂ} (hF : AEStronglyMeasurable F volume)
    (hW : MemLp (fun x => (1 + ‖x‖) ^ m * ‖F x‖) 2 volume)
    (hm : (k : ℝ) + n / 2 < m) (hj : j ≤ k) (x : EuclideanSpace ℝ (Fin n)) :
    ‖iteratedFDeriv ℝ j (𝓕⁻ F) x‖ ≤ (2 * π) ^ j *
      lpNorm (fun y : EuclideanSpace ℝ (Fin n) => (1 + ‖y‖) ^ (-(m - j))) 2 volume *
        lpNorm (fun y => (1 + ‖y‖) ^ m * ‖F y‖) 2 volume := by
  let L := -(innerSL ℝ : EuclideanSpace ℝ (Fin n) →L[ℝ]
    EuclideanSpace ℝ (Fin n) →L[ℝ] ℝ)
  have hmoment (a : ℕ) (ha : (a : ℕ∞) ≤ k) :
      Integrable (fun y => ‖y‖ ^ a * ‖F y‖) := by
    apply sobolevChain_integrable_moment hF hW
    have : (a : ℝ) ≤ k := by exact_mod_cast ha
    linarith
  have hj' : (j : ℕ∞) ≤ k := by exact_mod_cast hj
  have hI := VectorFourier.integrable_fourierPowSMulRight L (hmoment j hj') hF
  have hL : ‖L‖ ≤ 1 := (norm_neg (innerSL ℝ)).le.trans (norm_innerSL_le ℝ)
  rw [sobolevChain_fourierInv_eq,
    VectorFourier.iteratedFDeriv_fourierIntegral L hmoment hF hj']
  calc
    _ ≤ ∫ y, ‖VectorFourier.fourierPowSMulRight L F y j‖ :=
      VectorFourier.norm_fourierIntegral_le_integral_norm _ _ _ _ _
    _ ≤ ∫ y, (2 * π) ^ j * (‖y‖ ^ j * ‖F y‖) := by
      apply integral_mono hI.norm ((hmoment j hj').const_mul _)
      intro y
      apply (VectorFourier.norm_fourierPowSMulRight_le L F y j).trans
      calc
        _ ≤ (2 * π * 1) ^ j * ‖y‖ ^ j * ‖F y‖ := by gcongr
        _ = _ := by ring
    _ = (2 * π) ^ j * ∫ y, ‖y‖ ^ j * ‖F y‖ := integral_const_mul _ _
    _ ≤ _ := by
      rw [mul_assoc]
      apply mul_le_mul_of_nonneg_left (sobolevChain_integral_moment_le hF hW ?_) (by positivity)
      have : (j : ℝ) ≤ k := by exact_mod_cast hj
      linarith

end LiquidDrop

import NoCompromise.Elliptic.SobolevChainFourier
import NoCompromise.Elliptic.InteriorH2
import Mathlib.Analysis.Distribution.FourierMultiplier
import Mathlib.Analysis.Real.Pi.Bounds

/-!
# The H² uniform estimate on Schwartz functions

Fourier inversion, the Laplacian multiplier, and Plancherel give the uniform
estimate in dimensions less than four. This is an estimate for smooth functions;
continuity of weak Sobolev functions will be constructed by approximation.
-/

noncomputable section

open MeasureTheory Real SchwartzMap Laplacian FourierTransform
open scoped ENNReal Topology FourierTransform SchwartzMap

namespace LiquidDrop

/-- The exact Laplacian multiplier in mathlib's Fourier convention. -/
lemma sobolevChain_fourier_laplacian {n : ℕ}
    (f : 𝓢(EuclideanSpace ℝ (Fin n), ℂ)) :
    𝓕 (Δ f) = -(2 * π) ^ 2 •
      SchwartzMap.smulLeftCLM ℂ (fun x => ‖x‖ ^ 2) (𝓕 f) := by
  rw [SchwartzMap.laplacian_eq_fourierMultiplierCLM,
    SchwartzMap.fourierMultiplierCLM_apply, fourier_smul, fourier_fourierInv_eq]

/-- Plancherel expressed with the raw real L² seminorm. -/
lemma sobolevChain_lpNorm_fourier_schwartz {n : ℕ}
    (f : 𝓢(EuclideanSpace ℝ (Fin n), ℂ)) :
    lpNorm (⇑(𝓕 f : 𝓢(_, ℂ))) 2 volume = lpNorm f 2 volume := by
  simpa only [SchwartzMap.norm_toLp, toReal_eLpNorm,
    toReal_eLpNorm] using
    SchwartzMap.norm_fourier_toL2_eq f

/-- The quadratic Fourier weight is controlled by the function and its Laplacian. -/
lemma sobolevChain_fourier_weight_two {n : ℕ}
    (f : 𝓢(EuclideanSpace ℝ (Fin n), ℂ)) :
    MemLp (fun x => (1 + ‖x‖) ^ (2 : ℝ) * ‖𝓕 f x‖) 2 volume ∧
      lpNorm (fun x => (1 + ‖x‖) ^ (2 : ℝ) * ‖𝓕 f x‖) 2 volume ≤
        2 * (lpNorm f 2 volume + lpNorm (⇑(Δ f : 𝓢(_, ℂ))) 2 volume) := by
  let q := SchwartzMap.smulLeftCLM ℂ
    (fun x : EuclideanSpace ℝ (Fin n) => ‖x‖ ^ 2) (𝓕 f)
  have hq (x) : q x = ‖x‖ ^ 2 • 𝓕 f x := by
    exact congrFun (SchwartzMap.smulLeftCLM_apply
      (Function.hasTemperateGrowth_norm_sq _) (𝓕 f)) x
  have hnq (x) : ‖q x‖ = ‖x‖ ^ 2 * ‖𝓕 f x‖ := by
    rw [hq, norm_smul, Real.norm_of_nonneg (sq_nonneg _)]
  have hPl : lpNorm (⇑(Δ f : 𝓢(_, ℂ))) 2 volume = (2 * π) ^ 2 * lpNorm q 2 volume := by
    rw [← sobolevChain_lpNorm_fourier_schwartz (Δ f), sobolevChain_fourier_laplacian]
    change lpNorm (-(2 * π) ^ 2 • (q : EuclideanSpace ℝ (Fin n) → ℂ)) 2 volume = _
    rw [lpNorm_const_smul, coe_nnnorm, norm_neg, Real.norm_of_nonneg (sq_nonneg _)]
  have hqbound : lpNorm q 2 volume ≤ lpNorm (⇑(Δ f : 𝓢(_, ℂ))) 2 volume := by
    rw [hPl]
    have hπ : 1 ≤ (2 * π) ^ 2 := by nlinarith [Real.pi_gt_three]
    exact le_mul_of_one_le_left lpNorm_nonneg hπ
  let s := fun x => ‖𝓕 f x‖ + ‖q x‖
  have hms : MemLp s 2 volume := (𝓕 f).memLp 2 |>.norm.add (q.memLp 2).norm
  have hmW : AEStronglyMeasurable
      (fun x => (1 + ‖x‖) ^ (2 : ℝ) * ‖𝓕 f x‖) volume := by
    simp only [Real.rpow_two]
    exact (((continuous_const.add continuous_norm).pow 2).mul
      (𝓕 f).continuous.norm).aestronglyMeasurable
  have hb (x) : ‖(1 + ‖x‖) ^ (2 : ℝ) * ‖𝓕 f x‖‖ ≤ 2 * ‖s x‖ := by
    have hs : 0 ≤ s x := add_nonneg (norm_nonneg _) (norm_nonneg _)
    rw [Real.norm_of_nonneg (by positivity), Real.norm_of_nonneg hs,
      show s x = ‖𝓕 f x‖ + ‖q x‖ from rfl, hnq, Real.rpow_two]
    nlinarith [sq_nonneg (‖x‖ - 1), norm_nonneg (𝓕 f x)]
  have hw := poisson_lpNorm_le_mul_of_norm_le hms (by norm_num : (0 : ℝ) ≤ 2) hb
  refine ⟨(hms.const_mul 2).mono hmW ?_, hw.trans ?_⟩
  · filter_upwards with x
    simpa only [Pi.mul_apply, norm_mul, Real.norm_of_nonneg (by norm_num : (0 : ℝ) ≤ 2)]
      using hb x
  · have hadd := lpNorm_add_le ((𝓕 f).memLp 2).norm (g := fun x => ‖q x‖) (by norm_num)
    simp only [lpNorm_norm (𝓕 f).continuous.aestronglyMeasurable,
      lpNorm_norm q.continuous.aestronglyMeasurable,
      sobolevChain_lpNorm_fourier_schwartz] at hadd
    change lpNorm s 2 volume ≤ lpNorm f 2 volume + lpNorm q 2 volume at hadd
    exact mul_le_mul_of_nonneg_left (hadd.trans (add_le_add le_rfl hqbound))
      (by norm_num)

/-- The H² uniform estimate for complex Schwartz functions in dimensions below four. -/
theorem sobolevChain_schwartz_uniform_bound {n : ℕ} (hn : n < 4)
    (f : 𝓢(EuclideanSpace ℝ (Fin n), ℂ)) (x : EuclideanSpace ℝ (Fin n)) :
    ‖f x‖ ≤ 2 * lpNorm (fun y : EuclideanSpace ℝ (Fin n) =>
      (1 + ‖y‖) ^ (-2 : ℝ)) 2 volume *
        (lpNorm f 2 volume + lpNorm (⇑(Δ f : 𝓢(_, ℂ))) 2 volume) := by
  have hW := sobolevChain_fourier_weight_two f
  have h := sobolevChain_norm_iteratedFDeriv_fourierInv_le
    (k := 0) (j := 0) (m := 2) (𝓕 f).continuous.aestronglyMeasurable hW.1
    (by
      have : (n : ℝ) < 4 := by exact_mod_cast hn
      norm_num
      linarith) le_rfl x
  have hinv : 𝓕⁻ (⇑(𝓕 f : 𝓢(_, ℂ))) = ⇑f := by
    exact f.continuous.fourierInv_fourier_eq f.integrable (𝓕 f).integrable
  simp only [hinv, norm_iteratedFDeriv_zero, pow_zero, one_mul, Nat.cast_zero,
    sub_zero] at h
  apply h.trans
  calc
    _ ≤ lpNorm (fun y : EuclideanSpace ℝ (Fin n) => (1 + ‖y‖) ^ (-2 : ℝ)) 2 volume *
        (2 * (lpNorm f 2 volume + lpNorm (⇑(Δ f : 𝓢(_, ℂ))) 2 volume)) :=
      mul_le_mul_of_nonneg_left hW.2 lpNorm_nonneg
    _ = _ := by ring

lemma sobolevChain_laplacian_eq {n : ℕ} {u : EuclideanSpace ℝ (Fin n) → ℝ}
    (hu : ContDiff ℝ 2 u) (x : EuclideanSpace ℝ (Fin n)) :
    Δ u x = laplacianN u x := by
  rw [InnerProductSpace.laplacian_eq_iteratedFDeriv_orthonormalBasis u
    (EuclideanSpace.basisFun (Fin n) ℝ)]
  change (∑ i, _) = ∑ i, _
  apply Finset.sum_congr rfl
  intro i _
  rw [iteratedFDeriv_two_apply, poissonCoordinateDerivative_second hu]
  simp only [EuclideanSpace.basisFun_apply, Matrix.cons_val_zero, Matrix.cons_val_one]

lemma sobolevChain_laplacian_complex {n : ℕ} {u : EuclideanSpace ℝ (Fin n) → ℝ}
    (hu : ContDiff ℝ 2 u) (x : EuclideanSpace ℝ (Fin n)) :
    Δ (fun y => (u y : ℂ)) x = (laplacianN u x : ℂ) := by
  have h := hu.contDiffAt.laplacian_CLM_comp_left (l := Complex.ofRealCLM) (x := x)
  change Δ (fun y => (u y : ℂ)) x = (Δ u x : ℂ) at h
  rw [sobolevChain_laplacian_eq hu] at h
  exact h

lemma sobolevChain_laplacianN_sub {n : ℕ} {u v : EuclideanSpace ℝ (Fin n) → ℝ}
    (hu : ContDiff ℝ 2 u) (hv : ContDiff ℝ 2 v) :
    laplacianN (u - v) = laplacianN u - laplacianN v := by
  funext x
  calc
    laplacianN (u - v) x = Δ (u - v) x :=
      (sobolevChain_laplacian_eq (u := u - v) (hu.sub hv) x).symm
    _ = Δ u x - Δ v x := hu.contDiffAt.laplacian_sub hv.contDiffAt
    _ = _ := by rw [sobolevChain_laplacian_eq hu, sobolevChain_laplacian_eq hv]; rfl

/-- The canonical complex inclusion preserves the real Lᵖ seminorm. -/
lemma sobolevChain_lpNorm_complex {n : ℕ} {u : EuclideanSpace ℝ (Fin n) → ℝ}
    (hu : AEStronglyMeasurable u volume) (p : ℝ≥0∞) :
    lpNorm (fun x => (u x : ℂ)) p volume = lpNorm u p volume := by
  have hc := Complex.continuous_ofReal.comp_aestronglyMeasurable hu
  rw [← toReal_eLpNorm, ← toReal_eLpNorm]
  congr 1
  exact eLpNorm_congr_norm_ae hc hu (Filter.Eventually.of_forall fun x => Complex.norm_real (u x))

/-- The H² uniform estimate for real smooth compactly supported functions. -/
theorem sobolevChain_smooth_uniform_bound {n : ℕ} (hn : n < 4)
    {u : EuclideanSpace ℝ (Fin n) → ℝ} (hu : ContDiff ℝ (⊤ : ℕ∞) u)
    (hcu : HasCompactSupport u) (x : EuclideanSpace ℝ (Fin n)) :
    ‖u x‖ ≤ 2 * lpNorm (fun y : EuclideanSpace ℝ (Fin n) =>
      (1 + ‖y‖) ^ (-2 : ℝ)) 2 volume *
        (lpNorm u 2 volume + lpNorm (laplacianN u) 2 volume) := by
  have hc : HasCompactSupport (fun x => (u x : ℂ)) :=
    hcu.comp_left (g := Complex.ofReal) (by simp)
  have hd : ContDiff ℝ (⊤ : ℕ∞) (fun x => (u x : ℂ)) := Complex.ofRealCLM.contDiff.comp hu
  let f := hc.toSchwartzMap hd
  have hΔ : (⇑(Δ f : 𝓢(_, ℂ))) = fun x => (laplacianN u x : ℂ) := by
    funext y
    rw [SchwartzMap.laplacian_apply]
    exact sobolevChain_laplacian_complex (hu.of_le (by simp)) y
  have h := sobolevChain_schwartz_uniform_bound hn f x
  rw [hΔ] at h
  change ‖(u x : ℂ)‖ ≤ _ *
    (lpNorm (fun y => (u y : ℂ)) 2 volume +
      lpNorm (fun y => (laplacianN u y : ℂ)) 2 volume) at h
  simpa only [Complex.norm_real, sobolevChain_lpNorm_complex hu.continuous.aestronglyMeasurable,
    sobolevChain_lpNorm_complex
      (continuous_laplacianN (hu.of_le (by simp))).aestronglyMeasurable] using h

end LiquidDrop

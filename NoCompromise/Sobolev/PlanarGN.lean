import NoCompromise.Sobolev.H1Approximation
import NoCompromise.Sobolev.BV

/-!
# Whole-space planar H¹ to L⁴ estimate

The BV Sobolev inequality applied to squares gives the quantitative estimate
`‖f‖₄² ≤ 2 ‖f‖₂ ‖G‖₂` on the plane. Smooth bump approximations and Fatou
transfer the estimate to every function with an L² weak gradient. No boundary
extension theorem is assumed.
-/

noncomputable section

open MeasureTheory Filter Set
open scoped ENNReal NNReal Topology Gradient Convolution

namespace LiquidDrop

set_option maxSynthPendingDepth 8

/-- Cauchy–Schwarz for the integral of a scalar-vector product. -/
lemma integral_norm_smul_le_lpNorm_two_mul {α F : Type*} [MeasurableSpace α]
    [NormedAddCommGroup F] [NormedSpace ℝ F] {μ : Measure α}
    {f : α → ℝ} {G : α → F} (hf : MemLp f 2 μ) (hG : MemLp G 2 μ) :
    (∫ x, ‖f x • G x‖ ∂μ) ≤ lpNorm f 2 μ * lpNorm G 2 μ := by
  have hm : MemLp (f • G) 1 μ := hf.smul hG
  have h := ENNReal.toReal_mono (ENNReal.mul_ne_top hf.eLpNorm_ne_top hG.eLpNorm_ne_top)
    (eLpNorm_smul_le_mul_eLpNorm (p := 2) (q := 2) (r := 1) hf.aestronglyMeasurable
      hG.aestronglyMeasurable)
  simp only [ENNReal.toReal_mul, toReal_eLpNorm, toReal_eLpNorm,
    toReal_eLpNorm, lpNorm_one_eq_integral_norm hm.aestronglyMeasurable] at h
  exact h

/-- The L² norm of a real square is the square of the L⁴ norm, also at infinity. -/
lemma eLpNorm_sq_two {α : Type*} [MeasurableSpace α] {μ : Measure α} (f : α → ℝ)
    (hf : AEStronglyMeasurable f μ) :
    eLpNorm (fun x => f x ^ 2) 2 μ = eLpNorm f 4 μ ^ 2 := by
  have h := eLpNorm_norm_rpow (p := 2) (μ := μ) f hf (q := 2) (by norm_num)
  norm_num [Real.norm_eq_abs, sq_abs, Real.rpow_two, ENNReal.rpow_two] at h ⊢
  exact h

/-- A C¹ L² function with L² gradient has a BV square, with the product norm bound. -/
theorem isBVOn_sq_of_contDiff_memLp_two {n : ℕ}
    {f : EuclideanSpace ℝ (Fin n) → ℝ} (hc : ContDiff ℝ 1 f)
    (hf : MemLp f 2 volume) (hG : MemLp (gradient f) 2 volume) :
    IsBVOn (fun x => f x ^ 2) univ ∧
      variation (fun x => f x ^ 2) univ ≤
        ENNReal.ofReal (2 * lpNorm f 2 volume * lpNorm (gradient f) 2 volume) := by
  have heq : gradient (fun x => f x ^ 2) = fun x => (2 : ℝ) • (f x • gradient f x) := by
    funext x
    simpa only [pow_two, two_smul] using gradient_mul hc hc x
  have hi : Integrable (fun x => f x • gradient f x) :=
    memLp_one_iff_integrable.mp (hf.smul hG : MemLp (f • gradient f) 1 volume)
  have hgrad : Integrable (gradient (fun x => f x ^ 2)) := by
    rw [heq]
    exact Integrable.smul (2 : ℝ) hi
  have hb : (∫ x, ‖gradient (fun x => f x ^ 2) x‖) ≤
      2 * lpNorm f 2 volume * lpNorm (gradient f) 2 volume := by
    simp only [heq, norm_smul, Real.norm_ofNat]
    rw [integral_const_mul]
    simpa only [norm_smul] using
      (mul_le_mul_of_nonneg_left (integral_norm_smul_le_lpNorm_two_mul hf hG)
        (show (0 : ℝ) ≤ 2 by norm_num)).trans_eq (mul_assoc _ _ _).symm
  have hv := (variation_le_integral_norm_gradient (hc.pow 2) hgrad).trans
    (ENNReal.ofReal_le_ofReal hb)
  refine ⟨⟨?_, hv.trans_lt ENNReal.ofReal_lt_top⟩, hv⟩
  simp only [IntegrableOn, Measure.restrict_univ, pow_two]
  exact hf.integrable_mul hf

/-- The squared L⁴ estimate for smooth whole-space planar functions. -/
theorem eLpNorm_four_sq_le_of_contDiff {f : EuclideanSpace ℝ (Fin 2) → ℝ}
    (hc : ContDiff ℝ 1 f) (hf : MemLp f 2 volume)
    (hG : MemLp (gradient f) 2 volume) :
    eLpNorm f 4 volume ^ 2 ≤
      ENNReal.ofReal (2 * lpNorm f 2 volume * lpNorm (gradient f) 2 volume) := by
  obtain ⟨hbv, hv⟩ := isBVOn_sq_of_contDiff_memLp_two hc hf hG
  rw [← eLpNorm_sq_two f hc.continuous.aestronglyMeasurable]
  exact (bv_sobolev_two hbv).2.trans hv

/-- The planar Gagliardo–Nirenberg estimate for arbitrary whole-space H¹ functions,
in squared extended-norm form. -/
theorem HasH1GradientOn.eLpNorm_four_sq_le {f : EuclideanSpace ℝ (Fin 2) → ℝ}
    {G : EuclideanSpace ℝ (Fin 2) → EuclideanSpace ℝ (Fin 2)}
    (hf : HasH1GradientOn f G univ) :
    eLpNorm f 4 volume ^ 2 ≤ ENNReal.ofReal (2 * lpNorm f 2 volume * lpNorm G 2 volume) := by
  have hmf : MemLp f 2 volume := by
    simpa only [Measure.restrict_univ] using hf.memLp_function
  have hmG : MemLp G 2 volume := by
    simpa only [Measure.restrict_univ] using hf.memLp_gradient
  let φ (j : ℕ) : ContDiffBump (0 : EuclideanSpace ℝ (Fin 2)) :=
    ⟨(1 / ((j : ℝ) + 1)) / 2, 1 / ((j : ℝ) + 1),
      by positivity, half_lt_self (by positivity)⟩
  have hφ : Tendsto (fun j => (φ j).rOut) atTop (𝓝 0) :=
    tendsto_one_div_add_atTop_nhds_zero_nat (𝕜 := ℝ)
  let u (j : ℕ) := (φ j).normed volume ⋆[ContinuousLinearMap.lsmul ℝ ℝ] f
  have hu (j : ℕ) : MemLp (u j) 2 volume := by
    simpa only [Measure.restrict_univ] using
      (hf.bump_convolution (φ j)).2.2.1.memLp_function
  have hgrad (j : ℕ) : MemLp (gradient (u j)) 2 volume := by
    have h := (hf.bump_convolution (φ j)).2.2.1.memLp_gradient
    simp only [Measure.restrict_univ] at h
    have heq : gradient (u j) = (φ j).normed volume ⋆[ContinuousLinearMap.lsmul ℝ ℝ] G :=
      funext (hf.bump_convolution (φ j)).2.1
    rw [heq]
    exact h
  have huf (j : ℕ) : lpNorm (u j) 2 volume ≤ lpNorm f 2 volume := by
    have h := ENNReal.toReal_mono hmf.eLpNorm_ne_top (hf.bump_convolution (φ j)).2.2.2.1
    change (eLpNorm (u j) 2 volume).toReal ≤ (eLpNorm f 2 volume).toReal at h
    simpa only [toReal_eLpNorm, toReal_eLpNorm] using h
  have huG (j : ℕ) : lpNorm (gradient (u j)) 2 volume ≤ lpNorm G 2 volume := by
    have heq : gradient (u j) = (φ j).normed volume ⋆[ContinuousLinearMap.lsmul ℝ ℝ] G :=
      funext (hf.bump_convolution (φ j)).2.1
    have h := (hf.bump_convolution (φ j)).2.2.2.2
    rw [← heq] at h
    have h' := ENNReal.toReal_mono hmG.eLpNorm_ne_top h
    simpa only [toReal_eLpNorm, toReal_eLpNorm] using h'
  have hb (j : ℕ) : eLpNorm (fun x => u j x ^ 2) 2 volume ≤
      ENNReal.ofReal (2 * lpNorm f 2 volume * lpNorm G 2 volume) := by
    rw [eLpNorm_sq_two _ (hu j).aestronglyMeasurable]
    apply (eLpNorm_four_sq_le_of_contDiff
      ((hf.bump_convolution (φ j)).1.of_le (by simp)) (hu j) (hgrad j)).trans
    apply ENNReal.ofReal_le_ofReal
    exact mul_le_mul (mul_le_mul_of_nonneg_left (huf j) (by norm_num))
      (huG j) lpNorm_nonneg (mul_nonneg (by norm_num) lpNorm_nonneg)
  have ht : Tendsto (fun j => eLpNorm (u j - f) 2 volume) atTop (𝓝 0) :=
    tendsto_eLpNorm_bump_convolution_sub hmf hφ
  obtain ⟨σ, hσ, hae⟩ := (tendstoInMeasure_of_tendsto_eLpNorm (by norm_num : (2 : ℝ≥0∞) ≠ 0)
    ht).exists_seq_tendsto_ae
  have hsq : ∀ᵐ x ∂volume, Tendsto (fun j => u (σ j) x ^ 2) atTop (𝓝 (f x ^ 2)) := by
    filter_upwards [hae] with x hx
    exact hx.pow 2
  have hfatou := Lp.eLpNorm_lim_le_liminf_eLpNorm
    (fun j => (hu (σ j)).aestronglyMeasurable.pow 2) (fun x => f x ^ 2)
    (hmf.aestronglyMeasurable.pow 2) hsq (p := 2)
  rw [eLpNorm_sq_two f hmf.aestronglyMeasurable] at hfatou
  exact hfatou.trans ((liminf_le_liminf (Eventually.of_forall fun j => hb (σ j))).trans_eq
    tendsto_const_nhds.liminf_eq)

/-- Every whole-space planar H¹ function belongs to L⁴. -/
theorem HasH1GradientOn.memLp_four {f : EuclideanSpace ℝ (Fin 2) → ℝ}
    {G : EuclideanSpace ℝ (Fin 2) → EuclideanSpace ℝ (Fin 2)}
    (hf : HasH1GradientOn f G univ) : MemLp f 4 volume := by
  have hmf : MemLp f 2 volume := by
    simpa only [Measure.restrict_univ] using hf.memLp_function
  exact (ENNReal.pow_lt_top_iff.mp
    (hf.eLpNorm_four_sq_le.trans_lt ENNReal.ofReal_lt_top)).resolve_right (by decide)

/-- Quantitative whole-space planar Gagliardo–Nirenberg, in ordinary squared norms. -/
theorem HasH1GradientOn.lpNorm_four_sq_le {f : EuclideanSpace ℝ (Fin 2) → ℝ}
    {G : EuclideanSpace ℝ (Fin 2) → EuclideanSpace ℝ (Fin 2)}
    (hf : HasH1GradientOn f G univ) :
    lpNorm f 4 volume ^ 2 ≤ 2 * lpNorm f 2 volume * lpNorm G 2 volume := by
  have h := ENNReal.toReal_mono ENNReal.ofReal_ne_top hf.eLpNorm_four_sq_le
  rwa [ENNReal.toReal_pow, toReal_eLpNorm,
    ENNReal.toReal_ofReal (mul_nonneg (mul_nonneg (by norm_num) lpNorm_nonneg)
      lpNorm_nonneg)] at h

/-- The planar whole-space L⁴ norm is bounded by the sum of the H¹ component norms. -/
theorem HasH1GradientOn.lpNorm_four_le {f : EuclideanSpace ℝ (Fin 2) → ℝ}
    {G : EuclideanSpace ℝ (Fin 2) → EuclideanSpace ℝ (Fin 2)}
    (hf : HasH1GradientOn f G univ) :
    lpNorm f 4 volume ≤ lpNorm f 2 volume + lpNorm G 2 volume := by
  have h := hf.lpNorm_four_sq_le
  have hf0 : 0 ≤ lpNorm f 2 volume := lpNorm_nonneg
  have hG0 : 0 ≤ lpNorm G 2 volume := lpNorm_nonneg
  have h40 : 0 ≤ lpNorm f 4 volume := lpNorm_nonneg
  nlinarith [sq_nonneg (lpNorm f 2 volume), sq_nonneg (lpNorm G 2 volume)]

/-- Gradient-free membership form of the whole-space planar embedding. -/
theorem IsH1On.memLp_four {f : EuclideanSpace ℝ (Fin 2) → ℝ}
    (hf : IsH1On f univ) : MemLp f 4 volume := by
  obtain ⟨G, hG⟩ := hf
  exact hG.memLp_four

/-- A quantitative extension hypothesis transfers the whole-space estimate to a domain.
This corollary does not assert the existence of an H¹ extension operator. -/
theorem planar_gn_of_h1_extension {U : Set (EuclideanSpace ℝ (Fin 2))}
    {f : EuclideanSpace ℝ (Fin 2) → ℝ}
    {G : EuclideanSpace ℝ (Fin 2) → EuclideanSpace ℝ (Fin 2)} {C : ℝ}
    (hE : ∃ F H, HasH1GradientOn F H univ ∧ F =ᵐ[volume.restrict U] f ∧
      lpNorm F 2 volume + lpNorm H 2 volume ≤
        C * (lpNorm f 2 (volume.restrict U) + lpNorm G 2 (volume.restrict U))) :
    MemLp f 4 (volume.restrict U) ∧
      lpNorm f 4 (volume.restrict U) ≤
        C * (lpNorm f 2 (volume.restrict U) + lpNorm G 2 (volume.restrict U)) := by
  obtain ⟨F, H, hF, heq, hb⟩ := hE
  have hm : MemLp F 4 (volume.restrict U) := hF.memLp_four.mono_measure Measure.restrict_le_self
  have hmf : MemLp f 4 (volume.restrict U) := hm.ae_eq heq
  refine ⟨hmf, ?_⟩
  have hle : lpNorm f 4 (volume.restrict U) ≤ lpNorm F 4 volume := by
    rw [← toReal_eLpNorm, ← toReal_eLpNorm,
      ← eLpNorm_congr_ae heq]
    exact ENNReal.toReal_mono hF.memLp_four.eLpNorm_ne_top
      (eLpNorm_mono_measure F Measure.restrict_le_self)
  exact hle.trans (hF.lpNorm_four_le.trans hb)

end LiquidDrop

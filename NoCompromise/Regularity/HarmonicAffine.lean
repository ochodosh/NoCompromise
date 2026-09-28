import NoCompromise.Elliptic.HarmonicDerivative
import NoCompromise.Elliptic.HolderInterpolationGeometry
import Mathlib.MeasureTheory.Measure.Lebesgue.VolumeOfBalls

/-!
# Affine approximation of planar harmonic functions

The constant is chosen before the scale and the harmonic function. The extended
integral statement allows infinite Dirichlet energy on the outer open ball;
the real integral statement records the finite-energy case explicitly.
-/

noncomputable section
open MeasureTheory Metric Set InnerProductSpace
open scoped ENNReal NNReal Topology Gradient RealInnerProductSpace
namespace LiquidDrop
local notation "P" => EuclideanSpace ℝ (Fin 2)

/-- Taylor's remainder on a smaller concentric ball, using an actual Hessian bound. -/
lemma harmonicAffine_taylor_bound {h : P → ℝ} {s R M : ℝ}
    (hh : ContDiffOn ℝ 2 h (ball 0 R)) (hs : 0 < s) (hsR : s ≤ R) (hM : 0 ≤ M)
    (hb : ∀ x ∈ ball 0 R, ‖fderiv ℝ (fderiv ℝ h) x‖ ≤ M)
    {x : P} (hx : x ∈ ball 0 s) :
    ‖h x - h 0 - inner ℝ (gradient h 0) x‖ ≤ M * s ^ 2 := by
  have hsub : ball (0 : P) s ⊆ ball 0 R := ball_subset_ball hsR
  have h0 : (0 : P) ∈ ball 0 s := mem_ball_self hs
  have hd (y : P) (hy : y ∈ ball 0 s) : DifferentiableAt ℝ h y :=
    ((hh y (hsub hy)).contDiffAt (isOpen_ball.mem_nhds (hsub hy))).differentiableAt
      (by norm_num)
  have hb' (y : P) (hy : y ∈ ball 0 s) :
      ‖fderiv ℝ h y - fderiv ℝ h 0‖ ≤ M * s := by
    have ht := holderInterpolation_fderiv_sub_le hh hb (hsub h0) (hsub hy)
    simp only [sub_zero] at ht
    exact ht.trans (mul_le_mul_of_nonneg_left (mem_ball_zero_iff.mp hy).le hM)
  have ht := (convex_ball (0 : P) s).norm_image_sub_le_of_norm_fderiv_le'
    hd hb' h0 hx
  rw [sub_zero, ← inner_gradient_left] at ht
  exact ht.trans ((mul_le_mul_of_nonneg_left (mem_ball_zero_iff.mp hx).le
    (mul_nonneg hM hs.le)).trans_eq (by ring))

/-- The scale-independent pointwise estimate preceding the integral affine estimate. -/
theorem harmonic_affine_pointwise :
    ∃ C > 0, ∀ (h : P → ℝ),
      HasDistributionalLaplacianOn h (fun _ => 0) (ball 0 (1 / 4)) →
      ContinuousOn h (ball 0 (1 / 4)) →
      MemLp (gradient h) 2 (volume.restrict (ball 0 (1 / 4))) →
      ∀ θ : ℝ, 0 < θ → θ < 1 / 32 → ∀ x ∈ ball 0 (4 * θ),
        ‖h x - h 0 - inner ℝ (gradient h 0) x‖ ≤
          C * θ ^ 2 * lpNorm (gradient h) 2 (volume.restrict (ball 0 (1 / 4))) := by
  obtain ⟨C, hC, hb⟩ := harmonic_derivative_gradient_l2_bound (n := 2) (k := 1)
    (by norm_num) (by norm_num : (1 / 8 : ℝ) < 1 / 4)
  refine ⟨16 * C, by positivity, fun h hh hc hm θ hθ hθ' x hx => ?_⟩
  have hs := hh.contDiffOn_of_continuous (by norm_num : 2 < 4) isOpen_ball hc
  have hb' (y : P) (hy : y ∈ ball 0 (1 / 8)) :
      ‖fderiv ℝ (fderiv ℝ h) y‖ ≤
        C * lpNorm (gradient h) 2 (volume.restrict (ball 0 (1 / 4))) := by
    rw [← norm_iteratedFDeriv_one (fderiv ℝ h), norm_iteratedFDeriv_fderiv]
    exact hb 0 h hh hm hs y hy
  have ht := harmonicAffine_taylor_bound
    ((hs.mono (ball_subset_ball (by norm_num : (1 / 8 : ℝ) ≤ 1 / 4))).of_le
      (by norm_num)) (by positivity : 0 < 4 * θ) (by linarith : 4 * θ ≤ 1 / 8)
    (mul_nonneg hC.le lpNorm_nonneg) hb' hx
  convert ht using 1
  ring

/-- The real-integral affine approximation, with the finite outer energy made explicit. -/
theorem harmonic_affine_integral :
    ∃ C > 0, ∀ (h : P → ℝ),
      HasDistributionalLaplacianOn h (fun _ => 0) (ball 0 (1 / 4)) →
      ContinuousOn h (ball 0 (1 / 4)) →
      MemLp (gradient h) 2 (volume.restrict (ball 0 (1 / 4))) →
      ∀ θ : ℝ, 0 < θ → θ < 1 / 32 →
        (∫ x in ball 0 (4 * θ), ‖h x - h 0 - inner ℝ (gradient h 0) x‖ ^ 2) ≤
          C * θ ^ 6 * ∫ x in ball 0 (1 / 4), ‖gradient h x‖ ^ 2 := by
  obtain ⟨C, hC, hb⟩ := harmonic_affine_pointwise
  refine ⟨16 * Real.pi * C ^ 2, by positivity, fun h hh hc hm θ hθ hθ' => ?_⟩
  let L := lpNorm (gradient h) 2 (volume.restrict (ball 0 (1 / 4)))
  have hL : 0 ≤ L := lpNorm_nonneg
  have ht := norm_setIntegral_le_of_norm_le_const (μ := volume)
    (f := fun x => ‖h x - h 0 - inner ℝ (gradient h 0) x‖ ^ 2)
    (s := ball 0 (4 * θ)) isBounded_ball.measure_lt_top
    (fun x hx => show ‖‖h x - h 0 - inner ℝ (gradient h 0) x‖ ^ 2‖ ≤
      (C * θ ^ 2 * L) ^ 2 by
      rw [Real.norm_of_nonneg (sq_nonneg _)]
      exact pow_le_pow_left₀ (norm_nonneg _) (hb h hh hc hm θ hθ hθ' x hx) 2)
  have hv : volume.real (ball (0 : P) (4 * θ)) = Real.pi * (4 * θ) ^ 2 := by
    simp only [Measure.real, EuclideanSpace.volume_ball_fin_two, ENNReal.toReal_mul,
      ENNReal.toReal_pow, ENNReal.toReal_ofReal (by positivity : 0 ≤ 4 * θ),
      ENNReal.toReal_ofReal Real.pi_pos.le]
    ring
  rw [hv] at ht
  calc
    _ ≤ ‖∫ x in ball 0 (4 * θ), ‖h x - h 0 - inner ℝ (gradient h 0) x‖ ^ 2‖ :=
      le_abs_self _
    _ ≤ _ := ht
    _ = _ := by rw [← lpNorm_two_sq_eq_integral_norm_sq hm]; dsimp [L]; ring

/-- The squared remainder is genuinely integrable on every strictly smaller disk. -/
lemma harmonicAffine_integrable_remainder {h : P → ℝ}
    (hc : ContinuousOn h (ball 0 (1 / 4))) {θ : ℝ} (hθ : θ < 1 / 32) :
    IntegrableOn (fun x => ‖h x - h 0 - inner ℝ (gradient h 0) x‖ ^ 2)
      (ball 0 (4 * θ)) volume := by
  have hsub : closedBall (0 : P) (4 * θ) ⊆ ball 0 (1 / 4) :=
    closedBall_subset_ball (by linarith)
  have ht : ContinuousOn
      (fun x => ‖h x - h 0 - inner ℝ (gradient h 0) x‖ ^ 2)
      (closedBall 0 (4 * θ)) :=
    (((hc.mono hsub).sub continuousOn_const).sub
      (continuous_const.inner continuous_id).continuousOn).norm.pow 2
  exact (ht.integrableOn_compact (isCompact_closedBall _ _)).mono_set ball_subset_closedBall

/-- Blueprint `lem:harmonic-affine`, including the possibly infinite-energy case.
Harmonicity is distributional and continuity selects its actual smooth representative. -/
theorem harmonic_affine :
    ∃ C > 0, ∀ (h : P → ℝ),
      HasDistributionalLaplacianOn h (fun _ => 0) (ball 0 (1 / 4)) →
      ContinuousOn h (ball 0 (1 / 4)) → ∀ θ : ℝ, 0 < θ → θ < 1 / 32 →
        (∫⁻ x in ball 0 (4 * θ),
          ENNReal.ofReal (‖h x - h 0 - inner ℝ (gradient h 0) x‖ ^ 2)) ≤
          ENNReal.ofReal (C * θ ^ 6) *
            ∫⁻ x in ball 0 (1 / 4), ENNReal.ofReal (‖gradient h x‖ ^ 2) := by
  obtain ⟨C, hC, hb⟩ := harmonic_affine_integral
  refine ⟨C, hC, fun h hh hc θ hθ hθ' => ?_⟩
  by_cases hfin : (∫⁻ x in ball 0 (1 / 4), ENNReal.ofReal (‖gradient h x‖ ^ 2)) = ∞
  · rw [hfin, ENNReal.mul_top (ENNReal.ofReal_ne_zero_iff.mpr (by positivity))]
    exact le_top
  have hs := hh.contDiffOn_of_continuous (by norm_num : 2 < 4) isOpen_ball hc
  have hm : AEStronglyMeasurable (gradient h) (volume.restrict (ball 0 (1 / 4))) :=
    (harmonicDerivative_contDiffOn_gradient isOpen_ball hs).continuousOn
      |>.aestronglyMeasurable isOpen_ball.measurableSet
  have hi : IntegrableOn (fun x => ‖gradient h x‖ ^ 2) (ball 0 (1 / 4)) volume :=
    (lintegral_ofReal_ne_top_iff_integrable (hm.norm.pow 2)
      (Filter.Eventually.of_forall fun _ => sq_nonneg _)).mp hfin
  have hL := (memLp_two_iff_integrable_sq_norm hm).mpr hi
  have ht := ENNReal.ofReal_le_ofReal (hb h hh hc hL θ hθ hθ')
  rw [ofReal_integral_eq_lintegral_ofReal (harmonicAffine_integrable_remainder hc hθ')
    (Filter.Eventually.of_forall fun _ => sq_nonneg _),
    ENNReal.ofReal_mul (by positivity : 0 ≤ C * θ ^ 6),
    ofReal_integral_eq_lintegral_ofReal hi
      (Filter.Eventually.of_forall fun _ => sq_nonneg _)] at ht
  exact ht

end LiquidDrop

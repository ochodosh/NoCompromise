import NoCompromise.Regularity.TangentDilationTests
import NoCompromise.Regularity.TangentRadialGlobal
import Mathlib.Analysis.Distribution.AEEqOfIntegralContDiff

/-!
# Dilation invariance from the actual radial distributional identity

Every compact C¹ test has constant pairing along the exponential dilation flow.
Smooth-test uniqueness for locally integrable indicators then gives equality
modulo Lebesgue-null sets. No transport or cone-invariance premise is imposed.
-/

noncomputable section
open MeasureTheory Set Filter Metric InnerProductSpace
open scoped Topology ENNReal RealInnerProductSpace Pointwise
namespace LiquidDrop
set_option maxSynthPendingDepth 8

lemma tangent_dilation_test_integral_eq (F : Set AmbientSpace)
    (hrad : ∀ φ : AmbientSpace → ℝ, ContDiff ℝ 1 φ → HasCompactSupport φ →
      (∫ y in F, divergenceN (fun z => φ z • z) y) = 0)
    {φ : AmbientSpace → ℝ} (hφ : ContDiff ℝ 1 φ) (hcφ : HasCompactSupport φ) (t : ℝ) :
    (∫ y in F, Real.exp (3 * t) * φ (Real.exp t • y)) = ∫ y in F, φ y := by
  let J : ℝ → ℝ := fun s => ∫ y in F, Real.exp (3 * s) * φ (Real.exp s • y)
  have hJ (s : ℝ) : HasDerivAt J 0 s := by
    have hd := tangent_hasDerivAt_dilation_integral F hφ hcφ s
    have hψ : ContDiff ℝ 1 (fun y => φ (Real.exp s • y)) :=
      hφ.comp (contDiff_id.const_smul (Real.exp s))
    have hcψ : HasCompactSupport (fun y => φ (Real.exp s • y)) :=
      hcφ.comp_homeomorph (Homeomorph.smulOfNeZero (Real.exp s) (Real.exp_pos s).ne')
    have hz := hrad _ hψ hcψ
    simp_rw [divergenceN_radial_comp_pos_smul φ (Real.exp_pos s)] at hz
    simpa only [integral_const_mul, hz, mul_zero, J] using hd
  have hc := is_const_of_deriv_eq_zero (fun s => (hJ s).differentiableAt)
    (fun s => (hJ s).deriv) t 0
  simpa only [J, mul_zero, Real.exp_zero, one_smul, one_mul] using hc

lemma tangent_integral_dilation_image_eq (F : Set AmbientSpace)
    (hrad : ∀ φ : AmbientSpace → ℝ, ContDiff ℝ 1 φ → HasCompactSupport φ →
      (∫ y in F, divergenceN (fun z => φ z • z) y) = 0)
    {φ : AmbientSpace → ℝ} (hφ : ContDiff ℝ 1 φ) (hcφ : HasCompactSupport φ) (t : ℝ) :
    (∫ y in (fun z => Real.exp t • z) '' F, φ y) = ∫ y in F, φ y := by
  rw [setIntegral_image_smul _ _ (Real.exp_pos t)]
  have h := tangent_dilation_test_integral_eq F hrad hφ hcφ t
  rw [integral_const_mul] at h
  rw [← Real.exp_nat_mul]
  simpa only [Nat.cast_ofNat] using h

/-- Vanishing radial distributional derivative gives genuine AE dilation invariance. -/
theorem tangent_dilation_ae_eq_of_radial_pairing {F : Set AmbientSpace}
    (hmF : NullMeasurableSet F volume)
    (hrad : ∀ φ : AmbientSpace → ℝ, ContDiff ℝ 1 φ → HasCompactSupport φ →
      (∫ y in F, divergenceN (fun z => φ z • z) y) = 0) (t : ℝ) :
    ((fun y => Real.exp t • y) '' F : Set AmbientSpace) =ᵐ[volume] F := by
  let D : Set AmbientSpace := (fun y => Real.exp t • y) '' F
  have hmD : NullMeasurableSet D volume :=
    MeasureTheory.Measure.NullMeasurableSet.const_smul hmF (Real.exp t)
  have hpair : D.indicator (fun _ => (1 : ℝ)) =ᵐ[volume] F.indicator (fun _ => (1 : ℝ)) := by
    apply ae_eq_of_integral_contDiff_smul_eq
      (locallyIntegrable_indicator_one hmD) (locallyIntegrable_indicator_one hmF)
    intro φ hφ hcφ
    have hφ1 : ContDiff ℝ 1 φ := hφ.of_le (by simp)
    have he (G : Set AmbientSpace) :
        (fun y => φ y • G.indicator (fun _ => (1 : ℝ)) y) = G.indicator φ := by
      funext y
      by_cases hy : y ∈ G <;> simp [hy, smul_eq_mul]
    rw [he D, he F, integral_indicator₀ hmD, integral_indicator₀ hmF]
    exact tangent_integral_dilation_image_eq F hrad hφ1 hcφ t
  filter_upwards [hpair] with y hy
  change (y ∈ D) = (y ∈ F)
  by_cases hyD : y ∈ D <;> by_cases hyF : y ∈ F <;> simp [hyD, hyF] at hy ⊢

end LiquidDrop

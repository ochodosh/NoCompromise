module

public import NoCompromise.Sobolev.H1PositivePartTests
public import NoCompromise.Sobolev.PlanarGN

@[expose] public section

/-!
# Bounded-domain coercivity for the positive-part argument

Coordinate integration by parts gives an H¹₀ Poincaré inequality on every
bounded open Euclidean set in positive dimension. No boundary regularity or
connectedness is required.
-/

noncomputable section
open MeasureTheory Filter Set InnerProductSpace
open scoped ENNReal NNReal Topology Gradient RealInnerProductSpace
namespace LiquidDrop
set_option maxSynthPendingDepth 8

lemma integral_sq_eq_neg_twice_coordinate_gradient {n : ℕ}
    {D : Set (EuclideanSpace ℝ (Fin n))} (hD : IsOpen D)
    (f : h1ZeroTestFunctions D) (i : Fin n) :
    (∫ x in D, f.val x ^ 2) =
      -2 * ∫ x in D, f.val x * x i * gradient f.val x i := by
  have hf : ContDiff ℝ 1 f.val := f.property.1.of_le (by simp)
  have hcoord : ContDiff ℝ 1 (fun x : EuclideanSpace ℝ (Fin n) => x i) :=
    by fun_prop
  have hφ : ContDiff ℝ 1 (fun x => x i * f.val x) := hcoord.mul hf
  have hcφ : HasCompactSupport (fun x => x i * f.val x) := f.property.2.1.mul_left
  have hsφ : tsupport (fun x => x i * f.val x) ⊆ D :=
    tsupport_mul_subset_right.trans f.property.2.2
  have hd (x : EuclideanSpace ℝ (Fin n)) :
      fderiv ℝ (fun y => y i * f.val y) x (EuclideanSpace.single i 1) =
        f.val x + x i * gradient f.val x i := by
    have hp := ((EuclideanSpace.proj i).hasFDerivAt (x := x)).mul
      ((hf.differentiable one_ne_zero x).hasFDerivAt)
    change HasFDerivAt (fun y => y i * f.val y) _ x at hp
    rw [hp.fderiv]
    simp [EuclideanSpace.proj, smul_eq_mul, gradient_apply_eq_fderiv_single, add_comm]
  have hG : Continuous (gradient f.val) := continuous_gradient_of_contDiff hf
  have hI : IntegrableOn (fun x => f.val x * x i * gradient f.val x i) D :=
    ((hf.continuous.mul hcoord.continuous).mul
      ((EuclideanSpace.proj i).continuous.comp hG)).integrable_of_hasCompactSupport
        f.property.2.1.mul_right.mul_right |>.integrableOn
  have hsq : IntegrableOn (fun x => f.val x ^ 2) D :=
    (h1ZeroTestFunctions.hasH1GradientOn f hD).memLp_function.integrable_sq
  have hw := (h1ZeroTestFunctions.hasH1GradientOn f hD).test_eq i _ hφ hcφ hsφ
  simp_rw [hd] at hw
  have he (x : EuclideanSpace ℝ (Fin n)) :
      f.val x * (f.val x + x i * gradient f.val x i) =
        f.val x ^ 2 + f.val x * x i * gradient f.val x i := by ring
  simp_rw [he] at hw
  rw [integral_add hsq hI] at hw
  have hr : (∫ x in D, x i * f.val x * gradient f.val x i) =
      ∫ x in D, f.val x * x i * gradient f.val x i := by
    apply integral_congr_ae
    exact Eventually.of_forall fun x => by ring
  rw [hr] at hw
  linarith

lemma h1ZeroTestFunctions.poincare_bounded_coordinate {n : ℕ}
    {D : Set (EuclideanSpace ℝ (Fin n))} (hD : IsOpen D) (i : Fin n)
    {R : ℝ} (hR : 0 ≤ R) (hbound : ∀ x ∈ D, ‖x‖ ≤ R)
    (f : h1ZeroTestFunctions D) :
    ‖(h1ZeroTestFunctions.toH1Space hD f).toLp‖ ≤
      (2 * R) * ‖(h1ZeroTestFunctions.toH1Space hD f).gradientLp‖ := by
  have hH := h1ZeroTestFunctions.hasH1GradientOn f hD
  have hf : ContDiff ℝ 1 f.val := f.property.1.of_le (by simp)
  have hcoord : Continuous (fun x : EuclideanSpace ℝ (Fin n) => x i) :=
    (EuclideanSpace.proj i).continuous
  have hG : Continuous (gradient f.val) := continuous_gradient_of_contDiff hf
  have hI : IntegrableOn (fun x => f.val x * x i * gradient f.val x i) D :=
    ((hf.continuous.mul hcoord).mul ((EuclideanSpace.proj i).continuous.comp hG)
      ).integrable_of_hasCompactSupport f.property.2.1.mul_right.mul_right |>.integrableOn
  have hb : |∫ x in D, f.val x * x i * gradient f.val x i| ≤
      R * (lpNorm f.val 2 (volume.restrict D) *
        lpNorm (gradient f.val) 2 (volume.restrict D)) := by
    calc
      _ ≤ ∫ x in D, ‖f.val x * x i * gradient f.val x i‖ := abs_integral_le_integral_abs
      _ ≤ ∫ x in D, R * (‖f.val x‖ * ‖gradient f.val x‖) := by
        apply integral_mono_ae hI.norm
          ((hH.memLp_function.norm.integrable_mul hH.memLp_gradient.norm).const_mul R)
        filter_upwards [ae_restrict_mem hD.measurableSet] with x hx
        simp only [norm_mul]
        have hxR := (PiLp.norm_apply_le x i).trans (hbound x hx)
        have hgi := PiLp.norm_apply_le (gradient f.val x) i
        calc
          _ ≤ ‖f.val x‖ * R * ‖gradient f.val x‖ := by gcongr
          _ = _ := by simp only [Pi.mul_apply]; ring
      _ = R * ∫ x in D, ‖f.val x • gradient f.val x‖ := by
        simp_rw [norm_smul]
        rw [integral_const_mul]
      _ ≤ _ := mul_le_mul_of_nonneg_left
        (integral_norm_smul_le_lpNorm_two_mul hH.memLp_function hH.memLp_gradient) hR
  have he := integral_sq_eq_neg_twice_coordinate_gradient hD f i
  have hnorm := lpNorm_two_sq_eq_integral_norm_sq hH.memLp_function
  simp only [Real.norm_eq_abs, sq_abs] at hnorm
  have henergy : lpNorm f.val 2 (volume.restrict D) ^ 2 ≤
      (2 * R) * lpNorm f.val 2 (volume.restrict D) *
        lpNorm (gradient f.val) 2 (volume.restrict D) := by
    rw [hnorm, he]
    have h := neg_le_abs (∫ x in D, f.val x * x i * gradient f.val x i)
    nlinarith only [hb, h]
  change ‖hH.memLp_function.toLp f.val‖ ≤ (2 * R) *
    ‖hH.memLp_gradient.toLp (gradient f.val)‖
  rw [Lp.norm_toLp, Lp.norm_toLp, toReal_eLpNorm,
    toReal_eLpNorm]
  by_cases hz : lpNorm f.val 2 (volume.restrict D) = 0
  · rw [hz]
    exact mul_nonneg (mul_nonneg (by norm_num) hR) lpNorm_nonneg
  · have hp : 0 < lpNorm f.val 2 (volume.restrict D) :=
      lt_of_le_of_ne lpNorm_nonneg (Ne.symm hz)
    nlinarith only [henergy, hp]

/-- Elementary coordinate integration by parts proves H¹₀ Poincaré in every
positive dimension, on arbitrary bounded open sets. -/
theorem H1ZeroSpace.poincare_bounded {n : ℕ} (hn : 0 < n)
    {D : Set (EuclideanSpace ℝ (Fin n))} (hD : IsOpen D) (hbD : Bornology.IsBounded D) :
    ∃ C > 0, ∀ u : H1ZeroSpace hD, ‖u.val.toLp‖ ≤ C * ‖u.val.gradientLp‖ := by
  obtain ⟨R, hR, hb⟩ := hbD.exists_pos_norm_le
  refine ⟨2 * R, by positivity, ?_⟩
  intro u
  have hclosed : IsClosed {v : H1Space D | ‖v.toLp‖ ≤ (2 * R) * ‖v.gradientLp‖} :=
    isClosed_le H1Space.toLpCLM.continuous.norm
      (continuous_const.mul H1Space.gradientCLM.continuous.norm)
  apply closure_minimal
    (s := ((h1ZeroTestFunctions.toH1Space hD).range : Set (H1Space D)))
    (t := {v | ‖v.toLp‖ ≤ (2 * R) * ‖v.gradientLp‖}) ?_ hclosed u.property
  rintro v ⟨f, rfl⟩
  exact h1ZeroTestFunctions.poincare_bounded_coordinate hD ⟨0, hn⟩ hR.le hb f

end LiquidDrop

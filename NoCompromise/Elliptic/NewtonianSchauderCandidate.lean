module

public import NoCompromise.Elliptic.NewtonianSchauderFar
public import NoCompromise.Elliptic.NewtonianSchauderDistribution

@[expose] public section

/-!
# The compensated Newtonian Hessian integral

A Hölder increment makes the near part absolutely integrable. Radial cancellation
shows that the sum of the near and far integrals does not depend on the cutoff
scale. The distributional diagonal correction is kept explicitly.
-/

noncomputable section
open MeasureTheory Filter Metric Set InnerProductSpace
open scoped NNReal ENNReal Topology Gradient RealInnerProductSpace
namespace LiquidDrop
set_option maxSynthPendingDepth 8
local notation "E₃" => EuclideanSpace ℝ (Fin 3)

lemma integral_schauderNewtonHessianEntry_radial_zero {ψ : E₃ → ℝ}
    (hψ : ∀ (e : E₃ ≃ₗᵢ[ℝ] E₃) x, ψ (e x) = ψ x)
    (hi : ∀ i j, Integrable (fun x => schauderNewtonHessianEntry i j x * ψ x))
    (i j : Fin 3) : (∫ x, schauderNewtonHessianEntry i j x * ψ x) = 0 := by
  by_cases hij : i = j
  · subst j
    have he (j : Fin 3) : (∫ x, schauderNewtonHessianEntry j j x * ψ x) =
        ∫ x, schauderNewtonHessianEntry i i x * ψ x := by
      let e : E₃ ≃ₗᵢ[ℝ] E₃ := LinearIsometryEquiv.piLpCongrLeft 2 ℝ ℝ (Equiv.swap j i)
      have hx (x : E₃) : e x j = x i := by
        change x ((Equiv.swap j i).symm j) = x i
        simp
      have h := e.measurePreserving.integral_comp e.toHomeomorph.measurableEmbedding
        (fun x => schauderNewtonHessianEntry j j x * ψ x)
      simpa only [schauderNewtonHessianEntry_eq, ite_true, e.norm_map, hx, hψ] using h.symm
    have hs : (∑ j : Fin 3, ∫ x, schauderNewtonHessianEntry j j x * ψ x) = 0 := by
      rw [← integral_finsetSum _ (fun j _ => hi j j)]
      simp_rw [← Finset.sum_mul, schauderNewtonHessianEntry_trace, zero_mul, integral_zero]
    simp only [Fin.sum_univ_three, he] at hs
    linarith
  · have he (x : E₃) : schauderNewtonHessianEntry i j (coordinateReflection i x) *
        ψ (coordinateReflection i x) = -(schauderNewtonHessianEntry i j x * ψ x) := by
      simp [schauderNewtonHessianEntry_eq, hij, Ne.symm hij, hψ,
        (coordinateReflection i).norm_map, coordinateReflection_apply]
    have h := (coordinateReflection i).measurePreserving.integral_comp
      (coordinateReflection i).toHomeomorph.measurableEmbedding
      (fun x => schauderNewtonHessianEntry i j x * ψ x)
    simp_rw [he, integral_neg] at h
    linarith

lemma schauder_cutoff_difference_cancellation {d : ℝ} (hd : 0 < d) (i j : Fin 3) :
    Integrable (fun z => schauderNewtonHessianEntry i j z *
      (schauderRadialCutoff d z - schauderRadialBump z)) ∧
    (∫ z, schauderNewtonHessianEntry i j z *
      (schauderRadialCutoff d z - schauderRadialBump z)) = 0 := by
  have hc : ContDiff ℝ 1 (fun z => schauderRadialCutoff d z - schauderRadialBump z) :=
    ((contDiff_schauderRadialCutoff d).sub contDiff_schauderRadialBump).of_le (by simp)
  have hs : HasCompactSupport (fun z => schauderRadialCutoff d z - schauderRadialBump z) :=
    (schauderRadialCutoff_hasCompactSupport hd).sub schauderRadialBump_hasCompactSupport
  have h0 : schauderRadialCutoff d 0 - schauderRadialBump 0 = 0 := by
    rw [schauderRadialCutoff_one hd (by simpa using hd.le),
      schauderRadialBump_one (by simp), sub_self]
  have hi := fun i j => integrable_schauderNewtonHessian_mul_zero hc hs h0 i j
  exact ⟨hi i j, integral_schauderNewtonHessianEntry_radial_zero
    (fun e z => by simp only [schauderRadialCutoff_isometry, schauderRadialBump_isometry]) hi i j⟩

/-- The absolutely integrable near part, with the source value subtracted. -/
def schauderNearIntegrand (d : ℝ) (i j : Fin 3) (f : E₃ → ℝ) (x z : E₃) : ℝ :=
  schauderRadialCutoff d z * schauderNewtonHessianEntry i j z * (f (x - z) - f x)

lemma schauder_near_cutoff_bound {α d A : ℝ} (hα : 0 < α) (hd : 0 < d) (hA : 0 ≤ A)
    {f : E₃ → ℝ} (hf : Measurable f)
    (hinc : ∀ x y, ‖f x - f y‖ ≤ A * ‖x - y‖ ^ α) (i j : Fin 3) (x : E₃) :
    Integrable (schauderNearIntegrand d i j f x) ∧
    ‖∫ z, schauderNearIntegrand d i j f x z‖ ≤ 4 * A * (2 * d) ^ α / α := by
  let b : E₃ → ℝ := (ball (0 : E₃) (2 * d)).indicator
    (fun z => (Real.pi⁻¹ * A) * ‖z‖ ^ (α - 3))
  have hb : Integrable b := (integrable_indicator_iff measurableSet_ball).mpr
    ((integrableOn_schauder_near_power (R := 2 * d) hα).const_mul (Real.pi⁻¹ * A))
  have hm : Measurable (schauderNearIntegrand d i j f x) :=
    (((contDiff_schauderRadialCutoff d).continuous.measurable.mul
      (measurable_schauderNewtonHessianEntry i j)).mul
        ((hf.comp (continuous_const.sub continuous_id).measurable).sub measurable_const))
  have hmaj : ∀ z, ‖schauderNearIntegrand d i j f x z‖ ≤ b z := by
    intro z
    by_cases hz : z ∈ ball (0 : E₃) (2 * d)
    · rw [show b z = (Real.pi⁻¹ * A) * ‖z‖ ^ (α - 3) from indicator_of_mem hz _]
      by_cases hz0 : z = 0
      · subst z
        simp only [schauderNearIntegrand, sub_zero, sub_self, mul_zero, norm_zero]
        positivity
      have hn : 0 < ‖z‖ := norm_pos_iff.mpr hz0
      have hzinc := hinc (x - z) x
      rw [show x - z - x = -z by abel, norm_neg] at hzinc
      have hc := schauderRadialCutoff_mem_Icc d z
      have hc' : ‖schauderRadialCutoff d z‖ ≤ 1 := by
        simpa only [Real.norm_eq_abs, abs_of_nonneg hc.1] using hc.2
      calc
        _ ≤ 1 * (Real.pi⁻¹ * (‖z‖ ^ 3)⁻¹) * (A * ‖z‖ ^ α) := by
          rw [schauderNearIntegrand, norm_mul, norm_mul]
          exact mul_le_mul
            (mul_le_mul hc' (norm_schauderNewtonHessianEntry_le i j z)
              (norm_nonneg _) (by norm_num)) hzinc (norm_nonneg _) (by positivity)
        _ = _ := by
          rw [Real.rpow_sub hn α 3, Real.rpow_ofNat]
          ring
    · have hz' : 2 * d ≤ ‖z‖ := not_lt.mp (by simpa using hz)
      simp only [schauderNearIntegrand, schauderRadialCutoff_zero hd hz', zero_mul,
        norm_zero, b, indicator_of_notMem hz, le_refl]
  have hi := hb.mono' hm.aestronglyMeasurable (Eventually.of_forall hmaj)
  refine ⟨hi, (norm_integral_le_integral_norm _).trans
    ((integral_mono hi.norm hb hmaj).trans_eq ?_)⟩
  rw [show (∫ z, b z) = ∫ z in ball (0 : E₃) (2 * d),
    (Real.pi⁻¹ * A) * ‖z‖ ^ (α - 3) from integral_indicator measurableSet_ball]
  rw [integral_const_mul, integral_schauder_near_power hα (by positivity)]
  field_simp

lemma integrable_schauderFarKernel_mul_shift {d : ℝ} (hd : 0 < d) (i j : Fin 3)
    {f : E₃ → ℝ} (hf : Integrable f) (x : E₃) :
    Integrable (fun z => schauderFarKernel d i j z * f (x - z)) := by
  have h := (integrable_comp_sub_left
    (fun y => f y * schauderFarKernel d i j (x - y)) x).mpr
      (integrable_schauderFarConvolution hd i j hf x)
  simpa only [sub_sub_cancel, mul_comm] using h

lemma integral_schauderFarKernel_mul_shift (d : ℝ) (i j : Fin 3) (f : E₃ → ℝ) (x : E₃) :
    (∫ z, schauderFarKernel d i j z * f (x - z)) = schauderFarConvolution d i j f x := by
  have h := integral_sub_left_eq_self
    (fun y => f y * schauderFarKernel d i j (x - y)) volume x
  simpa only [sub_sub_cancel, mul_comm, schauderFarConvolution] using h

lemma integrable_schauderHessian_compensated {α A : ℝ} (hα : 0 < α) (hA : 0 ≤ A)
    {f : E₃ → ℝ} (hf : Measurable f) (hi : Integrable f)
    (hinc : ∀ x y, ‖f x - f y‖ ≤ A * ‖x - y‖ ^ α) (i j : Fin 3) (x : E₃) :
    Integrable (fun z => schauderNewtonHessianEntry i j z *
      (f (x - z) - f x * schauderRadialBump z)) := by
  have hn := (schauder_near_cutoff_bound hα (by norm_num : (0 : ℝ) < 1) hA hf hinc i j x).1
  have hfar := integrable_schauderFarKernel_mul_shift (by norm_num : (0 : ℝ) < 1) i j hi x
  apply (hn.add hfar).congr
  exact Eventually.of_forall fun z => by
    simp only [Pi.add_apply, schauderNearIntegrand, schauderFarKernel,
      schauderRadialCutoff, inv_one, one_smul]
    ring

/-- The compensated Hessian entry, including the actual diagonal distributional
correction for the convention `Δ(-1/(4π|x|)) = δ₀`. -/
def schauderHessianCandidate (i j : Fin 3) (f : E₃ → ℝ) (x : E₃) : ℝ :=
  (∫ z, schauderNewtonHessianEntry i j z * (f (x - z) - f x * schauderRadialBump z)) +
    (if i = j then (1 / 3 : ℝ) else 0) * f x

/-- An identity between absolutely convergent integrals, at every positive cutoff
scale. It is not a principal-value hypothesis. -/
lemma schauderHessianCandidate_split {α A d : ℝ} (hα : 0 < α) (hA : 0 ≤ A) (hd : 0 < d)
    {f : E₃ → ℝ} (hf : Measurable f) (hi : Integrable f)
    (hinc : ∀ x y, ‖f x - f y‖ ≤ A * ‖x - y‖ ^ α) (i j : Fin 3) (x : E₃) :
    schauderHessianCandidate i j f x =
      (∫ z, schauderNearIntegrand d i j f x z) + schauderFarConvolution d i j f x +
        (if i = j then (1 / 3 : ℝ) else 0) * f x := by
  have hn := (schauder_near_cutoff_bound hα hd hA hf hinc i j x).1
  have hfar := integrable_schauderFarKernel_mul_shift hd i j hi x
  obtain ⟨hc, he⟩ := schauder_cutoff_difference_cancellation hd i j
  have hfun : (fun z => schauderNewtonHessianEntry i j z *
      (f (x - z) - f x * schauderRadialBump z)) =
      (fun z => schauderNearIntegrand d i j f x z + schauderFarKernel d i j z * f (x - z) +
        f x * (schauderNewtonHessianEntry i j z *
          (schauderRadialCutoff d z - schauderRadialBump z))) := by
    funext z
    simp only [schauderNearIntegrand, schauderFarKernel]
    ring
  have hadd : Integrable (fun z =>
      schauderNearIntegrand d i j f x z + schauderFarKernel d i j z * f (x - z)) := hn.add hfar
  rw [schauderHessianCandidate, hfun, integral_add hadd (hc.const_mul (f x)),
    integral_add hn hfar, integral_const_mul, he, mul_zero, add_zero,
    integral_schauderFarKernel_mul_shift]

/-- The compensated Hessian has a genuine global Hölder estimate. The constant
is chosen before the source and its increment bound. -/
theorem exists_schauderHessianCandidate_holder_bound {α : ℝ} (hα : 0 < α) (hα1 : α < 1) :
    ∃ C > 0, ∀ A ≥ 0, ∀ (f : E₃ → ℝ), Measurable f → Integrable f →
      (∀ x y, ‖f x - f y‖ ≤ A * ‖x - y‖ ^ α) →
      ∀ (i j : Fin 3) (x y : E₃),
        ‖schauderHessianCandidate i j f x - schauderHessianCandidate i j f y‖ ≤
          C * A * ‖x - y‖ ^ α := by
  obtain ⟨B, hB, hBb⟩ := exists_schauderFarConvolution_increment_bound
  have hden : 0 < 1 - α := sub_pos.mpr hα1
  let C : ℝ := 8 * (2 : ℝ) ^ α / α + B / ((2 : ℝ) ^ (α - 1) * (1 - α)) + 1
  refine ⟨C, by dsimp [C]; positivity, fun A hA f hf hi hinc i j x y => ?_⟩
  by_cases hxy : x = y
  · subst y
    simp only [sub_self, norm_zero, Real.zero_rpow hα.ne', mul_zero, le_refl]
  have hd : 0 < ‖x - y‖ := norm_pos_iff.mpr (sub_ne_zero.mpr hxy)
  let d : ℝ := ‖x - y‖
  let N (w : E₃) : ℝ := ∫ z, schauderNearIntegrand d i j f w z
  let F := schauderFarConvolution d i j f
  let c : ℝ := if i = j then 1 / 3 else 0
  have hn (w : E₃) : ‖N w‖ ≤ 4 * A * (2 * d) ^ α / α :=
    (schauder_near_cutoff_bound hα hd hA hf hinc i j w).2
  have hfar : ‖F x - F y‖ ≤
      (B * A * (d / 2) ^ (α - 1) / (1 - α)) * d :=
    hBb α hα.le hα1 d hd A hA f hi hinc i j x y
  have hc : ‖c * (f x - f y)‖ ≤ A * d ^ α := by
    have hc0 : ‖c‖ ≤ 1 := by dsimp [c]; split_ifs <;> norm_num
    rw [norm_mul]
    simpa only [one_mul] using mul_le_mul hc0 (hinc x y) (norm_nonneg _) (by norm_num)
  have he : schauderHessianCandidate i j f x - schauderHessianCandidate i j f y =
      (N x - N y) + (F x - F y) + c * (f x - f y) := by
    rw [schauderHessianCandidate_split hα hA hd hf hi hinc i j x,
      schauderHessianCandidate_split hα hA hd hf hi hinc i j y]
    dsimp [N, F, c]
    ring
  rw [he]
  calc
    _ ≤ (‖N x‖ + ‖N y‖) + ‖F x - F y‖ + ‖c * (f x - f y)‖ := by
      apply (norm_add_le _ _).trans
      apply add_le_add _ le_rfl
      exact (norm_add_le _ _).trans (add_le_add (norm_sub_le _ _) le_rfl)
    _ ≤ (4 * A * (2 * d) ^ α / α + 4 * A * (2 * d) ^ α / α) +
        ((B * A * (d / 2) ^ (α - 1) / (1 - α)) * d) + A * d ^ α :=
      add_le_add (add_le_add (add_le_add (hn x) (hn y)) hfar) hc
    _ = C * A * ‖x - y‖ ^ α := by
      change _ = C * A * d ^ α
      rw [Real.mul_rpow (by norm_num : (0 : ℝ) ≤ 2) hd.le,
        Real.div_rpow hd.le (by norm_num : (0 : ℝ) ≤ 2), Real.rpow_sub_one hd.ne' α]
      dsimp [C]
      field_simp
      ring

lemma continuous_schauderHessianCandidate {α A : ℝ} (hα : 0 < α) (hα1 : α < 1)
    (hA : 0 ≤ A) {f : E₃ → ℝ} (hf : Measurable f) (hi : Integrable f)
    (hinc : ∀ x y, ‖f x - f y‖ ≤ A * ‖x - y‖ ^ α) (i j : Fin 3) :
    Continuous (schauderHessianCandidate i j f) := by
  obtain ⟨C, _, hb⟩ := exists_schauderHessianCandidate_holder_bound hα hα1
  apply continuous_iff_continuousAt.mpr
  intro x
  apply tendsto_iff_norm_sub_tendsto_zero.mpr
  have hc : Continuous (fun y : E₃ => C * A * ‖y - x‖ ^ α) :=
    continuous_const.mul ((Real.continuous_rpow_const hα.le).comp
      (continuous_id.sub continuous_const).norm)
  have ht : Tendsto (fun y : E₃ => C * A * ‖y - x‖ ^ α) (𝓝 x) (𝓝 0) := by
    simpa only [sub_self, norm_zero, Real.zero_rpow hα.ne', mul_zero] using hc.tendsto x
  exact squeeze_zero (fun y => norm_nonneg _)
    (fun y => hb A hA f hf hi hinc i j y x) ht

end LiquidDrop

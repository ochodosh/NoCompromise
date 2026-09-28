import NoCompromise.Elliptic.BoundaryHolderTangentialGrowth

/-! A fixed tangential localization and positive similarity preserve the
original weak boundary problem and its full coefficient hypotheses. The
constant in the energy bound is independent of the tangential center. -/

noncomputable section
open MeasureTheory Filter Metric Set InnerProductSpace
open scoped ENNReal NNReal Topology Gradient RealInnerProductSpace
namespace LiquidDrop
set_option maxSynthPendingDepth 8

theorem BoundaryHolderUnitData.normalize {a lam cap HA HG M : ℝ}
    (ha : 0 ≤ a) (hHA : 0 ≤ HA) (hHG : 0 ≤ HG)
    {u : EuclideanSpace ℝ (Fin 3) → ℝ}
    {F G : EuclideanSpace ℝ (Fin 3) → EuclideanSpace ℝ (Fin 3)}
    {A : EuclideanSpace ℝ (Fin 3) → EuclideanSpace ℝ (Fin 3) →L[ℝ]
      EuclideanSpace ℝ (Fin 3)}
    (h : BoundaryHolderUnitData a lam cap HA HG M u F G A)
    (z : EuclideanSpace ℝ (Fin 2)) (hz : ‖graphAppendN z 0‖ < 3 / 4) :
    BoundaryHolderUnitData a lam cap HA HG (512 * M)
      (u ∘ frozenBallScaling (graphAppendN z 0) (by norm_num : (0 : ℝ) < 1 / 512))
      (fun x => (1 / 512 : ℝ) • F
        (frozenBallScaling (graphAppendN z 0) (by norm_num : (0 : ℝ) < 1 / 512) x))
      (fun x => (1 / 512 : ℝ) • G
        (frozenBallScaling (graphAppendN z 0) (by norm_num : (0 : ℝ) < 1 / 512) x))
      (A ∘ frozenBallScaling (graphAppendN z 0) (by norm_num : (0 : ℝ) < 1 / 512)) := by
  let c := graphAppendN z 0
  have hδ : (0 : ℝ) < 1 / 512 := by norm_num
  let e := frozenBallScaling c hδ
  have hadd (x : EuclideanSpace ℝ (Fin 3)) : (1 / 512 : ℝ) • x + graphAppendN z 0 =
      graphAppendN z 0 + (1 / 512 : ℝ) • x := add_comm _ _
  have htrans := boundary_translated_radialData_of_holder ha hHG
    (by norm_num : (0 : ℝ) < 1 / 8) le_rfl z hz
    h.coefficient_continuous h.datum_continuous h.coefficient_bound h.elliptic
    h.coefficient_holder h.datum_holder h.h1 h.trace_zero h.equation
  have hscaled := htrans.h1.boundary_local_rescaled (by norm_num : (0 : ℝ) < 1 / 8)
    htrans.zero_trace
  have hscale : (1 / 8 : ℝ) / 64 = 1 / 512 := by norm_num
  have hmap : MapsTo e (boundaryHalfBall 1) (boundaryHalfBall 1) := by
    intro x hx
    have hxδ : frozenBallScaling 0 hδ x ∈ boundaryHalfBall (1 / 512 : ℝ) := by
      simpa only [mul_one] using (boundary_halfBall_scaling_mem hδ x 1).mpr hx
    have hh := boundary_small_translate_halfBall_subset hz
      (by norm_num : (1 / 512 : ℝ) ≤ 1 / 8) hxδ
    simpa only [frozenBallScaling_apply, zero_add, add_zero, e, c, hadd] using hh
  have hmapcl := hmap.closure_of_continuousOn e.continuous.continuousOn
  have hpow : (1 / 512 : ℝ) ^ a ≤ 1 := Real.rpow_le_one hδ.le (by norm_num) ha
  have hA : ContinuousOn (A ∘ e) (closure (boundaryHalfBall 1)) :=
    h.coefficient_continuous.comp e.continuous.continuousOn hmapcl
  have hG : ContinuousOn (fun x => (1 / 512 : ℝ) • G (e x))
      (closure (boundaryHalfBall 1)) := by
    simpa only [Pi.smul_apply, Function.comp_def] using!
      (h.datum_continuous.comp e.continuous.continuousOn hmapcl).const_smul (1 / 512 : ℝ)
  refine ⟨hA, hG, (fun x hx => h.coefficient_bound _ (hmapcl hx)),
    (fun x hx => h.elliptic _ (hmapcl hx)), ?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro x hx y hy
    have hh := h.coefficient_holder _ (hmapcl hx) _ (hmapcl hy)
    rw [quasilinear_ballScaling_dist c x y hδ, Real.mul_rpow hδ.le dist_nonneg] at hh
    apply hh.trans
    calc
      _ = (1 / 512 : ℝ) ^ a * (HA * dist x y ^ a) := by ring
      _ ≤ 1 * (HA * dist x y ^ a) := mul_le_mul_of_nonneg_right hpow
        (mul_nonneg hHA (Real.rpow_nonneg dist_nonneg a))
      _ = _ := one_mul _
  · intro x hx y hy
    rw [← smul_sub, norm_smul, Real.norm_of_nonneg hδ.le]
    have hh := h.datum_holder _ (hmapcl hx) _ (hmapcl hy)
    rw [quasilinear_ballScaling_dist c x y hδ, Real.mul_rpow hδ.le dist_nonneg] at hh
    have hp : HG * ((1 / 512 : ℝ) ^ a * dist x y ^ a) ≤ HG * dist x y ^ a := by
      calc
        _ = (1 / 512 : ℝ) ^ a * (HG * dist x y ^ a) := by ring
        _ ≤ 1 * (HG * dist x y ^ a) := mul_le_mul_of_nonneg_right hpow
          (mul_nonneg hHG (Real.rpow_nonneg dist_nonneg a))
        _ = _ := one_mul _
    have ht := mul_le_mul_of_nonneg_left (hh.trans hp) hδ.le
    have hnon : 0 ≤ HG * dist x y ^ a := mul_nonneg hHG (Real.rpow_nonneg dist_nonneg a)
    linarith
  · simpa only [hscale, Function.comp_def, frozenBallScaling_apply, zero_add, add_zero, e, c, hadd]
      using hscaled.1
  · simpa only [hscale, Function.comp_def, frozenBallScaling_apply, zero_add, add_zero, e, c, hadd]
      using hscaled.2
  · have he := (htrans.equation.mono (boundaryHalfBall_mono
        (by norm_num : (1 / 512 : ℝ) ≤ 1 / 8))).boundary_comp_scaling hδ
    simpa only [Function.comp_def, frozenBallScaling_apply, zero_add, add_zero, e, c, hadd] using he
  · have he := boundary_integral_energy_scaling (fun x => F (x + c)) hδ 1
    have hb := h.translated_energy z hz (by norm_num : (1 / 512 : ℝ) ≤ 1 / 8)
    have he' : (∫ x in boundaryHalfBall 1, ‖(1 / 512 : ℝ) • F (e x)‖ ^ 2) =
        512 * ∫ x in boundaryHalfBall (1 / 512 : ℝ), ‖F (x + c)‖ ^ 2 := by
      simp only [frozenBallScaling_apply, zero_add, c, hadd, mul_one] at he
      simpa only [e, c, frozenBallScaling_apply, one_div, inv_inv] using he
    rw [he']
    exact mul_le_mul_of_nonneg_left hb (by norm_num)

end LiquidDrop

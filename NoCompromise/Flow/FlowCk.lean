module

public import NoCompromise.Flow.ODE
public import Mathlib.Analysis.ODE.Gronwall
public import Mathlib.Topology.UniformSpace.HeineCantor

@[expose] public section

/-!
# thm:flow-Ck (first part): the spatial derivative of the flow is the variational matrix

For a bounded, globally Lipschitz `C¹` field, `D_x Φ_t (x) = A(t, x)`, where `A` solves
the variational equation. The remainder `Φ_t(x+z) - Φ_t(x) - A(t,x) z` satisfies a linear
differential inequality with forcing `o(|z|)` coming from the uniform differentiability of
`X` near the compact trajectory, and Grönwall's inequality closes the estimate.
-/

open Set Filter MeasureTheory Asymptotics
open scoped NNReal Topology Uniformity

namespace LiquidDrop

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]

omit [CompleteSpace E] in
/-- A two-sided Grönwall bound from a pointwise derivative inequality at all times. -/
theorem norm_le_gronwallBound_abs {r r' : ℝ → E} {K ε T : ℝ}
    (hr : ∀ s, HasDerivAt r (r' s) s) (h0 : r 0 = 0)
    (hb : ∀ s, |s| ≤ T → ‖r' s‖ ≤ K * ‖r s‖ + ε) {t : ℝ} (ht : |t| ≤ T) :
    ‖r t‖ ≤ gronwallBound 0 K ε |t| := by
  have hc : Continuous r := continuous_iff_continuousAt.mpr fun s => (hr s).continuousAt
  rcases le_total 0 t with ht0 | ht0
  · have h := norm_le_gronwallBound_of_norm_deriv_right_le (f := r) (f' := r') (δ := 0)
      (K := K) (ε := ε) (a := 0) (b := t) hc.continuousOn
      (fun s _ => (hr s).hasDerivWithinAt) (by simp [h0])
      (fun s hs => hb s (by rw [abs_of_nonneg hs.1]; exact hs.2.le.trans (by
        rw [abs_of_nonneg ht0] at ht; exact ht))) t ⟨ht0, le_rfl⟩
    simpa only [sub_zero, abs_of_nonneg ht0] using h
  · have hq : ∀ s, HasDerivAt (fun u => r (-u)) (-r' (-s)) s := fun s => by
      simpa [Function.comp_def] using (hr (-s)).scomp s (hasDerivAt_neg s)
    have h := norm_le_gronwallBound_of_norm_deriv_right_le (f := fun u => r (-u))
      (f' := fun s => -r' (-s)) (δ := 0) (K := K) (ε := ε) (a := 0) (b := -t)
      (hc.comp continuous_neg).continuousOn
      (fun s _ => (hq s).hasDerivWithinAt) (by simp [h0])
      (fun s hs => by
        rw [norm_neg]
        refine hb (-s) ?_
        rw [abs_neg, abs_of_nonneg hs.1]
        exact hs.2.le.trans (by rw [abs_of_nonpos ht0] at ht; exact ht))
      (-t) ⟨neg_nonneg.mpr ht0, le_rfl⟩
    simpa only [neg_neg, sub_zero, abs_of_nonpos ht0] using h

theorem gronwallBound_zero_left_eq_mul (K ε x : ℝ) :
    gronwallBound 0 K ε x = ε * gronwallBound 0 K 1 x := by
  unfold gronwallBound
  split_ifs <;> ring

/-- The time derivative of the variational matrix. -/
theorem hasDerivAt_variationalMatrix {X : E → E} {L : ℝ≥0} {M : ℝ}
    (hX : LipschitzWith L X) (hM : ∀ x, ‖X x‖ ≤ M) (hX1 : ContDiff ℝ 1 X) (x : E) (s : ℝ) :
    HasDerivAt (fun u => variationalMatrix X hX hM hX1 u x)
      ((fderiv ℝ X (globalFlow X hX hM s x)).comp (variationalMatrix X hX hM hX1 s x)) s := by
  let F : ℝ → (E →L[ℝ] E) := fun u =>
    (fderiv ℝ X (globalFlow X hX hM u x)).comp (variationalMatrix X hX hM hX1 u x)
  have hflow : Continuous (fun u => globalFlow X hX hM u x) :=
    continuous_iff_continuousAt.mpr fun u => (hasDerivAt_globalFlow hX hM x u).continuousAt
  have hA : Continuous (fun u => variationalMatrix X hX hM hX1 u x) :=
    (continuous_variationalMatrix hX hM hX1).comp (continuous_id.prodMk continuous_const)
  have hF : Continuous F :=
    ((hX1.continuous_fderiv one_ne_zero).comp hflow).clm_comp hA
  have heq : (fun u => variationalMatrix X hX hM hX1 u x) =
      fun u => ContinuousLinearMap.id ℝ E + ∫ v in (0 : ℝ)..u, F v :=
    funext fun u => variationalMatrix_integral hX hM hX1 u x
  rw [heq]
  have hI := intervalIntegral.integral_hasDerivAt_right (hF.intervalIntegrable 0 s)
    hF.aestronglyMeasurable.stronglyMeasurableAtFilter hF.continuousAt
  exact hI.const_add (ContinuousLinearMap.id ℝ E)

/-- thm:flow-Ck, first part: `D_x Φ_t(x) = A(t,x)`. -/
theorem hasFDerivAt_globalFlow {X : E → E} {L : ℝ≥0} {M : ℝ}
    (hX : LipschitzWith L X) (hM : ∀ x, ‖X x‖ ≤ M) (hX1 : ContDiff ℝ 1 X) (t : ℝ) (x : E) :
    HasFDerivAt (globalFlow X hX hM t) (variationalMatrix X hX hM hX1 t x) x := by
  set Φ := globalFlow X hX hM with hΦ
  set A := fun s => variationalMatrix X hX hM hX1 s x with hAdef
  set T := |t| with hT
  have hflow : Continuous (fun u => Φ u x) :=
    continuous_iff_continuousAt.mpr fun u => (hasDerivAt_globalFlow hX hM x u).continuousAt
  set K := (fun u => Φ u x) '' Icc (-T) T with hK
  have hKc : IsCompact K := (isCompact_Icc).image hflow
  have hDX : Continuous (fderiv ℝ X) := hX1.continuous_fderiv one_ne_zero
  have hDXL : ∀ p, ‖fderiv ℝ X p‖ ≤ L := fun p => norm_fderiv_le_of_lipschitz ℝ hX
  set Ee := Real.exp ((L : ℝ) * T) with hEe
  have hEe0 : 0 < Ee := Real.exp_pos _
  set G := gronwallBound 0 (L : ℝ) 1 T with hG
  have hG0 : 0 ≤ G := by
    rw [hG]
    unfold gronwallBound
    split_ifs with hL
    · rw [zero_add, one_mul]
      exact abs_nonneg t
    · have hLpos : 0 < (L : ℝ) := lt_of_le_of_ne L.2 (Ne.symm hL)
      have h1 : 1 ≤ Real.exp ((L : ℝ) * T) :=
        Real.one_le_exp (mul_nonneg L.2 (abs_nonneg t))
      rw [zero_mul, zero_add]
      exact mul_nonneg (div_nonneg zero_le_one hLpos.le) (by linarith)
  rw [hasFDerivAt_iff_isLittleO_nhds_zero, isLittleO_iff]
  intro c hc
  set η := c / (Ee * (G + 1)) with hη
  have hη0 : 0 < η := div_pos hc (mul_pos hEe0 (by linarith))
  obtain ⟨δ, hδ, hδK⟩ : ∃ δ > 0, ∀ p ∈ K, ∀ q, dist p q < δ →
      dist (fderiv ℝ X p) (fderiv ℝ X q) < η := by
    have hU := hKc.uniformContinuousAt_of_continuousAt (fderiv ℝ X)
      (fun a _ => hDX.continuousAt) (Metric.dist_mem_uniformity hη0)
    obtain ⟨δ, hδ, hδU⟩ := Metric.mem_uniformity_dist.mp hU
    exact ⟨δ, hδ, fun p hp q hpq => hδU hpq hp⟩
  have hunif : ∀ p ∈ K, ∀ w : E, ‖w‖ < δ →
      ‖X (p + w) - X p - fderiv ℝ X p w‖ ≤ η * ‖w‖ := by
    intro p hp w hw
    have h := (convex_ball p δ).norm_image_sub_le_of_norm_fderiv_le'
      (f := X) (φ := fderiv ℝ X p) (C := η)
      (fun q _ => hX1.differentiable one_ne_zero q)
      (fun q hq => by
        rw [← dist_eq_norm, dist_comm]
        exact (hδK p hp q (by rw [dist_comm]; exact hq)).le)
      (Metric.mem_ball_self hδ)
      (by rw [Metric.mem_ball, dist_eq_norm, add_sub_cancel_left]; exact hw)
    simpa using h
  have hball : ∀ᶠ z in 𝓝 (0 : E), ‖z‖ < δ / Ee := by
    have := (continuous_norm.tendsto (0 : E))
    simp only [norm_zero] at this
    exact this.eventually (gt_mem_nhds (div_pos hδ hEe0))
  filter_upwards [hball] with z hz
  have hclose : ∀ s, |s| ≤ T → ‖Φ s (x + z) - Φ s x‖ ≤ Ee * ‖z‖ := by
    intro s hs
    have h := dist_globalFlow_le hX hM s (x + z) x
    rw [dist_eq_norm, dist_eq_norm, add_sub_cancel_left] at h
    refine h.trans (mul_le_mul_of_nonneg_right ?_ (norm_nonneg z))
    exact Real.exp_le_exp.mpr (mul_le_mul_of_nonneg_left hs L.2)
  have hzδ : Ee * ‖z‖ < δ := by
    rw [lt_div_iff₀ hEe0] at hz
    linarith
  let r : ℝ → E := fun s => Φ s (x + z) - Φ s x - A s z
  let r' : ℝ → E := fun s =>
    X (Φ s (x + z)) - X (Φ s x) - (fderiv ℝ X (Φ s x)).comp (A s) z
  have hr : ∀ s, HasDerivAt r (r' s) s := by
    intro s
    have hAz : HasDerivAt (fun u => A u z) ((fderiv ℝ X (Φ s x)).comp (A s) z) s :=
      ((ContinuousLinearMap.apply ℝ E z).hasFDerivAt.comp_hasDerivAt s
        (hasDerivAt_variationalMatrix hX hM hX1 x s))
    exact ((hasDerivAt_globalFlow hX hM (x + z) s).sub
      (hasDerivAt_globalFlow hX hM x s)).sub hAz
  have hr0 : r 0 = 0 := by
    simp [r, hAdef, hΦ]
  have hbound : ∀ s, |s| ≤ T → ‖r' s‖ ≤ (L : ℝ) * ‖r s‖ + η * Ee * ‖z‖ := by
    intro s hs
    have hpK : Φ s x ∈ K := ⟨s, abs_le.mp hs, rfl⟩
    have hw := hclose s hs
    have h1 := hunif (Φ s x) hpK (Φ s (x + z) - Φ s x) (hw.trans_lt hzδ)
    rw [add_sub_cancel] at h1
    have hsplit : r' s = (X (Φ s (x + z)) - X (Φ s x) -
        fderiv ℝ X (Φ s x) (Φ s (x + z) - Φ s x)) + fderiv ℝ X (Φ s x) (r s) := by
      simp only [r', r, ContinuousLinearMap.comp_apply, map_sub]
      abel
    rw [hsplit]
    calc ‖(X (Φ s (x + z)) - X (Φ s x) - fderiv ℝ X (Φ s x) (Φ s (x + z) - Φ s x)) +
          fderiv ℝ X (Φ s x) (r s)‖
        ≤ η * ‖Φ s (x + z) - Φ s x‖ + L * ‖r s‖ :=
          (norm_add_le _ _).trans (add_le_add h1
            (((fderiv ℝ X (Φ s x)).le_opNorm _).trans
              (mul_le_mul_of_nonneg_right (hDXL _) (norm_nonneg _))))
      _ ≤ η * (Ee * ‖z‖) + L * ‖r s‖ :=
          add_le_add (mul_le_mul_of_nonneg_left hw hη0.le) le_rfl
      _ = L * ‖r s‖ + η * Ee * ‖z‖ := by ring
  have hmain := norm_le_gronwallBound_abs hr hr0 hbound (t := t) le_rfl
  rw [gronwallBound_zero_left_eq_mul] at hmain
  change ‖Φ t (x + z) - Φ t x - A t z‖ ≤ c * ‖z‖
  refine hmain.trans ?_
  rw [← hG]
  have hGle : G ≤ G + 1 := by linarith
  calc η * Ee * ‖z‖ * G = c * ‖z‖ * (G / (G + 1)) := by
        rw [hη]; field_simp
    _ ≤ c * ‖z‖ * 1 := mul_le_mul_of_nonneg_left
        ((div_le_one (by linarith)).mpr hGle) (by positivity)
    _ = c * ‖z‖ := mul_one _

/-- thm:flow-Ck: each time-`t` map is `C¹`, with derivative the variational matrix. -/
theorem contDiff_one_globalFlow {X : E → E} {L : ℝ≥0} {M : ℝ}
    (hX : LipschitzWith L X) (hM : ∀ x, ‖X x‖ ≤ M) (hX1 : ContDiff ℝ 1 X) (t : ℝ) :
    ContDiff ℝ 1 (globalFlow X hX hM t) := by
  have hd := fun x => hasFDerivAt_globalFlow hX hM hX1 t x
  rw [contDiff_one_iff_fderiv]
  refine ⟨fun x => (hd x).differentiableAt, ?_⟩
  have h : fderiv ℝ (globalFlow X hX hM t) = fun x => variationalMatrix X hX hM hX1 t x :=
    funext fun x => (hd x).fderiv
  rw [h]
  exact (continuous_variationalMatrix hX hM hX1).comp (continuous_const.prodMk continuous_id)

/-- thm:flow-Ck: `(D Φ_t)⁻¹ = D Φ_{-t}(Φ_t x)`, left inverse. -/
theorem variationalMatrix_neg_comp {X : E → E} {L : ℝ≥0} {M : ℝ}
    (hX : LipschitzWith L X) (hM : ∀ x, ‖X x‖ ≤ M) (hX1 : ContDiff ℝ 1 X) (t : ℝ) (x : E) :
    (variationalMatrix X hX hM hX1 (-t) (globalFlow X hX hM t x)).comp
      (variationalMatrix X hX hM hX1 t x) = ContinuousLinearMap.id ℝ E := by
  have hcomp := (hasFDerivAt_globalFlow hX hM hX1 (-t) (globalFlow X hX hM t x)).comp x
    (hasFDerivAt_globalFlow hX hM hX1 t x)
  have hid : (globalFlow X hX hM (-t)) ∘ (globalFlow X hX hM t) = id :=
    funext fun y => globalFlow_neg_left hX hM t y
  rw [hid] at hcomp
  exact hcomp.unique (hasFDerivAt_id x)

/-- thm:flow-Ck: `(D Φ_t)⁻¹ = D Φ_{-t}(Φ_t x)`, right inverse. -/
theorem variationalMatrix_comp_neg {X : E → E} {L : ℝ≥0} {M : ℝ}
    (hX : LipschitzWith L X) (hM : ∀ x, ‖X x‖ ≤ M) (hX1 : ContDiff ℝ 1 X) (t : ℝ) (x : E) :
    (variationalMatrix X hX hM hX1 t x).comp
      (variationalMatrix X hX hM hX1 (-t) (globalFlow X hX hM t x)) =
        ContinuousLinearMap.id ℝ E := by
  set y := globalFlow X hX hM t x
  have hx : globalFlow X hX hM (-t) y = x := globalFlow_neg_left hX hM t x
  have hcomp := (hasFDerivAt_globalFlow hX hM hX1 t (globalFlow X hX hM (-t) y)).comp y
    (hasFDerivAt_globalFlow hX hM hX1 (-t) y)
  have hid : (globalFlow X hX hM t) ∘ (globalFlow X hX hM (-t)) = id :=
    funext fun w => by simpa using globalFlow_neg_left hX hM (-t) w
  rw [hid, hx] at hcomp
  exact hcomp.unique (hasFDerivAt_id y)

end LiquidDrop

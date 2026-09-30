module

public import NoCompromise.Elliptic.NondivSchauderScalingNorm

@[expose] public section

/-!
# Explicit inverse scaling of C²,α norms

For 0<r≤1 and 0≤α≤1, pulling back from B₁/₂ to B(c,r/2)
costs at most r⁻³ in the full sum norm. The integer power is a useful
uniform upper bound for the exact derivative/Hölder scaling powers.
-/

noncomputable section
open MeasureTheory Filter Metric Set InnerProductSpace
open scoped ENNReal Topology Gradient RealInnerProductSpace
namespace LiquidDrop
set_option maxSynthPendingDepth 8

/-- For α≤1, composition with an L-Lipschitz map, L≥1, costs at most L in
the full Hölder norm. -/
lemma nondiv_holder_comp_expansion {E D F : Type*}
    [NormedAddCommGroup E] [NormedAddCommGroup D] [NormedAddCommGroup F]
    {α L : ℝ} (hα : 0 ≤ α) (hα1 : α ≤ 1) (hL : 1 ≤ L)
    {f : E → F} {e : D → E} {U : Set E} {V : Set D}
    (hf : HasFiniteHolderNormOn α f U) (hm : MapsTo e V U)
    (hd : ∀ x ∈ V, ∀ y ∈ V, ‖e x - e y‖ ≤ L * ‖x - y‖) :
    HasFiniteHolderNormOn α (f ∘ e) V ∧
      holderNorm α (f ∘ e) V ≤ L * holderNorm α f U := by
  have hL₀ : 0 ≤ L := zero_le_one.trans hL
  have hM := holderUniformNorm_nonneg hf.uniform_bounded
  have hH := hf.seminorm_nonneg
  have hv (x) (hx : x ∈ V) : ‖f (e x)‖ ≤ L * holderUniformNorm f U :=
    (norm_le_holderUniformNorm hf.uniform_bounded (hm hx)).trans
      (le_mul_of_one_le_left hM hL)
  have hpow : L ^ α ≤ L := by
    simpa only [Real.rpow_one] using Real.rpow_le_rpow_of_exponent_le hL hα1
  have hq (x) (hx : x ∈ V) (y) (hy : y ∈ V) :
      ‖f (e x) - f (e y)‖ / ‖x - y‖ ^ α ≤ L * holderSeminorm α f U := by
    by_cases he : x = y
    · subst y
      simp only [sub_self, norm_zero, zero_div]
      positivity
    · apply (div_le_iff₀ (Real.rpow_pos_of_pos
        (norm_pos_iff.mpr (sub_ne_zero.mpr he)) α)).mpr
      apply (hf.nondiv_norm_sub_le (hm hx) (hm hy)).trans
      have ht := Real.rpow_le_rpow (norm_nonneg _) (hd x hx y hy) hα
      rw [Real.mul_rpow hL₀ (norm_nonneg _)] at ht
      have hp := mul_le_mul_of_nonneg_right hpow (Real.rpow_nonneg (norm_nonneg (x - y)) α)
      have ht' := mul_le_mul_of_nonneg_left (ht.trans hp) hH
      nlinarith only [ht']
  refine ⟨HasFiniteHolderNormOn.of_bounds (mul_nonneg hL₀ hM) (mul_nonneg hL₀ hH) hv hq,
    (holderNorm_le (mul_nonneg hL₀ hM) (mul_nonneg hL₀ hH) hv hq).trans_eq ?_⟩
  dsimp [holderNorm]
  ring

lemma nondiv_fderiv_comp_ballScaling_symm {n : ℕ} {F : Type*}
    [NormedAddCommGroup F] [NormedSpace ℝ F]
    (c x : EuclideanSpace ℝ (Fin n)) {r : ℝ} (hr : 0 < r)
    {f : EuclideanSpace ℝ (Fin n) → F}
    (hf : DifferentiableAt ℝ f ((frozenBallScaling c hr).symm x)) :
    fderiv ℝ (f ∘ (frozenBallScaling c hr).symm) x =
      r⁻¹ • fderiv ℝ f ((frozenBallScaling c hr).symm x) := by
  have he : HasFDerivAt (frozenBallScaling c hr).symm
      (r⁻¹ • ContinuousLinearMap.id ℝ _) x := by
    rw [frozenBallScaling_symm_coe]
    exact ((hasFDerivAt_id x).sub_const c).const_smul r⁻¹
  simpa only [ContinuousLinearMap.comp_smul, ContinuousLinearMap.comp_id] using
    (hf.hasFDerivAt.comp x he).fderiv

lemma nondiv_ballScaling_symm_maps_half {n : ℕ}
    (c : EuclideanSpace ℝ (Fin n)) {r : ℝ} (hr : 0 < r) :
    MapsTo (frozenBallScaling c hr).symm (ball c (r / 2)) (ball 0 (1 / 2 : ℝ)) := by
  intro x hx
  apply (frozenBallScaling_mem_ball_iff c ((frozenBallScaling c hr).symm x) hr (1 / 2)).mp
  simpa only [Homeomorph.apply_symm_apply, mul_one_div] using hx

/-- The inverse similarity preserves actual C²,α regularity and has a quantitative
norm loss r⁻³, uniformly for 0≤α≤1. -/
theorem nondiv_c2Holder_comp_ballScaling_symm {n : ℕ} {α : ℝ}
    (hα : 0 ≤ α) (hα1 : α ≤ 1) (c : EuclideanSpace ℝ (Fin n)) {r : ℝ}
    (hr : 0 < r) (hr1 : r ≤ 1) {v : EuclideanSpace ℝ (Fin n) → ℝ}
    (hv : HasC2HolderOn α v (ball 0 (1 / 2 : ℝ))) :
    HasC2HolderOn α (v ∘ (frozenBallScaling c hr).symm) (ball c (r / 2)) ∧
      schauderC2HolderNorm α (v ∘ (frozenBallScaling c hr).symm) (ball c (r / 2)) ≤
        (r⁻¹) ^ 3 * schauderC2HolderNorm α v (ball 0 (1 / 2)) := by
  let e := (frozenBallScaling c hr).symm
  let U : Set (EuclideanSpace ℝ (Fin n)) := ball 0 (1 / 2)
  let V : Set (EuclideanSpace ℝ (Fin n)) := ball c (r / 2)
  have hm := nondiv_ballScaling_symm_maps_half c hr
  have hL : 1 ≤ r⁻¹ := (one_le_inv₀ hr).mpr hr1
  have hd (x) (_ : x ∈ V) (y) (_ : y ∈ V) : ‖e x - e y‖ ≤ r⁻¹ * ‖x - y‖ := by
    have ht : ‖e x - e y‖ = r⁻¹ * ‖x - y‖ := by
      simpa only [dist_eq_norm] using quasilinear_ballScaling_symm_dist c x y hr
    exact ht.le
  have hec : ContDiff ℝ 2 e := by
    change ContDiff ℝ 2 (frozenBallScaling c hr).symm
    rw [frozenBallScaling_symm_coe]
    exact (contDiff_id.sub contDiff_const).const_smul r⁻¹
  have hvc := hv.contDiff.comp hec.contDiffOn hm
  have hDf : ContDiffOn ℝ 1 (fderiv ℝ v) U :=
    (contDiffOn_succ_iff_fderiv_of_isOpen isOpen_ball).mp hv.contDiff |>.2.2
  have hD (x) (hx : x ∈ V) : fderiv ℝ (v ∘ e) x = r⁻¹ • fderiv ℝ v (e x) :=
    nondiv_fderiv_comp_ballScaling_symm c x hr
      ((hv.contDiff.contDiffAt (isOpen_ball.mem_nhds (hm hx))).differentiableAt (by norm_num))
  have hDD (x) (hx : x ∈ V) : fderiv ℝ (fderiv ℝ (v ∘ e)) x =
      (r⁻¹) ^ 2 • fderiv ℝ (fderiv ℝ v) (e x) := by
    have heq : fderiv ℝ (v ∘ e) =ᶠ[𝓝 x] (fun y => r⁻¹ • fderiv ℝ v (e y)) :=
      by
        filter_upwards [isOpen_ball.mem_nhds hx] with y hy
        exact hD y hy
    rw [heq.fderiv_eq]
    have hdv := (hDf.contDiffAt (isOpen_ball.mem_nhds (hm hx))).differentiableAt one_ne_zero
    have hde : DifferentiableAt ℝ (fderiv ℝ v ∘ e) x :=
      hdv.comp x (hec.differentiable (by norm_num) x)
    have he' : fderiv ℝ (fun y => r⁻¹ • fderiv ℝ v (e y)) x =
        r⁻¹ • fderiv ℝ (fderiv ℝ v ∘ e) x := by
      simpa only [Pi.smul_apply, Function.comp_apply] using! (hde.hasFDerivAt.const_smul r⁻¹).fderiv
    rw [he', nondiv_fderiv_comp_ballScaling_symm c x hr hdv, smul_smul, ← pow_two]
  obtain ⟨hV₀, hbV₀⟩ := nondiv_holder_comp_expansion hα hα1 hL hv.function_holder hm hd
  obtain ⟨hV₁, hbV₁⟩ := nondiv_holder_comp_expansion hα hα1 hL hv.derivative_holder hm hd
  obtain ⟨hV₂, hbV₂⟩ := nondiv_holder_comp_expansion hα hα1 hL hv.hessian_holder hm hd
  obtain ⟨hS₁, hbS₁⟩ := nondiv_holder_const_smul hV₁ r⁻¹
  obtain ⟨hS₂, hbS₂⟩ := nondiv_holder_const_smul hV₂ ((r⁻¹) ^ 2)
  have hDcongr := nondiv_holder_congr (α := α) hD
  have hHcongr := nondiv_holder_congr (α := α) hDD
  refine ⟨⟨hvc, hV₀, hDcongr.1.mpr hS₁, hHcongr.1.mpr hS₂⟩, ?_⟩
  have h₁ : holderNorm α (fderiv ℝ (v ∘ e)) V ≤
      (r⁻¹) ^ 2 * holderNorm α (fderiv ℝ v) U := by
    rw [hDcongr.2]
    apply hbS₁.trans
    rw [Real.norm_of_nonneg (inv_nonneg.mpr hr.le)]
    convert mul_le_mul_of_nonneg_left hbV₁ (inv_nonneg.mpr hr.le) using 1
    ring
  have h₂ : holderNorm α (fderiv ℝ (fderiv ℝ (v ∘ e))) V ≤
      (r⁻¹) ^ 3 * holderNorm α (fderiv ℝ (fderiv ℝ v)) U := by
    rw [hHcongr.2]
    apply hbS₂.trans
    rw [Real.norm_of_nonneg (sq_nonneg _)]
    convert mul_le_mul_of_nonneg_left hbV₂ (sq_nonneg r⁻¹) using 1
    ring
  have hpow₁ : r⁻¹ ≤ (r⁻¹) ^ 3 := by nlinarith [sq_nonneg (r⁻¹ - 1)]
  have hpow₂ : (r⁻¹) ^ 2 ≤ (r⁻¹) ^ 3 := by nlinarith [sq_nonneg r⁻¹]
  have hb₀ := hbV₀.trans (mul_le_mul_of_nonneg_right hpow₁ hv.function_holder.norm_nonneg)
  have hb₁ := h₁.trans (mul_le_mul_of_nonneg_right hpow₂ hv.derivative_holder.norm_nonneg)
  dsimp [schauderC2HolderNorm]
  nlinarith only [hb₀, hb₁, h₂]

end LiquidDrop

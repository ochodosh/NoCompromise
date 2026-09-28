import NoCompromise.Elliptic.NondivSchauderNorm
import NoCompromise.Elliptic.QuasilinearCampanatoPullback

/-!
# Hölder norms under similarities

These elementary composition estimates keep the radius dependence explicit.
They will rescale the already proved nondivergence bootstrap before applying
same-ball interpolation and nested-radius absorption.
-/

noncomputable section
open MeasureTheory Filter Metric Set InnerProductSpace
open scoped ENNReal Topology Gradient RealInnerProductSpace
namespace LiquidDrop
set_option maxSynthPendingDepth 8

lemma nondiv_holder_congr {E F : Type*} [NormedAddCommGroup E] [NormedAddCommGroup F]
    {α : ℝ} {f g : E → F} {U : Set E} (he : EqOn f g U) :
    (HasFiniteHolderNormOn α f U ↔ HasFiniteHolderNormOn α g U) ∧
      holderNorm α f U = holderNorm α g U := by
  have hv : (fun x => ‖f x‖) '' U = (fun x => ‖g x‖) '' U := by
    apply image_congr
    intro x hx
    rw [he hx]
  have hq : (fun p : E × E => ‖f p.1 - f p.2‖ / ‖p.1 - p.2‖ ^ α) '' (U ×ˢ U) =
      (fun p : E × E => ‖g p.1 - g p.2‖ / ‖p.1 - p.2‖ ^ α) '' (U ×ˢ U) := by
    apply image_congr
    intro p hp
    rw [he hp.1, he hp.2]
  constructor
  · constructor
    · intro hf
      exact ⟨by simpa only [hv] using hf.uniform_bounded,
        by simpa only [hq] using hf.seminorm_bounded⟩
    · intro hg
      exact ⟨by simpa only [hv] using hg.uniform_bounded,
        by simpa only [hq] using hg.seminorm_bounded⟩
  · simp only [holderNorm, holderUniformNorm, holderSeminorm, hv, hq]

lemma nondiv_holder_const_smul {E F : Type*} [NormedAddCommGroup E]
    [NormedAddCommGroup F] [NormedSpace ℝ F]
    {α : ℝ} {f : E → F} {U : Set E} (hf : HasFiniteHolderNormOn α f U) (c : ℝ) :
    HasFiniteHolderNormOn α (fun x => c • f x) U ∧
      holderNorm α (fun x => c • f x) U ≤ ‖c‖ * holderNorm α f U := by
  obtain ⟨hc, hb⟩ := nondiv_holder_comp_clm hf (c • ContinuousLinearMap.id ℝ F)
  have hn : ‖c • ContinuousLinearMap.id ℝ F‖ ≤ ‖c‖ := by
    rw [norm_smul]
    simpa only [mul_one] using mul_le_mul_of_nonneg_left
      (ContinuousLinearMap.norm_id_le (𝕜 := ℝ) (E := F)) (norm_nonneg c)
  exact ⟨hc, hb.trans (mul_le_mul_of_nonneg_right hn hf.norm_nonneg)⟩

/-- Composition by a contraction never increases the full Hölder norm. -/
lemma nondiv_holder_comp_contraction {E D F : Type*}
    [NormedAddCommGroup E] [NormedAddCommGroup D] [NormedAddCommGroup F]
    {α : ℝ} (hα : 0 ≤ α) {f : E → F} {e : D → E} {U : Set E} {V : Set D}
    (hf : HasFiniteHolderNormOn α f U) (hm : MapsTo e V U)
    (hd : ∀ x ∈ V, ∀ y ∈ V, ‖e x - e y‖ ≤ ‖x - y‖) :
    HasFiniteHolderNormOn α (f ∘ e) V ∧ holderNorm α (f ∘ e) V ≤ holderNorm α f U := by
  have hM := holderUniformNorm_nonneg hf.uniform_bounded
  have hH := hf.seminorm_nonneg
  have hv (x) (hx : x ∈ V) : ‖f (e x)‖ ≤ holderUniformNorm f U :=
    norm_le_holderUniformNorm hf.uniform_bounded (hm hx)
  have hq (x) (hx : x ∈ V) (y) (hy : y ∈ V) :
      ‖f (e x) - f (e y)‖ / ‖x - y‖ ^ α ≤ holderSeminorm α f U := by
    by_cases he : x = y
    · subst y
      simp only [sub_self, norm_zero, zero_div]
      exact hH
    · apply (div_le_iff₀ (Real.rpow_pos_of_pos
        (norm_pos_iff.mpr (sub_ne_zero.mpr he)) α)).mpr
      exact (hf.nondiv_norm_sub_le (hm hx) (hm hy)).trans
        (mul_le_mul_of_nonneg_left (Real.rpow_le_rpow (norm_nonneg _) (hd x hx y hy) hα) hH)
  exact ⟨HasFiniteHolderNormOn.of_bounds hM hH hv hq, holderNorm_le hM hH hv hq⟩

lemma nondiv_fderiv_comp_ballScaling {n : ℕ} {F : Type*}
    [NormedAddCommGroup F] [NormedSpace ℝ F]
    (c x : EuclideanSpace ℝ (Fin n)) {r : ℝ} (hr : 0 < r)
    {f : EuclideanSpace ℝ (Fin n) → F}
    (hf : DifferentiableAt ℝ f (frozenBallScaling c hr x)) :
    fderiv ℝ (f ∘ frozenBallScaling c hr) x = r • fderiv ℝ f (frozenBallScaling c hr x) := by
  have he : HasFDerivAt (frozenBallScaling c hr)
      (r • ContinuousLinearMap.id ℝ _) x :=
    ((hasFDerivAt_id x).const_smul r).const_add c
  simpa only [ContinuousLinearMap.comp_smul, ContinuousLinearMap.comp_id] using
    (hf.hasFDerivAt.comp x he).fderiv

/-- C¹,α norms do not grow under a contracting ball similarity. -/
theorem nondiv_c1Holder_comp_ballScaling {n : ℕ} {F : Type*}
    [NormedAddCommGroup F] [NormedSpace ℝ F]
    {α : ℝ} (hα : 0 ≤ α) (c : EuclideanSpace ℝ (Fin n)) {r : ℝ}
    (hr : 0 < r) (hr1 : r ≤ 1) {f : EuclideanSpace ℝ (Fin n) → F}
    (hf : HasC1HolderOn α f (ball c r)) :
    HasC1HolderOn α (f ∘ frozenBallScaling c hr) (ball 0 1) ∧
      nondivC1HolderNorm α (f ∘ frozenBallScaling c hr) (ball 0 1) ≤
        nondivC1HolderNorm α f (ball c r) := by
  let e := frozenBallScaling c hr
  have hm := quasilinear_ballScaling_maps_unit c hr
  have hd (x) (_ : x ∈ ball (0 : EuclideanSpace ℝ (Fin n)) 1)
      (y) (_ : y ∈ ball (0 : EuclideanSpace ℝ (Fin n)) 1) : ‖e x - e y‖ ≤ ‖x - y‖ := by
    have heq : ‖e x - e y‖ = r * ‖x - y‖ := by
      simpa only [dist_eq_norm] using quasilinear_ballScaling_dist c x y hr
    rw [heq]
    exact (mul_le_mul_of_nonneg_right hr1 (norm_nonneg _)).trans_eq (one_mul _)
  obtain ⟨hfc, hfcb⟩ := nondiv_holder_comp_contraction hα hf.function_holder hm hd
  obtain ⟨hDc, hDcb⟩ := nondiv_holder_comp_contraction hα hf.derivative_holder hm hd
  obtain ⟨hDs, hDsb⟩ := nondiv_holder_const_smul hDc r
  have heq : EqOn (fderiv ℝ (f ∘ e)) (fun x => r • fderiv ℝ f (e x)) (ball 0 1) := by
    intro x hx
    exact nondiv_fderiv_comp_ballScaling c x hr
      ((hf.contDiff.contDiffAt (isOpen_ball.mem_nhds (hm hx))).differentiableAt one_ne_zero)
  have hec : ContDiff ℝ 1 e := contDiff_const.add (contDiff_id.const_smul r)
  refine ⟨⟨hf.contDiff.comp hec.contDiffOn hm, hfc, (nondiv_holder_congr heq).1.mpr hDs⟩, ?_⟩
  unfold nondivC1HolderNorm
  rw [(nondiv_holder_congr heq).2]
  apply add_le_add hfcb
  apply hDsb.trans
  rw [Real.norm_of_nonneg hr.le]
  exact (mul_le_mul_of_nonneg_left hDcb hr.le).trans
    ((mul_le_mul_of_nonneg_right hr1 hf.derivative_holder.norm_nonneg).trans_eq (one_mul _))

end LiquidDrop

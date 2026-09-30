module

public import NoCompromise.Variation.CoulombBulk
public import Mathlib.MeasureTheory.Function.StronglyMeasurable.Inner

@[expose] public section

/-!
# Absolute integrability of the single-variable Coulomb variation

The inverse-square singularity is locally integrable in three dimensions. Splitting
at unit distance gives a uniform bound over every finite-volume set, and Tonelli
then proves integrability on products. This removes the extra integrability
premise from the unsymmetrized bulk first-variation formula.
-/

noncomputable section

open Set Filter MeasureTheory Metric
open scoped Topology NNReal ENNReal RealInnerProductSpace

namespace LiquidDrop

set_option maxSynthPendingDepth 8

local notation "E₃" => EuclideanSpace ℝ (Fin 3)

/-- The inverse-square singularity is integrable on every three-dimensional ball. -/
lemma integrableOn_inv_norm_sq_ball (r : ℝ) :
    IntegrableOn (fun y : E₃ => (‖y‖ ^ 2)⁻¹) (ball 0 r) := by
  apply (integrableOn_fun_norm_addHaar volume (f := fun y : ℝ => (y ^ 2)⁻¹)).mpr
  simp only [finrank_euclideanSpace, Fintype.card_fin, Nat.reduceSub, smul_eq_mul]
  refine ((continuous_const : Continuous (fun _ : ℝ => (1 : ℝ))).integrableOn_Icc.mono_set
    Ioo_subset_Icc_self).congr_fun
    (g := fun y : ℝ => y ^ 2 * (y ^ 2)⁻¹) ?_ measurableSet_Ioo
  intro y hy
  dsimp
  rw [mul_inv_cancel₀ (pow_ne_zero 2 (ne_of_gt hy.1))]

/-- Translation identifies every local inverse-square integral with the same finite constant. -/
lemma lintegral_inv_norm_sq_ball_shift (x : E₃) :
    (∫⁻ y in ball x 1, ENNReal.ofReal ((‖x - y‖ ^ 2)⁻¹)) =
      ENNReal.ofReal (∫ y : E₃ in ball 0 1, (‖y‖ ^ 2)⁻¹) := by
  have hchange := (volume.measurePreserving_sub_left x).setLIntegral_comp_preimage
    (s := ball (0 : E₃) 1) measurableSet_ball
    (f := fun y : E₃ => ENNReal.ofReal ((‖y‖ ^ 2)⁻¹)) (by fun_prop)
  have hpre : (fun y => x - y) ⁻¹' ball (0 : E₃) 1 = ball x 1 := by
    ext y
    simp [mem_ball, dist_eq_norm, norm_sub_rev]
  rw [hpre] at hchange
  exact hchange.trans (ofReal_integral_eq_lintegral_ofReal
    (integrableOn_inv_norm_sq_ball 1) (Eventually.of_forall fun y => by positivity)).symm

/-- The local singularity and a constant tail uniformly bound the inverse-square potential. -/
lemma lintegral_inv_norm_sq_le (E : Set E₃) (x : E₃) :
    (∫⁻ y in E, ENNReal.ofReal ((‖x - y‖ ^ 2)⁻¹)) ≤
      ENNReal.ofReal (∫ y : E₃ in ball 0 1, (‖y‖ ^ 2)⁻¹) + volume E := by
  have hm : Measurable (fun y : E₃ => ENNReal.ofReal ((‖x - y‖ ^ 2)⁻¹)) := by fun_prop
  calc
    _ ≤ ∫⁻ y in E, (ball x 1).indicator
        (fun y => ENNReal.ofReal ((‖x - y‖ ^ 2)⁻¹)) y + 1 := by
      apply lintegral_mono
      intro y
      by_cases hy : y ∈ ball x 1
      · simp only [indicator_of_mem hy]
        exact le_add_right le_rfl
      · simp only [indicator_of_notMem hy, zero_add]
        apply ENNReal.ofReal_le_one.mpr
        have hn : 1 ≤ ‖x - y‖ := by
          simpa only [mem_ball, dist_eq_norm, norm_sub_rev, not_lt] using hy
        have hs : 1 ≤ ‖x - y‖ ^ 2 := by nlinarith [norm_nonneg (x - y)]
        exact inv_le_one_of_one_le₀ hs
    _ = (∫⁻ y in E, (ball x 1).indicator
        (fun y => ENNReal.ofReal ((‖x - y‖ ^ 2)⁻¹)) y) + volume E := by
      rw [lintegral_add_left (hm.indicator measurableSet_ball), setLIntegral_const, one_mul]
    _ ≤ (∫⁻ y, (ball x 1).indicator
        (fun y => ENNReal.ofReal ((‖x - y‖ ^ 2)⁻¹)) y) + volume E :=
      add_le_add (lintegral_mono' Measure.restrict_le_self le_rfl) le_rfl
    _ = _ := by rw [lintegral_indicator measurableSet_ball, lintegral_inv_norm_sq_ball_shift]

/-- Finite outer volume suffices for absolute integrability of the inverse-square potential. -/
lemma integrableOn_inv_norm_sub_sq (E : Set E₃) (hE : volume E < ∞) (x : E₃) :
    IntegrableOn (fun y => (‖x - y‖ ^ 2)⁻¹) E := by
  have hm : Measurable (fun y : E₃ => ENNReal.ofReal ((‖x - y‖ ^ 2)⁻¹)) := by fun_prop
  have hfin := (lintegral_inv_norm_sq_le E x).trans_lt
    (ENNReal.add_lt_top.mpr ⟨ENNReal.ofReal_lt_top, hE⟩)
  have hi := integrable_toReal_of_lintegral_ne_top hm.aemeasurable hfin.ne
  simpa only [IntegrableOn, ENNReal.toReal_ofReal (inv_nonneg.mpr (sq_nonneg _))] using! hi

/-- Tonelli and the uniform potential bound control the inverse-square singularity on products. -/
lemma integrableOn_inv_norm_sub_sq_prod (E F : Set E₃)
    (hE : volume E < ∞) (hF : volume F < ∞) :
    IntegrableOn (fun p : E₃ × E₃ => (‖p.1 - p.2‖ ^ 2)⁻¹) (E ×ˢ F) := by
  have hm : Measurable (fun p : E₃ × E₃ => ENNReal.ofReal ((‖p.1 - p.2‖ ^ 2)⁻¹)) := by
    fun_prop
  have hfin : (∫⁻ p in E ×ˢ F, ENNReal.ofReal ((‖p.1 - p.2‖ ^ 2)⁻¹)) < ∞ := by
    rw [Measure.volume_eq_prod, setLIntegral_prod _ hm.aemeasurable]
    apply lt_of_le_of_lt (lintegral_mono fun x => lintegral_inv_norm_sq_le F x)
    rw [setLIntegral_const]
    exact ENNReal.mul_lt_top (ENNReal.add_lt_top.mpr ⟨ENNReal.ofReal_lt_top, hF⟩) hE
  have hi := integrable_toReal_of_lintegral_ne_top hm.aemeasurable hfin.ne
  simpa only [IntegrableOn, ENNReal.toReal_ofReal (inv_nonneg.mpr (sq_nonneg _))] using! hi

/-- A bounded vector field produces an integrable single-variable Coulomb force term. -/
lemma integrableOn_coulombBulkForce_of_bounded {X : E₃ → E₃}
    (hXm : AEStronglyMeasurable X volume) {B : ℝ} (hB : ∀ x, ‖X x‖ ≤ B)
    {E : Set E₃} (hE : volume E < ∞) :
    IntegrableOn (fun p : E₃ × E₃ => inner ℝ (p.1 - p.2) (X p.1) / ‖p.1 - p.2‖ ^ 3)
      (E ×ˢ E) := by
  have hm : AEStronglyMeasurable
      (fun p : E₃ × E₃ => inner ℝ (p.1 - p.2) (X p.1) / ‖p.1 - p.2‖ ^ 3) volume := by
    have hfst : AEStronglyMeasurable (fun p : E₃ × E₃ => X p.1) volume := by
      rw [Measure.volume_eq_prod]
      exact hXm.comp_fst
    exact (((continuous_fst.sub continuous_snd).aestronglyMeasurable.inner hfst).aemeasurable.div
      ((continuous_fst.sub continuous_snd).norm.pow 3).measurable.aemeasurable).aestronglyMeasurable
  apply ((integrableOn_inv_norm_sub_sq_prod E E hE hE).const_mul B).mono' hm.restrict
  apply Eventually.of_forall
  intro p
  by_cases hp : p.1 = p.2
  · simp [hp]
  have hn : 0 < ‖p.1 - p.2‖ := norm_pos_iff.mpr (sub_ne_zero.mpr hp)
  rw [Real.norm_eq_abs, abs_div, abs_of_pos (pow_pos hn 3)]
  calc
    _ ≤ (‖p.1 - p.2‖ * ‖X p.1‖) / ‖p.1 - p.2‖ ^ 3 :=
      div_le_div_of_nonneg_right (abs_real_inner_le_norm _ _) (by positivity)
    _ ≤ (‖p.1 - p.2‖ * B) / ‖p.1 - p.2‖ ^ 3 := by gcongr; exact hB p.1
    _ = B * (‖p.1 - p.2‖ ^ 2)⁻¹ := by field_simp

/-- The force term needs no assumption beyond compact support and continuity of the field. -/
lemma integrableOn_coulombBulkForce {X : E₃ → E₃} (hX : Continuous X)
    (hc : HasCompactSupport X) {E : Set E₃} (hE : volume E < ∞) :
    IntegrableOn (fun p : E₃ × E₃ => inner ℝ (p.1 - p.2) (X p.1) / ‖p.1 - p.2‖ ^ 3)
      (E ×ˢ E) := by
  obtain ⟨B, hB⟩ := (hc.isCompact_range hX).isBounded.exists_norm_le
  exact integrableOn_coulombBulkForce_of_bounded hX.aestronglyMeasurable
    (fun x => hB _ (mem_range_self x)) hE

/-- The single-variable divergence term is absolutely integrable. -/
lemma integrableOn_coulombBulkDivergence {X : E₃ → E₃} (hXC : ContDiff ℝ 1 X)
    (hc : HasCompactSupport X) {E : Set E₃} (hE : volume E < ∞) :
    IntegrableOn (fun p : E₃ × E₃ => divergenceN X p.1 * ‖p.1 - p.2‖⁻¹) (E ×ˢ E) := by
  obtain ⟨B, _, hB⟩ := exists_bound_comp_fderiv hXC hc
    continuous_standardMatrix3.matrix_trace
  have hd : Continuous (divergenceN X) :=
    continuous_standardMatrix3.matrix_trace.comp (hXC.continuous_fderiv (by simp))
  have hm : Measurable (fun p : E₃ × E₃ => divergenceN X p.1 * ‖p.1 - p.2‖⁻¹) :=
    (hd.comp continuous_fst).measurable.mul
      (continuous_fst.sub continuous_snd).norm.measurable.inv
  apply ((integrableOn_coulombKernel_prod E E hE hE).const_mul B).mono'
    hm.aestronglyMeasurable
  apply Eventually.of_forall
  intro p
  rw [norm_mul, Real.norm_eq_abs ‖p.1 - p.2‖⁻¹,
    abs_of_nonneg (inv_nonneg.mpr (norm_nonneg _))]
  exact mul_le_mul_of_nonneg_right (hB p.1) (inv_nonneg.mpr (norm_nonneg _))

/-- No separate integrability hypothesis is needed for the unsymmetrized bulk density. -/
lemma integrableOn_coulombBulkSingleIntegrand {X : E₃ → E₃} (hXC : ContDiff ℝ 1 X)
    (hc : HasCompactSupport X) {E : Set E₃} (hE : volume E < ∞) :
    IntegrableOn (coulombBulkSingleIntegrand X) (E ×ˢ E) :=
  (integrableOn_coulombBulkDivergence hXC hc hE).sub
    (integrableOn_coulombBulkForce hXC.continuous hc hE)

/-- Actual single-variable bulk first variation for every finite-volume Lebesgue-measurable set. -/
theorem hasDerivAt_coulombEnergy_straightPerturbation_single_of_finiteVolume
    {X : E₃ → E₃} (hXC : ContDiff ℝ 1 X) (hc : HasCompactSupport X) {E : Set E₃}
    (hE : NullMeasurableSet E volume) (hEfin : volume E < ∞) :
    HasDerivAt (fun t : ℝ => (coulombEnergy (straightPerturbation X t '' E)).toReal)
      (∫ p in E ×ˢ E, coulombBulkSingleIntegrand X p) 0 :=
  hasDerivAt_coulombEnergy_straightPerturbation_single hXC hc hE hEfin
    (integrableOn_coulombBulkSingleIntegrand hXC hc hEfin)

/-- Fubini connects the bulk expression to the already-defined Newtonian potential.
The force integral is explicit; no potential-gradient identity is assumed. -/
lemma integral_coulombBulkSingleIntegrand_eq_potential {X : E₃ → E₃}
    (hXC : ContDiff ℝ 1 X) (hc : HasCompactSupport X) {E : Set E₃} (hE : volume E < ∞) :
    (∫ p in E ×ˢ E, coulombBulkSingleIntegrand X p) =
      (∫ x in E, divergenceN X x * (coulombPotential E x).toReal) -
        ∫ x in E, ∫ y in E, inner ℝ (x - y) (X x) / ‖x - y‖ ^ 3 := by
  have hD := integrableOn_coulombBulkDivergence hXC hc hE
  have hF := integrableOn_coulombBulkForce hXC.continuous hc hE
  simp only [coulombBulkSingleIntegrand]
  rw [integral_sub hD hF]
  rw [Measure.volume_eq_prod] at hD hF ⊢
  rw [setIntegral_prod _ hD, setIntegral_prod _ hF]
  simp only [integral_const_mul, coulombPotential_toReal E hE]

/-- Single-variable first variation using the Newtonian potential and explicit force integral. -/
theorem hasDerivAt_coulombEnergy_straightPerturbation_potential
    {X : E₃ → E₃} (hXC : ContDiff ℝ 1 X) (hc : HasCompactSupport X) {E : Set E₃}
    (hE : NullMeasurableSet E volume) (hEfin : volume E < ∞) :
    HasDerivAt (fun t : ℝ => (coulombEnergy (straightPerturbation X t '' E)).toReal)
      ((∫ x in E, divergenceN X x * (coulombPotential E x).toReal) -
        ∫ x in E, ∫ y in E, inner ℝ (x - y) (X x) / ‖x - y‖ ^ 3) 0 := by
  rw [← integral_coulombBulkSingleIntegrand_eq_potential hXC hc hEfin]
  exact hasDerivAt_coulombEnergy_straightPerturbation_single_of_finiteVolume hXC hc hE hEfin

end LiquidDrop

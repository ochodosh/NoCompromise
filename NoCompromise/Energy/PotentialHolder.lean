import NoCompromise.Energy.PotentialRegularity
import Mathlib.Analysis.SpecialFunctions.Integrability.Basic
import Mathlib.Topology.MetricSpace.Holder

/-!
# Hölder regularity of the Newtonian gradient

For each exponent strictly between zero and one, a fractional-power kernel bound
is integrable in three dimensions. This gives a global Hölder bound for the
genuine gradient without a Calderón--Zygmund theorem.
-/

noncomputable section

open Set Filter MeasureTheory Metric
open scoped Topology NNReal ENNReal RealInnerProductSpace

namespace LiquidDrop

set_option maxSynthPendingDepth 8

local notation "E₃" => EuclideanSpace ℝ (Fin 3)
local notation "D₃" => E₃ →L[ℝ] ℝ

lemma inv_cube_sub_mul_le {r s : ℝ} (hr : 0 < r) (hrs : r ≤ s) :
    ((r ^ 3)⁻¹ - (s ^ 3)⁻¹) * r ≤ 3 * (s - r) * (r ^ 3)⁻¹ := by
  have hs : 0 < s := hr.trans_le hrs
  have heq : 3 * (s - r) * (r ^ 3)⁻¹ - ((r ^ 3)⁻¹ - (s ^ 3)⁻¹) * r =
      (s - r) ^ 2 * (3 * s ^ 2 + 2 * s * r + r ^ 2) / (r ^ 3 * s ^ 3) := by
    field_simp
    ring
  have hn : 0 ≤ (s - r) ^ 2 * (3 * s ^ 2 + 2 * s * r + r ^ 2) /
      (r ^ 3 * s ^ 3) := by positivity
  linarith

/-- A direct inverse-cube calculation bounds the derivative-kernel difference. -/
lemma norm_newtonDerivativeKernel_sub_le_of_norm_le {z w : E₃} (hz : z ≠ 0)
    (hzw : ‖z‖ ≤ ‖w‖) :
    ‖newtonDerivativeKernel z - newtonDerivativeKernel w‖ ≤
      4 * ‖z - w‖ / ‖z‖ ^ 3 := by
  have hr : 0 < ‖z‖ := norm_pos_iff.mpr hz
  have hs : 0 < ‖w‖ := hr.trans_le hzw
  have hi : (‖w‖ ^ 3)⁻¹ ≤ (‖z‖ ^ 3)⁻¹ :=
    inv_anti₀ (pow_pos hr 3) (pow_le_pow_left₀ hr.le hzw 3)
  have heq : newtonDerivativeKernel z - newtonDerivativeKernel w =
      -(‖w‖ ^ 3)⁻¹ • innerSL ℝ (z - w) +
        ((‖w‖ ^ 3)⁻¹ - (‖z‖ ^ 3)⁻¹) • innerSL ℝ z := by
    simp only [newtonDerivativeKernel, map_sub, smul_sub, sub_smul]
    module
  have hdist : ‖w‖ - ‖z‖ ≤ ‖z - w‖ := by
    simpa only [norm_sub_rev] using norm_sub_norm_le w z
  rw [heq]
  calc
    _ ≤ ‖-(‖w‖ ^ 3)⁻¹ • innerSL ℝ (z - w)‖ +
        ‖((‖w‖ ^ 3)⁻¹ - (‖z‖ ^ 3)⁻¹) • innerSL ℝ z‖ := norm_add_le _ _
    _ = (‖w‖ ^ 3)⁻¹ * ‖z - w‖ +
        ((‖z‖ ^ 3)⁻¹ - (‖w‖ ^ 3)⁻¹) * ‖z‖ := by
      rw [norm_smul, norm_smul, innerSL_apply_norm, innerSL_apply_norm,
        Real.norm_eq_abs, abs_neg, abs_of_pos (inv_pos.mpr (pow_pos hs 3)),
        Real.norm_eq_abs, abs_of_nonpos (sub_nonpos.mpr hi)]
      ring
    _ ≤ (‖z‖ ^ 3)⁻¹ * ‖z - w‖ + 3 * (‖w‖ - ‖z‖) * (‖z‖ ^ 3)⁻¹ :=
      add_le_add (mul_le_mul_of_nonneg_right hi (norm_nonneg _)) (inv_cube_sub_mul_le hr hzw)
    _ ≤ (‖z‖ ^ 3)⁻¹ * ‖z - w‖ + 3 * ‖z - w‖ * (‖z‖ ^ 3)⁻¹ := by gcongr
    _ = _ := by ring

lemma rpow_kernel_interpolation {a h r β : ℝ} (hh : 0 ≤ h) (hr : 0 < r)
    (hβ0 : 0 < β) (hβ1 : β < 1)
    (ha0 : a ≤ 2 * (r ^ 2)⁻¹) (ha1 : a ≤ 4 * h / r ^ 3) :
    a ≤ 4 * h ^ β * r ^ (-2 - β) := by
  have heq : (r ^ 2)⁻¹ * (h / r) ^ β = h ^ β * r ^ (-2 - β) := by
    rw [Real.div_rpow hh hr.le, div_eq_mul_inv, ← Real.rpow_neg hr.le,
      show (r ^ 2)⁻¹ = r ^ (-2 : ℝ) by rw [Real.rpow_neg hr.le, Real.rpow_two]]
    rw [show (-2 - β) = (-2 : ℝ) + -β by ring, Real.rpow_add hr]
    ring
  by_cases hhr : h ≤ r
  · have hq := Real.self_le_rpow_of_le_one (div_nonneg hh hr.le)
      ((div_le_one hr).mpr hhr) hβ1.le
    calc
      _ ≤ 4 * h / r ^ 3 := ha1
      _ = 4 * ((r ^ 2)⁻¹ * (h / r)) := by field_simp
      _ ≤ 4 * ((r ^ 2)⁻¹ * (h / r) ^ β) := by gcongr
      _ = _ := by rw [heq]; ring
  · have hq : 1 ≤ (h / r) ^ β := Real.one_le_rpow
      ((one_le_div hr).mpr (le_of_not_ge hhr)) hβ0.le
    calc
      _ ≤ 2 * (r ^ 2)⁻¹ := ha0
      _ ≤ 4 * ((r ^ 2)⁻¹ * (h / r) ^ β) := by
        nlinarith [inv_nonneg.mpr (sq_nonneg r),
          mul_le_mul_of_nonneg_left hq (inv_nonneg.mpr (sq_nonneg r))]
      _ = _ := by rw [heq]; ring

/-- The fractional-power majorant is symmetric in the two kernel arguments. -/
lemma norm_newtonDerivativeKernel_sub_le_rpow {β : ℝ} (hβ0 : 0 < β) (hβ1 : β < 1)
    {z w : E₃} (hz : z ≠ 0) (hw : w ≠ 0) :
    ‖newtonDerivativeKernel z - newtonDerivativeKernel w‖ ≤
      4 * ‖z - w‖ ^ β * (‖z‖ ^ (-2 - β) + ‖w‖ ^ (-2 - β)) := by
  wlog hzw : ‖z‖ ≤ ‖w‖ generalizing z w
  · simpa only [norm_sub_rev, add_comm] using this hw hz (le_of_not_ge hzw)
  have hr : 0 < ‖z‖ := norm_pos_iff.mpr hz
  have hnorm : ‖newtonDerivativeKernel z - newtonDerivativeKernel w‖ ≤
      2 * (‖z‖ ^ 2)⁻¹ := by
    calc
      _ ≤ ‖newtonDerivativeKernel z‖ + ‖newtonDerivativeKernel w‖ := norm_sub_le _ _
      _ = (‖z‖ ^ 2)⁻¹ + (‖w‖ ^ 2)⁻¹ := by
        rw [norm_newtonDerivativeKernel, norm_newtonDerivativeKernel]
      _ ≤ (‖z‖ ^ 2)⁻¹ + (‖z‖ ^ 2)⁻¹ := add_le_add le_rfl
        (inv_anti₀ (sq_pos_of_pos hr) (pow_le_pow_left₀ hr.le hzw 2))
      _ = _ := by ring
  exact (rpow_kernel_interpolation (norm_nonneg _) hr hβ0 hβ1 hnorm
    (norm_newtonDerivativeKernel_sub_le_of_norm_le hz hzw)).trans
      (mul_le_mul_of_nonneg_left (le_add_of_nonneg_right (Real.rpow_nonneg (norm_nonneg _) _))
        (by positivity))

/-- The fractional majorant is locally integrable precisely below the dimensional threshold. -/
lemma integrableOn_newtonHolderKernel_ball {β : ℝ} (hβ : β < 1) :
    IntegrableOn (fun z : E₃ => ‖z‖ ^ (-2 - β)) (ball 0 1) := by
  apply (integrableOn_fun_norm_addHaar volume (f := fun r : ℝ => r ^ (-2 - β))).mpr
  simp only [finrank_euclideanSpace, Fintype.card_fin, Nat.reduceSub, smul_eq_mul]
  have hi : IntegrableOn (fun r : ℝ => r ^ (-β)) (Ioo 0 1) :=
    (intervalIntegral.integrableOn_Ioo_rpow_iff zero_lt_one).mpr (by linarith)
  apply hi.congr_fun _ measurableSet_Ioo
  intro r hr
  dsimp only
  rw [← Real.rpow_two, ← Real.rpow_add hr.1]
  congr 1
  ring

lemma lintegral_newtonHolderKernel_ball_shift {β : ℝ} (hβ : β < 1) (x : E₃) :
    (∫⁻ y in ball x 1, ENNReal.ofReal (‖x - y‖ ^ (-2 - β))) =
      ENNReal.ofReal (∫ z : E₃ in ball 0 1, ‖z‖ ^ (-2 - β)) := by
  have hchange := (volume.measurePreserving_sub_left x).setLIntegral_comp_preimage
    (s := ball (0 : E₃) 1) measurableSet_ball
    (f := fun z : E₃ => ENNReal.ofReal (‖z‖ ^ (-2 - β))) (by fun_prop)
  have hpre : (fun y => x - y) ⁻¹' ball (0 : E₃) 1 = ball x 1 := by
    ext y
    simp [mem_ball, dist_eq_norm, norm_sub_rev]
  rw [hpre] at hchange
  exact hchange.trans (ofReal_integral_eq_lintegral_ofReal
    (integrableOn_newtonHolderKernel_ball hβ)
    (Eventually.of_forall fun z => Real.rpow_nonneg (norm_nonneg z) _)).symm

lemma lintegral_newtonHolderKernel_le {β : ℝ} (hβ0 : 0 < β) (hβ1 : β < 1)
    (E : Set E₃) (x : E₃) :
    (∫⁻ y in E, ENNReal.ofReal (‖x - y‖ ^ (-2 - β))) ≤
      ENNReal.ofReal (∫ z : E₃ in ball 0 1, ‖z‖ ^ (-2 - β)) + volume E := by
  have hm : Measurable (fun y : E₃ => ENNReal.ofReal (‖x - y‖ ^ (-2 - β))) := by fun_prop
  calc
    _ ≤ ∫⁻ y in E, (ball x 1).indicator
        (fun y => ENNReal.ofReal (‖x - y‖ ^ (-2 - β))) y + 1 := by
      apply lintegral_mono
      intro y
      by_cases hy : y ∈ ball x 1
      · simp only [indicator_of_mem hy]
        exact le_add_right le_rfl
      · simp only [indicator_of_notMem hy, zero_add]
        apply ENNReal.ofReal_le_one.mpr
        have hn : 1 ≤ ‖x - y‖ := by
          simpa only [mem_ball, dist_eq_norm, norm_sub_rev, not_lt] using hy
        exact Real.rpow_le_one_of_one_le_of_nonpos hn (by linarith)
    _ = (∫⁻ y in E, (ball x 1).indicator
        (fun y => ENNReal.ofReal (‖x - y‖ ^ (-2 - β))) y) + volume E := by
      rw [lintegral_add_left (hm.indicator measurableSet_ball), setLIntegral_const, one_mul]
    _ ≤ (∫⁻ y, (ball x 1).indicator
        (fun y => ENNReal.ofReal (‖x - y‖ ^ (-2 - β))) y) + volume E :=
      add_le_add (lintegral_mono' Measure.restrict_le_self le_rfl) le_rfl
    _ = _ := by rw [lintegral_indicator measurableSet_ball,
      lintegral_newtonHolderKernel_ball_shift hβ1]

lemma integrableOn_newtonHolderKernel {β : ℝ} (hβ0 : 0 < β) (hβ1 : β < 1)
    (E : Set E₃) (hE : volume E < ∞) (x : E₃) :
    IntegrableOn (fun y => ‖x - y‖ ^ (-2 - β)) E := by
  have hm : Measurable (fun y : E₃ => ENNReal.ofReal (‖x - y‖ ^ (-2 - β))) := by fun_prop
  have hfin := (lintegral_newtonHolderKernel_le hβ0 hβ1 E x).trans_lt
    (ENNReal.add_lt_top.mpr ⟨ENNReal.ofReal_lt_top, hE⟩)
  have hi := integrable_toReal_of_lintegral_ne_top hm.aemeasurable hfin.ne
  simpa only [IntegrableOn, ENNReal.toReal_ofReal (Real.rpow_nonneg (norm_nonneg _) _)] using! hi

lemma integral_newtonHolderKernel_le {β : ℝ} (hβ0 : 0 < β) (hβ1 : β < 1)
    (E : Set E₃) (hE : volume E < ∞) (x : E₃) :
    (∫ y in E, ‖x - y‖ ^ (-2 - β)) ≤
      (∫ z : E₃ in ball 0 1, ‖z‖ ^ (-2 - β)) + (volume E).toReal := by
  have hC : 0 ≤ ∫ z : E₃ in ball 0 1, ‖z‖ ^ (-2 - β) :=
    integral_nonneg fun z => Real.rpow_nonneg (norm_nonneg z) _
  have hi := integrableOn_newtonHolderKernel hβ0 hβ1 E hE x
  have hnn : 0 ≤ ∫ y in E, ‖x - y‖ ^ (-2 - β) :=
    integral_nonneg fun y => Real.rpow_nonneg (norm_nonneg _) _
  have h := ENNReal.toReal_mono
    (ENNReal.add_lt_top.mpr ⟨ENNReal.ofReal_lt_top, hE⟩).ne
    (lintegral_newtonHolderKernel_le hβ0 hβ1 E x)
  rw [← ofReal_integral_eq_lintegral_ofReal hi
    (Eventually.of_forall fun y => Real.rpow_nonneg (norm_nonneg _) _),
    ENNReal.toReal_ofReal hnn, ENNReal.toReal_add ENNReal.ofReal_ne_top hE.ne,
    ENNReal.toReal_ofReal hC] at h
  exact h

/-- A global Hölder estimate for the derivative integral on every finite-volume source. -/
lemma newtonPotentialDerivative_holder_bound {β : ℝ} (hβ0 : 0 < β) (hβ1 : β < 1)
    {E : Set E₃} (hE : volume E < ∞) (x z : E₃) :
    ‖newtonPotentialDerivative E x - newtonPotentialDerivative E z‖ ≤
      (8 * ((∫ y : E₃ in ball 0 1, ‖y‖ ^ (-2 - β)) + (volume E).toReal)) *
        ‖x - z‖ ^ β := by
  have hx := integrableOn_newtonHolderKernel hβ0 hβ1 E hE x
  have hz := integrableOn_newtonHolderKernel hβ0 hβ1 E hE z
  have hDx := integrableOn_newtonDerivativeKernel E hE x
  have hDz := integrableOn_newtonDerivativeKernel E hE z
  have hn : ∀ᵐ y : E₃ ∂volume.restrict E, x - y ≠ 0 ∧ z - y ≠ 0 := by
    have hxn : ∀ᵐ y : E₃ ∂volume, y ≠ x := by simp [ae_iff]
    have hzn : ∀ᵐ y : E₃ ∂volume, y ≠ z := by simp [ae_iff]
    filter_upwards [ae_restrict_of_ae (s := E) hxn, ae_restrict_of_ae (s := E) hzn] with y hyx hyz
    exact ⟨sub_ne_zero.mpr hyx.symm, sub_ne_zero.mpr hyz.symm⟩
  have hdiff (y : E₃) : (x - y) - (z - y) = x - z := by abel
  rw [newtonPotentialDerivative, newtonPotentialDerivative, ← integral_sub hDx hDz]
  calc
    _ ≤ ∫ y in E, ‖newtonDerivativeKernel (x - y) - newtonDerivativeKernel (z - y)‖ :=
      norm_integral_le_integral_norm _
    _ ≤ ∫ y in E, 4 * ‖x - z‖ ^ β *
        (‖x - y‖ ^ (-2 - β) + ‖z - y‖ ^ (-2 - β)) := by
      apply integral_mono_ae (hDx.sub hDz).norm ((hx.add hz).const_mul _)
      filter_upwards [hn] with y hy
      simpa only [hdiff, Pi.sub_apply, Pi.add_apply] using
        norm_newtonDerivativeKernel_sub_le_rpow hβ0 hβ1 hy.1 hy.2
    _ = 4 * ‖x - z‖ ^ β *
        ((∫ y in E, ‖x - y‖ ^ (-2 - β)) + (∫ y in E, ‖z - y‖ ^ (-2 - β))) := by
      rw [integral_const_mul, integral_add hx hz]
    _ ≤ 4 * ‖x - z‖ ^ β *
        (((∫ y : E₃ in ball 0 1, ‖y‖ ^ (-2 - β)) + (volume E).toReal) +
          ((∫ y : E₃ in ball 0 1, ‖y‖ ^ (-2 - β)) + (volume E).toReal)) :=
      mul_le_mul_of_nonneg_left (add_le_add
        (integral_newtonHolderKernel_le hβ0 hβ1 E hE x)
        (integral_newtonHolderKernel_le hβ0 hβ1 E hE z)) (by positivity)
    _ = _ := by ring

/-- The genuine gradient satisfies the same global fractional-power estimate. -/
theorem gradient_coulombPotential_holder_bound {β : ℝ} (hβ0 : 0 < β) (hβ1 : β < 1)
    {E : Set E₃} (hEb : Bornology.IsBounded E) (x z : E₃) :
    ‖gradient (fun a => (coulombPotential E a).toReal) x -
        gradient (fun a => (coulombPotential E a).toReal) z‖ ≤
      (8 * ((∫ y : E₃ in ball 0 1, ‖y‖ ^ (-2 - β)) + (volume E).toReal)) *
        ‖x - z‖ ^ β := by
  have hnorm : ‖gradient (fun a => (coulombPotential E a).toReal) x -
        gradient (fun a => (coulombPotential E a).toReal) z‖ =
      ‖newtonPotentialDerivative E x - newtonPotentialDerivative E z‖ := by
    rw [← (InnerProductSpace.toDual ℝ E₃).norm_map, map_sub,
      toDual_gradient, toDual_gradient,
      (hasFDerivAt_coulombPotential_of_isBounded hEb x).fderiv,
      (hasFDerivAt_coulombPotential_of_isBounded hEb z).fderiv]
  rw [hnorm]
  exact newtonPotentialDerivative_holder_bound hβ0 hβ1 hEb.measure_lt_top x z

/-- Blueprint `lem:potential-C1beta`, with the conventional Hölder range made explicit. -/
theorem coulombPotential_contDiff_one_and_holder {β : ℝ} (hβ0 : 0 < β) (hβ1 : β < 1)
    {E : Set E₃} (hEb : Bornology.IsBounded E) :
    ContDiff ℝ 1 (fun x => (coulombPotential E x).toReal) ∧
      ∃ C : ℝ, 0 ≤ C ∧ ∀ x z : E₃,
        ‖gradient (fun a => (coulombPotential E a).toReal) x -
            gradient (fun a => (coulombPotential E a).toReal) z‖ ≤ C * ‖x - z‖ ^ β := by
  refine ⟨contDiff_one_coulombPotential_of_isBounded hEb,
    8 * ((∫ y : E₃ in ball 0 1, ‖y‖ ^ (-2 - β)) + (volume E).toReal), ?_,
    gradient_coulombPotential_holder_bound hβ0 hβ1 hEb⟩
  have hC : 0 ≤ ∫ y : E₃ in ball 0 1, ‖y‖ ^ (-2 - β) :=
    integral_nonneg fun y => Real.rpow_nonneg (norm_nonneg y) _
  positivity

/-- The global gradient estimate packaged using mathlib's Hölder-continuity predicate. -/
theorem holderWith_gradient_coulombPotential {β : ℝ} (hβ0 : 0 < β) (hβ1 : β < 1)
    {E : Set E₃} (hEb : Bornology.IsBounded E) :
    ∃ C : ℝ≥0, HolderWith C ⟨β, hβ0.le⟩
      (gradient (fun x => (coulombPotential E x).toReal)) := by
  obtain ⟨C, hC, hb⟩ := (coulombPotential_contDiff_one_and_holder hβ0 hβ1 hEb).2
  let Cn : ℝ≥0 := ⟨C, hC⟩
  refine ⟨Cn, ?_⟩
  intro x z
  have hreal : dist (gradient (fun a => (coulombPotential E a).toReal) x)
      (gradient (fun a => (coulombPotential E a).toReal) z) ≤
      (Cn : ℝ) * dist x z ^ β := by
    simpa [dist_eq_norm, Cn] using! hb x z
  have he := ENNReal.ofReal_le_ofReal hreal
  rw [ENNReal.ofReal_mul Cn.coe_nonneg, ENNReal.ofReal_coe_nnreal,
    ← ENNReal.ofReal_rpow_of_nonneg dist_nonneg hβ0.le] at he
  simpa [edist_dist] using! he

/-- A standard C¹-plus-Hölder endpoint for blueprint `lem:potential-C1beta`. -/
theorem coulombPotential_contDiff_one_and_holderWith {β : ℝ} (hβ0 : 0 < β) (hβ1 : β < 1)
    {E : Set E₃} (hEb : Bornology.IsBounded E) :
    ContDiff ℝ 1 (fun x => (coulombPotential E x).toReal) ∧
      ∃ C : ℝ≥0, HolderWith C ⟨β, hβ0.le⟩
        (gradient (fun x => (coulombPotential E x).toReal)) :=
  ⟨contDiff_one_coulombPotential_of_isBounded hEb,
    holderWith_gradient_coulombPotential hβ0 hβ1 hEb⟩

end LiquidDrop

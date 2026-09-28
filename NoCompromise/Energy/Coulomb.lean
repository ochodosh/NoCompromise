import NoCompromise.Energy.CoulombDefs
import Mathlib.MeasureTheory.Constructions.HaarToSphere
import Mathlib.MeasureTheory.Measure.Lebesgue.VolumeOfBalls
import Mathlib.Analysis.SpecialFunctions.Integrals.Basic
import Mathlib.MeasureTheory.Group.Integral
import Mathlib.Tactic

/-!
# Coulomb bounds and integral representations

Tonelli identifies the product integral with the iterated potential integral,
including infinite values. Blueprint `lem:potential-bound` then gives uniform
potential and energy bounds on finite-volume sets. The diagonal-null and
integrability lemmas identify these definitions with the real-valued integrals
in `def:coulomb`. The bilinear identity and quantitative continuity estimate
implement `lem:coulomb-bilinear` and `lem:coulomb-lipschitz`. The disjoint-union
identity and strict positivity of interaction implement `lem:coulomb-disjoint`.
The separation bound and its limit implement `lem:cross-decay`.

Only finite volume is needed for the potential bound; no finite-perimeter or
minimizer hypothesis is used. That bound also holds for the restricted measure
of any set with finite outer volume. The bilinear identity and the Lipschitz
and continuity estimates additionally assume Lebesgue-measurable sets. The
union identities need measurability of one summand and disjointness; their
extended-real versions do not require finite volume.
-/

noncomputable section

open MeasureTheory Metric Set Filter
open scoped ENNReal symmDiff Topology

namespace LiquidDrop

theorem coulombKernel_symm (x y : AmbientSpace) : coulombKernel x y = coulombKernel y x := by
  simp only [coulombKernel, norm_sub_rev]

theorem measurable_coulombKernel :
    Measurable (fun p : AmbientSpace × AmbientSpace => coulombKernel p.1 p.2) := by
  unfold coulombKernel
  fun_prop

theorem coulombInteraction_eq_lintegral_potential (E F : Set AmbientSpace) :
    coulombInteraction E F = ∫⁻ x in E, coulombPotential F x := by
  unfold coulombInteraction coulombPotential
  rw [Measure.volume_eq_prod]
  exact setLIntegral_prod _ measurable_coulombKernel.aemeasurable

theorem coulombEnergy_eq_half_interaction (E : Set AmbientSpace) :
    coulombEnergy E = (2 : ℝ≥0∞)⁻¹ * coulombInteraction E E := rfl

theorem coulombEnergy_eq_lintegral_potential (E : Set AmbientSpace) :
    coulombEnergy E = (2 : ℝ≥0∞)⁻¹ * ∫⁻ x in E, coulombPotential E x := by
  rw [coulombEnergy_eq_half_interaction, coulombInteraction_eq_lintegral_potential]

theorem coulombEnergy_congr_ae {E F : Set AmbientSpace} (hEF : E =ᵐ[volume] F) :
    coulombEnergy E = coulombEnergy F := by
  have hprod : E ×ˢ E =ᵐ[volume] F ×ˢ F := by
    rw [Measure.volume_eq_prod]
    exact Measure.set_prod_ae_eq hEF hEF
  simp only [coulombEnergy, Measure.restrict_congr_set hprod]

/-- Blueprint `not:C0`. -/
def coulombBoundConstant : ℝ := 2 * Real.pi + 1

/-! ## The singular kernel on a ball -/

theorem integrableOn_inv_norm_ball (r : ℝ) :
    IntegrableOn (fun y : AmbientSpace => ‖y‖⁻¹) (ball 0 r) := by
  rw [integrableOn_fun_norm_addHaar volume]
  simp only [AmbientSpace, finrank_euclideanSpace, Fintype.card_fin, Nat.reduceSub, smul_eq_mul]
  refine (continuous_id.integrableOn_Icc.mono_set Ioo_subset_Icc_self).congr_fun
    ?_ measurableSet_Ioo
  intro y hy
  dsimp
  field_simp

theorem integral_inv_norm_ball {r : ℝ} (hr : 0 ≤ r) :
    (∫ y : AmbientSpace in ball 0 r, ‖y‖⁻¹) = 2 * Real.pi * r ^ 2 := by
  have hrad := integral_fun_norm_addHaar (volume : Measure AmbientSpace)
    ((Iio r).indicator fun t : ℝ => t⁻¹)
  have hleft : (fun y : AmbientSpace => (Iio r).indicator (fun t : ℝ => t⁻¹) ‖y‖) =
      (ball (0 : AmbientSpace) r).indicator (fun y => ‖y‖⁻¹) := by
    ext y
    simp [indicator]
  rw [hleft, integral_indicator measurableSet_ball] at hrad
  simp only [AmbientSpace, finrank_euclideanSpace, Fintype.card_fin, Nat.reduceSub,
    smul_eq_mul] at hrad
  have hright : (∫ y in Ioi (0 : ℝ), y ^ 2 * (Iio r).indicator (fun t => t⁻¹) y) = r ^ 2 / 2 := by
    calc
      _ = ∫ y in Ioi (0 : ℝ), (Iio r).indicator (fun t => t) y := by
        apply setIntegral_congr_fun measurableSet_Ioi
        intro y hy
        by_cases hyr : y < r
        · simp only [indicator_of_mem (show y ∈ Iio r from hyr)]
          field_simp
        · simp [hyr]
      _ = ∫ y in Ioo (0 : ℝ) r, y := by
        rw [integral_indicator measurableSet_Iio, Measure.restrict_restrict measurableSet_Iio]
        rw [inter_comm, Ioi_inter_Iio]
      _ = r ^ 2 / 2 := by
        rw [← integral_Ioc_eq_integral_Ioo, ← intervalIntegral.integral_of_le hr, integral_id]
        simp
  rw [hright] at hrad
  simp only [Measure.real, EuclideanSpace.volume_ball_fin_three, ENNReal.ofReal_one,
    one_pow, one_mul, ENNReal.toReal_ofReal (show 0 ≤ Real.pi * 4 / 3 by positivity),
    nsmul_eq_mul, Nat.cast_ofNat] at hrad
  rw [hrad]
  ring

theorem coulombKernel_toReal (x y : AmbientSpace) :
    (coulombKernel x y).toReal = ‖x - y‖⁻¹ := by
  simp [coulombKernel, ENNReal.toReal_inv]

theorem coulombKernel_ae_eq_ofReal (x : AmbientSpace) :
    coulombKernel x =ᵐ[volume] fun y => ENNReal.ofReal (‖x - y‖⁻¹) := by
  have hne : ∀ᵐ y : AmbientSpace ∂volume, y ≠ x := by simp [ae_iff]
  filter_upwards [hne] with y hy
  exact (ENNReal.ofReal_inv_of_pos (norm_pos_iff.mpr (sub_ne_zero.mpr hy.symm))).symm

theorem lintegral_coulombKernel_ball (x : AmbientSpace) {r : ℝ} (hr : 0 ≤ r) :
    (∫⁻ y in ball x r, coulombKernel x y) = ENNReal.ofReal (2 * Real.pi * r ^ 2) := by
  have hzero : (∫⁻ y : AmbientSpace in ball 0 r, (ENNReal.ofReal ‖y‖)⁻¹) =
      ENNReal.ofReal (2 * Real.pi * r ^ 2) := by
    calc
      _ = ∫⁻ y : AmbientSpace in ball 0 r, ENNReal.ofReal (‖y‖⁻¹) := by
        apply lintegral_congr_ae
        filter_upwards [(coulombKernel_ae_eq_ofReal 0).restrict (s := ball 0 r)] with y hy
        simpa only [coulombKernel, zero_sub, norm_neg] using hy
      _ = ENNReal.ofReal (∫ y : AmbientSpace in ball 0 r, ‖y‖⁻¹) := by
        exact (ofReal_integral_eq_lintegral_ofReal (integrableOn_inv_norm_ball r)
          (Filter.Eventually.of_forall fun y => inv_nonneg.mpr (norm_nonneg y))).symm
      _ = _ := by rw [integral_inv_norm_ball hr]
  have hchange := (volume.measurePreserving_sub_left x).setLIntegral_comp_preimage
    (s := ball (0 : AmbientSpace) r) measurableSet_ball
    (f := fun y : AmbientSpace => (ENNReal.ofReal ‖y‖)⁻¹) (by fun_prop)
  have hpre : (fun y => x - y) ⁻¹' ball (0 : AmbientSpace) r = ball x r := by
    ext y
    simp [mem_ball, dist_eq_norm, norm_sub_rev]
  rw [hpre] at hchange
  exact hchange.trans hzero

/-! ## Uniform bounds and finiteness -/

/-- Split into a ball around the singularity and its complement. -/
theorem coulombPotential_le_split (E : Set AmbientSpace) (x : AmbientSpace)
    {r : ℝ} (hr : 0 < r) :
    coulombPotential E x ≤ ENNReal.ofReal (2 * Real.pi * r ^ 2) +
      (ENNReal.ofReal r)⁻¹ * volume E := by
  have hkernel : Measurable (coulombKernel x) := by
    unfold coulombKernel
    fun_prop
  calc
    _ ≤ ∫⁻ y in E, (ball x r).indicator (coulombKernel x) y + (ENNReal.ofReal r)⁻¹ := by
      apply lintegral_mono
      intro y
      by_cases hy : y ∈ ball x r
      · simp only [indicator_of_mem hy]
        exact le_add_right le_rfl
      · simp only [indicator_of_notMem hy, zero_add]
        apply ENNReal.inv_le_inv.mpr
        apply ENNReal.ofReal_le_ofReal
        simpa [mem_ball, dist_eq_norm, norm_sub_rev] using hy
    _ = (∫⁻ y in E, (ball x r).indicator (coulombKernel x) y) +
        (ENNReal.ofReal r)⁻¹ * volume E := by
      rw [lintegral_add_left (hkernel.indicator measurableSet_ball), setLIntegral_const]
    _ ≤ (∫⁻ y, (ball x r).indicator (coulombKernel x) y) +
        (ENNReal.ofReal r)⁻¹ * volume E := by
      exact add_le_add (lintegral_mono' Measure.restrict_le_self le_rfl) le_rfl
    _ = _ := by rw [lintegral_indicator measurableSet_ball, lintegral_coulombKernel_ball x hr.le]

theorem coulombPotential_le_split_real (E : Set AmbientSpace) (hE : volume E < ∞)
    (x : AmbientSpace) {r : ℝ} (hr : 0 < r) :
    coulombPotential E x ≤ ENNReal.ofReal (2 * Real.pi * r ^ 2 + volume.real E / r) := by
  have hM : 0 ≤ volume.real E := ENNReal.toReal_nonneg
  rw [ENNReal.ofReal_add (by positivity) (by positivity), ENNReal.ofReal_div_of_pos hr,
    Measure.real, ENNReal.ofReal_toReal hE.ne, div_eq_mul_inv, mul_comm (volume E)]
  exact coulombPotential_le_split E x hr

/-- Blueprint `lem:potential-bound`: the bound holds at every point. -/
theorem coulombPotential_le (E : Set AmbientSpace) (hE : volume E < ∞) (x : AmbientSpace) :
    coulombPotential E x ≤
      ENNReal.ofReal (coulombBoundConstant * volume.real E ^ ((2 : ℝ) / 3)) := by
  by_cases hzero : volume E = 0
  · simp [coulombPotential, Measure.restrict_eq_zero.mpr hzero]
  have hM : 0 < volume.real E := ENNReal.toReal_pos hzero hE.ne
  have hr : 0 < volume.real E ^ ((1 : ℝ) / 3) := Real.rpow_pos_of_pos hM _
  have hcube : (volume.real E ^ ((1 : ℝ) / 3)) ^ 3 = volume.real E := by
    rw [← Real.rpow_natCast, ← Real.rpow_mul hM.le]
    norm_num
  have hsquare : (volume.real E ^ ((1 : ℝ) / 3)) ^ 2 = volume.real E ^ ((2 : ℝ) / 3) := by
    rw [← Real.rpow_natCast, ← Real.rpow_mul hM.le]
    norm_num
  have hquot : volume.real E / volume.real E ^ ((1 : ℝ) / 3) =
      (volume.real E ^ ((1 : ℝ) / 3)) ^ 2 := by
    apply (div_eq_iff hr.ne').2
    nlinarith [hcube]
  calc
    _ ≤ ENNReal.ofReal (2 * Real.pi * (volume.real E ^ ((1 : ℝ) / 3)) ^ 2 +
        volume.real E / volume.real E ^ ((1 : ℝ) / 3)) := coulombPotential_le_split_real E hE x hr
    _ = _ := by rw [hquot, hsquare]; congr 1; unfold coulombBoundConstant; ring

theorem coulombPotential_lt_top (E : Set AmbientSpace) (hE : volume E < ∞) (x : AmbientSpace) :
    coulombPotential E x < ∞ :=
  (coulombPotential_le E hE x).trans_lt ENNReal.ofReal_lt_top

theorem coulombInteraction_le (E F : Set AmbientSpace) (hE : volume E < ∞) (hF : volume F < ∞) :
    coulombInteraction E F ≤
      ENNReal.ofReal (coulombBoundConstant * volume.real F ^ ((2 : ℝ) / 3) * volume.real E) := by
  rw [coulombInteraction_eq_lintegral_potential]
  calc
    _ ≤ ∫⁻ x in E, ENNReal.ofReal (coulombBoundConstant * volume.real F ^ ((2 : ℝ) / 3)) :=
      lintegral_mono fun x => coulombPotential_le F hF x
    _ = _ := by
      rw [setLIntegral_const,
        ENNReal.ofReal_mul (p := coulombBoundConstant * volume.real F ^ ((2 : ℝ) / 3))
          (by unfold coulombBoundConstant; positivity)]
      simp only [Measure.real, ENNReal.ofReal_toReal hE.ne]

theorem coulombInteraction_lt_top (E F : Set AmbientSpace) (hE : volume E < ∞) (hF : volume F < ∞) :
    coulombInteraction E F < ∞ :=
  (coulombInteraction_le E F hE hF).trans_lt ENNReal.ofReal_lt_top

/-- Blueprint `lem:potential-bound`: the self-interaction energy estimate. -/
theorem coulombEnergy_le (E : Set AmbientSpace) (hE : volume E < ∞) :
    coulombEnergy E ≤
      ENNReal.ofReal ((1 / 2 : ℝ) * coulombBoundConstant * volume.real E ^ ((5 : ℝ) / 3)) := by
  have hpower : volume.real E ^ ((2 : ℝ) / 3) * volume.real E =
      volume.real E ^ ((5 : ℝ) / 3) := by
    rw [← Real.rpow_add_one' (show 0 ≤ volume.real E from ENNReal.toReal_nonneg)
      (by norm_num : (2 : ℝ) / 3 + 1 ≠ 0)]
    norm_num
  rw [coulombEnergy_eq_half_interaction]
  calc
    _ ≤ (2 : ℝ≥0∞)⁻¹ * ENNReal.ofReal
        (coulombBoundConstant * volume.real E ^ ((2 : ℝ) / 3) * volume.real E) :=
      mul_le_mul' le_rfl (coulombInteraction_le E E hE hE)
    _ = _ := by
      rw [mul_assoc coulombBoundConstant, hpower]
      have hhalf : (2 : ℝ≥0∞)⁻¹ = ENNReal.ofReal (1 / 2 : ℝ) := by
        rw [one_div, ENNReal.ofReal_inv_of_pos (by norm_num), ENNReal.ofReal_ofNat]
      rw [hhalf]
      rw [← ENNReal.ofReal_mul (by positivity)]
      congr 1
      ring

theorem coulombEnergy_lt_top (E : Set AmbientSpace) (hE : volume E < ∞) :
    coulombEnergy E < ∞ := (coulombEnergy_le E hE).trans_lt ENNReal.ofReal_lt_top

/-! ## Agreement with real-valued integrals -/

/-- The singular diagonal is null for six-dimensional volume. -/
theorem volume_diagonal_eq_zero :
    volume {p : AmbientSpace × AmbientSpace | p.1 = p.2} = 0 := by
  rw [Measure.volume_eq_prod,
    Measure.prod_apply (isClosed_eq continuous_fst continuous_snd).measurableSet]
  simp [Set.preimage]

theorem coulombKernel_prod_ae_eq_ofReal :
    (fun p : AmbientSpace × AmbientSpace => coulombKernel p.1 p.2) =ᵐ[volume]
      fun p => ENNReal.ofReal (‖p.1 - p.2‖⁻¹) := by
  have hne : ∀ᵐ p : AmbientSpace × AmbientSpace ∂volume, p.1 ≠ p.2 := by
    simpa only [ae_iff, not_not] using volume_diagonal_eq_zero
  filter_upwards [hne] with p hp
  exact (ENNReal.ofReal_inv_of_pos (norm_pos_iff.mpr (sub_ne_zero.mpr hp))).symm

/-- The ordinary reciprocal kernel is integrable on every finite-volume set. -/
theorem integrableOn_coulombKernel (E : Set AmbientSpace) (hE : volume E < ∞) (x : AmbientSpace) :
    IntegrableOn (fun y => ‖x - y‖⁻¹) E := by
  have hm : Measurable (coulombKernel x) := by unfold coulombKernel; fun_prop
  simpa only [IntegrableOn, coulombKernel_toReal] using
    integrable_toReal_of_lintegral_ne_top hm.aemeasurable (coulombPotential_lt_top E hE x).ne

/-- Agreement with the real-valued potential in blueprint `def:coulomb`. -/
theorem coulombPotential_eq_ofReal_integral (E : Set AmbientSpace) (hE : volume E < ∞)
    (x : AmbientSpace) :
    coulombPotential E x = ENNReal.ofReal (∫ y in E, ‖x - y‖⁻¹) := by
  calc
    _ = ∫⁻ y in E, ENNReal.ofReal (‖x - y‖⁻¹) :=
      lintegral_congr_ae (coulombKernel_ae_eq_ofReal x).restrict
    _ = _ := (ofReal_integral_eq_lintegral_ofReal (integrableOn_coulombKernel E hE x)
      (Filter.Eventually.of_forall fun y => inv_nonneg.mpr (norm_nonneg _))).symm

theorem coulombPotential_toReal (E : Set AmbientSpace) (hE : volume E < ∞) (x : AmbientSpace) :
    (coulombPotential E x).toReal = ∫ y in E, ‖x - y‖⁻¹ := by
  rw [coulombPotential_eq_ofReal_integral E hE x,
    ENNReal.toReal_ofReal (integral_nonneg fun y => inv_nonneg.mpr (norm_nonneg _))]

/-- Integrability of the ordinary kernel on a product of finite-volume sets. -/
theorem integrableOn_coulombKernel_prod (E F : Set AmbientSpace)
    (hE : volume E < ∞) (hF : volume F < ∞) :
    IntegrableOn (fun p : AmbientSpace × AmbientSpace => ‖p.1 - p.2‖⁻¹) (E ×ˢ F) := by
  simpa only [IntegrableOn, coulombKernel_toReal] using
    integrable_toReal_of_lintegral_ne_top measurable_coulombKernel.aemeasurable
      (coulombInteraction_lt_top E F hE hF).ne

theorem coulombInteraction_eq_ofReal_integral (E F : Set AmbientSpace)
    (hE : volume E < ∞) (hF : volume F < ∞) :
    coulombInteraction E F = ENNReal.ofReal (∫ p in E ×ˢ F, ‖p.1 - p.2‖⁻¹) := by
  calc
    _ = ∫⁻ p in E ×ˢ F, ENNReal.ofReal (‖p.1 - p.2‖⁻¹) :=
      lintegral_congr_ae coulombKernel_prod_ae_eq_ofReal.restrict
    _ = _ := (ofReal_integral_eq_lintegral_ofReal (integrableOn_coulombKernel_prod E F hE hF)
      (Filter.Eventually.of_forall fun p => inv_nonneg.mpr (norm_nonneg _))).symm

/-- Agreement with the real-valued product integral in blueprint `def:coulomb`. -/
theorem coulombEnergy_eq_ofReal_integral (E : Set AmbientSpace) (hE : volume E < ∞) :
    coulombEnergy E = ENNReal.ofReal ((1 / 2 : ℝ) * ∫ p in E ×ˢ E, ‖p.1 - p.2‖⁻¹) := by
  rw [coulombEnergy_eq_half_interaction, coulombInteraction_eq_ofReal_integral E E hE hE,
    ENNReal.ofReal_mul (by norm_num : (0 : ℝ) ≤ 1 / 2), one_div,
    ENNReal.ofReal_inv_of_pos (by norm_num : (0 : ℝ) < 2), ENNReal.ofReal_ofNat]

theorem measurable_coulombPotential (E : Set AmbientSpace) : Measurable (coulombPotential E) := by
  exact measurable_coulombKernel.lintegral_prod_right'

/-- A finite-volume potential is integrable on any finite-volume set. -/
theorem integrableOn_coulombPotential (E F : Set AmbientSpace)
    (hE : volume E < ∞) (hF : volume F < ∞) :
    IntegrableOn (fun x => (coulombPotential F x).toReal) E := by
  apply integrable_toReal_of_lintegral_ne_top (measurable_coulombPotential F).aemeasurable
  rw [← coulombInteraction_eq_lintegral_potential]
  exact (coulombInteraction_lt_top E F hE hF).ne

theorem coulombEnergy_eq_ofReal_integral_potential (E : Set AmbientSpace) (hE : volume E < ∞) :
    coulombEnergy E = ENNReal.ofReal ((1 / 2 : ℝ) * ∫ x in E, (coulombPotential E x).toReal) := by
  rw [ENNReal.ofReal_mul (by norm_num : (0 : ℝ) ≤ 1 / 2),
    ofReal_integral_eq_lintegral_ofReal (integrableOn_coulombPotential E E hE hE)
      (Filter.Eventually.of_forall fun x => ENNReal.toReal_nonneg),
    one_div, ENNReal.ofReal_inv_of_pos (by norm_num : (0 : ℝ) < 2), ENNReal.ofReal_ofNat,
    coulombEnergy_eq_lintegral_potential]
  congr 1
  apply lintegral_congr
  intro x
  exact (ENNReal.ofReal_toReal (coulombPotential_lt_top E hE x).ne).symm

/-- Agreement with one half of the iterated real integral in the paper. -/
theorem coulombEnergy_eq_ofReal_iteratedIntegral (E : Set AmbientSpace) (hE : volume E < ∞) :
    coulombEnergy E = ENNReal.ofReal ((1 / 2 : ℝ) * ∫ x in E, ∫ y in E, ‖x - y‖⁻¹) := by
  simpa only [coulombPotential_toReal E hE] using coulombEnergy_eq_ofReal_integral_potential E hE

theorem coulombInteraction_toReal (E F : Set AmbientSpace)
    (hE : volume E < ∞) (hF : volume F < ∞) :
    (coulombInteraction E F).toReal = ∫ p in E ×ˢ F, ‖p.1 - p.2‖⁻¹ := by
  rw [coulombInteraction_eq_ofReal_integral E F hE hF,
    ENNReal.toReal_ofReal (integral_nonneg fun p => inv_nonneg.mpr (norm_nonneg _))]

theorem coulombEnergy_toReal (E : Set AmbientSpace) (hE : volume E < ∞) :
    (coulombEnergy E).toReal = (1 / 2 : ℝ) * ∫ p in E ×ˢ E, ‖p.1 - p.2‖⁻¹ := by
  rw [coulombEnergy_eq_ofReal_integral E hE,
    ENNReal.toReal_ofReal (mul_nonneg (by norm_num)
      (integral_nonneg fun p => inv_nonneg.mpr (norm_nonneg _)))]

theorem coulombEnergy_toReal_eq_integral_potential (E : Set AmbientSpace) (hE : volume E < ∞) :
    (coulombEnergy E).toReal = (1 / 2 : ℝ) * ∫ x in E, (coulombPotential E x).toReal := by
  rw [coulombEnergy_eq_ofReal_integral_potential E hE,
    ENNReal.toReal_ofReal (mul_nonneg (by norm_num)
      (integral_nonneg fun x => ENNReal.toReal_nonneg))]

/-- The uniform potential estimate in ordinary real notation. -/
theorem integral_coulombKernel_le (E : Set AmbientSpace) (hE : volume E < ∞) (x : AmbientSpace) :
    (∫ y in E, ‖x - y‖⁻¹) ≤ coulombBoundConstant * volume.real E ^ ((2 : ℝ) / 3) := by
  have h := ENNReal.toReal_mono ENNReal.ofReal_ne_top (coulombPotential_le E hE x)
  rwa [coulombPotential_toReal E hE x,
    ENNReal.toReal_ofReal (by unfold coulombBoundConstant; positivity)] at h

/-- The energy estimate in ordinary real notation. -/
theorem coulombEnergy_toReal_le (E : Set AmbientSpace) (hE : volume E < ∞) :
    (coulombEnergy E).toReal ≤
      (1 / 2 : ℝ) * coulombBoundConstant * volume.real E ^ ((5 : ℝ) / 3) := by
  have h := ENNReal.toReal_mono ENNReal.ofReal_ne_top (coulombEnergy_le E hE)
  rwa [ENNReal.toReal_ofReal (by unfold coulombBoundConstant; positivity)] at h

/-! ## Bilinear identity and continuity -/

theorem coulombInteraction_symm (E F : Set AmbientSpace) :
    coulombInteraction E F = coulombInteraction F E := by
  calc
    _ = ∫⁻ y in F, ∫⁻ x in E, coulombKernel x y := by
      unfold coulombInteraction
      rw [Measure.volume_eq_prod]
      exact setLIntegral_prod_symm _ measurable_coulombKernel.aemeasurable
    _ = _ := by
      rw [coulombInteraction_eq_lintegral_potential]
      simp only [coulombPotential, coulombKernel_symm]

theorem coulombInteraction_toReal_eq_integral_potential (E F : Set AmbientSpace)
    (hE : volume E < ∞) (hF : volume F < ∞) :
    (coulombInteraction E F).toReal = ∫ x in E, (coulombPotential F x).toReal := by
  have hfinite : (∫⁻ x in E, coulombPotential F x) ≠ ∞ := by
    rw [← coulombInteraction_eq_lintegral_potential]
    exact (coulombInteraction_lt_top E F hE hF).ne
  rw [coulombInteraction_eq_lintegral_potential]
  exact (integral_toReal (measurable_coulombPotential F).aemeasurable
    (ae_lt_top (measurable_coulombPotential F) hfinite)).symm

/-- Blueprint `lem:coulomb-bilinear`. -/
theorem coulombEnergy_bilinear (E F : Set AmbientSpace)
    (hEm : NullMeasurableSet E volume) (hFm : NullMeasurableSet F volume)
    (hE : volume E < ∞) (hF : volume F < ∞) :
    (coulombEnergy E).toReal - (coulombEnergy F).toReal =
      (1 / 2 : ℝ) * ∫ x, (E.indicator (fun _ => (1 : ℝ)) x - F.indicator (fun _ => 1) x) *
        ((coulombPotential E x).toReal + (coulombPotential F x).toReal) := by
  let f := fun x => (coulombPotential E x).toReal + (coulombPotential F x).toReal
  have hEf : IntegrableOn f E := (integrableOn_coulombPotential E E hE hE).add
    (integrableOn_coulombPotential E F hE hF)
  have hFf : IntegrableOn f F := (integrableOn_coulombPotential F E hF hE).add
    (integrableOn_coulombPotential F F hF hF)
  have hfun : (fun x => (E.indicator (fun _ => (1 : ℝ)) x - F.indicator (fun _ => 1) x) * f x) =
      fun x => E.indicator f x - F.indicator f x := by
    ext x
    by_cases hxE : x ∈ E <;> by_cases hxF : x ∈ F <;> simp [hxE, hxF]
  change _ = (1 / 2 : ℝ) * ∫ x, (E.indicator (fun _ => (1 : ℝ)) x -
    F.indicator (fun _ => 1) x) * f x
  rw [hfun, integral_sub (hEf.integrable_indicator₀ hEm) (hFf.integrable_indicator₀ hFm),
    integral_indicator₀ hEm, integral_indicator₀ hFm]
  dsimp only [f]
  rw [integral_add (integrableOn_coulombPotential E E hE hE)
      (integrableOn_coulombPotential E F hE hF),
    integral_add (integrableOn_coulombPotential F E hF hE)
      (integrableOn_coulombPotential F F hF hF),
    ← coulombInteraction_toReal_eq_integral_potential E F hE hF,
    ← coulombInteraction_toReal_eq_integral_potential F E hF hE,
    coulombInteraction_symm E F,
    coulombEnergy_toReal_eq_integral_potential E hE,
    coulombEnergy_toReal_eq_integral_potential F hF]
  ring

theorem coulombPotential_toReal_le_of_volume_le (E : Set AmbientSpace) {M : ℝ}
    (hM : 0 ≤ M) (hE : volume E ≤ ENNReal.ofReal M) (x : AmbientSpace) :
    (coulombPotential E x).toReal ≤ coulombBoundConstant * M ^ ((2 : ℝ) / 3) := by
  have hfin : volume E < ∞ := hE.trans_lt ENNReal.ofReal_lt_top
  rw [coulombPotential_toReal E hfin x]
  refine (integral_coulombKernel_le E hfin x).trans ?_
  exact mul_le_mul_of_nonneg_left
    (Real.rpow_le_rpow ENNReal.toReal_nonneg (ENNReal.toReal_le_of_le_ofReal hM hE) (by norm_num))
    (by unfold coulombBoundConstant; positivity)

/-- Blueprint `lem:coulomb-lipschitz`. -/
theorem coulombEnergy_lipschitz (E F : Set AmbientSpace)
    (hEm : NullMeasurableSet E volume) (hFm : NullMeasurableSet F volume)
    {M : ℝ} (hM : 0 ≤ M) (hE : volume E ≤ ENNReal.ofReal M)
    (hF : volume F ≤ ENNReal.ofReal M) :
    |(coulombEnergy E).toReal - (coulombEnergy F).toReal| ≤
      coulombBoundConstant * M ^ ((2 : ℝ) / 3) * volume.real (E ∆ F) := by
  have hEfin : volume E < ∞ := hE.trans_lt ENNReal.ofReal_lt_top
  have hFfin : volume F < ∞ := hF.trans_lt ENNReal.ofReal_lt_top
  have hdiff : volume (E ∆ F) < ∞ :=
    (measure_mono symmDiff_subset_union).trans_lt
      ((measure_union_le E F).trans_lt (ENNReal.add_lt_top.mpr ⟨hEfin, hFfin⟩))
  let g := fun x => (E.indicator (fun _ => (1 : ℝ)) x - F.indicator (fun _ => 1) x) *
    ((coulombPotential E x).toReal + (coulombPotential F x).toReal)
  have hsupport : (E ∆ F).indicator g = g := by
    ext x
    by_cases hxE : x ∈ E <;> by_cases hxF : x ∈ F <;> simp [g, hxE, hxF, mem_symmDiff]
  have hnorm : ∀ x, ‖g x‖ ≤ 2 * coulombBoundConstant * M ^ ((2 : ℝ) / 3) := by
    intro x
    have hsum : |(coulombPotential E x).toReal + (coulombPotential F x).toReal| ≤
        2 * coulombBoundConstant * M ^ ((2 : ℝ) / 3) := by
      rw [abs_of_nonneg (add_nonneg ENNReal.toReal_nonneg ENNReal.toReal_nonneg)]
      linarith [coulombPotential_toReal_le_of_volume_le E hM hE x,
        coulombPotential_toReal_le_of_volume_le F hM hF x]
    have hchi : |E.indicator (fun _ => (1 : ℝ)) x - F.indicator (fun _ => 1) x| ≤ 1 := by
      by_cases hxE : x ∈ E <;> by_cases hxF : x ∈ F <;> simp [hxE, hxF]
    calc
      _ = |E.indicator (fun _ => (1 : ℝ)) x - F.indicator (fun _ => 1) x| *
          |(coulombPotential E x).toReal + (coulombPotential F x).toReal| := by
        exact abs_mul _ _
      _ ≤ 1 * (2 * coulombBoundConstant * M ^ ((2 : ℝ) / 3)) :=
        mul_le_mul hchi hsum (abs_nonneg _) (by norm_num)
      _ = _ := one_mul _
  have hint : ‖∫ x, g x‖ ≤
      (2 * coulombBoundConstant * M ^ ((2 : ℝ) / 3)) * volume.real (E ∆ F) := by
    calc
      _ = ‖∫ x in E ∆ F, g x‖ := by
        rw [← integral_indicator₀ (hEm.symmDiff hFm), hsupport]
      _ ≤ _ := norm_setIntegral_le_of_norm_le_const hdiff (fun x _ => hnorm x)
  rw [coulombEnergy_bilinear E F hEm hFm hEfin hFfin]
  change |(1 / 2 : ℝ) * ∫ x, g x| ≤ _
  rw [abs_mul, abs_of_pos (by norm_num : (0 : ℝ) < 1 / 2)]
  have h := mul_le_mul_of_nonneg_left hint (by norm_num : (0 : ℝ) ≤ 1 / 2)
  simp only [Real.norm_eq_abs] at h
  nlinarith only [h]

/-- For finite-volume sets this is the L¹ distance between their indicator functions. -/
theorem integral_abs_indicator_sub (E F : Set AmbientSpace)
    (hEm : NullMeasurableSet E volume) (hFm : NullMeasurableSet F volume) :
    (∫ x, |E.indicator (fun _ => (1 : ℝ)) x - F.indicator (fun _ => 1) x|) =
      volume.real (E ∆ F) := by
  calc
    _ = ∫ x, (E ∆ F).indicator (fun _ => (1 : ℝ)) x := by
      apply integral_congr_ae
      filter_upwards with x
      by_cases hxE : x ∈ E <;> by_cases hxF : x ∈ F <;> simp [hxE, hxF, mem_symmDiff]
    _ = _ := by
      rw [integral_indicator₀ (hEm.symmDiff hFm), setIntegral_const]
      simp

/-- Coulomb energy is continuous for convergence in symmetric-difference volume,
within any fixed finite volume bound. -/
theorem tendsto_coulombEnergy_of_symmDiff {E : ℕ → Set AmbientSpace} {F : Set AmbientSpace}
    (hEm : ∀ n, NullMeasurableSet (E n) volume) (hFm : NullMeasurableSet F volume)
    {M : ℝ} (hM : 0 ≤ M) (hE : ∀ n, volume (E n) ≤ ENNReal.ofReal M)
    (hF : volume F ≤ ENNReal.ofReal M)
    (hconv : Tendsto (fun n => volume.real (E n ∆ F)) atTop (𝓝 0)) :
    Tendsto (fun n => (coulombEnergy (E n)).toReal) atTop (𝓝 (coulombEnergy F).toReal) := by
  rw [tendsto_iff_dist_tendsto_zero]
  simp only [Real.dist_eq]
  apply squeeze_zero (fun n => abs_nonneg _) (fun n => coulombEnergy_lipschitz (E n) F
    (hEm n) hFm hM (hE n) hF)
  simpa only [mul_zero] using hconv.const_mul (coulombBoundConstant * M ^ ((2 : ℝ) / 3))

/-- The global L¹-convergence consequence in blueprint `lem:coulomb-lipschitz`. -/
theorem tendsto_coulombEnergy_of_l1 {E : ℕ → Set AmbientSpace} {F : Set AmbientSpace}
    (hEm : ∀ n, NullMeasurableSet (E n) volume) (hFm : NullMeasurableSet F volume)
    {M : ℝ} (hM : 0 ≤ M) (hE : ∀ n, volume (E n) ≤ ENNReal.ofReal M)
    (hF : volume F ≤ ENNReal.ofReal M)
    (hconv : Tendsto (fun n => ∫ x,
      |(E n).indicator (fun _ => (1 : ℝ)) x - F.indicator (fun _ => 1) x|) atTop (𝓝 0)) :
    Tendsto (fun n => (coulombEnergy (E n)).toReal) atTop (𝓝 (coulombEnergy F).toReal) := by
  apply tendsto_coulombEnergy_of_symmDiff hEm hFm hM hE hF
  simpa only [integral_abs_indicator_sub _ F (hEm _) hFm] using hconv

/-! ## Disjoint unions and positive interaction -/

theorem coulombPotential_union (E F : Set AmbientSpace)
    (hFm : NullMeasurableSet F volume) (hEF : Disjoint E F) (x : AmbientSpace) :
    coulombPotential (E ∪ F) x = coulombPotential E x + coulombPotential F x := by
  simp only [coulombPotential, Measure.restrict_union₀ hEF.aedisjoint hFm,
    lintegral_add_measure]

theorem coulombInteraction_union_left (E F G : Set AmbientSpace)
    (hFm : NullMeasurableSet F volume) (hEF : Disjoint E F) :
    coulombInteraction (E ∪ F) G = coulombInteraction E G + coulombInteraction F G := by
  simp only [coulombInteraction_eq_lintegral_potential,
    Measure.restrict_union₀ hEF.aedisjoint hFm, lintegral_add_measure]

theorem coulombInteraction_union_right (E F G : Set AmbientSpace)
    (hGm : NullMeasurableSet G volume) (hFG : Disjoint F G) :
    coulombInteraction E (F ∪ G) = coulombInteraction E F + coulombInteraction E G := by
  rw [coulombInteraction_symm E (F ∪ G), coulombInteraction_union_left F G E hGm hFG,
    coulombInteraction_symm F E, coulombInteraction_symm G E]

/-- Blueprint `lem:coulomb-disjoint`, in nonnegative extended reals. -/
theorem coulombEnergy_union (E F : Set AmbientSpace)
    (hFm : NullMeasurableSet F volume) (hEF : Disjoint E F) :
    coulombEnergy (E ∪ F) = coulombEnergy E + coulombEnergy F + coulombInteraction E F := by
  simp only [coulombEnergy_eq_half_interaction]
  rw [coulombInteraction_union_left E F (E ∪ F) hFm hEF,
    coulombInteraction_union_right E E F hFm hEF,
    coulombInteraction_union_right F E F hFm hEF, coulombInteraction_symm F E]
  calc
    _ = (2 : ℝ≥0∞)⁻¹ * coulombInteraction E E + (2 : ℝ≥0∞)⁻¹ * coulombInteraction F F +
        ((2 : ℝ≥0∞)⁻¹ + (2 : ℝ≥0∞)⁻¹) * coulombInteraction E F := by ring
    _ = _ := by rw [ENNReal.inv_two_add_inv_two, one_mul]

/-- The kernel is positive everywhere, including its infinite diagonal values. -/
theorem coulombKernel_pos (x y : AmbientSpace) : 0 < coulombKernel x y := by
  exact ENNReal.inv_pos.mpr ENNReal.ofReal_ne_top

/-- Positive-volume sets have positive interaction, with no disjointness requirement. -/
theorem coulombInteraction_pos (E F : Set AmbientSpace)
    (hE : 0 < volume E) (hF : 0 < volume F) : 0 < coulombInteraction E F := by
  unfold coulombInteraction
  rw [setLIntegral_pos_iff measurable_coulombKernel]
  have hsupport : Function.support (fun p : AmbientSpace × AmbientSpace =>
      coulombKernel p.1 p.2) = univ := by
    ext p
    simp only [Function.mem_support, mem_univ, iff_true]
    exact (coulombKernel_pos p.1 p.2).ne'
  rw [hsupport, univ_inter, Measure.volume_eq_prod, Measure.prod_prod]
  exact ENNReal.mul_pos_iff.mpr ⟨hE, hF⟩

/-- The disjoint-union formula for the real energies in the paper. -/
theorem coulombEnergy_toReal_union (E F : Set AmbientSpace)
    (hFm : NullMeasurableSet F volume) (hEF : Disjoint E F)
    (hE : volume E < ∞) (hF : volume F < ∞) :
    (coulombEnergy (E ∪ F)).toReal = (coulombEnergy E).toReal +
      (coulombEnergy F).toReal + (coulombInteraction E F).toReal := by
  have hDE := (coulombEnergy_lt_top E hE).ne
  have hDF := (coulombEnergy_lt_top F hF).ne
  have hI := (coulombInteraction_lt_top E F hE hF).ne
  rw [coulombEnergy_union E F hFm hEF, ENNReal.toReal_add (ENNReal.add_ne_top.mpr ⟨hDE, hDF⟩) hI,
    ENNReal.toReal_add hDE hDF]

/-- The strict positivity assertion in blueprint `lem:coulomb-disjoint`. -/
theorem coulombInteraction_toReal_pos (E F : Set AmbientSpace)
    (hE : 0 < volume E) (hF : 0 < volume F)
    (hEfin : volume E < ∞) (hFfin : volume F < ∞) :
    0 < (coulombInteraction E F).toReal :=
  ENNReal.toReal_pos (coulombInteraction_pos E F hE hF).ne'
    (coulombInteraction_lt_top E F hEfin hFfin).ne

/-! ## Decay under translation -/


/-- A uniform separation bounds the interaction by the product of the volumes. -/
theorem coulombInteraction_le_of_separated (E F : Set AmbientSpace) {d : ℝ}
    (hsep : ∀ x ∈ E, ∀ y ∈ F, d ≤ ‖x - y‖) :
    coulombInteraction E F ≤ volume E * volume F / ENNReal.ofReal d := by
  calc
    _ ≤ ∫⁻ p in E ×ˢ F, (ENNReal.ofReal d)⁻¹ := by
      apply setLIntegral_mono measurable_const
      intro p hp
      exact ENNReal.inv_le_inv.mpr (ENNReal.ofReal_le_ofReal (hsep p.1 hp.1 p.2 hp.2))
    _ = _ := by
      rw [setLIntegral_const, Measure.volume_eq_prod, Measure.prod_prod]
      simp only [div_eq_mul_inv, mul_comm]

/-- Blueprint `lem:cross-decay`, in nonnegative extended reals. -/
theorem coulombInteraction_translate_le {E F : Set AmbientSpace} {R t : ℝ}
    {e : AmbientSpace} (hE : E ⊆ ball 0 R) (hF : F ⊆ ball 0 R)
    (he : ‖e‖ = 1) (ht : 2 * R < t) :
    coulombInteraction E ((fun y => y + t • e) '' F) ≤
      volume E * volume F / ENNReal.ofReal (t - 2 * R) := by
  have hvol : volume ((fun y => y + t • e) '' F) = volume F := by
    have hset : (fun y => y + t • e) '' F = (fun y => y + -(t • e)) ⁻¹' F := by
      ext y
      constructor
      · rintro ⟨z, hz, rfl⟩
        simpa using hz
      · intro hy
        exact ⟨y + -(t • e), hy, by simp⟩
    rw [hset, measure_preimage_add_right]
  rw [← hvol]
  apply coulombInteraction_le_of_separated
  intro x hx y hy
  obtain ⟨z, hz, rfl⟩ := hy
  have hxR : ‖x‖ < R := by simpa using hE hx
  have hzR : ‖z‖ < R := by simpa using hF hz
  have ht0 : 0 ≤ t := by linarith [norm_nonneg x]
  have hnorm : ‖t • e‖ = t := by rw [norm_smul, he, mul_one, Real.norm_eq_abs, abs_of_nonneg ht0]
  have hid : t • e = (x - z) - (x - (z + t • e)) := by abel
  have htri := norm_sub_le (x - z) (x - (z + t • e))
  rw [← hid, hnorm] at htri
  have htri' := norm_sub_le x z
  linarith

/-- The real-valued cross-interaction estimate for bounded sets. -/
theorem coulombInteraction_translate_toReal_le {E F : Set AmbientSpace} {R t : ℝ}
    {e : AmbientSpace} (hE : E ⊆ ball 0 R) (hF : F ⊆ ball 0 R)
    (he : ‖e‖ = 1) (ht : 2 * R < t) :
    (coulombInteraction E ((fun y => y + t • e) '' F)).toReal ≤
      (volume E).toReal * (volume F).toReal / (t - 2 * R) := by
  have hEfin := (Metric.isBounded_ball.subset hE).measure_lt_top (μ := volume)
  have hFfin := (Metric.isBounded_ball.subset hF).measure_lt_top (μ := volume)
  have hd : 0 < t - 2 * R := sub_pos.mpr ht
  have hfinite : volume E * volume F / ENNReal.ofReal (t - 2 * R) ≠ ∞ := by
    apply ENNReal.div_ne_top
    · exact ENNReal.mul_ne_top hEfin.ne hFfin.ne
    · exact (ENNReal.ofReal_pos.mpr hd).ne'
  have h := ENNReal.toReal_mono hfinite (coulombInteraction_translate_le hE hF he ht)
  simpa only [ENNReal.toReal_div, ENNReal.toReal_mul, ENNReal.toReal_ofReal hd.le] using h

/-- Blueprint `lem:cross-decay`: interaction tends to zero along a unit direction. -/
theorem tendsto_coulombInteraction_translate {E F : Set AmbientSpace} {R : ℝ}
    {e : AmbientSpace} (hE : E ⊆ ball 0 R) (hF : F ⊆ ball 0 R) (he : ‖e‖ = 1) :
    Tendsto (fun t : ℝ => (coulombInteraction E ((fun y => y + t • e) '' F)).toReal)
      atTop (𝓝 0) := by
  apply squeeze_zero' (Eventually.of_forall fun _ => ENNReal.toReal_nonneg)
    (eventually_gt_atTop (2 * R) |>.mono fun _ ht =>
      coulombInteraction_translate_toReal_le hE hF he ht)
  apply tendsto_const_nhds.div_atTop
  simpa only [sub_eq_add_neg, id_eq] using tendsto_atTop_add_const_right atTop (-(2 * R))
    (tendsto_id : Tendsto (fun t : ℝ => t) atTop atTop)


end LiquidDrop

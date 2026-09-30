module

public import NoCompromise.Variation.Volume
public import NoCompromise.Energy.Coulomb
public import Mathlib.Analysis.Calculus.ParametricIntegral
public import Mathlib.Analysis.InnerProductSpace.Calculus

@[expose] public section

/-!
# The bulk first variation of Coulomb energy

The energy definition retains its extended-real singular kernel. Its established
diagonal-null bridge permits differentiation of the real kernel after pulling
both variables back by the actual straight perturbation. No boundary formula is
assumed here.
-/

noncomputable section

open Set Filter MeasureTheory Metric
open scoped Topology NNReal ENNReal RealInnerProductSpace

namespace LiquidDrop

set_option maxSynthPendingDepth 8

local notation "E₃" => EuclideanSpace ℝ (Fin 3)
local notation "L₃" => E₃ →L[ℝ] E₃

/-- The signed determinant of a straight perturbation. -/
def straightJacobian (X : E₃ → E₃) (t : ℝ) (x : E₃) : ℝ :=
  (ContinuousLinearMap.id ℝ E₃ + t • fderiv ℝ X x).det

@[simp] lemma straightJacobian_zero (X : E₃ → E₃) (x : E₃) :
    straightJacobian X 0 x = 1 := by
  rw [straightJacobian, det_id_add_smul_three]
  simp

lemma hasDerivAt_straightJacobian (X : E₃ → E₃) (x : E₃) :
    HasDerivAt (fun t => straightJacobian X t x) (divergenceN X x) 0 := by
  simp only [straightJacobian, det_id_add_smul_three, standardMatrix3_fderiv_trace]
  simpa [Pi.add_def, Pi.pow_def] using (((hasDerivAt_const (0 : ℝ) (1 : ℝ)).add
    ((hasDerivAt_id (0 : ℝ)).mul_const (divergenceN X x))).add
    (((hasDerivAt_id (0 : ℝ)).pow 2).mul_const
      (standardMatrix3 (cofactor3 (fderiv ℝ X x))).trace)).add
    (((hasDerivAt_id (0 : ℝ)).pow 3).mul_const (fderiv ℝ X x).det)

/-- Reciprocal-distance derivative along an affine motion, away from the singularity. -/
lemma hasDerivAt_inv_norm_add_smul {a b : E₃} (ha : a ≠ 0) :
    HasDerivAt (fun t : ℝ => ‖a + t • b‖⁻¹) (-inner ℝ a b / ‖a‖ ^ 3) 0 := by
  have hn : ‖a‖ ≠ 0 := norm_ne_zero_iff.mpr ha
  have hd : HasDerivAt (fun t : ℝ => a + t • b) b 0 := by
    simpa only [Pi.add_def, id_eq, zero_add, one_smul] using
      (hasDerivAt_const (0 : ℝ) a).add ((hasDerivAt_id (0 : ℝ)).smul_const b)
  have hs := hd.norm_sq.sqrt (by simpa using pow_ne_zero 2 hn)
  have hnorm : HasDerivAt (fun t : ℝ => ‖a + t • b‖) (inner ℝ a b / ‖a‖) 0 := by
    convert! hs using 1
    · funext t
      rw [Real.sqrt_sq (norm_nonneg _)]
    · simp only [zero_smul, add_zero, Real.sqrt_sq (norm_nonneg a)]
      field_simp
  convert! hnorm.inv (by simpa using hn) using 1
  simp only [zero_smul, add_zero]
  field_simp

/-- The real pulled-back energy density. The total reciprocal convention is zero on the diagonal. -/
def straightCoulombDensity (X : E₃ → E₃) (t : ℝ) (p : E₃ × E₃) : ℝ :=
  straightJacobian X t p.1 * straightJacobian X t p.2 *
    ‖straightPerturbation X t p.1 - straightPerturbation X t p.2‖⁻¹

@[simp] lemma straightCoulombDensity_zero (X : E₃ → E₃) (p : E₃ × E₃) :
    straightCoulombDensity X 0 p = ‖p.1 - p.2‖⁻¹ := by
  simp [straightCoulombDensity]

/-- The symmetric bulk first-variation density, before the energy's factor `1/2`. -/
def coulombBulkVariationIntegrand (X : E₃ → E₃) (p : E₃ × E₃) : ℝ :=
  (divergenceN X p.1 + divergenceN X p.2) * ‖p.1 - p.2‖⁻¹ -
    inner ℝ (p.1 - p.2) (X p.1 - X p.2) / ‖p.1 - p.2‖ ^ 3

lemma hasDerivAt_straightCoulombDensity (X : E₃ → E₃) (p : E₃ × E₃) :
    HasDerivAt (fun t => straightCoulombDensity X t p) (coulombBulkVariationIntegrand X p) 0 := by
  by_cases hp : p.1 = p.2
  · simpa [straightCoulombDensity, coulombBulkVariationIntegrand, hp] using
      hasDerivAt_const (0 : ℝ) (0 : ℝ)
  have hk := hasDerivAt_inv_norm_add_smul (b := X p.1 - X p.2) (sub_ne_zero.mpr hp)
  have heq (t : ℝ) : straightPerturbation X t p.1 - straightPerturbation X t p.2 =
      (p.1 - p.2) + t • (X p.1 - X p.2) := by
    simp only [straightPerturbation, smul_sub]
    abel
  have h := ((hasDerivAt_straightJacobian X p.1).mul
    (hasDerivAt_straightJacobian X p.2)).mul hk
  simpa only [straightCoulombDensity, heq, coulombBulkVariationIntegrand,
    Pi.mul_def, straightJacobian_zero, mul_one, one_mul, zero_smul, add_zero, neg_div,
    sub_eq_add_neg] using h

/-- Lower separation and reciprocal-kernel control for sufficiently small perturbations. -/
lemma inv_norm_straightPerturbation_sub_bound {X : E₃ → E₃} {L : ℝ≥0}
    (hXL : LipschitzWith L X) {t : ℝ} (ht : |t| * L ≤ 1 / 2) (x y : E₃) :
    ‖straightPerturbation X t x - straightPerturbation X t y‖⁻¹ ≤ 2 * ‖x - y‖⁻¹ ∧
    |‖straightPerturbation X t x - straightPerturbation X t y‖⁻¹ - ‖x - y‖⁻¹| ≤
      2 * L * |t| * ‖x - y‖⁻¹ := by
  by_cases hxy : x = y
  · simp [hxy]
  let r := ‖x - y‖
  let s := ‖straightPerturbation X t x - straightPerturbation X t y‖
  have hr : 0 < r := norm_pos_iff.mpr (sub_ne_zero.mpr hxy)
  have hlow : r / 2 ≤ s := by
    have h := norm_sub_straightPerturbation_ge hXL t x y
    dsimp [r, s]
    nlinarith [mul_le_mul_of_nonneg_right ht (norm_nonneg (x - y))]
  have hs : 0 < s := lt_of_lt_of_le (by positivity) hlow
  have hdist : |s - r| ≤ |t| * L * r := by
    have hnorm := abs_norm_sub_norm_le
      (straightPerturbation X t x - straightPerturbation X t y) (x - y)
    have heq : (straightPerturbation X t x - straightPerturbation X t y) - (x - y) =
        t • (X x - X y) := by simp only [straightPerturbation, smul_sub]; abel
    rw [heq, norm_smul, Real.norm_eq_abs] at hnorm
    exact hnorm.trans ((mul_le_mul_of_nonneg_left (hXL.norm_sub_le x y)
      (abs_nonneg t)).trans_eq (mul_assoc _ _ _).symm)
  have hinv : s⁻¹ ≤ 2 * r⁻¹ := by
    rw [← one_div, ← div_eq_mul_inv]
    apply (div_le_div_iff₀ hs hr).mpr
    linarith
  change s⁻¹ ≤ 2 * r⁻¹ ∧ |s⁻¹ - r⁻¹| ≤ 2 * L * |t| * r⁻¹
  refine ⟨hinv, ?_⟩
  calc
    _ = |s - r| * s⁻¹ * r⁻¹ := by
      rw [inv_sub_inv' hs.ne' hr.ne', abs_mul, abs_mul,
        abs_of_nonneg (inv_nonneg.mpr hs.le), abs_of_nonneg (inv_nonneg.mpr hr.le), abs_sub_comm]
      ring
    _ ≤ (|t| * L * r) * s⁻¹ * r⁻¹ := by gcongr
    _ = |t| * L * s⁻¹ := by field_simp [hr.ne']
    _ ≤ |t| * L * (2 * r⁻¹) := by gcongr
    _ = _ := by ring

/-- Uniform determinant and first-difference bounds. -/
lemma exists_straightJacobian_bounds {X : E₃ → E₃} (hXC : ContDiff ℝ 1 X)
    (hc : HasCompactSupport X) :
    ∃ K : ℝ, 1 ≤ K ∧ ∀ t : ℝ, |t| ≤ 1 → ∀ x : E₃,
      |straightJacobian X t x| ≤ K ∧ |straightJacobian X t x - 1| ≤ K * |t| := by
  obtain ⟨C, hC, hrem⟩ := exists_uniform_straight_cofactor_expansion hXC hc
  obtain ⟨B, hB, hb⟩ := exists_bound_comp_fderiv hXC hc
    continuous_standardMatrix3.matrix_trace
  refine ⟨C + B + 1, by linarith, ?_⟩
  intro t ht x
  have htsq : t ^ 2 ≤ |t| := by
    nlinarith [sq_abs t, mul_nonneg (abs_nonneg t) (sub_nonneg.mpr ht)]
  have hdiv : |divergenceN X x| ≤ B := by
    simpa only [Real.norm_eq_abs, standardMatrix3_fderiv_trace] using hb x
  have herror : |straightJacobian X t x - 1 - t * divergenceN X x| ≤ C * t ^ 2 := by
    simpa only [straightJacobian,
      fderiv_straightPerturbation (hXC.differentiable (by simp) x) t] using (hrem t ht x).2.1
  have hdiff : |straightJacobian X t x - 1| ≤ (C + B) * |t| := by
    calc
      _ = |(straightJacobian X t x - 1 - t * divergenceN X x) +
          t * divergenceN X x| := by congr 1; ring
      _ ≤ |straightJacobian X t x - 1 - t * divergenceN X x| +
          |t * divergenceN X x| := abs_add_le _ _
      _ ≤ C * t ^ 2 + |t| * B := by
        rw [abs_mul]
        exact add_le_add herror (mul_le_mul_of_nonneg_left hdiv (abs_nonneg t))
      _ ≤ _ := by nlinarith [mul_le_mul_of_nonneg_left htsq hC]
  constructor
  · have htri := abs_add_le (straightJacobian X t x - 1) 1
    have hmul := mul_le_mul_of_nonneg_left ht (show 0 ≤ C + B by linarith)
    simp only [sub_add_cancel, abs_one, mul_one] at htri hmul
    linarith
  · nlinarith [abs_nonneg t]

/-- An integrable Coulomb kernel dominates the density's difference quotient. -/
lemma straightCoulombDensity_sub_zero_bound {X : E₃ → E₃} {L : ℝ≥0}
    (hXL : LipschitzWith L X) {K t : ℝ} (hK : 1 ≤ K)
    (hJ : ∀ x, |straightJacobian X t x| ≤ K ∧
      |straightJacobian X t x - 1| ≤ K * |t|)
    (ht : |t| * L ≤ 1 / 2) (p : E₃ × E₃) :
    |straightCoulombDensity X t p - straightCoulombDensity X 0 p| ≤
      (2 * (K ^ 2 + K) + 2 * L) * ‖p.1 - p.2‖⁻¹ * |t| := by
  have hK0 : 0 ≤ K := by linarith
  have hprod : |straightJacobian X t p.1 * straightJacobian X t p.2 - 1| ≤
      (K ^ 2 + K) * |t| := by
    calc
      _ = |straightJacobian X t p.1 * (straightJacobian X t p.2 - 1) +
          (straightJacobian X t p.1 - 1)| := by congr 1; ring
      _ ≤ |straightJacobian X t p.1| * |straightJacobian X t p.2 - 1| +
          |straightJacobian X t p.1 - 1| := by
        simpa only [abs_mul] using abs_add_le
          (straightJacobian X t p.1 * (straightJacobian X t p.2 - 1))
          (straightJacobian X t p.1 - 1)
      _ ≤ K * (K * |t|) + K * |t| :=
        add_le_add (mul_le_mul (hJ p.1).1 (hJ p.2).2 (abs_nonneg _) hK0) (hJ p.1).2
      _ = _ := by ring
  obtain ⟨hk, hd⟩ := inv_norm_straightPerturbation_sub_bound hXL ht p.1 p.2
  rw [straightCoulombDensity_zero, straightCoulombDensity]
  calc
    _ = |(straightJacobian X t p.1 * straightJacobian X t p.2 - 1) *
        ‖straightPerturbation X t p.1 - straightPerturbation X t p.2‖⁻¹ +
        (‖straightPerturbation X t p.1 - straightPerturbation X t p.2‖⁻¹ -
          ‖p.1 - p.2‖⁻¹)| := by congr 1; ring
    _ ≤ |straightJacobian X t p.1 * straightJacobian X t p.2 - 1| *
        ‖straightPerturbation X t p.1 - straightPerturbation X t p.2‖⁻¹ +
        |‖straightPerturbation X t p.1 - straightPerturbation X t p.2‖⁻¹ -
          ‖p.1 - p.2‖⁻¹| := by
      simpa only [abs_mul, abs_of_nonneg (inv_nonneg.mpr (norm_nonneg _))] using
        abs_add_le ((straightJacobian X t p.1 * straightJacobian X t p.2 - 1) *
          ‖straightPerturbation X t p.1 - straightPerturbation X t p.2‖⁻¹)
          (‖straightPerturbation X t p.1 - straightPerturbation X t p.2‖⁻¹ -
            ‖p.1 - p.2‖⁻¹)
    _ ≤ ((K ^ 2 + K) * |t|) * (2 * ‖p.1 - p.2‖⁻¹) +
        2 * L * |t| * ‖p.1 - p.2‖⁻¹ :=
      add_le_add (mul_le_mul hprod hk (inv_nonneg.mpr (norm_nonneg _)) (by positivity)) hd
    _ = _ := by ring

/-- Scalar dominated differentiation from a bound on differences from the base point. -/
lemma hasDerivAt_integral_of_dominated_origin_bound
    {α : Type*} [MeasurableSpace α] {μ : Measure α} {F : ℝ → α → ℝ}
    {F' bound : α → ℝ} {s : Set ℝ} {t₀ : ℝ} (hs : s ∈ 𝓝 t₀)
    (hm : ∀ t ∈ s, AEStronglyMeasurable (F t) μ) (hi : Integrable (F t₀) μ)
    (hm' : AEStronglyMeasurable F' μ)
    (hb : ∀ᵐ a ∂μ, ∀ t ∈ s, ‖F t a - F t₀ a‖ ≤ bound a * ‖t - t₀‖)
    (hbi : Integrable bound μ) (hd : ∀ᵐ a ∂μ, HasDerivAt (fun t => F t a) (F' a) t₀) :
    Integrable F' μ ∧ HasDerivAt (fun t => ∫ a, F t a ∂μ) (∫ a, F' a ∂μ) t₀ := by
  let L : ℝ →L[ℝ] ℝ →L[ℝ] ℝ := ContinuousLinearMap.smulRightL ℝ ℝ ℝ 1
  have hd' : ∀ᵐ a ∂μ, HasFDerivAt (fun t => F t a) (L (F' a)) t₀ :=
    hd.mono fun _ h => h.hasFDerivAt
  have hmL : AEStronglyMeasurable (L ∘ F') μ := L.continuous.comp_aestronglyMeasurable hm'
  obtain ⟨hiL, hdL⟩ := hasFDerivAt_integral_of_dominated_loc_of_lip'
    hs hm hi hmL hb hbi hd'
  have hi' : Integrable F' μ := by
    rw [← integrable_norm_iff hmL] at hiL
    apply (integrable_norm_iff hm').mp
    simpa [L, Function.comp_def] using! hiL
  refine ⟨hi', ?_⟩
  rw [hasDerivAt_iff_hasFDerivAt]
  simpa only [Function.comp_def, ContinuousLinearMap.integral_comp_comm _ hi'] using! hdL

lemma continuous_straightJacobian {X : E₃ → E₃} (hXC : ContDiff ℝ 1 X) (t : ℝ) :
    Continuous (straightJacobian X t) := by
  apply ContinuousLinearMap.continuous_det.comp
  have hd := hXC.continuous_fderiv (by simp)
  fun_prop

lemma measurable_straightCoulombDensity {X : E₃ → E₃} (hXC : ContDiff ℝ 1 X) (t : ℝ) :
    Measurable (straightCoulombDensity X t) := by
  have hF := (contDiff_straightPerturbation hXC t).continuous
  exact (((continuous_straightJacobian hXC t).comp continuous_fst).mul
    ((continuous_straightJacobian hXC t).comp continuous_snd)).measurable.mul
      (((hF.comp continuous_fst).sub (hF.comp continuous_snd)).norm.measurable.inv)

lemma measurable_coulombBulkVariationIntegrand {X : E₃ → E₃} (hXC : ContDiff ℝ 1 X) :
    Measurable (coulombBulkVariationIntegrand X) := by
  have hdiv : Continuous (divergenceN X) :=
    continuous_standardMatrix3.matrix_trace.comp (hXC.continuous_fderiv (by simp))
  have hn : Continuous (fun p : E₃ × E₃ => ‖p.1 - p.2‖) :=
    (continuous_fst.sub continuous_snd).norm
  have hi : Continuous (fun p : E₃ × E₃ => inner ℝ (p.1 - p.2) (X p.1 - X p.2)) :=
    (continuous_fst.sub continuous_snd).inner
      ((hXC.continuous.comp continuous_fst).sub (hXC.continuous.comp continuous_snd))
  exact (((hdiv.comp continuous_fst).add (hdiv.comp continuous_snd)).measurable.mul
    hn.measurable.inv).sub (hi.measurable.div (hn.pow 3).measurable)

/-- Differentiation of the actual pulled-back real density over an arbitrary finite-volume set. -/
lemma hasDerivAt_integral_straightCoulombDensity {X : E₃ → E₃}
    (hXC : ContDiff ℝ 1 X) (hc : HasCompactSupport X) {E : Set E₃}
    (hEfin : volume E < ∞) :
    IntegrableOn (coulombBulkVariationIntegrand X) (E ×ˢ E) ∧
      HasDerivAt (fun t => ∫ p in E ×ˢ E, straightCoulombDensity X t p)
        (∫ p in E ×ˢ E, coulombBulkVariationIntegrand X p) 0 := by
  obtain ⟨K, hK, hJ⟩ := exists_straightJacobian_bounds hXC hc
  let L : ℝ≥0 := ‖straightDerivativeField hXC hc‖₊
  let s : Set ℝ := {t | |t| < 1 ∧ |t| * L < 1 / 2}
  have hs : s ∈ 𝓝 0 := by
    have ha : Continuous (fun t : ℝ => |t|) := continuous_abs
    have hb : Continuous (fun t : ℝ => |t| * L) := by fun_prop
    exact (ha.continuousAt.eventually (gt_mem_nhds (by norm_num))).and
      (hb.continuousAt.eventually (gt_mem_nhds (by norm_num)))
  apply hasDerivAt_integral_of_dominated_origin_bound hs
    (bound := fun p : E₃ × E₃ => (2 * (K ^ 2 + K) + 2 * L) * ‖p.1 - p.2‖⁻¹)
  · exact fun t _ => (measurable_straightCoulombDensity hXC t).aestronglyMeasurable
  · rw [show straightCoulombDensity X 0 = (fun p => ‖p.1 - p.2‖⁻¹) by
      funext p; exact straightCoulombDensity_zero X p]
    exact integrableOn_coulombKernel_prod E E hEfin hEfin
  · exact (measurable_coulombBulkVariationIntegrand hXC).aestronglyMeasurable
  · apply Eventually.of_forall
    intro p t ht
    simpa only [Real.norm_eq_abs, sub_zero] using straightCoulombDensity_sub_zero_bound
      (lipschitzWith_straightDerivativeField hXC hc) hK (hJ t ht.1.le) ht.2.le p
  · exact (integrableOn_coulombKernel_prod E E hEfin hEfin).const_mul _
  · exact Eventually.of_forall (hasDerivAt_straightCoulombDensity X)

/-- Change of variables in both variables, with Lebesgue-measurable source sets. -/
lemma integral_coulombKernel_straight_image {X : E₃ → E₃}
    (hXC : ContDiff ℝ 1 X) {L : ℝ≥0} (hXL : LipschitzWith L X) {t : ℝ}
    (ht : |t| * L < 1) {E : Set E₃} (hE : NullMeasurableSet E volume)
    (hpos : ∀ x : E₃, 0 < straightJacobian X t x) :
    (∫ p in (straightPerturbation X t '' E) ×ˢ (straightPerturbation X t '' E),
      ‖p.1 - p.2‖⁻¹) = ∫ p in E ×ˢ E, straightCoulombDensity X t p := by
  let F : E₃ × E₃ → E₃ × E₃ :=
    Prod.map (straightPerturbation X t) (straightPerturbation X t)
  let A (x : E₃) : L₃ := ContinuousLinearMap.id ℝ E₃ + t • fderiv ℝ X x
  let D (p : E₃ × E₃) := (A p.1).prodMap (A p.2)
  have hD (p : E₃ × E₃) : HasFDerivAt F (D p) p :=
    HasFDerivAt.prodMap p
      (hasFDerivAt_straightPerturbation (hXC.differentiable (by simp) p.1).hasFDerivAt t)
      (hasFDerivAt_straightPerturbation (hXC.differentiable (by simp) p.2).hasFDerivAt t)
  have hinj : Function.Injective F :=
    (straightPerturbation_bijective hXL ht).1.prodMap (straightPerturbation_bijective hXL ht).1
  have hEP : NullMeasurableSet (E ×ˢ E) (volume : Measure (E₃ × E₃)) := hE.prod hE
  have : (volume : Measure (E₃ × E₃)).IsAddHaarMeasure := by
    rw [Measure.volume_eq_prod]
    infer_instance
  have hmap := map_withDensity_abs_det_fderiv_eq_addHaar volume hEP
    (fun p _ => (hD p).hasFDerivWithinAt) hinj.injOn
  have hF : Measurable F := ((contDiff_straightPerturbation hXC t).continuous.prodMap
    (contDiff_straightPerturbation hXC t).continuous).measurable
  have hg : StronglyMeasurable (fun p : E₃ × E₃ => ‖p.1 - p.2‖⁻¹) :=
    ((continuous_fst.sub continuous_snd).norm.measurable.inv).stronglyMeasurable
  have hdet (p : E₃ × E₃) :
      (D p).det = straightJacobian X t p.1 * straightJacobian X t p.2 := by
    exact LinearMap.det_prodMap (A p.1).toLinearMap (A p.2).toLinearMap
  have hw : Measurable (fun p : E₃ × E₃ => ENNReal.ofReal |(D p).det|) := by
    simp_rw [hdet]
    exact ENNReal.continuous_ofReal.measurable.comp
      ((((continuous_straightJacobian hXC t).comp continuous_fst).mul
        ((continuous_straightJacobian hXC t).comp continuous_snd)).abs.measurable)
  rw [← prodMap_image_prod, ← hmap, integral_map_of_stronglyMeasurable hF hg,
    integral_withDensity_eq_integral_toReal_smul hw (Eventually.of_forall fun _ =>
      ENNReal.ofReal_lt_top)]
  apply integral_congr_ae
  apply Eventually.of_forall
  intro p
  dsimp only
  rw [ENNReal.toReal_ofReal (abs_nonneg _), hdet,
    abs_of_pos (mul_pos (hpos p.1) (hpos p.2))]
  rfl

/-- The actual extended-real energy agrees near zero with the real pulled-back double integral. -/
lemma eventually_coulombEnergy_straightPerturbation_eq_integral {X : E₃ → E₃}
    (hXC : ContDiff ℝ 1 X) (hc : HasCompactSupport X) {E : Set E₃}
    (hE : NullMeasurableSet E volume) (hEfin : volume E < ∞) :
    ∀ᶠ t : ℝ in 𝓝 0,
      (coulombEnergy (straightPerturbation X t '' E)).toReal =
        (1 / 2 : ℝ) * ∫ p in E ×ˢ E, straightCoulombDensity X t p := by
  obtain ⟨δ, hδ, hpos⟩ := exists_pos_det_straightPerturbation hXC hc
  have htδ : ∀ᶠ t : ℝ in 𝓝 0, |t| < δ := by
    filter_upwards [Metric.ball_mem_nhds (0 : ℝ) hδ] with t ht
    simpa only [Metric.mem_ball, dist_zero_right, Real.norm_eq_abs] using ht
  have hsmall : ∀ᶠ t : ℝ in 𝓝 0, |t| * ‖straightDerivativeField hXC hc‖ < 1 := by
    have hcont : Continuous (fun t : ℝ => |t| * ‖straightDerivativeField hXC hc‖) := by
      fun_prop
    exact hcont.continuousAt.eventually (gt_mem_nhds (by simp))
  filter_upwards [htδ, hsmall] with t htδ ht
  rw [coulombEnergy_toReal _
    (volume_straightPerturbation_image_finite_and_toReal hXC hc ht hE hEfin).1]
  congr 1
  apply integral_coulombKernel_straight_image hXC
    (lipschitzWith_straightDerivativeField hXC hc) ht hE
  intro x
  simpa only [straightJacobian,
    fderiv_straightPerturbation (hXC.differentiable (by simp) x) t] using hpos t htδ x

/-- Bulk first variation of Coulomb energy for every finite-volume Lebesgue-measurable set.
The integrable density is symmetric; no boundary regularity or Gauss--Green premise is used. -/
theorem hasDerivAt_coulombEnergy_straightPerturbation {X : E₃ → E₃}
    (hXC : ContDiff ℝ 1 X) (hc : HasCompactSupport X) {E : Set E₃}
    (hE : NullMeasurableSet E volume) (hEfin : volume E < ∞) :
    HasDerivAt (fun t : ℝ => (coulombEnergy (straightPerturbation X t '' E)).toReal)
      ((1 / 2 : ℝ) * ∫ p in E ×ˢ E, coulombBulkVariationIntegrand X p) 0 := by
  exact ((hasDerivAt_integral_straightCoulombDensity hXC hc hEfin).2.const_mul
    (1 / 2)).congr_of_eventuallyEq
      (eventually_coulombEnergy_straightPerturbation_eq_integral hXC hc hE hEfin)

/-- The symmetric bulk density is absolutely integrable on every finite-volume product. -/
lemma integrableOn_coulombBulkVariationIntegrand {X : E₃ → E₃}
    (hXC : ContDiff ℝ 1 X) (hc : HasCompactSupport X) {E : Set E₃}
    (hEfin : volume E < ∞) : IntegrableOn (coulombBulkVariationIntegrand X) (E ×ˢ E) :=
  (hasDerivAt_integral_straightCoulombDensity hXC hc hEfin).1

/-- The unsymmetrized density used before integration by parts in the first variable. -/
def coulombBulkSingleIntegrand (X : E₃ → E₃) (p : E₃ × E₃) : ℝ :=
  divergenceN X p.1 * ‖p.1 - p.2‖⁻¹ - inner ℝ (p.1 - p.2) (X p.1) / ‖p.1 - p.2‖ ^ 3

lemma coulombBulkVariationIntegrand_eq_add_swap (X : E₃ → E₃) (p : E₃ × E₃) :
    coulombBulkVariationIntegrand X p =
      coulombBulkSingleIntegrand X p + coulombBulkSingleIntegrand X p.swap := by
  dsimp [coulombBulkVariationIntegrand, coulombBulkSingleIntegrand]
  rw [norm_sub_rev p.2 p.1, show p.2 - p.1 = -(p.1 - p.2) by abel,
    inner_neg_left, inner_sub_right]
  ring

/-- Symmetrization removes the factor `1/2` when the unsymmetrized density is integrable. -/
lemma integral_coulombBulkVariationIntegrand_eq_twice {X : E₃ → E₃} {E : Set E₃}
    (hi : IntegrableOn (coulombBulkSingleIntegrand X) (E ×ˢ E)) :
    (1 / 2 : ℝ) * (∫ p in E ×ˢ E, coulombBulkVariationIntegrand X p) =
      ∫ p in E ×ˢ E, coulombBulkSingleIntegrand X p := by
  have his : IntegrableOn (fun p => coulombBulkSingleIntegrand X p.swap) (E ×ˢ E) := by
    rw [IntegrableOn, Measure.volume_eq_prod, ← Measure.prod_restrict] at hi ⊢
    exact hi.swap
  simp_rw [coulombBulkVariationIntegrand_eq_add_swap]
  rw [integral_add hi his]
  have hswap : (∫ p in E ×ˢ E, coulombBulkSingleIntegrand X p.swap) =
      ∫ p in E ×ˢ E, coulombBulkSingleIntegrand X p := by
    rw [Measure.volume_eq_prod]
    exact setIntegral_prod_swap E E (coulombBulkSingleIntegrand X)
  rw [hswap]
  ring

/-- The single-variable bulk formula, with its absolute-integrability requirement explicit. -/
theorem hasDerivAt_coulombEnergy_straightPerturbation_single {X : E₃ → E₃}
    (hXC : ContDiff ℝ 1 X) (hc : HasCompactSupport X) {E : Set E₃}
    (hE : NullMeasurableSet E volume) (hEfin : volume E < ∞)
    (hi : IntegrableOn (coulombBulkSingleIntegrand X) (E ×ˢ E)) :
    HasDerivAt (fun t : ℝ => (coulombEnergy (straightPerturbation X t '' E)).toReal)
      (∫ p in E ×ˢ E, coulombBulkSingleIntegrand X p) 0 := by
  rw [← integral_coulombBulkVariationIntegrand_eq_twice hi]
  exact hasDerivAt_coulombEnergy_straightPerturbation hXC hc hE hEfin

end LiquidDrop

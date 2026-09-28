import NoCompromise.Variation.OneDimensionalTranslation

/-!
# Uniform local domination of binary BV translations

A bounded weight supported in a fixed interval has normalized translation
integrals bounded by its uniform bound times the actual one-dimensional variation
on a fixed enlarged interval, for every shift of magnitude at most one. This
estimate is independent of jump separation and is suitable for transverse
dominated convergence. The proof uses the finite step presentation and atom
weights already established for the canonical binary BV representative.
-/

noncomputable section
open MeasureTheory Filter Set Metric
open scoped ENNReal Topology
namespace LiquidDrop

lemma leftContinuousStep_difference_zero_of_outside {a b s t j : ℝ}
    (hs : s ∈ Icc a b) (hst : s + t ∈ Icc a b) (hj : j ∉ Icc a b) :
    leftContinuousStep j (s + t) - leftContinuousStep j s = 0 := by
  simp only [mem_Icc, not_and_or, not_le] at hj
  rcases hj with hj | hj
  · have h1 : j < s + t := hj.trans_le hst.1
    have h2 : j < s := hj.trans_le hs.1
    simp [leftContinuousStep, h1, h2]
  · have h1 : ¬j < s + t := not_lt.mpr (hst.2.trans hj.le)
    have h2 : ¬j < s := not_lt.mpr (hs.2.trans hj.le)
    simp [leftContinuousStep, h1, h2]

lemma finite_step_difference_le_filtered (J : Finset ℝ) (w : ℝ → ℝ)
    {a b s t : ℝ} (hs : s ∈ Icc a b) (hst : s + t ∈ Icc a b) :
    |(∑ j ∈ J, w j * leftContinuousStep j (s + t)) -
      ∑ j ∈ J, w j * leftContinuousStep j s| ≤
      ∑ j ∈ J.filter (fun j => j ∈ Icc a b),
        |w j| * |leftContinuousStep j (s + t) - leftContinuousStep j s| := by
  classical
  rw [← Finset.sum_sub_distrib]
  simp_rw [← mul_sub]
  have he : (∑ j ∈ J, w j * (leftContinuousStep j (s + t) - leftContinuousStep j s)) =
      ∑ j ∈ J.filter (fun j => j ∈ Icc a b),
        w j * (leftContinuousStep j (s + t) - leftContinuousStep j s) := by
    rw [Finset.sum_filter]
    apply Finset.sum_congr rfl
    intro j hj
    by_cases hjK : j ∈ Icc a b
    · simp [hjK]
    · simp [hjK, leftContinuousStep_difference_zero_of_outside hs hst hjK]
  rw [he]
  simpa only [abs_mul] using Finset.abs_sum_le_sum_abs
    (fun j => w j * (leftContinuousStep j (s + t) - leftContinuousStep j s))
    (J.filter (fun j => j ∈ Icc a b))

lemma integral_abs_step_difference (j t : ℝ) :
    (∫ s, |leftContinuousStep j (s + t) - leftContinuousStep j s|) = |t| := by
  have he := integral_step_difference_abs (ζ := fun _ => (1 : ℝ)) j t
  simpa only [one_mul, integral_const, Measure.restrict_apply_univ,
    smul_eq_mul, mul_one, measureReal_def, Real.volume_uIoc,
    show j - (j - t) = t by ring, ENNReal.toReal_ofReal (abs_nonneg t)] using he

lemma finite_step_weighted_translation_bound (J : Finset ℝ) (w : ℝ → ℝ)
    (c : ℝ) {ζ : ℝ → ℝ} {a b t C : ℝ} (hC : 0 ≤ C)
    (hζ : ∀ s, |ζ s| ≤ C) (hs : Function.support ζ ⊆ Icc a b)
    (hst : ∀ s ∈ Function.support ζ, s + t ∈ Icc a b) :
    abs (∫ s, ζ s * |(c + ∑ j ∈ J, w j * leftContinuousStep j (s + t)) -
      (c + ∑ j ∈ J, w j * leftContinuousStep j s)|) ≤
      C * |t| * ∑ j ∈ J.filter (fun j => j ∈ Icc a b), |w j| := by
  classical
  let L := J.filter (fun j => j ∈ Icc a b)
  let D (s : ℝ) := C * ∑ j ∈ L,
    |w j| * |leftContinuousStep j (s + t) - leftContinuousStep j s|
  have hi : Integrable D volume := by
    apply Integrable.const_mul
    apply integrable_finsetSum
    intro j hj
    have hi := integrable_step_difference_abs (ζ := fun _ => (1 : ℝ)) continuous_const j t
    simp only [one_mul] at hi
    exact hi.const_mul |w j|
  have hb (s : ℝ) : abs (ζ s * |(c + ∑ j ∈ J, w j * leftContinuousStep j (s + t)) -
      (c + ∑ j ∈ J, w j * leftContinuousStep j s)|) ≤ D s := by
    rw [abs_mul, abs_abs, add_sub_add_left_eq_sub]
    by_cases hz : ζ s = 0
    · simp only [hz, abs_zero, zero_mul]
      exact mul_nonneg hC (Finset.sum_nonneg fun j _ => mul_nonneg (abs_nonneg _) (abs_nonneg _))
    · exact mul_le_mul (hζ s) (finite_step_difference_le_filtered J w (hs hz) (hst s hz))
        (abs_nonneg _) hC
  calc
    abs (∫ s, ζ s * |(c + ∑ j ∈ J, w j * leftContinuousStep j (s + t)) -
        (c + ∑ j ∈ J, w j * leftContinuousStep j s)|) ≤
        ∫ s, abs (ζ s * |(c + ∑ j ∈ J, w j * leftContinuousStep j (s + t)) -
          (c + ∑ j ∈ J, w j * leftContinuousStep j s)|) := abs_integral_le_integral_abs
    _ ≤ ∫ s, D s := integral_mono_of_nonneg (Eventually.of_forall fun _ => abs_nonneg _)
      hi (Eventually.of_forall hb)
    _ = C * |t| * ∑ j ∈ L, |w j| := by
      rw [show (∫ s, D s) = C * ∫ s, ∑ j ∈ L,
        |w j| * |leftContinuousStep j (s + t) - leftContinuousStep j s| from integral_const_mul _ _,
        integral_finsetSum L]
      · simp_rw [integral_const_mul, integral_abs_step_difference]
        rw [← Finset.sum_mul]
        ring
      · intro j hj
        have hi := integrable_step_difference_abs (ζ := fun _ => (1 : ℝ)) continuous_const j t
        simp only [one_mul] at hi
        exact hi.const_mul |w j|

/-- Uniform local domination of normalized weighted translations by the actual
slice variation on one fixed compact interval. No separation scale of individual
jumps occurs in the bound. -/
theorem IsRealBVPolar.weighted_translation_bound {q σ : ℝ → ℝ} {μ : Measure ℝ}
    (h : IsRealBVPolar q μ σ) (hq : IsLocallyBVOn (q ∘ euclideanOneReal) univ)
    (hb : ∀ᵐ s : ℝ, q s ∈ ({0, 1} : Set ℝ))
    {ζ : ℝ → ℝ} {R C t : ℝ} (hC : 0 ≤ C) (hζ : ∀ s, |ζ s| ≤ C)
    (hsζ : Function.support ζ ⊆ Icc (-R) R) (ht : |t| ≤ 1) :
    abs (|t|⁻¹ * ∫ s, ζ s * |q (s + t) - q s|) ≤ C * μ.real (Icc (-(R + 2)) (R + 2)) := by
  classical
  let := h.finiteOnCompacts
  have hb' : ∀ᵐ s : ℝ, (q ∘ euclideanOneReal) (euclideanOneReal.symm s) ∈
      ({0, 1} : Set ℝ) := by simpa only [Function.comp_def,
        LinearIsometryEquiv.apply_symm_apply] using hb
  obtain ⟨g, hg, hc, he, hgb, _⟩ :=
    hq.exists_binary_representative_Ioo hb' (-(R + 3)) (R + 3)
  have hrep : IsBinaryBVRepresentativeOn q g (-(R + 3)) (R + 3) := by
    refine ⟨hg, hc, ?_, hgb⟩
    simpa only [Function.comp_def, LinearIsometryEquiv.apply_symm_apply] using he
  have hK : Icc (-(R + 2)) (R + 2) ⊆ Ioo (-(R + 3)) (R + 3) := by
    intro s hs
    constructor <;> linarith [hs.1, hs.2]
  obtain ⟨J, c, heq, _⟩ := h.exists_finite_step_presentation hrep hK
  let L := J.filter (fun j => j ∈ Icc (-(R + 2)) (R + 2))
  have hmass : (∑ j ∈ L, |oneDimensionalJump g j|) ≤
      μ.real (Icc (-(R + 2)) (R + 2)) := by
    calc
      (∑ j ∈ L, |oneDimensionalJump g j|) = ∑ j ∈ L, μ.real {j} := by
        apply Finset.sum_congr rfl
        intro j hj
        exact h.abs_jump_eq_measureReal_singleton hrep.ae_eq hrep.leftContinuous
          (hK (Finset.mem_filter.mp hj).2)
      _ = μ.real (L : Set ℝ) := sum_measureReal_singleton L
      _ ≤ μ.real (Icc (-(R + 2)) (R + 2)) :=
        measureReal_mono (fun _ hj => (Finset.mem_filter.mp hj).2)
          isCompact_Icc.measure_lt_top.ne
  have hsmall : q =ᵐ[volume.restrict (Ioo (-(R + 2)) (R + 2))] g :=
    ae_restrict_of_ae_restrict_of_subset (Ioo_subset_Icc_self.trans hK) hrep.ae_eq
  have hstep : q =ᵐ[volume.restrict (Ioo (-(R + 2)) (R + 2))]
      (fun s => c + ∑ j ∈ J, oneDimensionalJump g j * leftContinuousStep j s) :=
    hsmall.trans (ae_restrict_of_forall_mem measurableSet_Ioo heq)
  have hsU : Function.support ζ ⊆ Ioo (-(R + 2)) (R + 2) := by
    intro s hs
    have hh := hsζ hs
    constructor <;> linarith [hh.1, hh.2]
  have hstU (s : ℝ) (hs : s ∈ Function.support ζ) : s + t ∈ Ioo (-(R + 2)) (R + 2) := by
    have hh := hsζ hs
    have htt := abs_le.mp ht
    constructor <;> linarith [hh.1, hh.2, htt.1, htt.2]
  rw [integral_weighted_translation_congr_ae_on measurableSet_Ioo hstep t hsU hstU]
  have hi := finite_step_weighted_translation_bound J (oneDimensionalJump g) c hC hζ
    (hsU.trans Ioo_subset_Icc_self) (fun s hs => Ioo_subset_Icc_self (hstU s hs))
  by_cases ht0 : t = 0
  · simp only [ht0, abs_zero, inv_zero, zero_mul]
    exact mul_nonneg hC measureReal_nonneg
  · rw [abs_mul, abs_of_nonneg (inv_nonneg.mpr (abs_nonneg t))]
    calc
      |t|⁻¹ * abs (∫ s, ζ s *
          |(c + ∑ j ∈ J, oneDimensionalJump g j * leftContinuousStep j (s + t)) -
            (c + ∑ j ∈ J, oneDimensionalJump g j * leftContinuousStep j s)|) ≤
          |t|⁻¹ * (C * |t| * ∑ j ∈ L, |oneDimensionalJump g j|) :=
        mul_le_mul_of_nonneg_left hi (inv_nonneg.mpr (abs_nonneg t))
      _ = C * ∑ j ∈ L, |oneDimensionalJump g j| := by
        field_simp
      _ ≤ C * μ.real (Icc (-(R + 2)) (R + 2)) := mul_le_mul_of_nonneg_left hmass hC

end LiquidDrop

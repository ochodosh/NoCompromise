import NoCompromise.BV.JumpSlicing
import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus

/-!
# Weighted one-dimensional translation identity

For a distributionally locally BV function on the real line that is binary
almost everywhere, normalized weighted translation differences converge to the
integral of the weight against the actual total variation of its derivative.
The limit is two-sided and punctured, and continuous compactly supported signed
weights are allowed. Changes to the original representative on a Lebesgue null
set leave every weighted translation integral unchanged.

The proof establishes the exact translation formula for a single left-continuous
step, sums over separated finite jumps, and obtains a finite step representation
on a compact interval from the actual scalar polar measure. No pre-existing BV
translation identity is used.
-/

noncomputable section
open MeasureTheory Filter Set Metric
open scoped ENNReal Topology
namespace LiquidDrop

/-- The left-continuous unit step with its jump immediately to the right of `j`. -/
def leftContinuousStep (j s : ℝ) : ℝ := (Ioi j).indicator (fun _ => 1) s

lemma leftContinuousStep_difference_abs (j s t : ℝ) :
    |leftContinuousStep j (s + t) - leftContinuousStep j s| =
      (uIoc (j - t) j).indicator (fun _ => (1 : ℝ)) s := by
  classical
  by_cases hst : j < s + t <;> by_cases hs : j < s <;>
    simp only [leftContinuousStep, mem_Ioi, indicator_apply, hst, hs, ite_true, ite_false]
  all_goals
    by_cases ht : 0 ≤ t
    · rw [uIoc_of_le (by linarith)]
      simp only [mem_Ioc]
      split_ifs
      all_goals
        simp_all
        all_goals linarith
    · rw [uIoc_of_ge (by linarith)]
      simp only [mem_Ioc]
      split_ifs <;> simp_all <;> linarith

lemma integral_step_difference_abs {ζ : ℝ → ℝ} (j t : ℝ) :
    (∫ s, ζ s * |leftContinuousStep j (s + t) - leftContinuousStep j s|) =
      ∫ s in uIoc (j - t) j, ζ s := by
  simp_rw [leftContinuousStep_difference_abs]
  rw [← integral_indicator measurableSet_uIoc]
  apply integral_congr_ae
  exact Eventually.of_forall fun s => by
    by_cases hs : s ∈ uIoc (j - t) j <;> simp [hs]

lemma integral_step_difference_abs_div {ζ : ℝ → ℝ} (j t : ℝ) :
    |t|⁻¹ * (∫ s, ζ s * |leftContinuousStep j (s + t) - leftContinuousStep j s|) =
      t⁻¹ * ∫ s in (j - t)..j, ζ s := by
  rw [integral_step_difference_abs]
  by_cases ht : 0 ≤ t
  · rw [abs_of_nonneg ht, intervalIntegral.integral_of_le (by linarith),
      uIoc_of_le (by linarith)]
  · have ht' : t ≤ 0 := le_of_not_ge ht
    rw [abs_of_nonpos ht', intervalIntegral.integral_of_ge (by linarith),
      uIoc_of_ge (by linarith), inv_neg, neg_mul, mul_neg]

lemma tendsto_integral_step_difference_abs {ζ : ℝ → ℝ} (hζ : Continuous ζ) (j : ℝ) :
    Tendsto (fun t : ℝ => |t|⁻¹ *
      (∫ s, ζ s * |leftContinuousStep j (s + t) - leftContinuousStep j s|))
      (𝓝[≠] 0) (𝓝 (ζ j)) := by
  have hd := intervalIntegral.integral_hasDerivAt_right
    (hζ.intervalIntegrable j j) hζ.stronglyMeasurable.stronglyMeasurableAtFilter
    (hζ.continuousAt (x := j))
  have ht := hd.tendsto_slope_zero
  simp only [intervalIntegral.integral_same, sub_zero, smul_eq_mul] at ht
  have hneg : Tendsto (fun t : ℝ => -t) (𝓝[≠] 0) (𝓝[≠] 0) := by
    apply tendsto_nhdsWithin_iff.mpr
    refine ⟨by simpa using (continuous_neg.tendsto (0 : ℝ)).mono_left nhdsWithin_le_nhds, ?_⟩
    filter_upwards [self_mem_nhdsWithin] with t ht
    simpa using ht
  have hh := ht.comp hneg
  apply hh.congr'
  exact Eventually.of_forall fun t => by
    change (-t)⁻¹ * (∫ x in j..j + (-t), ζ x) =
      |t|⁻¹ * (∫ s, ζ s * |leftContinuousStep j (s + t) - leftContinuousStep j s|)
    rw [integral_step_difference_abs_div, inv_neg,
      show j + -t = j - t from rfl, intervalIntegral.integral_symm j (j - t)]
    ring

lemma integrable_step_difference_abs {ζ : ℝ → ℝ} (hζ : Continuous ζ) (j t : ℝ) :
    Integrable (fun s => ζ s * |leftContinuousStep j (s + t) - leftContinuousStep j s|)
      volume := by
  have he : (fun s => ζ s * |leftContinuousStep j (s + t) - leftContinuousStep j s|) =
      (uIoc (j - t) j).indicator ζ := by
    funext s
    rw [leftContinuousStep_difference_abs]
    by_cases hs : s ∈ uIoc (j - t) j <;> simp [hs]
  rw [he]
  exact (hζ.intervalIntegrable (j - t) j).def'.integrable_indicator measurableSet_uIoc

lemma leftContinuousStep_crossing_distance {j k s t : ℝ}
    (hj : leftContinuousStep j (s + t) - leftContinuousStep j s ≠ 0)
    (hk : leftContinuousStep k (s + t) - leftContinuousStep k s ≠ 0) :
    |j - k| ≤ |t| := by
  have hj' : s ∈ uIoc (j - t) j := by
    by_contra hs
    have ha := leftContinuousStep_difference_abs j s t
    simp only [indicator_of_notMem hs] at ha
    exact hj (abs_eq_zero.mp ha)
  have hk' : s ∈ uIoc (k - t) k := by
    by_contra hs
    have ha := leftContinuousStep_difference_abs k s t
    simp only [indicator_of_notMem hs] at ha
    exact hk (abs_eq_zero.mp ha)
  by_cases ht : 0 ≤ t
  · rw [uIoc_of_le (by linarith)] at hj' hk'
    rw [abs_of_nonneg ht, abs_le]
    constructor <;> linarith [hj'.1, hj'.2, hk'.1, hk'.2]
  · rw [uIoc_of_ge (by linarith)] at hj' hk'
    rw [abs_of_nonpos (le_of_not_ge ht), abs_le]
    constructor <;> linarith [hj'.1, hj'.2, hk'.1, hk'.2]

lemma abs_finset_sum_eq_of_one_nonzero {ι : Type*} (J : Finset ι) (a : ι → ℝ)
    (ha : ∀ j ∈ J, ∀ k ∈ J, j ≠ k → a j = 0 ∨ a k = 0) :
    |∑ j ∈ J, a j| = ∑ j ∈ J, |a j| := by
  classical
  by_cases hn : ∃ j ∈ J, a j ≠ 0
  · obtain ⟨j, hj, hjn⟩ := hn
    have hz (k) (hk : k ∈ J) (hkj : k ≠ j) : a k = 0 :=
      (ha k hk j hj hkj).resolve_right hjn
    rw [Finset.sum_eq_single_of_mem j hj hz,
      Finset.sum_eq_single_of_mem j hj (fun k hk hkj => by rw [hz k hk hkj, abs_zero])]
  · have hz (j) (hj : j ∈ J) : a j = 0 := by
      by_contra hjn
      exact hn ⟨j, hj, hjn⟩
    rw [Finset.sum_eq_zero hz, abs_zero, Finset.sum_eq_zero (fun j hj => by rw [hz j hj, abs_zero])]

lemma finite_step_difference_abs (J : Finset ℝ) (w : ℝ → ℝ) (s t : ℝ)
    (hsep : ∀ j ∈ J, ∀ k ∈ J, j ≠ k → |t| < |j - k|) :
    |(∑ j ∈ J, w j * leftContinuousStep j (s + t)) -
      ∑ j ∈ J, w j * leftContinuousStep j s| =
      ∑ j ∈ J, |w j| * |leftContinuousStep j (s + t) - leftContinuousStep j s| := by
  rw [← Finset.sum_sub_distrib]
  simp_rw [← mul_sub]
  rw [abs_finset_sum_eq_of_one_nonzero]
  · simp only [abs_mul]
  · intro j hj k hk hne
    by_cases ha : w j * (leftContinuousStep j (s + t) - leftContinuousStep j s) = 0
    · exact Or.inl ha
    · right
      by_contra hb
      have hd := leftContinuousStep_crossing_distance (mul_ne_zero_iff.mp ha).2
        (mul_ne_zero_iff.mp hb).2
      exact (not_lt_of_ge hd) (hsep j hj k hk hne)

lemma tendsto_finite_step_translation {ζ : ℝ → ℝ} (hζ : Continuous ζ)
    (J : Finset ℝ) (w : ℝ → ℝ) (c : ℝ) :
    Tendsto (fun t : ℝ => |t|⁻¹ * ∫ s, ζ s *
      |(c + ∑ j ∈ J, w j * leftContinuousStep j (s + t)) -
        (c + ∑ j ∈ J, w j * leftContinuousStep j s)|)
      (𝓝[≠] 0) (𝓝 (∑ j ∈ J, |w j| * ζ j)) := by
  have hsep : ∀ᶠ t : ℝ in 𝓝 0, ∀ j ∈ J, ∀ k ∈ J, j ≠ k → |t| < |j - k| := by
    apply (eventually_all_finset J).mpr
    intro j hj
    apply (eventually_all_finset J).mpr
    intro k hk
    by_cases hne : j = k
    · exact Eventually.of_forall fun _ h => (h hne).elim
    · have hpos : 0 < |j - k| := abs_pos.mpr (sub_ne_zero.mpr hne)
      have ht := (continuous_abs.continuousAt (x := (0 : ℝ))).eventually
        (Iio_mem_nhds (show |(0 : ℝ)| < |j - k| by simpa using hpos))
      simpa only [abs_zero] using ht.mono (fun t ht _ => ht)
  have hlim := tendsto_finsetSum J (fun j _ =>
    (tendsto_integral_step_difference_abs hζ j).const_mul |w j|)
  apply hlim.congr'
  filter_upwards [hsep.filter_mono nhdsWithin_le_nhds] with t ht
  have he (s : ℝ) :
      ζ s * |(c + ∑ j ∈ J, w j * leftContinuousStep j (s + t)) -
        (c + ∑ j ∈ J, w j * leftContinuousStep j s)| =
        ∑ j ∈ J, |w j| * (ζ s *
          |leftContinuousStep j (s + t) - leftContinuousStep j s|) := by
    rw [add_sub_add_left_eq_sub, finite_step_difference_abs J w s t ht, Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro j hj
    ring
  simp_rw [he]
  rw [integral_finsetSum J (fun j _ => (integrable_step_difference_abs hζ j t).const_mul |w j|)]
  simp_rw [integral_const_mul, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro j hj
  ring

lemma IsRealBVPolar.abs_jump_eq_measureReal_singleton {q g σ : ℝ → ℝ}
    {μ : Measure ℝ} (h : IsRealBVPolar q μ σ) {a b j : ℝ}
    (hqg : q =ᵐ[volume.restrict (Ioo a b)] g)
    (hc : ∀ s, ContinuousWithinAt g (Iic s) s) (hj : j ∈ Ioo a b) :
    |oneDimensionalJump g j| = μ.real {j} := by
  have he : (∫ s in {j}, |σ s| ∂μ) = ∫ _s in {j}, (1 : ℝ) ∂μ :=
    integral_congr_ae (ae_restrict_of_ae h.norm_ae)
  simp only [integral_singleton, smul_eq_mul, mul_one] at he
  rw [h.oneDimensionalJump_eq_atom hqg hc hj, abs_mul,
    abs_of_nonneg measureReal_nonneg, he]

/-- On a compact interval inside a binary BV region, the canonical representative
is a finite step sum, and the actual variation measure integrates weights by the
absolute values of those same jumps. -/
lemma IsRealBVPolar.exists_finite_step_presentation {q g σ : ℝ → ℝ}
    {μ : Measure ℝ} (h : IsRealBVPolar q μ σ) {A B a b : ℝ}
    (hg : IsBinaryBVRepresentativeOn q g A B) (hK : Icc a b ⊆ Ioo A B) :
    ∃ J : Finset ℝ, ∃ c : ℝ,
      EqOn g (fun s => c + ∑ j ∈ J, oneDimensionalJump g j * leftContinuousStep j s)
        (Ioo a b) ∧
      ∀ ζ : ℝ → ℝ, Continuous ζ → Function.support ζ ⊆ Icc a b →
        (∫ s, ζ s ∂μ) = ∑ j ∈ J, |oneDimensionalJump g j| * ζ j := by
  classical
  let := h.finiteOnCompacts
  let : IsFiniteMeasure (μ.restrict (Icc a b)) := ⟨by
    simpa using (isCompact_Icc : IsCompact (Icc a b)).measure_lt_top (μ := μ)⟩
  have hfJ := hg.finite_jumps isCompact_Icc hK
  let J := hfJ.toFinset
  have hJK {j : ℝ} (hj : j ∈ J) : j ∈ Icc a b := (hfJ.mem_toFinset.mp hj).1
  have hJae : ∀ᵐ j ∂μ.restrict (Icc a b), j ∈ (J : Set ℝ) := by
    filter_upwards [ae_restrict_of_ae_restrict_of_subset hK
      (h.ae_mem_jumps_on_binary_region isOpen_Ioo hg.ae_eq hg.boundedVariation
        hg.leftContinuous hg.binary), ae_restrict_mem measurableSet_Icc] with j hj hjK
    exact hfJ.mem_toFinset.mpr ⟨hjK, hj⟩
  have hm (j : ℝ) (hj : j ∈ J) : (μ.restrict (Icc a b)).real {j} = μ.real {j} := by
    rw [measureReal_def, measureReal_def, Measure.restrict_apply (measurableSet_singleton j),
      singleton_inter_of_mem (hJK hj)]
  have hi : Integrable σ (μ.restrict (Icc a b)) :=
    Integrable.of_bound h.measurable.aestronglyMeasurable.restrict 1
      ((ae_restrict_of_ae h.norm_ae).mono fun j hj => by simpa only [Real.norm_eq_abs] using hj.le)
  have hsum (s : ℝ) : (∫ j in Iio s, σ j ∂μ.restrict (Icc a b)) =
      ∑ j ∈ J, oneDimensionalJump g j * leftContinuousStep j s := by
    rw [← integral_indicator measurableSet_Iio,
      integral_eq_setIntegral hJae (fun j => (Iio s).indicator σ j),
      setIntegral_finset J (hi.indicator measurableSet_Iio).integrableOn]
    apply Finset.sum_congr rfl
    intro j hj
    rw [hm j hj, smul_eq_mul, h.oneDimensionalJump_eq_atom hg.ae_eq
      hg.leftContinuous (hK (hJK hj))]
    by_cases hjs : j < s <;> simp [leftContinuousStep, hjs]
  have hqg : q =ᵐ[volume.restrict (Ioo a b)] g :=
    ae_restrict_of_ae_restrict_of_subset (Ioo_subset_Icc_self.trans hK) hg.ae_eq
  obtain ⟨c, hc⟩ := h.exists_cumulative_eqOn_Ioo a b hqg hg.leftContinuous
  refine ⟨J, c, ?_, ?_⟩
  · intro s hs
    rw [hc hs]
    change (∫ j in Iio s, σ j ∂μ.restrict (Icc a b)) + c = _
    rw [hsum s, add_comm]
  · intro ζ hζ hsζ
    have hζi : Integrable ζ (μ.restrict (Icc a b)) :=
      hζ.continuousOn.integrableOn_compact isCompact_Icc
    rw [← setIntegral_eq_integral_of_forall_compl_eq_zero
      (μ := μ) (s := Icc a b) (f := ζ) (fun s hs => by
        by_contra hn
        exact hs (hsζ hn)), integral_eq_setIntegral hJae ζ,
      setIntegral_finset J hζi.integrableOn]
    apply Finset.sum_congr rfl
    intro j hj
    rw [smul_eq_mul, hm j hj, h.abs_jump_eq_measureReal_singleton hg.ae_eq
      hg.leftContinuous (hK (hJK hj))]

lemma integral_weighted_translation_congr_ae_on {q g ζ : ℝ → ℝ} {U : Set ℝ}
    (hU : MeasurableSet U) (hqg : q =ᵐ[volume.restrict U] g) (t : ℝ)
    (hs : Function.support ζ ⊆ U)
    (hst : ∀ s ∈ Function.support ζ, s + t ∈ U) :
    (∫ s, ζ s * |q (s + t) - q s|) = ∫ s, ζ s * |g (s + t) - g s| := by
  have he : ∀ᵐ s, s ∈ U → q s = g s := (ae_restrict_iff' hU).mp hqg
  have het : ∀ᵐ s : ℝ, s + t ∈ U → q (s + t) = g (s + t) := by
    have hh := (quasiMeasurePreserving_add_left volume t).ae he
    simpa only [add_comm t] using hh
  apply integral_congr_ae
  filter_upwards [he, het] with s hs0 hst0
  by_cases hz : ζ s = 0
  · simp [hz]
  · rw [hs0 (hs hz), hst0 (hst s hz)]

lemma integral_weighted_translation_congr_ae {q g : ℝ → ℝ}
    (hqg : q =ᵐ[volume] g) (ζ : ℝ → ℝ) (t : ℝ) :
    (∫ s, ζ s * |q (s + t) - q s|) = ∫ s, ζ s * |g (s + t) - g s| :=
  integral_weighted_translation_congr_ae_on MeasurableSet.univ
    (by simpa using hqg) t (subset_univ _) (fun _ _ => mem_univ _)

/-- The weighted one-dimensional translation limit, for any continuous compactly
supported real weight, with the actual total variation of the distributional
binary BV derivative. The limit is the full two-sided punctured limit. -/
theorem IsRealBVPolar.tendsto_weighted_translation {q σ : ℝ → ℝ} {μ : Measure ℝ}
    (h : IsRealBVPolar q μ σ) (hq : IsLocallyBVOn (q ∘ euclideanOneReal) univ)
    (hb : ∀ᵐ s : ℝ, q s ∈ ({0, 1} : Set ℝ))
    {ζ : ℝ → ℝ} (hζ : Continuous ζ) (hcζ : HasCompactSupport ζ) :
    Tendsto (fun t : ℝ => |t|⁻¹ * ∫ s, ζ s * |q (s + t) - q s|)
      (𝓝[≠] 0) (𝓝 (∫ s, ζ s ∂μ)) := by
  obtain ⟨R₀, hR₀⟩ := hcζ.isBounded.subset_closedBall 0
  let R := max R₀ 0
  have hR (s : ℝ) (hs : s ∈ Function.support ζ) : |s| ≤ R := by
    have hh := hR₀ (subset_tsupport ζ hs)
    rw [mem_closedBall, Real.dist_eq, sub_zero] at hh
    exact hh.trans (le_max_left _ _)
  have hb' : ∀ᵐ t : ℝ, (q ∘ euclideanOneReal) (euclideanOneReal.symm t) ∈
      ({0, 1} : Set ℝ) := by simpa only [Function.comp_def,
        LinearIsometryEquiv.apply_symm_apply] using hb
  obtain ⟨g, hg, hgc, hqg, hgb, _⟩ :=
    hq.exists_binary_representative_Ioo hb' (-(R + 2)) (R + 2)
  have hrep : IsBinaryBVRepresentativeOn q g (-(R + 2)) (R + 2) := by
    refine ⟨hg, hgc, ?_, hgb⟩
    simpa only [Function.comp_def, LinearIsometryEquiv.apply_symm_apply] using hqg
  have hK : Icc (-(R + 1)) (R + 1) ⊆ Ioo (-(R + 2)) (R + 2) := by
    intro s hs
    constructor <;> linarith [hs.1, hs.2]
  obtain ⟨J, c, heq, hw⟩ := h.exists_finite_step_presentation hrep hK
  have hsζ : Function.support ζ ⊆ Icc (-(R + 1)) (R + 1) := by
    intro s hs
    have hh := abs_le.mp (hR s hs)
    constructor <;> linarith [hh.1, hh.2]
  rw [hw ζ hζ hsζ]
  have hstep : q =ᵐ[volume.restrict (Ioo (-(R + 1)) (R + 1))]
      (fun s => c + ∑ j ∈ J, oneDimensionalJump g j * leftContinuousStep j s) := by
    have hsmall : q =ᵐ[volume.restrict (Ioo (-(R + 1)) (R + 1))] g :=
      ae_restrict_of_ae_restrict_of_subset (Ioo_subset_Icc_self.trans hK) hrep.ae_eq
    exact hsmall.trans (ae_restrict_of_forall_mem measurableSet_Ioo heq)
  have hsU : Function.support ζ ⊆ Ioo (-(R + 1)) (R + 1) := by
    intro s hs
    have hh := abs_le.mp (hR s hs)
    constructor <;> linarith [hh.1, hh.2]
  apply (tendsto_finite_step_translation hζ J (oneDimensionalJump g) c).congr'
  have hnear : ∀ᶠ t : ℝ in 𝓝[≠] 0, |t| < 1 := by
    apply (continuous_abs.continuousAt (x := (0 : ℝ))).eventually
      (Iio_mem_nhds (by norm_num : |(0 : ℝ)| < 1)) |>.filter_mono nhdsWithin_le_nhds
  filter_upwards [hnear] with t ht
  apply congrArg (fun I : ℝ => |t|⁻¹ * I)
  symm
  apply integral_weighted_translation_congr_ae_on measurableSet_Ioo hstep t hsU
  intro s hs
  have hhs := abs_le.mp (hR s hs)
  have hht := abs_lt.mp ht
  constructor <;> linarith [hhs.1, hhs.2, hht.1, hht.2]

/-- Existence form of the weighted translation theorem for distributionally
locally BV, almost-everywhere binary functions on the ordinary real line. -/
theorem IsLocallyBVOn.exists_weighted_translation_measure {q : ℝ → ℝ}
    (hq : IsLocallyBVOn (q ∘ euclideanOneReal) univ)
    (hb : ∀ᵐ s : ℝ, q s ∈ ({0, 1} : Set ℝ)) :
    ∃ μ : Measure ℝ, ∃ σ : ℝ → ℝ, IsRealBVPolar q μ σ ∧
      ∀ ζ : ℝ → ℝ, Continuous ζ → HasCompactSupport ζ →
        Tendsto (fun t : ℝ => |t|⁻¹ * ∫ s, ζ s * |q (s + t) - q s|)
          (𝓝[≠] 0) (𝓝 (∫ s, ζ s ∂μ)) := by
  obtain ⟨μ, σ, h⟩ := exists_real_bv_polar hq
  exact ⟨μ, σ, h, fun _ hζ hcζ => h.tendsto_weighted_translation hq hb hζ hcζ⟩

end LiquidDrop

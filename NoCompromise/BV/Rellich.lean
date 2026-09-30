module

public import NoCompromise.BV.Compactness
public import NoCompromise.Sobolev.Extension
public import Mathlib.MeasureTheory.Integral.MeanInequalities
public import Mathlib.MeasureTheory.Function.LpSeminorm.LpNorm

@[expose] public section

/-!
# L² interpolation and the strong-convergence step of Rellich

Hölder gives the L¹–L⁴ interpolation estimate with constant one. A uniform finite
L⁴ bound and L¹ convergence give convergence of L² classes. Combined with the
proved BV compactness theorem, this yields an L²-convergent subsequence on each
relatively compact open region with uniform BV and L⁴ bounds.

Weak-gradient H¹ representatives and their quantitative BV bound on finite-volume
domains are defined and proved below. The planar H¹ extension, Gagliardo–Nirenberg
estimate, Hilbert-space construction, and full Rellich theorem remain to be proved.
No Sobolev or Rellich inequality is imported as a premise.
-/

open MeasureTheory Filter Metric Set InnerProductSpace
open scoped ENNReal Topology Gradient Pointwise
namespace LiquidDrop
set_option maxSynthPendingDepth 8

/-- Blueprint `lem:L2-interp`, in extended norms and for any measure and normed
codomain. This formulation also covers infinite norms. -/
theorem l2_interpolation {α F : Type*} [MeasurableSpace α] [NormedAddCommGroup F]
    {μ : Measure α} {f : α → F} (hf : AEStronglyMeasurable f μ) :
    eLpNorm f 2 μ ≤ (eLpNorm f 1 μ) ^ (1 / 3 : ℝ) *
      (eLpNorm f 4 μ) ^ (2 / 3 : ℝ) := by
  have hh := ENNReal.lintegral_mul_norm_pow_le hf.enorm (hf.enorm.pow_const (4 : ℝ))
    (by norm_num : (0 : ℝ) ≤ 2 / 3) (by norm_num : (0 : ℝ) ≤ 1 / 3) (by norm_num)
  have he (x : α) : ‖f x‖ₑ ^ (2 / 3 : ℝ) * (‖f x‖ₑ ^ (4 : ℝ)) ^ (1 / 3 : ℝ) =
      ‖f x‖ₑ ^ (2 : ℝ) := by
    rw [← ENNReal.rpow_mul, ← ENNReal.rpow_add_of_nonneg _ _ (by norm_num) (by norm_num)]
    norm_num
  simp only [he] at hh
  have hr := ENNReal.rpow_le_rpow hh (by norm_num : (0 : ℝ) ≤ 1 / 2)
  rw [ENNReal.mul_rpow_of_nonneg _ _ (by norm_num : (0 : ℝ) ≤ 1 / 2),
    ← ENNReal.rpow_mul, ← ENNReal.rpow_mul] at hr
  simp only [eLpNorm_eq_lintegral_rpow_enorm_toReal (by norm_num : (2 : ℝ≥0∞) ≠ 0)
    (by norm_num : (2 : ℝ≥0∞) ≠ ∞) hf,
    eLpNorm_eq_lintegral_rpow_enorm_toReal (by norm_num : (4 : ℝ≥0∞) ≠ 0)
    (by norm_num : (4 : ℝ≥0∞) ≠ ∞) hf, eLpNorm_one_eq_lintegral_enorm hf]
  norm_num only [ENNReal.toReal_ofNat, one_div, ← ENNReal.rpow_mul] at hr ⊢
  convert hr using 1

/-- Finite L¹ and L⁴ norms imply membership in L² and the ordinary real-norm bound. -/
theorem memLp_two_and_l2_interpolation {α F : Type*} [MeasurableSpace α]
    [NormedAddCommGroup F] {μ : Measure α} {f : α → F}
    (hf1 : MemLp f 1 μ) (hf4 : MemLp f 4 μ) :
    MemLp f 2 μ ∧ lpNorm f 2 μ ≤
      (lpNorm f 1 μ) ^ (1 / 3 : ℝ) * (lpNorm f 4 μ) ^ (2 / 3 : ℝ) := by
  have hb := l2_interpolation hf1.aestronglyMeasurable
  have hfin : (eLpNorm f 1 μ) ^ (1 / 3 : ℝ) * (eLpNorm f 4 μ) ^ (2 / 3 : ℝ) < ∞ := by
    exact ENNReal.mul_lt_top
      (ENNReal.rpow_lt_top_of_nonneg (by norm_num) hf1.eLpNorm_ne_top)
      (ENNReal.rpow_lt_top_of_nonneg (by norm_num) hf4.eLpNorm_ne_top)
  refine ⟨hb.trans_lt hfin, ?_⟩
  have hr := ENNReal.toReal_mono hfin.ne hb
  simpa only [ENNReal.toReal_mul, ← ENNReal.toReal_rpow, toReal_eLpNorm] using hr

/-- L¹ convergence and a uniform finite L⁴ bound give L² convergence of the
errors. The limiting function inherits the L⁴ bound. -/
theorem tendsto_eLpNorm_two_of_one_and_four_bound {α F : Type*} [MeasurableSpace α]
    [NormedAddCommGroup F] {μ : Measure α} {f : ℕ → α → F} {g : α → F}
    (hf : ∀ j, AEStronglyMeasurable (f j) μ) (hg : AEStronglyMeasurable g μ)
    (ht : Tendsto (fun j => eLpNorm (f j - g) 1 μ) atTop (𝓝 0))
    {C : ℝ≥0∞} (hC : C < ∞) (hb : ∀ j, eLpNorm (f j) 4 μ ≤ C) :
    eLpNorm g 4 μ ≤ C ∧ Tendsto (fun j => eLpNorm (f j - g) 2 μ) atTop (𝓝 0) := by
  have hm := tendstoInMeasure_of_tendsto_eLpNorm one_ne_zero ht
  have hgb : eLpNorm g 4 μ ≤ C :=
    eLpNorm_le_of_tendstoInMeasure (Eventually.of_forall hb) hm hf
  refine ⟨hgb, ?_⟩
  have hdiff (j) : eLpNorm (f j - g) 4 μ ≤ C + C :=
    (eLpNorm_sub_le (by norm_num)).trans (add_le_add (hb j) hgb)
  have hfin : (C + C) ^ (2 / 3 : ℝ) ≠ ∞ :=
    (ENNReal.rpow_lt_top_of_nonneg (by norm_num) (ENNReal.add_lt_top.mpr ⟨hC, hC⟩).ne).ne
  have ht' : Tendsto (fun j => (eLpNorm (f j - g) 1 μ) ^ (1 / 3 : ℝ)) atTop (𝓝 0) := by
    simpa only [ENNReal.zero_rpow_of_pos (by norm_num : (0 : ℝ) < 1 / 3), Function.comp_def] using
      (ENNReal.continuous_rpow_const (y := (1 / 3 : ℝ))).continuousAt.tendsto.comp ht
  have ht'' := ENNReal.Tendsto.mul_const ht' (Or.inr hfin)
  simp only [zero_mul] at ht''
  apply tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds ht''
    (fun _ => bot_le)
  intro j
  exact (l2_interpolation ((hf j).sub hg)).trans
    (mul_le_mul' le_rfl (ENNReal.rpow_le_rpow (hdiff j) (by norm_num)))

/-- The ordinary L¹ integral convergence used in BV compactness upgrades to
strong convergence of L² classes under a uniform L⁴ bound. -/
theorem l2_convergence_of_l1_and_l4_bound {α F : Type*} [MeasurableSpace α]
    [NormedAddCommGroup F] {μ : Measure α} {f : ℕ → α → F} {g : α → F}
    (hf : ∀ j, Integrable (f j) μ) (hg : Integrable g μ)
    (ht : Tendsto (fun j => ∫ x, ‖f j x - g x‖ ∂μ) atTop (𝓝 0))
    {C : ℝ≥0∞} (hC : C < ∞) (hb : ∀ j, eLpNorm (f j) 4 μ ≤ C) :
    ∃ hf2 : ∀ j, MemLp (f j) 2 μ, ∃ hg2 : MemLp g 2 μ,
      Tendsto (fun j => (hf2 j).toLp (f j)) atTop (𝓝 (hg2.toLp g)) := by
  have ht1 : Tendsto (fun j => eLpNorm (f j - g) 1 μ) atTop (𝓝 0) := by
    have he := ENNReal.continuous_ofReal.continuousAt.tendsto.comp ht
    simp only [ENNReal.ofReal_zero] at he
    convert he using 1
    ext j
    rw [eLpNorm_one_eq_lintegral_enorm ((hf j).sub hg).aestronglyMeasurable,
      ← ofReal_integral_norm_eq_lintegral_enorm ((hf j).sub hg)]
    rfl
  obtain ⟨hgb, ht2⟩ := tendsto_eLpNorm_two_of_one_and_four_bound
    (fun j => (hf j).1) hg.1 ht1 hC hb
  have hf2 (j) : MemLp (f j) 2 μ :=
    (memLp_two_and_l2_interpolation ((memLp_one_iff_integrable).mpr (hf j))
      ((hb j).trans_lt hC)).1
  have hg2 : MemLp g 2 μ :=
    (memLp_two_and_l2_interpolation ((memLp_one_iff_integrable).mpr hg)
      (hgb.trans_lt hC)).1
  exact ⟨hf2, hg2, (Lp.tendsto_Lp_iff_tendsto_eLpNorm'' f hf2 g hg2).mpr ht2⟩

/-- The strong-convergence step of Rellich: local uniform BV and L⁴ bounds
produce an L²-convergent subsequence on a relatively compact open region. -/
theorem exists_subseq_l2_of_bv_l4_bounds {n : ℕ}
    {A Q : Set (EuclideanSpace ℝ (Fin n))} (hA : IsOpen A) (hQ : IsOpen Q)
    (hcQ : IsCompact (closure Q)) (hQA : closure Q ⊆ A)
    (f : ℕ → EuclideanSpace ℝ (Fin n) → ℝ) (hf : ∀ j, IsBVOn (f j) A)
    {L V : ℝ} (hL : 0 ≤ L) (hLb : ∀ j, (∫ x in A, |f j x|) ≤ L)
    (hVb : ∀ j, (variation (f j) A).toReal ≤ V)
    {C : ℝ≥0∞} (hC : C < ∞) (h4 : ∀ j, eLpNorm (f j) 4 (volume.restrict Q) ≤ C) :
    ∃ g : EuclideanSpace ℝ (Fin n) → ℝ, ∃ σ : ℕ → ℕ, StrictMono σ ∧ IsBVOn g Q ∧
      ∃ hf2 : ∀ j, MemLp (f (σ j)) 2 (volume.restrict Q),
        ∃ hg2 : MemLp g 2 (volume.restrict Q),
          Tendsto (fun j => (hf2 j).toLp (f (σ j))) atTop (𝓝 (hg2.toLp g)) := by
  obtain ⟨g, σ, hσ, hg, _, ht⟩ := exists_subseq_bvOn_of_bv_bounds hA hQ hcQ hQA f hf hL hLb hVb
  have hnorm : Tendsto (fun j => ∫ x in Q, ‖f (σ j) x - g x‖) atTop (𝓝 0) := by
    simpa only [Real.norm_eq_abs] using ht
  exact ⟨g, σ, hσ, hg, l2_convergence_of_l1_and_l4_bound
    (fun j => (hf (σ j)).1.mono_set (subset_closure.trans hQA)) hg.1 hnorm hC
    (fun j => h4 (σ j))⟩


/-! ## Weak-gradient H¹ representatives and the BV bound -/

/-- A representative together with its weak L² gradient. This is the domain-based H¹
interface; the local integrability clauses follow automatically from the L² hypotheses. -/
structure HasH1GradientOn {n : ℕ} (f : EuclideanSpace ℝ (Fin n) → ℝ)
    (G : EuclideanSpace ℝ (Fin n) → EuclideanSpace ℝ (Fin n))
    (U : Set (EuclideanSpace ℝ (Fin n))) : Prop extends HasWeakGradientOn f G U where
  memLp_function : MemLp f 2 (volume.restrict U)
  memLp_gradient : MemLp G 2 (volume.restrict U)

/-- Membership in H¹ on an open domain, stated without choosing a weak gradient. -/
def IsH1On {n : ℕ} (f : EuclideanSpace ℝ (Fin n) → ℝ)
    (U : Set (EuclideanSpace ℝ (Fin n))) : Prop := ∃ G, HasH1GradientOn f G U

lemma hasH1GradientOn_of_memLp_test {n : ℕ}
    {U : Set (EuclideanSpace ℝ (Fin n))} {f : EuclideanSpace ℝ (Fin n) → ℝ}
    {G : EuclideanSpace ℝ (Fin n) → EuclideanSpace ℝ (Fin n)}
    (hf : MemLp f 2 (volume.restrict U)) (hG : MemLp G 2 (volume.restrict U))
    (h : ∀ (i : Fin n) (φ : EuclideanSpace ℝ (Fin n) → ℝ),
      ContDiff ℝ 1 φ → HasCompactSupport φ → tsupport φ ⊆ U →
      -(∫ x in U, f x * fderiv ℝ φ x (EuclideanSpace.single i 1)) =
        ∫ x in U, φ x * G x i) : HasH1GradientOn f G U := by
  exact ⟨⟨locallyIntegrableOn_of_locallyIntegrable_restrict (hf.locallyIntegrable (by norm_num)),
    locallyIntegrableOn_of_locallyIntegrable_restrict (hG.locallyIntegrable (by norm_num)), h⟩,
    hf, hG⟩

/-- On a finite-volume domain, an H¹ function is BV. -/
theorem HasH1GradientOn.isBVOn {n : ℕ}
    {U : Set (EuclideanSpace ℝ (Fin n))} (hU : volume U < ∞)
    {f : EuclideanSpace ℝ (Fin n) → ℝ}
    {G : EuclideanSpace ℝ (Fin n) → EuclideanSpace ℝ (Fin n)} (hf : HasH1GradientOn f G U) :
    IsBVOn f U := by
  let : IsFiniteMeasure (volume.restrict U) := ⟨by simpa using hU⟩
  exact hf.toHasWeakGradientOn.isBVOn
    ((memLp_one_iff_integrable).mp (hf.memLp_function.mono_exponent (by norm_num)))
    ((memLp_one_iff_integrable).mp (hf.memLp_gradient.mono_exponent (by norm_num)))

/-- The explicit H¹-to-BV bound used in the Rellich compactness argument. -/
theorem HasH1GradientOn.bv_bound {n : ℕ}
    {U : Set (EuclideanSpace ℝ (Fin n))} (hU : volume U < ∞)
    {f : EuclideanSpace ℝ (Fin n) → ℝ}
    {G : EuclideanSpace ℝ (Fin n) → EuclideanSpace ℝ (Fin n)} (hf : HasH1GradientOn f G U) :
    eLpNorm f 1 (volume.restrict U) + variation f U ≤
      volume U ^ (1 / 2 : ℝ) *
        (eLpNorm f 2 (volume.restrict U) + eLpNorm G 2 (volume.restrict U)) := by
  let : IsFiniteMeasure (volume.restrict U) := ⟨by simpa using hU⟩
  have hiG : IntegrableOn G U :=
    (memLp_one_iff_integrable).mp (hf.memLp_gradient.mono_exponent (by norm_num))
  have hvar : variation f U ≤ eLpNorm G 1 (volume.restrict U) := by
    rw [eLpNorm_one_eq_lintegral_enorm hiG.aestronglyMeasurable,
      ← ofReal_integral_norm_eq_lintegral_enorm hiG]
    exact hf.toHasWeakGradientOn.variation_le hiG
  have h1 := eLpNorm_le_eLpNorm_mul_rpow_measure_univ (by norm_num : (1 : ℝ≥0∞) ≤ 2)
    hf.memLp_function.aestronglyMeasurable
  have h2 := eLpNorm_le_eLpNorm_mul_rpow_measure_univ (by norm_num : (1 : ℝ≥0∞) ≤ 2)
    hf.memLp_gradient.aestronglyMeasurable
  norm_num only [ENNReal.toReal_one, ENNReal.toReal_ofNat, Measure.restrict_apply_univ] at h1 h2
  exact (add_le_add le_rfl hvar).trans ((add_le_add h1 h2).trans_eq (by ring))


/-- The ordinary-norm form of the quantitative H¹-to-BV estimate. -/
theorem HasH1GradientOn.bv_bound_real {n : ℕ}
    {U : Set (EuclideanSpace ℝ (Fin n))} (hU : volume U < ∞)
    {f : EuclideanSpace ℝ (Fin n) → ℝ}
    {G : EuclideanSpace ℝ (Fin n) → EuclideanSpace ℝ (Fin n)} (hf : HasH1GradientOn f G U) :
    (∫ x in U, ‖f x‖) + (variation f U).toReal ≤
      (volume U).toReal ^ (1 / 2 : ℝ) *
        (lpNorm f 2 (volume.restrict U) + lpNorm G 2 (volume.restrict U)) := by
  let : IsFiniteMeasure (volume.restrict U) := ⟨by simpa using hU⟩
  have hf1 := hf.memLp_function.mono_exponent (by norm_num : (1 : ℝ≥0∞) ≤ 2)
  have hfin : volume U ^ (1 / 2 : ℝ) *
      (eLpNorm f 2 (volume.restrict U) + eLpNorm G 2 (volume.restrict U)) < ∞ :=
    ENNReal.mul_lt_top (ENNReal.rpow_lt_top_of_nonneg (by norm_num) hU.ne)
      (ENNReal.add_lt_top.mpr ⟨hf.memLp_function.eLpNorm_lt_top, hf.memLp_gradient.eLpNorm_lt_top⟩)
  have h := ENNReal.toReal_mono hfin.ne (hf.bv_bound hU)
  simpa only [ENNReal.toReal_add hf1.eLpNorm_ne_top (hf.isBVOn hU).2.ne,
    ENNReal.toReal_mul, ← ENNReal.toReal_rpow,
    ENNReal.toReal_add hf.memLp_function.eLpNorm_ne_top hf.memLp_gradient.eLpNorm_ne_top,
    toReal_eLpNorm,
    lpNorm_one_eq_integral_norm hf.memLp_function.aestronglyMeasurable] using h

/-- Uniform H¹ and L⁴ bounds give strong L² compactness on relatively compact open regions.
The disk theorem still requires extension and the L⁴ estimate from H¹ alone. -/
theorem exists_subseq_l2_of_h1_l4_bounds {n : ℕ}
    {A Q : Set (EuclideanSpace ℝ (Fin n))} (hA : IsOpen A) (hvol : volume A < ∞)
    (hQ : IsOpen Q) (hcQ : IsCompact (closure Q)) (hQA : closure Q ⊆ A)
    (f : ℕ → EuclideanSpace ℝ (Fin n) → ℝ)
    (G : ℕ → EuclideanSpace ℝ (Fin n) → EuclideanSpace ℝ (Fin n))
    (hf : ∀ j, HasH1GradientOn (f j) (G j) A) {C : ℝ}
    (hbound : ∀ j, lpNorm (f j) 2 (volume.restrict A) +
      lpNorm (G j) 2 (volume.restrict A) ≤ C)
    {B : ℝ≥0∞} (hB : B < ∞) (h4 : ∀ j, eLpNorm (f j) 4 (volume.restrict Q) ≤ B) :
    ∃ g : EuclideanSpace ℝ (Fin n) → ℝ, ∃ σ : ℕ → ℕ, StrictMono σ ∧ IsBVOn g Q ∧
      ∃ hf2 : ∀ j, MemLp (f (σ j)) 2 (volume.restrict Q),
        ∃ hg2 : MemLp g 2 (volume.restrict Q),
          Tendsto (fun j => (hf2 j).toLp (f (σ j))) atTop (𝓝 (hg2.toLp g)) := by
  have hC : 0 ≤ C := (add_nonneg lpNorm_nonneg lpNorm_nonneg).trans (hbound 0)
  let L := (volume A).toReal ^ (1 / 2 : ℝ) * C
  have hL : 0 ≤ L := mul_nonneg (Real.rpow_nonneg ENNReal.toReal_nonneg _) hC
  have hb (j) : (∫ x in A, |f j x|) + (variation (f j) A).toReal ≤ L := by
    have h := ((hf j).bv_bound_real hvol).trans
      (mul_le_mul_of_nonneg_left (hbound j) (Real.rpow_nonneg ENNReal.toReal_nonneg _))
    simpa only [Real.norm_eq_abs] using h
  apply exists_subseq_l2_of_bv_l4_bounds hA hQ hcQ hQA f
    (fun j => (hf j).isBVOn hvol) hL (fun j => ?_) (V := L) (fun j => ?_) hB h4
  · have hv := ENNReal.toReal_nonneg (a := variation (f j) A)
    linarith [hb j]
  · have hi : 0 ≤ ∫ x in A, |f j x| := integral_nonneg fun _ => abs_nonneg _
    linarith [hb j]

end LiquidDrop

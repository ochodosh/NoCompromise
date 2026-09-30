module

public import NoCompromise.BV.CoareaLayerCake

@[expose] public section

/-!
# The reverse BV coarea inequality

Subtracting the zero-level baseline makes the signed layer-cake integrand integrable.
Fubini and the compact divergence-test definition then bound variation by integrated
superlevel perimeter, including infinite values. No coarea identity is assumed.
-/

noncomputable section
open MeasureTheory Filter Set
open scoped ENNReal Topology
namespace LiquidDrop
set_option maxSynthPendingDepth 8

lemma integral_scalar_superlevel_difference (a b : ℝ) :
    Integrable (fun t : ℝ => (if t < a then (1 : ℝ) else 0) -
      (if t < b then 1 else 0)) ∧
    (∫ t : ℝ, (if t < a then (1 : ℝ) else 0) - (if t < b then 1 else 0)) = a - b := by
  classical
  have hi (l u : ℝ) : Integrable ((Ico l u).indicator (fun _ : ℝ => (1 : ℝ))) := by
    apply (integrable_indicator_iff measurableSet_Ico).mpr
    exact integrableOn_const (by simp)
  rcases le_total b a with hba | hab
  · have heq : (fun t : ℝ => (if t < a then (1 : ℝ) else 0) -
        (if t < b then 1 else 0)) = (Ico b a).indicator (fun _ => 1) := by
      funext t
      by_cases hta : t < a <;> by_cases htb : t < b <;>
        simp only [hta, htb, ↓reduceIte, indicator_apply, mem_Ico]
      all_goals split_ifs <;> norm_num at * <;> linarith
    rw [heq]
    refine ⟨hi b a, ?_⟩
    have h := integral_indicator_const (μ := volume) (1 : ℝ) (s := Ico b a) measurableSet_Ico
    simpa only [Measure.real, Real.volume_Ico, ENNReal.toReal_ofReal (sub_nonneg.mpr hba),
      smul_eq_mul, mul_one] using h
  · have heq : (fun t : ℝ => (if t < a then (1 : ℝ) else 0) -
        (if t < b then 1 else 0)) = -(Ico a b).indicator (fun _ => 1) := by
      funext t
      by_cases hta : t < a <;> by_cases htb : t < b <;>
        simp only [hta, htb, ↓reduceIte, Pi.neg_apply, indicator_apply, mem_Ico]
      all_goals split_ifs <;> norm_num at * <;> linarith
    rw [heq]
    refine ⟨(hi a b).neg, ?_⟩
    change (∫ t : ℝ, -((Ico a b).indicator (fun _ => (1 : ℝ)) t)) = a - b
    rw [integral_neg]
    have h := integral_indicator_const (μ := volume) (1 : ℝ) (s := Ico a b) measurableSet_Ico
    simp only [Measure.real, Real.volume_Ico, ENNReal.toReal_ofReal (sub_nonneg.mpr hab),
      smul_eq_mul, mul_one] at h
    rw [h]
    ring
/-- The total absolute mass of a signed scalar level difference is the value difference. -/
lemma integral_norm_scalar_superlevel_difference (a b : ℝ) :
    (∫ t : ℝ, ‖(if t < a then (1 : ℝ) else 0) - (if t < b then 1 else 0)‖) = |a - b| := by
  rw [integral_norm_eq_lintegral_enorm (integral_scalar_superlevel_difference a b).1.1]
  simp only [Real.enorm_eq_ofReal_abs, lintegral_abs_superlevel_difference,
    ENNReal.toReal_ofReal (abs_nonneg _)]

/-- Signed layer cake against an integrable zero-mean weight. The weighted product,
rather than the original function, is required to be integrable. -/
theorem integral_mul_eq_integral_superlevel_mul {α : Type*} [MeasurableSpace α]
    {μ : Measure α} [SFinite μ] {f g : α → ℝ} (hf : Measurable f) (hg : Measurable g)
    (hi : Integrable g μ) (hfg : Integrable (fun x => f x * g x) μ)
    (hzero : (∫ x, g x ∂μ) = 0) :
    (∫ x, f x * g x ∂μ) = ∫ t : ℝ, ∫ x, superlevelIndicator f t x * g x ∂μ := by
  let F (p : ℝ × α) := (superlevelIndicator f p.1 p.2 -
    superlevelIndicator (fun _ : α => (0 : ℝ)) p.1 p.2) * g p.2
  have hmeas : Measurable F :=
    ((measurable_superlevelIndicator_uncurry hf).sub
      (measurable_superlevelIndicator_uncurry measurable_const)).mul (hg.comp measurable_snd)
  have hinorm (x : α) : (∫ t : ℝ, ‖F (t, x)‖) = ‖f x * g x‖ := by
    simp only [F, superlevelIndicator_apply, norm_mul]
    rw [integral_mul_const, integral_norm_scalar_superlevel_difference, sub_zero,
      Real.norm_eq_abs]
    simp only [Real.norm_eq_abs]
  have hF : Integrable F (volume.prod μ) := by
    apply (integrable_prod_iff' hmeas.aestronglyMeasurable).mpr
    constructor
    · exact Eventually.of_forall fun x => by
        simpa only [F, superlevelIndicator_apply] using
          (integral_scalar_superlevel_difference (f x) 0).1.mul_const (g x)
    · simpa only [hinorm] using hfg.norm
  have hilevel (t : ℝ) : Integrable (fun x => superlevelIndicator f t x * g x) μ := by
    have heq : (fun x => superlevelIndicator f t x * g x) = {x | t < f x}.indicator g := by
      ext x
      by_cases hx : t < f x <;> simp [superlevelIndicator_apply, hx]
    rw [heq]
    exact hi.indicator (measurableSet_lt measurable_const hf)
  have hinner (t : ℝ) : (∫ x, F (t, x) ∂μ) =
      ∫ x, superlevelIndicator f t x * g x ∂μ := by
    simp only [F, superlevelIndicator_apply (fun _ : α => (0 : ℝ)), sub_mul]
    have hic : Integrable (fun x => (if t < 0 then (1 : ℝ) else 0) * g x) μ :=
      hi.const_mul _
    rw [integral_sub (hilevel t) hic, integral_const_mul, hzero,
      mul_zero, sub_zero]
  calc
    _ = ∫ x, (∫ t : ℝ, F (t, x)) ∂μ := by
      apply integral_congr_ae
      filter_upwards with x
      simp only [F, superlevelIndicator_apply]
      rw [integral_mul_const, (integral_scalar_superlevel_difference (f x) 0).2, sub_zero]
    _ = ∫ t : ℝ, ∫ x, F (t, x) ∂μ := (integral_integral_swap hF).symm
    _ = _ := by simp only [hinner]

/-- Every compact divergence pairing is bounded by variation in extended norm. -/
lemma enorm_integral_mul_divergenceN_le_variation {n : ℕ}
    {U : Set (EuclideanSpace ℝ (Fin n))} {f : EuclideanSpace ℝ (Fin n) → ℝ}
    {X : EuclideanSpace ℝ (Fin n) → EuclideanSpace ℝ (Fin n)}
    (hX : IsVariationTestField U X) :
    ‖∫ x in U, f x * divergenceN X x‖ₑ ≤ variation f U := by
  by_cases hfin : variation f U = ∞
  · simp only [hfin, le_top]
  · rw [Real.enorm_eq_ofReal_abs]
    exact (ENNReal.ofReal_le_ofReal
      (abs_integral_mul_divergenceN_le_variation hfin hX)).trans_eq
      (ENNReal.ofReal_toReal hfin)

/-- Reverse coarea for a measurable, locally integrable representative. -/
theorem variation_le_lintegral_perimeter_superlevel_of_measurable {n : ℕ}
    {U : Set (EuclideanSpace ℝ (Fin n))} (_hU : IsOpen U)
    {f : EuclideanSpace ℝ (Fin n) → ℝ} (hf : LocallyIntegrableOn f U)
    (hm : Measurable f) :
    variation f U ≤ ∫⁻ t : ℝ, perimeterIn {x | t < f x} U := by
  apply iSup_le
  intro X
  apply iSup_le
  intro hX
  have hi := (integrable_divergenceN hX.1 hX.2.1).integrableOn (s := U)
  have hfg := (integrable_mul_divergenceN hf hX.1 hX.2.1 hX.2.2.1).integrableOn (s := U)
  have hzero : (∫ x in U, divergenceN X x) = 0 := by
    rw [setIntegral_eq_integral_of_forall_compl_eq_zero]
    · exact integral_divergenceN_eq_zero hX.1 hX.2.1
    · intro x hx
      exact divergenceN_eq_zero_of_notMem_tsupport (fun hx' => hx (hX.2.2.1 hx'))
  have hlayer := integral_mul_eq_integral_superlevel_mul hm
    (continuous_divergenceN hX.1).measurable hi hfg hzero
  rw [hlayer]
  apply (Real.ofReal_le_enorm _).trans ((enorm_integral_le_lintegral_enorm _).trans ?_)
  apply lintegral_mono
  intro t
  exact enorm_integral_mul_divergenceN_le_variation (f := superlevelIndicator f t) hX

/-- The reverse coarea inequality holds for every locally integrable function on an open set.
It needs neither finite variation nor measurability of the perimeter as a function of level. -/
theorem variation_le_lintegral_perimeter_superlevel {n : ℕ}
    {U : Set (EuclideanSpace ℝ (Fin n))} (hU : IsOpen U)
    {f : EuclideanSpace ℝ (Fin n) → ℝ} (hf : LocallyIntegrableOn f U) :
    variation f U ≤ ∫⁻ t : ℝ, perimeterIn {x | t < f x} U := by
  let g := hf.aestronglyMeasurable.aemeasurable.mk f
  have hg : Measurable g := hf.aestronglyMeasurable.aemeasurable.measurable_mk
  have heq : f =ᵐ[volume.restrict U] g := hf.aestronglyMeasurable.aemeasurable.ae_eq_mk
  have hig : LocallyIntegrableOn g U := LocallyIntegrableOn.congr heq hf
  have hv := variation_le_lintegral_perimeter_superlevel_of_measurable hU hig hg
  rw [← variation_congr_ae U heq] at hv
  convert hv using 1
  apply lintegral_congr
  intro t
  apply variation_congr_ae
  filter_upwards [heq] with x hx
  simp only [indicator_apply, mem_ofPred_eq, hx]

/-- The reverse inequality in blueprint `thm:bv-coarea`, including infinite variation. -/
theorem IsLocallyBVOn.variation_le_lintegral_perimeter_superlevel {n : ℕ}
    {U : Set (EuclideanSpace ℝ (Fin n))} (hU : IsOpen U)
    {f : EuclideanSpace ℝ (Fin n) → ℝ} (hf : IsLocallyBVOn f U) :
    variation f U ≤ ∫⁻ t : ℝ, perimeterIn {x | t < f x} U :=
  LiquidDrop.variation_le_lintegral_perimeter_superlevel hU hf.1

end LiquidDrop

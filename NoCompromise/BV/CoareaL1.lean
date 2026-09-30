module

public import NoCompromise.BV.WeightedCoarea
public import Mathlib.MeasureTheory.Integral.Bochner.Basic

@[expose] public section

/-!
# Coarea with an integrable signed weight

On the regular locus the gradient norm cancels the inverse-gradient weight.
Null sets have null regular fibers for almost every level, so the identity
holds for arbitrary Lebesgue integrable representatives, not only Borel ones.
-/

noncomputable section
open MeasureTheory Set Filter Function InnerProductSpace
open scoped ENNReal NNReal Topology Gradient
namespace LiquidDrop
set_option maxSynthPendingDepth 8

/-- Restriction of weighted coarea to a Borel subset of the open domain. -/
lemma weighted_c1_coarea_on_measurable {n : ℕ} (hn : 2 ≤ n)
    {U : Set (EuclideanSpace ℝ (Fin n))} (hU : IsOpen U)
    {u : EuclideanSpace ℝ (Fin n) → ℝ} (hu : ContDiffOn ℝ 1 u U)
    {A : Set (EuclideanSpace ℝ (Fin n))} (hA : MeasurableSet A) (hAU : A ⊆ U) :
    HasWeightedCoareaOn u A := by
  intro g hg
  obtain ⟨hm, he⟩ := hasWeightedCoareaOn_of_contDiffOn hn hU hu
    (A.indicator g) (hg.indicator hA)
  have hsource : (∫⁻ x in U, A.indicator g x * ENNReal.ofReal ‖gradient u x‖) =
      ∫⁻ x in A, g x * ENNReal.ofReal ‖gradient u x‖ := by
    have hind : (fun x => A.indicator g x * ENNReal.ofReal ‖gradient u x‖) =
        A.indicator (fun x => g x * ENNReal.ofReal ‖gradient u x‖) := by
      funext x
      by_cases hx : x ∈ A <;> simp [hx]
    rw [hind, setLIntegral_indicator hA, inter_eq_left.mpr hAU]
  have hlevel (t : ℝ) :
      (∫⁻ x in U ∩ u ⁻¹' {t}, A.indicator g x
        ∂Measure.euclideanHausdorffMeasure (n - 1)) =
      ∫⁻ x in A ∩ u ⁻¹' {t}, g x ∂Measure.euclideanHausdorffMeasure (n - 1) := by
    rw [setLIntegral_indicator hA]
    congr 2
    exact inter_assoc A U (u ⁻¹' {t}) |>.symm.trans
      (congrArg (· ∩ u ⁻¹' {t}) (inter_eq_left.mpr hAU))
  refine ⟨hm.congr (Eventually.of_forall hlevel), ?_⟩
  exact hsource.symm.trans (he.trans (lintegral_congr hlevel))

/-- Extended nonnegative coarea with cancellation of the gradient norm. -/
lemma coarea_lintegral_div_gradient {n : ℕ} (hn : 2 ≤ n)
    {U : Set (EuclideanSpace ℝ (Fin n))} (hU : IsOpen U)
    {u : EuclideanSpace ℝ (Fin n) → ℝ} (hu : ContDiffOn ℝ 1 u U)
    {A : Set (EuclideanSpace ℝ (Fin n))} (hA : MeasurableSet A) (hAU : A ⊆ U)
    (hreg : ∀ x ∈ A, gradient u x ≠ 0)
    {g : EuclideanSpace ℝ (Fin n) → ℝ≥0∞} (hg : Measurable g) :
    AEMeasurable (fun t : ℝ => ∫⁻ x in A ∩ u ⁻¹' {t},
      g x / ENNReal.ofReal ‖gradient u x‖
        ∂Measure.euclideanHausdorffMeasure (n - 1)) volume ∧
    (∫⁻ x in A, g x) = ∫⁻ t : ℝ, ∫⁻ x in A ∩ u ⁻¹' {t},
      g x / ENNReal.ofReal ‖gradient u x‖
        ∂Measure.euclideanHausdorffMeasure (n - 1) := by
  have hgrad : Measurable (gradient u) :=
    (toDual ℝ (EuclideanSpace ℝ (Fin n))).symm.continuous.measurable.comp
      (measurable_fderiv ℝ u)
  obtain ⟨hm, he⟩ := weighted_c1_coarea_on_measurable hn hU hu hA hAU
    (fun x => g x / ENNReal.ofReal ‖gradient u x‖) (hg.div hgrad.norm.ennreal_ofReal)
  refine ⟨hm, ?_⟩
  rw [← he]
  apply setLIntegral_congr_fun hA
  intro x hx
  dsimp only
  exact (ENNReal.div_mul_cancel (ne_of_gt (ENNReal.ofReal_pos.mpr
    (norm_pos_iff.mpr (hreg x hx)))) ENNReal.ofReal_ne_top).symm

/-- A null subset of the domain has null fibers for almost every level. -/
lemma ae_null_coarea_fibers {n : ℕ} (hn : 2 ≤ n)
    {U : Set (EuclideanSpace ℝ (Fin n))} (hU : IsOpen U)
    {u : EuclideanSpace ℝ (Fin n) → ℝ} (hu : ContDiffOn ℝ 1 u U)
    {A : Set (EuclideanSpace ℝ (Fin n))} (hA : MeasurableSet A) (hAU : A ⊆ U)
    (hnull : volume A = 0) :
    ∀ᵐ t : ℝ, Measure.euclideanHausdorffMeasure (n - 1) (A ∩ u ⁻¹' {t}) = 0 := by
  obtain ⟨hm, he⟩ := weighted_c1_coarea_on_measurable hn hU hu hA hAU
    (fun _ => 1) measurable_const
  have hi : (∫⁻ t : ℝ, ∫⁻ x in A ∩ u ⁻¹' {t}, (1 : ℝ≥0∞)
      ∂Measure.euclideanHausdorffMeasure (n - 1)) = 0 := by
    rw [← he, Measure.restrict_eq_zero.mpr hnull, lintegral_zero_measure]
  simpa only [setLIntegral_const, one_mul, EventuallyEq, Pi.zero_apply] using
    (lintegral_eq_zero_iff' hm).mp hi

/-- Equality of volume representatives descends to almost every level fiber. -/
lemma ae_coarea_fiber_eq {n : ℕ} (hn : 2 ≤ n)
    {U : Set (EuclideanSpace ℝ (Fin n))} (hU : IsOpen U)
    {u : EuclideanSpace ℝ (Fin n) → ℝ} (hu : ContDiffOn ℝ 1 u U)
    {A : Set (EuclideanSpace ℝ (Fin n))} (hA : MeasurableSet A) (hAU : A ⊆ U)
    {β : Type*}
    {f g : EuclideanSpace ℝ (Fin n) → β} (hfg : f =ᵐ[volume.restrict A] g) :
    ∀ᵐ t : ℝ, f =ᵐ[(Measure.euclideanHausdorffMeasure (n - 1)).restrict
      (A ∩ u ⁻¹' {t})] g := by
  let N := toMeasurable volume {x | x ∈ A ∧ f x ≠ g x} ∩ A
  have hNm : MeasurableSet N := (measurableSet_toMeasurable _ _).inter hA
  have hNnull : volume N = 0 := by
    apply measure_mono_null inter_subset_left
    rw [measure_toMeasurable]
    simpa [EventuallyEq, ae_iff, Measure.restrict_apply' hA, ofPred_and, inter_comm] using hfg
  filter_upwards [ae_null_coarea_fibers hn hU hu hNm
    (inter_subset_right.trans hAU) hNnull] with t ht
  rw [EventuallyEq, ae_iff, Measure.restrict_apply'
    (measurableSet_coarea_level_of_continuousOn hA (hu.continuousOn.mono hAU) t)]
  apply measure_mono_null _ ht
  rintro x ⟨hxne, hxA, hxt⟩
  exact ⟨⟨subset_toMeasurable volume _ ⟨hxA, hxne⟩, hxA⟩, hxt⟩

/-- Positive and negative parts may be inserted before the inverse-gradient quotient. -/
lemma coarea_lintegral_ofReal_div_gradient {n : ℕ} (hn : 2 ≤ n)
    {U : Set (EuclideanSpace ℝ (Fin n))} (hU : IsOpen U)
    {u : EuclideanSpace ℝ (Fin n) → ℝ} (hu : ContDiffOn ℝ 1 u U)
    {A : Set (EuclideanSpace ℝ (Fin n))} (hA : MeasurableSet A) (hAU : A ⊆ U)
    (hreg : ∀ x ∈ A, gradient u x ≠ 0)
    {G : EuclideanSpace ℝ (Fin n) → ℝ} (hG : Measurable G) :
    AEMeasurable (fun t : ℝ => ∫⁻ x in A ∩ u ⁻¹' {t},
      ENNReal.ofReal (G x / ‖gradient u x‖)
        ∂Measure.euclideanHausdorffMeasure (n - 1)) volume ∧
    (∫⁻ x in A, ENNReal.ofReal (G x)) = ∫⁻ t : ℝ, ∫⁻ x in A ∩ u ⁻¹' {t},
      ENNReal.ofReal (G x / ‖gradient u x‖)
        ∂Measure.euclideanHausdorffMeasure (n - 1) := by
  obtain ⟨hm, he⟩ := coarea_lintegral_div_gradient hn hU hu hA hAU hreg hG.ennreal_ofReal
  have heq (t : ℝ) :
      (∫⁻ x in A ∩ u ⁻¹' {t}, ENNReal.ofReal (G x) / ENNReal.ofReal ‖gradient u x‖
        ∂Measure.euclideanHausdorffMeasure (n - 1)) =
      ∫⁻ x in A ∩ u ⁻¹' {t}, ENNReal.ofReal (G x / ‖gradient u x‖)
        ∂Measure.euclideanHausdorffMeasure (n - 1) := by
    apply setLIntegral_congr_fun
      (measurableSet_coarea_level_of_continuousOn hA (hu.continuousOn.mono hAU) t)
    intro x hx
    exact (ENNReal.ofReal_div_of_pos (norm_pos_iff.mpr (hreg x hx.1))).symm
  exact ⟨hm.congr (Eventually.of_forall heq), he.trans (lintegral_congr heq)⟩

/-- The signed L¹ identity for a Borel representative on the regular locus. -/
lemma coarea_integral_div_gradient_of_measurable {n : ℕ} (hn : 2 ≤ n)
    {U : Set (EuclideanSpace ℝ (Fin n))} (hU : IsOpen U)
    {u : EuclideanSpace ℝ (Fin n) → ℝ} (hu : ContDiffOn ℝ 1 u U)
    {A : Set (EuclideanSpace ℝ (Fin n))} (hA : MeasurableSet A) (hAU : A ⊆ U)
    (hreg : ∀ x ∈ A, gradient u x ≠ 0)
    {G : EuclideanSpace ℝ (Fin n) → ℝ} (hG : Measurable G)
    (hGi : Integrable G (volume.restrict A)) :
    (∀ᵐ t : ℝ, Integrable (fun x => G x / ‖gradient u x‖)
      ((Measure.euclideanHausdorffMeasure (n - 1)).restrict (A ∩ u ⁻¹' {t}))) ∧
    Integrable (fun t : ℝ => ∫ x in A ∩ u ⁻¹' {t}, G x / ‖gradient u x‖
      ∂Measure.euclideanHausdorffMeasure (n - 1)) ∧
    (∫ x in A, G x) = ∫ t : ℝ, ∫ x in A ∩ u ⁻¹' {t}, G x / ‖gradient u x‖
      ∂Measure.euclideanHausdorffMeasure (n - 1) := by
  let P := fun t : ℝ => ∫⁻ x in A ∩ u ⁻¹' {t}, ENNReal.ofReal (G x / ‖gradient u x‖)
    ∂Measure.euclideanHausdorffMeasure (n - 1)
  let N := fun t : ℝ => ∫⁻ x in A ∩ u ⁻¹' {t}, ENNReal.ofReal (-G x / ‖gradient u x‖)
    ∂Measure.euclideanHausdorffMeasure (n - 1)
  let Q := fun t : ℝ => ∫⁻ x in A ∩ u ⁻¹' {t}, ENNReal.ofReal (‖G x‖ / ‖gradient u x‖)
    ∂Measure.euclideanHausdorffMeasure (n - 1)
  obtain ⟨hPm, hPe⟩ := coarea_lintegral_ofReal_div_gradient hn hU hu hA hAU hreg hG
  obtain ⟨hNm, hNe⟩ := coarea_lintegral_ofReal_div_gradient hn hU hu hA hAU hreg hG.neg
  obtain ⟨hQm, hQe⟩ := coarea_lintegral_ofReal_div_gradient hn hU hu hA hAU hreg hG.norm
  simp only [Pi.neg_apply] at hNm hNe
  change AEMeasurable P volume at hPm
  change AEMeasurable N volume at hNm
  change AEMeasurable Q volume at hQm
  change (∫⁻ x in A, ENNReal.ofReal (G x)) = ∫⁻ t, P t at hPe
  change (∫⁻ x in A, ENNReal.ofReal (-G x)) = ∫⁻ t, N t at hNe
  change (∫⁻ x in A, ENNReal.ofReal ‖G x‖) = ∫⁻ t, Q t at hQe
  have hQfin : (∫⁻ t, Q t) < ∞ := by
    rw [← hQe]
    exact (hasFiniteIntegral_iff_norm _).mp hGi.hasFiniteIntegral
  have hPfin : (∫⁻ t, P t) < ∞ := by
    rw [← hPe]
    exact (lintegral_mono fun x => ENNReal.ofReal_le_ofReal (le_abs_self (G x))).trans_lt
      ((hasFiniteIntegral_iff_norm _).mp hGi.hasFiniteIntegral)
  have hNfin : (∫⁻ t, N t) < ∞ := by
    rw [← hNe]
    exact (lintegral_mono fun x => ENNReal.ofReal_le_ofReal (neg_le_abs (G x))).trans_lt
      ((hasFiniteIntegral_iff_norm _).mp hGi.hasFiniteIntegral)
  have hPi := integrable_toReal_of_lintegral_ne_top hPm hPfin.ne
  have hNi := integrable_toReal_of_lintegral_ne_top hNm hNfin.ne
  have hgrad : Measurable (gradient u) :=
    (toDual ℝ (EuclideanSpace ℝ (Fin n))).symm.continuous.measurable.comp
      (measurable_fderiv ℝ u)
  have hQi : ∀ᵐ t : ℝ, Integrable (fun x => G x / ‖gradient u x‖)
      ((Measure.euclideanHausdorffMeasure (n - 1)).restrict (A ∩ u ⁻¹' {t})) := by
    filter_upwards [ae_lt_top' hQm hQfin.ne] with t ht
    refine ⟨(hG.div hgrad.norm).aestronglyMeasurable, ?_⟩
    rw [hasFiniteIntegral_iff_norm]
    simpa only [Q, Real.norm_eq_abs, abs_div, abs_norm] using ht
  have hi : (fun t : ℝ => ∫ x in A ∩ u ⁻¹' {t}, G x / ‖gradient u x‖
      ∂Measure.euclideanHausdorffMeasure (n - 1)) =ᵐ[volume]
      (fun t => (P t).toReal - (N t).toReal) := by
    filter_upwards [hQi] with t ht
    simpa only [neg_div, P, N] using
      integral_eq_lintegral_pos_part_sub_lintegral_neg_part ht
  refine ⟨hQi, (hPi.sub hNi).congr hi.symm, ?_⟩
  rw [integral_congr_ae hi, integral_sub hPi hNi,
    integral_toReal hPm (ae_lt_top' hPm hPfin.ne),
    integral_toReal hNm (ae_lt_top' hNm hNfin.ne), ← hPe, ← hNe]
  exact integral_eq_lintegral_pos_part_sub_lintegral_neg_part hGi

/-- Coarea for any integrable representative on a regular Borel subset. -/
theorem coarea_integral_div_gradient {n : ℕ} (hn : 2 ≤ n)
    {U : Set (EuclideanSpace ℝ (Fin n))} (hU : IsOpen U)
    {u : EuclideanSpace ℝ (Fin n) → ℝ} (hu : ContDiffOn ℝ 1 u U)
    {A : Set (EuclideanSpace ℝ (Fin n))} (hA : MeasurableSet A) (hAU : A ⊆ U)
    (hreg : ∀ x ∈ A, gradient u x ≠ 0)
    {G : EuclideanSpace ℝ (Fin n) → ℝ} (hGi : Integrable G (volume.restrict A)) :
    (∀ᵐ t : ℝ, Integrable (fun x => G x / ‖gradient u x‖)
      ((Measure.euclideanHausdorffMeasure (n - 1)).restrict (A ∩ u ⁻¹' {t}))) ∧
    Integrable (fun t : ℝ => ∫ x in A ∩ u ⁻¹' {t}, G x / ‖gradient u x‖
      ∂Measure.euclideanHausdorffMeasure (n - 1)) ∧
    (∫ x in A, G x) = ∫ t : ℝ, ∫ x in A ∩ u ⁻¹' {t}, G x / ‖gradient u x‖
      ∂Measure.euclideanHausdorffMeasure (n - 1) := by
  let G' := hGi.aestronglyMeasurable.mk G
  have heq : G =ᵐ[volume.restrict A] G' := hGi.aestronglyMeasurable.ae_eq_mk
  obtain ⟨hf, hi, he⟩ := coarea_integral_div_gradient_of_measurable hn hU hu hA hAU hreg
    hGi.aestronglyMeasurable.measurable_mk (hGi.congr heq)
  have heqf : ∀ᵐ t : ℝ,
      (fun x => G x / ‖gradient u x‖) =ᵐ[(Measure.euclideanHausdorffMeasure (n - 1)).restrict
        (A ∩ u ⁻¹' {t})] (fun x => G' x / ‖gradient u x‖) := by
    filter_upwards [ae_coarea_fiber_eq hn hU hu hA hAU heq] with t ht
    exact ht.div (Eventually.of_forall fun _ => rfl)
  have heqi : (fun t : ℝ => ∫ x in A ∩ u ⁻¹' {t}, G x / ‖gradient u x‖
      ∂Measure.euclideanHausdorffMeasure (n - 1)) =ᵐ[volume]
      (fun t : ℝ => ∫ x in A ∩ u ⁻¹' {t}, G' x / ‖gradient u x‖
        ∂Measure.euclideanHausdorffMeasure (n - 1)) :=
    heqf.mono fun _ ht => integral_congr_ae ht
  refine ⟨?_, hi.congr heqi.symm,
    (integral_congr_ae heq).trans (he.trans (integral_congr_ae heqi.symm))⟩
  filter_upwards [hf, heqf] with t ht heqt
  exact ht.congr heqt.symm

/-- Blueprint `cor:coarea-L1`, with the almost-everywhere fiber and outer
integrability conclusions made explicit. -/
theorem coarea_L1_with_integrability {n : ℕ} (hn : 2 ≤ n)
    {U : Set (EuclideanSpace ℝ (Fin n))} (hU : IsOpen U)
    {u : EuclideanSpace ℝ (Fin n) → ℝ} (hu : ContDiffOn ℝ 1 u U)
    {A : Set (EuclideanSpace ℝ (Fin n))} (hA : MeasurableSet A) (hAU : A ⊆ U)
    {G : EuclideanSpace ℝ (Fin n) → ℝ} (hGi : Integrable G (volume.restrict A)) :
    (∀ᵐ t : ℝ, Integrable (fun x => G x / ‖gradient u x‖)
      ((Measure.euclideanHausdorffMeasure (n - 1)).restrict
        ((A ∩ {x | 0 < ‖gradient u x‖}) ∩ u ⁻¹' {t}))) ∧
    Integrable (fun t : ℝ => ∫ x in (A ∩ {x | 0 < ‖gradient u x‖}) ∩ u ⁻¹' {t},
      G x / ‖gradient u x‖ ∂Measure.euclideanHausdorffMeasure (n - 1)) ∧
    (∫ x in A ∩ {x | 0 < ‖gradient u x‖}, G x) =
      ∫ t : ℝ, ∫ x in (A ∩ {x | 0 < ‖gradient u x‖}) ∩ u ⁻¹' {t},
        G x / ‖gradient u x‖ ∂Measure.euclideanHausdorffMeasure (n - 1) := by
  have hgrad : Measurable (gradient u) :=
    (toDual ℝ (EuclideanSpace ℝ (Fin n))).symm.continuous.measurable.comp
      (measurable_fderiv ℝ u)
  exact coarea_integral_div_gradient hn hU hu
    (hA.inter (measurableSet_lt measurable_const hgrad.norm)) (inter_subset_left.trans hAU)
    (fun x hx => norm_pos_iff.mp hx.2)
    (hGi.mono_measure (Measure.restrict_mono inter_subset_left le_rfl))

/-- The signed coarea equality, allowing critical points in the domain. -/
theorem coarea_L1 {n : ℕ} (hn : 2 ≤ n)
    {U : Set (EuclideanSpace ℝ (Fin n))} (hU : IsOpen U)
    {u : EuclideanSpace ℝ (Fin n) → ℝ} (hu : ContDiffOn ℝ 1 u U)
    {A : Set (EuclideanSpace ℝ (Fin n))} (hA : MeasurableSet A) (hAU : A ⊆ U)
    {G : EuclideanSpace ℝ (Fin n) → ℝ} (hGi : Integrable G (volume.restrict A)) :
    (∫ x in A ∩ {x | 0 < ‖gradient u x‖}, G x) =
      ∫ t : ℝ, ∫ x in (A ∩ {x | 0 < ‖gradient u x‖}) ∩ u ⁻¹' {t},
        G x / ‖gradient u x‖ ∂Measure.euclideanHausdorffMeasure (n - 1) :=
  (coarea_L1_with_integrability hn hU hu hA hAU hGi).2.2

/-- If the gradient never vanishes on `A`, no regular-locus restrictions remain. -/
theorem coarea_L1_of_gradient_ne_zero {n : ℕ} (hn : 2 ≤ n)
    {U : Set (EuclideanSpace ℝ (Fin n))} (hU : IsOpen U)
    {u : EuclideanSpace ℝ (Fin n) → ℝ} (hu : ContDiffOn ℝ 1 u U)
    {A : Set (EuclideanSpace ℝ (Fin n))} (hA : MeasurableSet A) (hAU : A ⊆ U)
    (hreg : ∀ x ∈ A, gradient u x ≠ 0)
    {G : EuclideanSpace ℝ (Fin n) → ℝ} (hGi : Integrable G (volume.restrict A)) :
    (∫ x in A, G x) = ∫ t : ℝ, ∫ x in A ∩ u ⁻¹' {t}, G x / ‖gradient u x‖
      ∂Measure.euclideanHausdorffMeasure (n - 1) :=
  (coarea_integral_div_gradient hn hU hu hA hAU hreg hGi).2.2

end LiquidDrop

module

public import NoCompromise.BV.CoareaL1

@[expose] public section

/-!
# Coarea on Lebesgue measurable sets

Borel representatives of a Lebesgue measurable domain agree on almost every
Hausdorff level fiber. This removes the Borel restriction from the signed L¹
coarea corollary while retaining its integrability conclusions.
-/

noncomputable section
open MeasureTheory Set Filter Function InnerProductSpace
open scoped ENNReal NNReal Topology Gradient
namespace LiquidDrop
set_option maxSynthPendingDepth 8

/-- Volume-almost-equal subsets of the domain have almost-equal Hausdorff fibers
for almost every level. No measurability of the two subsets is required. -/
lemma ae_coarea_fiber_set_eq {n : ℕ} (hn : 2 ≤ n)
    {U : Set (EuclideanSpace ℝ (Fin n))} (hU : IsOpen U)
    {u : EuclideanSpace ℝ (Fin n) → ℝ} (hu : ContDiffOn ℝ 1 u U)
    {A B : Set (EuclideanSpace ℝ (Fin n))} (hAU : A ⊆ U) (hBU : B ⊆ U)
    (hAB : A =ᵐ[volume] B) :
    ∀ᵐ t : ℝ, (A ∩ u ⁻¹' {t} : Set (EuclideanSpace ℝ (Fin n)))
      =ᵐ[Measure.euclideanHausdorffMeasure (n - 1)]
        (B ∩ u ⁻¹' {t} : Set (EuclideanSpace ℝ (Fin n))) := by
  have hf := ae_coarea_fiber_eq hn hU hu hU.measurableSet (Subset.refl U) hAB.restrict
  filter_upwards [hf] with t ht
  have ht' := (ae_restrict_iff'
    (measurableSet_coarea_level_of_continuousOn hU.measurableSet hu.continuousOn t)).mp ht
  filter_upwards [ht'] with x hx
  apply propext
  constructor
  · intro h
    exact ⟨(eq_iff_iff.mp (hx ⟨hAU h.1, h.2⟩)).mp h.1, h.2⟩
  · intro h
    exact ⟨(eq_iff_iff.mp (hx ⟨hBU h.1, h.2⟩)).mpr h.1, h.2⟩

/-- The signed L¹ coarea theorem on a Lebesgue measurable regular subset. -/
theorem coarea_integral_div_gradient_nullMeasurable {n : ℕ} (hn : 2 ≤ n)
    {U : Set (EuclideanSpace ℝ (Fin n))} (hU : IsOpen U)
    {u : EuclideanSpace ℝ (Fin n) → ℝ} (hu : ContDiffOn ℝ 1 u U)
    {A : Set (EuclideanSpace ℝ (Fin n))} (hA : NullMeasurableSet A volume) (hAU : A ⊆ U)
    (hreg : ∀ x ∈ A, gradient u x ≠ 0)
    {G : EuclideanSpace ℝ (Fin n) → ℝ} (hGi : Integrable G (volume.restrict A)) :
    (∀ᵐ t : ℝ, Integrable (fun x => G x / ‖gradient u x‖)
      ((Measure.euclideanHausdorffMeasure (n - 1)).restrict (A ∩ u ⁻¹' {t}))) ∧
    Integrable (fun t : ℝ => ∫ x in A ∩ u ⁻¹' {t}, G x / ‖gradient u x‖
      ∂Measure.euclideanHausdorffMeasure (n - 1)) ∧
    (∫ x in A, G x) = ∫ t : ℝ, ∫ x in A ∩ u ⁻¹' {t}, G x / ‖gradient u x‖
      ∂Measure.euclideanHausdorffMeasure (n - 1) := by
  have hgrad : Measurable (gradient u) :=
    (toDual ℝ (EuclideanSpace ℝ (Fin n))).symm.continuous.measurable.comp
      (measurable_fderiv ℝ u)
  let B := (toMeasurable volume A ∩ U) ∩ {x | gradient u x ≠ 0}
  have hBm : MeasurableSet B :=
    ((measurableSet_toMeasurable _ _).inter hU.measurableSet).inter
      (hgrad (measurableSet_singleton 0)).compl
  have hBA : B =ᵐ[volume] A := by
    filter_upwards [hA.toMeasurable_ae_eq] with x hx
    apply propext
    constructor
    · exact fun h => (eq_iff_iff.mp hx).mp h.1.1
    · exact fun h => ⟨⟨(eq_iff_iff.mp hx).mpr h, hAU h⟩, hreg x h⟩
  have hmeasure := Measure.restrict_congr_set hBA
  have hBG : Integrable G (volume.restrict B) := by rwa [hmeasure]
  obtain ⟨hf, hi, he⟩ := coarea_integral_div_gradient hn hU hu hBm
    (fun _ hx => hx.1.2) (fun _ hx => hx.2) hBG
  have hmf : ∀ᵐ t : ℝ,
      (Measure.euclideanHausdorffMeasure (n - 1)).restrict (B ∩ u ⁻¹' {t}) =
      (Measure.euclideanHausdorffMeasure (n - 1)).restrict (A ∩ u ⁻¹' {t}) :=
    (ae_coarea_fiber_set_eq hn hU hu (fun _ hx => hx.1.2) hAU hBA).mono
      fun _ ht => Measure.restrict_congr_set ht
  have hieq : (fun t : ℝ => ∫ x in B ∩ u ⁻¹' {t}, G x / ‖gradient u x‖
      ∂Measure.euclideanHausdorffMeasure (n - 1)) =ᵐ[volume]
      (fun t : ℝ => ∫ x in A ∩ u ⁻¹' {t}, G x / ‖gradient u x‖
        ∂Measure.euclideanHausdorffMeasure (n - 1)) :=
    hmf.mono fun _ ht => congrArg (fun μ => ∫ x, G x / ‖gradient u x‖ ∂μ) ht
  refine ⟨?_, hi.congr hieq, ?_⟩
  · filter_upwards [hf, hmf] with t ht heqt
    rwa [← heqt]
  · rw [hmeasure] at he
    exact he.trans (integral_congr_ae hieq)

/-- Blueprint `cor:coarea-L1` for a Lebesgue measurable set and an arbitrary
integrable signed representative, including fiber and outer integrability. -/
theorem coarea_L1_nullMeasurable {n : ℕ} (hn : 2 ≤ n)
    {U : Set (EuclideanSpace ℝ (Fin n))} (hU : IsOpen U)
    {u : EuclideanSpace ℝ (Fin n) → ℝ} (hu : ContDiffOn ℝ 1 u U)
    {A : Set (EuclideanSpace ℝ (Fin n))} (hA : NullMeasurableSet A volume) (hAU : A ⊆ U)
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
  exact coarea_integral_div_gradient_nullMeasurable hn hU hu
    (hA.inter (measurableSet_lt measurable_const hgrad.norm).nullMeasurableSet)
    (inter_subset_left.trans hAU) (fun x hx => norm_pos_iff.mp hx.2)
    (hGi.mono_measure (Measure.restrict_mono inter_subset_left le_rfl))

end LiquidDrop

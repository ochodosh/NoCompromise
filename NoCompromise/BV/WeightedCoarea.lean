module

public import NoCompromise.BV.CoareaRegular
public import NoCompromise.BV.CoareaCritical

@[expose] public section

/-!
# Weighted C¹ coarea without Sard's theorem

The regular part is proved by inverse coordinate charts, ordinary change of
variables and graph area. The critical fibers have zero normalized Hausdorff
measure for almost every level by the elementary covering argument. Together
they give the full weighted identity, allowing arbitrary nonnegative extended
Borel weights and critical levels.
-/

noncomputable section
open MeasureTheory Set Filter Function InnerProductSpace
open scoped ENNReal NNReal Topology Gradient
namespace LiquidDrop
set_option maxSynthPendingDepth 8

/-- Full weighted C¹ coarea, including critical points and critical levels. -/
theorem hasWeightedCoareaOn_of_contDiffOn {n : ℕ} (hn : 2 ≤ n)
    {U : Set (EuclideanSpace ℝ (Fin n))} (hU : IsOpen U)
    {u : EuclideanSpace ℝ (Fin n) → ℝ} (hu : ContDiffOn ℝ 1 u U) :
    HasWeightedCoareaOn u U := by
  intro g hg
  let R := {x | x ∈ U ∧ gradient u x ≠ 0}
  have hgrad : Measurable (gradient u) :=
    (toDual ℝ (EuclideanSpace ℝ (Fin n))).symm.continuous.measurable.comp
      (measurable_fderiv ℝ u)
  have hRm : MeasurableSet R :=
    hU.measurableSet.inter ((hgrad (measurableSet_singleton 0)).compl)
  have hsource : (∫⁻ x in U, g x * ENNReal.ofReal ‖gradient u x‖) =
      ∫⁻ x in R, g x * ENNReal.ofReal ‖gradient u x‖ := by
    rw [← lintegral_indicator hU.measurableSet, ← lintegral_indicator hRm]
    congr 1
    funext x
    by_cases hx : x ∈ U <;> by_cases hz : gradient u x = 0 <;> simp [R, hx, hz]
  have hlevel : (fun t : ℝ =>
      ∫⁻ x in U ∩ u ⁻¹' {t}, g x ∂Measure.euclideanHausdorffMeasure (n - 1)) =ᵐ[volume]
      (fun t : ℝ => ∫⁻ x in R ∩ u ⁻¹' {t},
        g x ∂Measure.euclideanHausdorffMeasure (n - 1)) := by
    filter_upwards [coarea_critical_part hn hU hu] with t ht
    have hnull : ∀ᵐ x ∂Measure.euclideanHausdorffMeasure (n - 1),
        ¬(x ∈ U ∧ gradient u x = 0 ∧ u x = t) := by
      apply ae_iff.mpr
      simpa only [not_not] using ht
    have hsets : (U ∩ u ⁻¹' {t} : Set (EuclideanSpace ℝ (Fin n)))
        =ᵐ[Measure.euclideanHausdorffMeasure (n - 1)]
        (R ∩ u ⁻¹' {t} : Set (EuclideanSpace ℝ (Fin n))) := by
      filter_upwards [hnull] with x hx
      apply propext
      constructor
      · rintro ⟨hxU, hxt⟩
        refine ⟨⟨hxU, ?_⟩, hxt⟩
        intro hz
        exact hx ⟨hxU, hz, hxt⟩
      · exact fun h => ⟨h.1.1, h.2⟩
    exact congrArg (fun μ => ∫⁻ x, g x ∂μ) (Measure.restrict_congr_set hsets)
  obtain ⟨hm, he⟩ := coarea_regular_part hn hU hu g hg
  refine ⟨hm.congr hlevel.symm, ?_⟩
  exact hsource.trans (he.trans (lintegral_congr_ae hlevel.symm))

/-- Blueprint `thm:weighted-coarea`, for every nonnegative extended Borel weight. -/
theorem weighted_c1_coarea {n : ℕ} (hn : 2 ≤ n)
    {U : Set (EuclideanSpace ℝ (Fin n))} (hU : IsOpen U)
    {u : EuclideanSpace ℝ (Fin n) → ℝ} (hu : ContDiffOn ℝ 1 u U)
    {g : EuclideanSpace ℝ (Fin n) → ℝ≥0∞} (hg : Measurable g) :
    (∫⁻ x in U, g x * ENNReal.ofReal ‖gradient u x‖) =
      ∫⁻ t : ℝ, ∫⁻ x in U ∩ u ⁻¹' {t}, g x ∂Measure.euclideanHausdorffMeasure (n - 1) :=
  (hasWeightedCoareaOn_of_contDiffOn hn hU hu g hg).2

/-- The inner weighted level integral is Lebesgue measurable; the critical part
is an almost-everywhere zero modification of the regular-level integral. -/
lemma aemeasurable_c1_level_integral {n : ℕ} (hn : 2 ≤ n)
    {U : Set (EuclideanSpace ℝ (Fin n))} (hU : IsOpen U)
    {u : EuclideanSpace ℝ (Fin n) → ℝ} (hu : ContDiffOn ℝ 1 u U)
    {g : EuclideanSpace ℝ (Fin n) → ℝ≥0∞} (hg : Measurable g) :
    AEMeasurable (fun t : ℝ =>
      ∫⁻ x in U ∩ u ⁻¹' {t}, g x ∂Measure.euclideanHausdorffMeasure (n - 1)) volume :=
  (hasWeightedCoareaOn_of_contDiffOn hn hU hu g hg).1

/-- Only the weight restricted to the open domain must be Borel. Values outside
that domain are immaterial, so this is the exact `g : U → [0,∞]` formulation. -/
theorem weighted_c1_coarea_of_measurable_restriction {n : ℕ} (hn : 2 ≤ n)
    {U : Set (EuclideanSpace ℝ (Fin n))} (hU : IsOpen U)
    {u : EuclideanSpace ℝ (Fin n) → ℝ} (hu : ContDiffOn ℝ 1 u U)
    {g : EuclideanSpace ℝ (Fin n) → ℝ≥0∞} (hg : Measurable (U.domRestrict g)) :
    AEMeasurable (fun t : ℝ =>
      ∫⁻ x in U ∩ u ⁻¹' {t}, g x ∂Measure.euclideanHausdorffMeasure (n - 1)) volume ∧
    (∫⁻ x in U, g x * ENNReal.ofReal ‖gradient u x‖) =
      ∫⁻ t : ℝ, ∫⁻ x in U ∩ u ⁻¹' {t}, g x ∂Measure.euclideanHausdorffMeasure (n - 1) := by
  obtain ⟨g', hg', hcomp⟩ :=
    (MeasurableEmbedding.subtype_coe hU.measurableSet).exists_measurable_extend hg
      (fun _ => inferInstance)
  have heq (x) (hx : x ∈ U) : g x = g' x := (congr_fun hcomp ⟨x, hx⟩).symm
  have hsource : (∫⁻ x in U, g x * ENNReal.ofReal ‖gradient u x‖) =
      ∫⁻ x in U, g' x * ENNReal.ofReal ‖gradient u x‖ := by
    apply setLIntegral_congr_fun hU.measurableSet
    intro x hx
    dsimp only
    rw [heq x hx]
  have hlevel (t : ℝ) :
      (∫⁻ x in U ∩ u ⁻¹' {t}, g x ∂Measure.euclideanHausdorffMeasure (n - 1)) =
        ∫⁻ x in U ∩ u ⁻¹' {t}, g' x ∂Measure.euclideanHausdorffMeasure (n - 1) := by
    apply setLIntegral_congr_fun
      (measurableSet_coarea_level_of_continuousOn hU.measurableSet hu.continuousOn t)
    intro x hx
    exact heq x hx.1
  obtain ⟨hm, he⟩ := hasWeightedCoareaOn_of_contDiffOn hn hU hu g' hg'
  refine ⟨hm.congr (Eventually.of_forall fun t => (hlevel t).symm), ?_⟩
  exact hsource.trans (he.trans (lintegral_congr fun t => (hlevel t).symm))

end LiquidDrop

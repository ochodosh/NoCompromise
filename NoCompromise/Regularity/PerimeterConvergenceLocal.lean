module

public import NoCompromise.BV.AnnularGluing
public import NoCompromise.BV.Coarea
public import NoCompromise.Regularity.DensityCutComparison

@[expose] public section

/-!
# Local finite-perimeter realizations for convergence arguments

The limit set and competitors need finite perimeter only locally in the given
open domain. Compact localization and the proved BV coarea theorem produce
actual global finite-perimeter realizations where good-radius gluing is needed.
-/

noncomputable section
open MeasureTheory Set Filter Metric
open scoped ENNReal Topology symmDiff
namespace LiquidDrop
set_option maxSynthPendingDepth 8

/-- Uniformly local perimeter bounds and genuine local L¹ convergence give
local finite variation of the limiting indicator on the original open set. -/
theorem locallyBV_indicator_of_locally_l1_perimeter_bound {n : ℕ}
    {U F : Set (EuclideanSpace ℝ (Fin n))} {E : ℕ → Set (EuclideanSpace ℝ (Fin n))}
    (hmE : ∀ j, NullMeasurableSet (E j) volume)
    (hmF : NullMeasurableSet F volume)
    (hbound : ∀ A : Set (EuclideanSpace ℝ (Fin n)), IsOpen A → IsCompact (closure A) →
      closure A ⊆ U → ∃ C : ℝ≥0∞, C < ∞ ∧ ∀ j, perimeterIn (E j) A ≤ C)
    (hlim : ∀ K : Set (EuclideanSpace ℝ (Fin n)), IsCompact K → K ⊆ U →
      Tendsto (fun j => ∫ z in K,
        |(E j).indicator (fun _ => (1 : ℝ)) z - F.indicator (fun _ => (1 : ℝ)) z|)
        atTop (𝓝 0)) : IsLocallyBVOn (F.indicator (fun _ => (1 : ℝ))) U := by
  refine ⟨(locallyIntegrable_indicator_one hmF).locallyIntegrableOn U, ?_⟩
  intro A hA hcA hAU
  obtain ⟨C, hC, hb⟩ := hbound A hA hcA hAU
  have hlsc := perimeterIn_le_liminf_of_locally_l1 hA hmE hmF
    (fun K hK hKA => hlim K hK (hKA.trans (subset_closure.trans hAU)))
  exact (hlsc.trans ((liminf_le_liminf (Eventually.of_forall hb)).trans_eq
    (liminf_const _))).trans_lt hC

/-- Coarea of a compactly localized BV indicator supplies a genuine global
finite-perimeter set agreeing with the original set near a prescribed compact. -/
theorem IsLocallyBVOn.exists_finitePerimeter_eq_near_compact {n : ℕ}
    {U K F : Set (EuclideanSpace ℝ (Fin n))} (hU : IsOpen U)
    (hf : IsLocallyBVOn (F.indicator (fun _ => (1 : ℝ))) U)
    (hK : IsCompact K) (hKU : K ⊆ U) :
    ∃ G : Set (EuclideanSpace ℝ (Fin n)), NullMeasurableSet G volume ∧
      HasFinitePerimeter G ∧ HasLocallyFinitePerimeter G ∧ F =ᶠ[𝓝ˢ K] G := by
  obtain ⟨g, hg, hfg⟩ := hf.exists_globalBV_eq_near_compact hU hK hKU
  have hgl := isLocallyBVOn_of_variation_lt_top isOpen_univ hg.1.locallyIntegrableOn hg.2
  have ha := ae_perimeter_superlevel_lt_top isOpen_univ hgl hg.2
  obtain ⟨t, ht, hpt⟩ := Measure.exists_mem_of_measure_ne_zero_of_ae
    (show volume (Ioo (0 : ℝ) 1) ≠ 0 by simp) (ae_restrict_of_ae ha)
  let G := {z | t < g z}
  have hmg : AEStronglyMeasurable g volume := by
    simpa only [Measure.restrict_univ] using hg.1.aestronglyMeasurable
  have hmG : NullMeasurableSet G volume := nullMeasurableSet_lt aemeasurable_const hmg.aemeasurable
  refine ⟨G, hmG, hpt, ?_, ?_⟩
  · intro A _ _
    exact (variation_mono MeasurableSet.univ (subset_univ A)).trans_lt hpt
  · filter_upwards [hfg] with z hz
    change (z ∈ F) = (t < g z)
    rw [← hz]
    by_cases hzF : z ∈ F
    · simp only [indicator_of_mem hzF, ht.2, hzF]
    · simp only [indicator_of_notMem hzF, not_lt_of_ge (le_of_lt ht.1),
        hzF]

/-- Subadditivity of perimeter for genuinely disjoint measurable sets. -/
lemma perimeterIn_disjoint_union_le {n : ℕ}
    {E F U : Set (EuclideanSpace ℝ (Fin n))}
    (hmE : NullMeasurableSet E volume) (hmF : NullMeasurableSet F volume)
    (hEF : Disjoint E F) :
    perimeterIn (E ∪ F) U ≤ perimeterIn E U + perimeterIn F U := by
  unfold perimeterIn
  rw [indicator_union_of_disjoint hEF]
  exact variation_add_le
    ((locallyIntegrable_indicator_one hmE).locallyIntegrableOn U)
    ((locallyIntegrable_indicator_one hmF).locallyIntegrableOn U)

lemma hasLocallyFinitePerimeter_disjoint_union {n : ℕ}
    {E F : Set (EuclideanSpace ℝ (Fin n))}
    (hmE : NullMeasurableSet E volume) (hmF : NullMeasurableSet F volume)
    (hE : HasLocallyFinitePerimeter E) (hF : HasLocallyFinitePerimeter F)
    (hEF : Disjoint E F) : HasLocallyFinitePerimeter (E ∪ F) := by
  intro A hA hcA
  exact (perimeterIn_disjoint_union_le hmE hmF hEF).trans_lt
    (ENNReal.add_lt_top.mpr ⟨hE A hA hcA, hF A hA hcA⟩)

/-- The actual set obtained by good-radius gluing is an admissible global
locally finite-perimeter competitor. -/
theorem IsGoodRadius.hasLocallyFinitePerimeter_gluing {E F : Set AmbientSpace}
    {hE : HasLocallyFinitePerimeter E} {hmE : NullMeasurableSet E volume}
    {hF : HasLocallyFinitePerimeter F} {hmF : NullMeasurableSet F volume}
    {x : AmbientSpace} {r : ℝ} (hgE : IsGoodRadius E hE hmE x r)
    (hgF : IsGoodRadius F hF hmF x r) :
    HasLocallyFinitePerimeter ((F ∩ ball x r) ∪ (E \ ball x r)) := by
  have hFi : HasLocallyFinitePerimeter (F ∩ ball x r) := by
    intro A _ _
    exact (variation_mono MeasurableSet.univ (subset_univ A)).trans_lt
      hgF.hasFinitePerimeter_cut_in
  exact hasLocallyFinitePerimeter_disjoint_union
    (hmF.inter measurableSet_ball.nullMeasurableSet)
    (hmE.diff measurableSet_ball.nullMeasurableSet) hFi hgE.hasLocallyFinitePerimeter_cut_out
    (Set.disjoint_left.mpr fun _ hz hw => hw.2 hz.2)

end LiquidDrop

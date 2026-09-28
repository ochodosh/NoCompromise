import NoCompromise.BV.CoareaApproximation
import NoCompromise.BV.CoareaBound
import NoCompromise.BV.CoareaMeasurability
import NoCompromise.BV.CoareaSmooth
import NoCompromise.BV.Compactness

/-!
# Coarea for locally BV functions

Strict approximation, level-set convergence, and smooth-transition majorants
prove the upper bound; signed layer cake proves the reverse bound. Perimeter
is Borel measurable in the level. No smooth Hausdorff coarea or Sard theorem
is assumed, and both sides may be infinite.
-/

noncomputable section
open MeasureTheory Filter Set
open scoped ENNReal Topology
namespace LiquidDrop
set_option maxSynthPendingDepth 8

/-- The upper BV coarea inequality, with infinite total variation allowed. -/
theorem lintegral_perimeter_superlevel_le_variation {n : ℕ}
    {U : Set (EuclideanSpace ℝ (Fin n))} (hU : IsOpen U)
    {f : EuclideanSpace ℝ (Fin n) → ℝ} (hf : IsLocallyBVOn f U) :
    (∫⁻ t : ℝ, perimeterIn {x | t < f x} U) ≤ variation f U := by
  by_cases hfin : variation f U < ∞
  · obtain ⟨g, hg, _, _, hlevels, hgrad⟩ :=
      strict_approximation_with_superlevel_convergence hU hf
    obtain ⟨hi, he⟩ := hgrad hfin
    choose q hq hbound henergy using fun j =>
      exists_measurable_superlevel_perimeter_majorant_of_integrable_gradient hU
        ((hg j).of_le (by simp)) (hi j)
    apply lintegral_perimeter_superlevel_le_of_majorants hU
      (fun j => (hg j).continuousOn.locallyIntegrableOn hU.measurableSet) hf.1
      hlevels hq hbound henergy
    have ht := ENNReal.continuous_ofReal.continuousAt.tendsto.comp he
    simpa only [Function.comp_def, ENNReal.ofReal_toReal hfin.ne] using ht
  · have htop : variation f U = ∞ := top_unique (not_lt.mp hfin)
    simp only [htop, le_top]

/-- Blueprint `thm:bv-coarea`: total variation is the integral of strict-superlevel perimeters. -/
theorem bv_coarea {n : ℕ} {U : Set (EuclideanSpace ℝ (Fin n))} (hU : IsOpen U)
    {f : EuclideanSpace ℝ (Fin n) → ℝ} (hf : IsLocallyBVOn f U) :
    variation f U = ∫⁻ t : ℝ, perimeterIn {x | t < f x} U :=
  le_antisymm (variation_le_lintegral_perimeter_superlevel hU hf.1)
    (lintegral_perimeter_superlevel_le_variation hU hf)

/-- The smooth BV coarea identity directly identifies the full gradient mass. -/
theorem lintegral_perimeter_superlevel_eq_lintegral_norm_gradient {n : ℕ}
    {U : Set (EuclideanSpace ℝ (Fin n))} (hU : IsOpen U)
    {f : EuclideanSpace ℝ (Fin n) → ℝ} (hf : ContDiffOn ℝ 1 f U) :
    (∫⁻ t : ℝ, perimeterIn {x | t < f x} U) =
      ∫⁻ x in U, ENNReal.ofReal ‖gradient f x‖ := by
  obtain ⟨q, _, hbound, henergy⟩ :=
    exists_measurable_superlevel_perimeter_majorant_of_contDiffOn hU hf
  apply le_antisymm ((lintegral_mono hbound).trans henergy)
  rw [← variation_eq_lintegral_norm_gradient_of_contDiffOn hU hf]
  exact variation_le_lintegral_perimeter_superlevel hU
    (hf.continuousOn.locallyIntegrableOn hU.measurableSet)

/-- Finite total variation implies finite superlevel perimeter for almost every level. -/
theorem ae_perimeter_superlevel_lt_top {n : ℕ}
    {U : Set (EuclideanSpace ℝ (Fin n))} (hU : IsOpen U)
    {f : EuclideanSpace ℝ (Fin n) → ℝ} (hf : IsLocallyBVOn f U)
    (hfin : variation f U < ∞) : ∀ᵐ t : ℝ ∂volume, perimeterIn {x | t < f x} U < ∞ := by
  apply ae_lt_top (measurable_perimeter_superlevel hf.1)
  rw [← bv_coarea hU hf]
  exact hfin.ne

/-- For almost every level the superlevel indicator is locally BV on the original domain. -/
theorem ae_isLocallyBVOn_superlevelIndicator {n : ℕ}
    {U : Set (EuclideanSpace ℝ (Fin n))} (hU : IsOpen U)
    {f : EuclideanSpace ℝ (Fin n) → ℝ} (hf : IsLocallyBVOn f U) :
    ∀ᵐ t : ℝ ∂volume, IsLocallyBVOn (superlevelIndicator f t) U := by
  obtain ⟨Q, hmono, hQ, hcQ, hnext, hcover⟩ := exists_open_relatively_compact_exhaustion hU
  have hsub (j : ℕ) : Q j ⊆ U := by
    rw [← hcover]
    exact subset_iUnion Q j
  have hcl (j : ℕ) : closure (Q j) ⊆ U := (hnext j).trans (hsub (j + 1))
  have hfv (j : ℕ) : IsLocallyBVOn f (Q j) :=
    ⟨hf.1.mono_set (hsub j), fun A hA hcA hAQ => hf.2 A hA hcA (hAQ.trans (hsub j))⟩
  have ha (j : ℕ) : ∀ᵐ t : ℝ ∂volume, perimeterIn {x | t < f x} (Q j) < ∞ :=
    ae_perimeter_superlevel_lt_top (hQ j) (hfv j) (hf.2 _ (hQ j) (hcQ j) (hcl j))
  filter_upwards [ae_all_iff.mpr ha] with t ht
  refine ⟨locallyIntegrableOn_superlevelIndicator hU hf.1 t, ?_⟩
  intro A hA hcA hAU
  obtain ⟨j, hj⟩ := compact_subset_exhaustion hmono hQ hcover hcA hAU
  exact (variation_mono (hQ j).measurableSet (subset_closure.trans hj)).trans_lt (ht j)

end LiquidDrop

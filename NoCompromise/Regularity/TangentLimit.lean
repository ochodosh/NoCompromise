import NoCompromise.Regularity.TangentScaling
import NoCompromise.Regularity.TangentCompactness
import NoCompromise.Regularity.PerimeterConvergence

/-!
# Minimizing limits of quasiminimal blow-ups

The actual rescaled sets have error ωr tending to zero and admissible scales
1/r tending to infinity. The already proved perimeter-convergence theorem
therefore yields local perimeter minimality and convergence of genuine local
perimeter measures, in addition to the locally L¹ indicator convergence.
-/

noncomputable section
open MeasureTheory Set Filter Metric
open scoped Topology ENNReal CompactlySupported symmDiff
namespace LiquidDrop
set_option maxSynthPendingDepth 8

lemma IsLocallyOmegaMinimalOn.isLocallyPerimeterMinimizing {F : Set AmbientSpace}
    (hF : IsLocallyOmegaMinimalOn F 0 univ) : IsLocallyPerimeterMinimizing F := by
  rw [isLocallyPerimeterMinimizing_iff]
  refine ⟨le_rfl, by simp, hF.nullMeasurable, ?_, ?_⟩
  · intro A hA hcA
    exact hF.locallyBV.2 A hA hcA (subset_univ _)
  · intro x R hR _ G hmG hpG _ hs
    have h := hF.comparison x R hR (subset_univ _) G hmG
      (hpG.isLocallyBVOn_indicator hmG univ) (by rwa [symmDiff_comm])
    simpa only [ENNReal.ofReal_zero, zero_mul, add_zero] using h

lemma eventually_blowup_scale_admissible {r : ℕ → ℝ}
    (hr : ∀ j, 0 < r j) (ht : Tendsto r atTop (𝓝 0)) (R : ℝ) :
    ∀ᶠ j in atTop, ENNReal.ofReal R ≤ ENNReal.ofReal (r j)⁻¹ := by
  have ht' : Tendsto r atTop (𝓝[>] (0 : ℝ)) :=
    tendsto_nhdsWithin_iff.mpr ⟨ht, Eventually.of_forall hr⟩
  have hi := tendsto_inv_nhdsGT_zero.comp ht'
  filter_upwards [hi.eventually (eventually_ge_atTop R)] with j hj
  exact ENNReal.ofReal_le_ofReal hj

/-- The compactness and minimality portion of tangent-cone existence, retaining
all compact-test measure convergence and every precompact continuity set. -/
theorem IsOmegaMinimal.exists_minimizing_blowup_limit
    {E : Set AmbientSpace} {ω : ℝ} (hE : IsOmegaMinimal E ω) (x : AmbientSpace)
    {r : ℕ → ℝ} (hr : ∀ j, 0 < r j) (ht : Tendsto r atTop (𝓝 0)) :
    ∃ F : Set AmbientSpace, MeasurableSet F ∧
      ∃ hF : IsLocallyOmegaMinimalOn F 0 univ, IsLocallyPerimeterMinimizing F ∧
      ∃ σ : ℕ → ℕ, StrictMono σ ∧
      (∀ K : Set AmbientSpace, IsCompact K →
        Tendsto (fun j => ∫ y in K,
          |(LiquidDrop.blowupSet E x (r (σ j))).indicator (fun _ => (1 : ℝ)) y -
            F.indicator (fun _ => (1 : ℝ)) y|) atTop (𝓝 0)) ∧
      (∀ φ : C_c((univ : Set AmbientSpace), ℝ),
        Tendsto (fun j => ∫ z : (univ : Set AmbientSpace), φ z ∂localPerimeterMeasure
          isOpen_univ ((hE.blowupSet x (hr (σ j))).locallyFinite.isLocallyBVOn_indicator
            (hE.blowupSet x (hr (σ j))).nullMeasurable univ))
          atTop (𝓝 (∫ z : (univ : Set AmbientSpace),
            φ z ∂localPerimeterMeasure isOpen_univ hF.locallyBV))) ∧
      ∀ A : Set AmbientSpace, IsOpen A → IsCompact (closure A) →
        localPerimeterMeasure isOpen_univ hF.locallyBV (Subtype.val ⁻¹' frontier A) = 0 →
        Tendsto (fun j => perimeterIn (LiquidDrop.blowupSet E x (r (σ j))) A)
          atTop (𝓝 (perimeterIn F A)) := by
  obtain ⟨F, hmF, _, σ, hσ, hlim⟩ := hE.exists_blowup_subsequence x hr ht
  have hts : Tendsto (fun j => r (σ j)) atTop (𝓝 0) := ht.comp hσ.tendsto_atTop
  have hω : Tendsto (fun j => ω * r (σ j)) atTop (𝓝 0) := by
    simpa only [mul_zero] using hts.const_mul ω
  have hbounds (A : Set AmbientSpace) (hA : IsOpen A) (hcA : IsCompact (closure A))
      (_ : closure A ⊆ univ) : ∃ C : ℝ≥0∞, C < ∞ ∧
      ∀ j, perimeterIn (LiquidDrop.blowupSet E x (r (σ j))) A ≤ C :=
    hE.bounded_perimeterIn_blowupSet_ennreal x (fun j => hr (σ j)) hts hA hcA
  obtain ⟨hF, hweak, hper⟩ := perimeter_measure_convergence isOpen_univ
    (fun j => hE.blowupSet x (hr (σ j))) hmF.nullMeasurableSet hω hbounds
    (fun _ R _ _ => eventually_blowup_scale_admissible (fun j => hr (σ j)) hts R)
    (fun K hK _ => hlim K hK)
  exact ⟨F, hmF, hF, hF.isLocallyPerimeterMinimizing, σ, hσ, hlim, hweak,
    fun A hA hcA hn => hper A hA hcA (subset_univ _) hn⟩

end LiquidDrop

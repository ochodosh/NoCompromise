module

public import NoCompromise.Regularity.PerimeterConvergenceWeak
public import NoCompromise.Regularity.PerimeterConvergenceContinuity
public import NoCompromise.Regularity.PerimeterConvergenceMinimality

@[expose] public section

/-!
# Perimeter-measure convergence at varying admissible scales

Both conclusions of blueprint `lem:perimeter-measure-convergence` hold on an
arbitrary open domain. Local BV of the limit is derived from the original
uniform perimeter bounds. The positive measures are the actual distributional
variation measures, and the boundary-null condition concerns that measure.
-/

noncomputable section
open MeasureTheory Set Filter Metric
open scoped ENNReal Topology CompactlySupported
namespace LiquidDrop
set_option maxSynthPendingDepth 8

/-- Weak convergence of genuine perimeter measures, together with local L¹
convergence, gives perimeter convergence on every precompact open continuity set. -/
theorem tendsto_perimeterIn_of_weak_localPerimeterMeasure {n : ℕ}
    {U F : Set (EuclideanSpace ℝ (Fin n))} (hU : IsOpen U)
    {E : ℕ → Set (EuclideanSpace ℝ (Fin n))}
    (hmE : ∀ j, NullMeasurableSet (E j) volume) (hmF : NullMeasurableSet F volume)
    (hf : ∀ j, IsLocallyBVOn ((E j).indicator (fun _ => (1 : ℝ))) U)
    (hF : IsLocallyBVOn (F.indicator (fun _ => (1 : ℝ))) U)
    (hlim : ∀ K : Set (EuclideanSpace ℝ (Fin n)), IsCompact K → K ⊆ U →
      Tendsto (fun j => ∫ z in K,
        |(E j).indicator (fun _ => (1 : ℝ)) z - F.indicator (fun _ => (1 : ℝ)) z|)
        atTop (𝓝 0))
    (hweak : ∀ φ : C_c(U, ℝ),
      Tendsto (fun j => ∫ z : U, φ z ∂localPerimeterMeasure hU (hf j))
        atTop (𝓝 (∫ z : U, φ z ∂localPerimeterMeasure hU hF)))
    {A : Set (EuclideanSpace ℝ (Fin n))} (hA : IsOpen A) (hcA : IsCompact (closure A))
    (hAU : closure A ⊆ U)
    (hnull : localPerimeterMeasure hU hF (Subtype.val ⁻¹' frontier A) = 0) :
    Tendsto (fun j => perimeterIn (E j) A) atTop (𝓝 (perimeterIn F A)) := by
  let : ∀ j, IsFiniteMeasureOnCompacts (localPerimeterMeasure hU (hf j)) :=
    fun j => (localPerimeterMeasure_data hU (hf j)).2.1
  let : IsFiniteMeasureOnCompacts (localPerimeterMeasure hU hF) :=
    (localPerimeterMeasure_data hU hF).2.1
  have hu := limsup_local_set_le_of_compact_test_convergence hU
    (fun j => localPerimeterMeasure hU (hf j)) (localPerimeterMeasure hU hF)
    hweak hcA hAU hnull
  simp only [localPerimeterMeasure_open hU _ hA (subset_closure.trans hAU)] at hu
  apply tendsto_of_le_liminf_of_limsup_le _ hu
  exact perimeterIn_le_liminf_of_locally_l1 hA hmE hmF
    (fun K hK hKA => hlim K hK (hKA.trans (subset_closure.trans hAU)))

/-- Full blueprint `lem:perimeter-measure-convergence`: actual local limit
quasiminimality, positive weak perimeter-measure convergence, and convergence
of perimeters on every precompact open set with null limiting boundary. -/
theorem perimeter_measure_convergence
    {U F : Set AmbientSpace} (hU : IsOpen U)
    {E : ℕ → Set AmbientSpace} {ω : ℕ → ℝ} {s : ℕ → ℝ≥0∞}
    (hE : ∀ j, IsOmegaMinimalAtScales (E j) (ω j) (s j))
    (hmF : NullMeasurableSet F volume) {ω₀ : ℝ} (hω : Tendsto ω atTop (𝓝 ω₀))
    (hbound : ∀ A : Set AmbientSpace, IsOpen A → IsCompact (closure A) →
      closure A ⊆ U → ∃ C : ℝ≥0∞, C < ∞ ∧ ∀ j, perimeterIn (E j) A ≤ C)
    (hscale : ∀ (x : AmbientSpace) (R : ℝ), 0 < R → closedBall x R ⊆ U →
      ∀ᶠ j in atTop, ENNReal.ofReal R ≤ s j)
    (hlim : ∀ K : Set AmbientSpace, IsCompact K → K ⊆ U →
      Tendsto (fun j => ∫ z in K,
        |(E j).indicator (fun _ => (1 : ℝ)) z - F.indicator (fun _ => (1 : ℝ)) z|)
        atTop (𝓝 0)) :
    ∃ hF : IsLocallyOmegaMinimalOn F ω₀ U,
      (∀ φ : C_c(U, ℝ),
        Tendsto (fun j => ∫ z : U, φ z ∂localPerimeterMeasure hU
          ((hE j).locallyFinite.isLocallyBVOn_indicator (hE j).nullMeasurable U))
          atTop (𝓝 (∫ z : U, φ z ∂localPerimeterMeasure hU hF.locallyBV))) ∧
      ∀ A : Set AmbientSpace, IsOpen A → IsCompact (closure A) → closure A ⊆ U →
        localPerimeterMeasure hU hF.locallyBV (Subtype.val ⁻¹' frontier A) = 0 →
        Tendsto (fun j => perimeterIn (E j) A) atTop (𝓝 (perimeterIn F A)) := by
  let hf (j : ℕ) :=
    (hE j).locallyFinite.isLocallyBVOn_indicator (hE j).nullMeasurable U
  have hF := locally_omegaMinimal_of_locally_l1 hU hE hmF hω hbound hscale hlim
  have hw := tendsto_localPerimeterMeasure_of_locally_l1 hU hE hf hmF hF.locallyBV
    hω hbound hscale hlim
  refine ⟨hF, hw, ?_⟩
  intro A hA hcA hAU hnull
  exact tendsto_perimeterIn_of_weak_localPerimeterMeasure hU
    (fun j => (hE j).nullMeasurable) hmF hf hF.locallyBV hlim hw hA hcA hAU hnull

end LiquidDrop

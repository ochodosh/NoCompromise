module

public import NoCompromise.Regularity.PerimeterConvergenceIdentification

@[expose] public section

/-! # Full local weak convergence of the actual positive perimeter measures -/

noncomputable section
open MeasureTheory Set Filter Metric
open scoped ENNReal Topology CompactlySupported
namespace LiquidDrop
set_option maxSynthPendingDepth 8

/-- Every subsequence has a further positive weak limit, and genuine annular
gluing identifies all of those limits with the local perimeter of the L¹ limit. -/
theorem tendsto_localPerimeterMeasure_of_locally_l1
    {U F : Set AmbientSpace} (hU : IsOpen U)
    {E : ℕ → Set AmbientSpace} {ω : ℕ → ℝ} {s : ℕ → ℝ≥0∞}
    (hE : ∀ j, IsOmegaMinimalAtScales (E j) (ω j) (s j))
    (hf : ∀ j, IsLocallyBVOn ((E j).indicator (fun _ => (1 : ℝ))) U)
    (hmF : NullMeasurableSet F volume)
    (hF : IsLocallyBVOn (F.indicator (fun _ => (1 : ℝ))) U)
    {ω₀ : ℝ} (hω : Tendsto ω atTop (𝓝 ω₀))
    (hbound : ∀ A : Set AmbientSpace, IsOpen A → IsCompact (closure A) →
      closure A ⊆ U → ∃ C : ℝ≥0∞, C < ∞ ∧ ∀ j, perimeterIn (E j) A ≤ C)
    (hscale : ∀ (x : AmbientSpace) (R : ℝ), 0 < R → closedBall x R ⊆ U →
      ∀ᶠ j in atTop, ENNReal.ofReal R ≤ s j)
    (hlim : ∀ K : Set AmbientSpace, IsCompact K → K ⊆ U →
      Tendsto (fun j => ∫ z in K,
        |(E j).indicator (fun _ => (1 : ℝ)) z - F.indicator (fun _ => (1 : ℝ)) z|)
        atTop (𝓝 0)) (φ : C_c(U, ℝ)) :
    Tendsto (fun j => ∫ z : U, φ z ∂localPerimeterMeasure hU (hf j))
      atTop (𝓝 (∫ z : U, φ z ∂localPerimeterMeasure hU hF)) := by
  apply Filter.tendsto_of_subseq_tendsto
  intro ns hns
  have hb : ∀ A : Set AmbientSpace, IsOpen A → IsCompact (closure A) →
      closure A ⊆ U → ∃ C : ℝ≥0∞, C < ∞ ∧ ∀ j, perimeterIn (E (ns j)) A ≤ C := by
    intro A hA hcA hAU
    obtain ⟨C, hC, hb⟩ := hbound A hA hcA hAU
    exact ⟨C, hC, fun j => hb (ns j)⟩
  obtain ⟨τ, σ, hσ, hτ, _, hweak⟩ :=
    exists_subseq_local_perimeter_measure hU (fun j => hf (ns j)) hb
  let : τ.Regular := hτ
  have ht : Tendsto (fun j => ns (σ j)) atTop atTop := hns.comp hσ.tendsto_atTop
  have heq := localPerimeterMeasure_eq_of_weak_limit hU
    (fun j => hE (ns (σ j))) (fun j => hf (ns (σ j))) hmF hF (hω.comp ht)
    (fun x R hR hRU => ht.eventually (hscale x R hR hRU))
    (fun K hK hKU => (hlim K hK hKU).comp ht) τ hweak
  refine ⟨σ, ?_⟩
  simpa only [← heq] using hweak φ

end LiquidDrop

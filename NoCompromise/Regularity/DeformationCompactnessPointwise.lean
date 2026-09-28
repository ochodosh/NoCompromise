import NoCompromise.Regularity.DeformationCompactness
import NoCompromise.Regularity.DeformationCompactnessAE

/-! # Simultaneous local L¹ and almost-everywhere compression compactness -/

noncomputable section
open MeasureTheory Set Filter Metric
open scoped ENNReal Topology
namespace LiquidDrop
set_option maxSynthPendingDepth 8

/-- Actual compressed competitors have one subsequence converging both locally
in L¹ and almost everywhere to a measurable locally finite-perimeter set. -/
theorem IsSlabCapConfiguration.exists_compressionCompetitor_subsequence_ae
    {E : Set AmbientSpace} {hE : HasLocallyFinitePerimeter E}
    {hmE : NullMeasurableSet E volume} {r c η : ℝ}
    (h : IsSlabCapConfiguration E hE hmE r c η)
    {σ τ : ℝ} (hσ : 0 < σ) (hst : σ < τ) (hτr : τ ≤ r)
    {ε : ℕ → ℝ} (hε : ∀ j, 0 < ε j) (hε1 : ∀ j, ε j ≤ 1) :
    ∃ F : Set AmbientSpace, MeasurableSet F ∧ HasLocallyFinitePerimeter F ∧
      ∃ k : ℕ → ℕ, StrictMono k ∧
        (∀ K : Set AmbientSpace, IsCompact K →
          Tendsto (fun j => ∫ x in K,
            |(compressionCompetitor E r σ τ (ε (k j)) c).indicator (fun _ => (1 : ℝ)) x -
              F.indicator (fun _ => (1 : ℝ)) x|) atTop (𝓝 0)) ∧
        ∀ᵐ x ∂volume,
          Tendsto (fun j =>
            (compressionCompetitor E r σ τ (ε (k j)) c).indicator (fun _ => (1 : ℝ)) x)
              atTop (𝓝 (F.indicator (fun _ => (1 : ℝ)) x)) := by
  obtain ⟨F, hmF, hF, k, hk, ht⟩ :=
    h.exists_compressionCompetitor_subsequence hσ hst hτr hε hε1
  have hm (j : ℕ) := (compressionCompetitor_locallyFinitePerimeter hE hmE h.1.1.le
    hσ hst (hε (k j)) (hε1 (k j)) c).2
  obtain ⟨l, hl, hae⟩ := exists_subseq_ae_of_locally_l1_fixed_exterior
    hm hmF.nullMeasurableSet hmE (isCompact_closedBall 0 (2 * r + 1))
    (fun j x hx => compressionCompetitor_indicator_eq_outside_fixed_ball E h.1.1 hst hτr
      (ε (k j)) c hx) ht
  refine ⟨F, hmF, hF, k ∘ l, hk.comp hl, ?_, hae⟩
  intro K hK
  exact (ht K hK).comp hl.tendsto_atTop

end LiquidDrop

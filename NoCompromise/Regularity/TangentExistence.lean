module

public import NoCompromise.Regularity.TangentLimit
public import NoCompromise.Regularity.TangentDensity
public import NoCompromise.Regularity.TangentBoundary

@[expose] public section

/-!
# Existence of nontrivial locally minimizing tangent limits

This is blueprint `lem:tangent-cone-minimizing`. The positive density θ is chosen
before the sequence of scales. Every positive sequence tending to zero has a
subsequence with an actual measurable, locally perimeter-minimizing limit. The
origin is on the boundary of its density-one representative. The conclusion
retains the locally L¹ and genuine perimeter-measure convergence, and the exact
constant density ratio at every positive radius. Monotonicity of the original
sequence of scales is unnecessary.
-/

noncomputable section
open MeasureTheory Set Filter Metric
open scoped Topology ENNReal CompactlySupported
namespace LiquidDrop
set_option maxSynthPendingDepth 8

/-- Full tangent-limit existence, with density chosen before the scale sequence. -/
theorem IsOmegaMinimal.exists_tangent_limit
    {E : Set AmbientSpace} {ω : ℝ} (hE : IsOmegaMinimal E ω)
    {x : AmbientSpace} (hx : x ∈ frontier (densityOne E)) :
    ∃ θ : ℝ, 0 < θ ∧
      Tendsto (fun s : ℝ => (perimeterIn E (ball x s)).toReal / s ^ 2)
        (𝓝[>] (0 : ℝ)) (𝓝 θ) ∧
      ∀ (r : ℕ → ℝ) (hr : ∀ j, 0 < r j), Tendsto r atTop (𝓝 0) →
      ∃ F : Set AmbientSpace, MeasurableSet F ∧
      ∃ hF : IsLocallyOmegaMinimalOn F 0 univ, IsLocallyPerimeterMinimizing F ∧
        (0 : AmbientSpace) ∈ frontier (densityOne F) ∧
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
      (∀ R : ℝ, 0 < R → (perimeterIn F (ball 0 R)).toReal / R ^ 2 = θ) ∧
      ∀ A : Set AmbientSpace, IsOpen A → IsCompact (closure A) →
        localPerimeterMeasure isOpen_univ hF.locallyBV (Subtype.val ⁻¹' frontier A) = 0 →
        Tendsto (fun j => perimeterIn (LiquidDrop.blowupSet E x (r (σ j))) A)
          atTop (𝓝 (perimeterIn F A)) := by
  obtain ⟨θ, hθ, hθlim⟩ := hE.exists_pos_perimeter_density (by rwa [hE.frontier_densityOne] at hx)
  refine ⟨θ, hθ, hθlim, ?_⟩
  intro r hr ht
  obtain ⟨F, hmF, hF, hmin, σ, hσ, hl1, hweak, hper⟩ :=
    hE.exists_minimizing_blowup_limit x hr ht
  have hd := tangent_density_of_perimeter_convergence hE.locallyFinite hE.nullMeasurable
    x hF.locallyBV hθlim (fun j => hr (σ j)) (ht.comp hσ.tendsto_atTop)
    (fun R _ hn => hper (ball 0 R) isOpen_ball isBounded_ball.isCompact_closure hn)
  refine ⟨F, hmF, hF, hmin, hmin.zero_mem_frontier_of_density hθ hd, σ, hσ,
    hl1, hweak, ?_, hper⟩
  intro R hR
  rw [hd R hR]
  exact mul_div_cancel_right₀ θ (sq_pos_of_pos hR).ne'

end LiquidDrop

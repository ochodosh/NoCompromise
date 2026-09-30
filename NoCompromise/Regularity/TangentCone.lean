module

public import NoCompromise.Regularity.TangentDilation
public import NoCompromise.Regularity.TangentRepresentative
public import NoCompromise.Regularity.TangentExistence

@[expose] public section

/-!
# Tangent limits are cones

This is blueprint `prop:tangent-is-cone`. The actual local perimeter minimum and
the constant density ratios, supplied by `exists_tangent_limit`, imply invariance
under every exponential dilation modulo null sets. The density-one representative
is invariant as an actual set under every positive dilation.
-/

noncomputable section
open MeasureTheory Set Filter Metric
open scoped Topology ENNReal
namespace LiquidDrop

/-- Local minimality plus the already established constant density ratios force
both the AE cone property and exact cone invariance of the canonical representative. -/
theorem IsLocallyPerimeterMinimizing.tangent_is_cone {F : Set AmbientSpace}
    (hF : IsLocallyPerimeterMinimizing F) {θ : ℝ}
    (hd : ∀ R : ℝ, 0 < R → (perimeterIn F (ball 0 R)).toReal / R ^ 2 = θ) :
    (∀ t : ℝ, ((fun y => Real.exp t • y) '' F : Set AmbientSpace) =ᵐ[volume] F) ∧
      ∀ r : ℝ, 0 < r → (fun y => r • y) '' densityOne F = densityOne F := by
  have hae (t : ℝ) := tangent_dilation_ae_eq_of_radial_pairing hF.isOmegaMinimal.nullMeasurable
    (fun _ hφ hcφ => hF.radial_pairing_eq_zero hd hφ hcφ) t
  refine ⟨hae, ?_⟩
  intro r hr
  apply tangent_densityOne_invariant_of_ae hr
  simpa only [Real.exp_log hr] using hae (Real.log r)

end LiquidDrop

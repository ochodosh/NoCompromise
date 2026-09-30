module

public import NoCompromise.BV.Basic
public import NoCompromise.Measure.BallDifferentiation

@[expose] public section

/-!
# Ambient perimeter polar fields and differentiation

The existing distributional polar representation on the whole-space subtype is
transported to a regular measure on three-dimensional Euclidean space. Its
measurable outward unit field has both norm and vector differentiation limits
over open balls. Total perimeter need not be finite.

The derivative density is the negative of the outward field, so the divergence
pairing has positive sign. No reduced-boundary definition or structure theorem
is used here.
-/

noncomputable section

open MeasureTheory Filter Set Metric
open scoped ENNReal Topology

namespace LiquidDrop

/-- An ambient-space outward perimeter polar field. Its negative is the density
of the distributional derivative, while the divergence pairing has positive sign. -/
structure IsAmbientOutwardPerimeterPolar (E : Set AmbientSpace) (μ : Measure AmbientSpace)
    (ν : AmbientSpace → AmbientSpace) : Prop where
  regular : μ.Regular
  finiteOnCompacts : IsFiniteMeasureOnCompacts μ
  measurable : Measurable ν
  norm_ae : ∀ᵐ x ∂μ, ‖ν x‖ = 1
  open_eq : ∀ O, IsOpen O → μ O = perimeterIn E O
  coordinate_eq : ∀ (i : Fin 3) (φ : CompactlySupportedContinuousMap AmbientSpace ℝ),
    ContDiff ℝ 1 φ →
    -(∫ x, E.indicator (fun _ => (1 : ℝ)) x *
      fderiv ℝ φ x (EuclideanSpace.single i 1)) =
        ∫ x, φ x * (-ν x i) ∂μ
  divergence_eq : ∀ (X : AmbientSpace → AmbientSpace), ContDiff ℝ 1 X → HasCompactSupport X →
    (∫ x in E, divergenceN X x) = ∫ x, inner ℝ (X x) (ν x) ∂μ

/-- The subtype-valued polar representation on the whole open space transports
to a regular ambient measure and an ambient measurable outward field. -/
theorem exists_ambient_outward_perimeter_polar {E : Set AmbientSpace}
    (hE : HasLocallyFinitePerimeter E) (hmE : NullMeasurableSet E volume) :
    ∃ μ : Measure AmbientSpace, ∃ ν : AmbientSpace → AmbientSpace,
      IsAmbientOutwardPerimeterPolar E μ ν := by
  obtain ⟨ρ, νs, hρ, hνs, hnorm, hpolar, hper, _, hdiv⟩ :=
    exists_outward_perimeter_polar (U := univ) isOpen_univ hE hmE
  let e : (univ : Set AmbientSpace) ≃ₜ AmbientSpace := Homeomorph.Set.univ AmbientSpace
  let μ : Measure AmbientSpace := Measure.map e ρ
  let ν : AmbientSpace → AmbientSpace := fun x => νs (e.symm x)
  let : ρ.Regular := hρ
  let : μ.Regular := Measure.Regular.map e
  refine ⟨μ, ν, ⟨inferInstance, inferInstance, hνs.comp e.symm.continuous.measurable, ?_, ?_,
    ?_, ?_⟩⟩
  · change ∀ᵐ x ∂Measure.map e ρ, ‖ν x‖ = 1
    rw [e.measurableEmbedding.ae_map_iff]
    simpa only [ν, e.symm_apply_apply] using hnorm
  · intro O hO
    rw [show μ = Measure.map e ρ from rfl,
      Measure.map_apply e.continuous.measurable hO.measurableSet]
    exact (hper O hO (subset_univ O)).symm
  · intro i φ hφ
    rw [show μ = Measure.map e ρ from rfl, e.measurableEmbedding.integral_map]
    simp only [ν, e.symm_apply_apply]
    simpa only [Pi.neg_apply, PiLp.neg_apply, Measure.restrict_univ, e,
      Homeomorph.Set.univ_apply] using
      hpolar.test_eq i φ hφ (subset_univ _)
  · intro X hX hcX
    rw [show μ = Measure.map e ρ from rfl, e.measurableEmbedding.integral_map]
    have h := hdiv X hX hcX (subset_univ _)
    have hi : (fun x => E.indicator (fun _ => (1 : ℝ)) x * divergenceN X x) =
        E.indicator (divergenceN X) := by
      funext x
      by_cases hx : x ∈ E <;> simp [hx]
    simp only [ν, e.symm_apply_apply]
    simpa only [Measure.restrict_univ, hi, integral_indicator₀ hmE, e,
      Homeomorph.Set.univ_apply] using h

namespace IsAmbientOutwardPerimeterPolar

variable {E : Set AmbientSpace} {μ : Measure AmbientSpace} {ν : AmbientSpace → AmbientSpace}

/-- The unit polar field is locally integrable even when total perimeter is infinite. -/
theorem locallyIntegrable (h : IsAmbientOutwardPerimeterPolar E μ ν) : LocallyIntegrable ν μ := by
  let := h.finiteOnCompacts
  exact locallyIntegrable_of_ae_norm_le μ h.measurable.aestronglyMeasurable
    (h.norm_ae.mono fun _ hx => hx.le)

/-- The actual outward perimeter polar field has the norm Lebesgue-point property
and convergent vector averages over open balls almost everywhere. -/
theorem ae_differentiation (h : IsAmbientOutwardPerimeterPolar E μ ν) :
    ∀ᵐ x ∂μ,
      Tendsto (fun r => ⨍ y in ball x r, ‖ν y - ν x‖ ∂μ) (𝓝[>] 0) (𝓝 0) ∧
      Tendsto (fun r => ⨍ y in ball x r, ν y ∂μ) (𝓝[>] 0) (𝓝 (ν x)) := by
  let := h.finiteOnCompacts
  exact (ae_tendsto_average_norm_sub_ball μ h.locallyIntegrable).and
    (ae_tendsto_average_ball μ h.locallyIntegrable)

end IsAmbientOutwardPerimeterPolar

/-- Ambient outward polar decomposition together with its open-ball differentiation
limits, for a measurable set with globally locally finite perimeter. -/
theorem exists_ambient_outward_perimeter_polar_differentiation {E : Set AmbientSpace}
    (hE : HasLocallyFinitePerimeter E) (hmE : NullMeasurableSet E volume) :
    ∃ μ : Measure AmbientSpace, ∃ ν : AmbientSpace → AmbientSpace,
      IsAmbientOutwardPerimeterPolar E μ ν ∧
      (∀ᵐ x ∂μ,
        Tendsto (fun r => ⨍ y in ball x r, ‖ν y - ν x‖ ∂μ) (𝓝[>] 0) (𝓝 0) ∧
        Tendsto (fun r => ⨍ y in ball x r, ν y ∂μ) (𝓝[>] 0) (𝓝 (ν x))) := by
  obtain ⟨μ, ν, h⟩ := exists_ambient_outward_perimeter_polar hE hmE
  exact ⟨μ, ν, h, h.ae_differentiation⟩

end LiquidDrop

import NoCompromise.Nonexistence.Slicing
import NoCompromise.Classification.Subcritical

/-!
# `lem:slicing-inequality` for fixed-volume minimisers, unconditionally

`slicing_inequality` (Nonexistence/Slicing.lean) is proved for a Borel fixed-volume minimiser
`Ω` with the boundedness of `Ω` as the only named hypothesis `hbdd`, standing for "the bounded
representative of `cor:minimizer-stationary`". That representative is now constructed without
hypotheses: `IsLebesgueFixedVolumeMinimizer.minimizerRep_densityOne` with the proved
`noSingularPointsStatement` (`prop:no-singular-points`) gives `MinimizerRep V (densityOne Ω₀)`
(bounded, open, `C¹` boundary, a fixed-volume minimiser) with `densityOne Ω₀ =ᵐ Ω₀`, and
`cor:minimizer-stationary` holds for it (`MinimizerRep.isStationaryDomain`).

* `MinimizerRep.slicing_inequality`: `eq:slice-perimeter` and `eq:slice-coulomb` for the
  representative, with no named hypothesis;
* `slicing_inequality_of_isLebesgueFixedVolumeMinimizer`,
  `slicing_inequality_of_isFixedVolumeMinimizer`: the same for the representative
  `densityOne Ω₀` of an arbitrary fixed-volume minimiser `Ω₀` at volume `V > 0`, in both
  measurability conventions;
* `le_eight_of_isLebesgueFixedVolumeMinimizer`: its consumer `prop:V-le-8`, `V ≤ 8`, for every
  fixed-volume minimiser (no boundedness hypothesis).
-/

noncomputable section
open MeasureTheory Set
open scoped ENNReal

namespace LiquidDrop

/-- **`lem:slicing-inequality`** for the bounded open `C¹` representative `Ω` of a fixed-volume
minimiser at volume `V > 0` (`MinimizerRep`), with no named hypothesis: for every unit vector
`ν` and a.e. `ℓ ∈ ℝ`, with `Ω^± = Ω ∩ {±(ν·x − ℓ) > 0}`,
`Per(Ω⁺) + Per(Ω⁻) = Per(Ω) + 2H²(Ω ∩ {ν·x = ℓ})` (`eq:slice-perimeter`) and
`∬_{Ω⁺×Ω⁻} |x − y|⁻¹ dx dy ≤ 2H²(Ω ∩ {ν·x = ℓ})` (`eq:slice-coulomb`). -/
theorem MinimizerRep.slicing_inequality {V : ℝ} {Ω : Set AmbientSpace} (h : MinimizerRep V Ω)
    {ν : AmbientSpace} (hν : ‖ν‖ = 1) :
    ∀ᵐ ℓ : ℝ,
      perimeter (Ω ∩ {x | ℓ < inner ℝ ν x}) + perimeter (Ω ∩ {x | inner ℝ ν x < ℓ}) =
          perimeter Ω + 2 * hausdorffMeasure2 3 (Ω ∩ {x | inner ℝ ν x = ℓ}) ∧
      (∫⁻ x in Ω ∩ {x | ℓ < inner ℝ ν x}, ∫⁻ y in Ω ∩ {y | inner ℝ ν y < ℓ},
          ENNReal.ofReal (‖x - y‖⁻¹)) ≤
        2 * hausdorffMeasure2 3 (Ω ∩ {x | inner ℝ ν x = ℓ}) :=
  LiquidDrop.slicing_inequality
    ((isFixedVolumeMinimizer_iff_lebesgue V Ω h.isOpen.measurableSet).mpr h.minimizer)
    h.bounded hν

/-- **`lem:slicing-inequality`**, unconditional: let `Ω₀` be a fixed-volume minimiser
(Lebesgue-measurable convention) at volume `V > 0`, and `Ω = densityOne Ω₀` its bounded
representative (`cor:minimizer-stationary`, `not:minimizer-rep`). Then `Ω` is a bounded Borel
fixed-volume minimiser with `Ω =ᵐ Ω₀`, and for every unit `ν` and a.e. `ℓ`,
`eq:slice-perimeter` and `eq:slice-coulomb` hold for `Ω`. -/
theorem slicing_inequality_of_isLebesgueFixedVolumeMinimizer {V : ℝ} {Ω₀ : Set AmbientSpace}
    (hV : 0 < V) (hΩ₀ : IsLebesgueFixedVolumeMinimizer V Ω₀) :
    IsFixedVolumeMinimizer V (densityOne Ω₀) ∧ Bornology.IsBounded (densityOne Ω₀) ∧
      densityOne Ω₀ =ᵐ[volume] Ω₀ ∧
      ∀ ν : AmbientSpace, ‖ν‖ = 1 → ∀ᵐ ℓ : ℝ,
        perimeter (densityOne Ω₀ ∩ {x | ℓ < inner ℝ ν x}) +
            perimeter (densityOne Ω₀ ∩ {x | inner ℝ ν x < ℓ}) =
          perimeter (densityOne Ω₀) +
            2 * hausdorffMeasure2 3 (densityOne Ω₀ ∩ {x | inner ℝ ν x = ℓ}) ∧
        (∫⁻ x in densityOne Ω₀ ∩ {x | ℓ < inner ℝ ν x},
            ∫⁻ y in densityOne Ω₀ ∩ {y | inner ℝ ν y < ℓ}, ENNReal.ofReal (‖x - y‖⁻¹)) ≤
          2 * hausdorffMeasure2 3 (densityOne Ω₀ ∩ {x | inner ℝ ν x = ℓ}) := by
  obtain ⟨h, hae⟩ := hΩ₀.minimizerRep_densityOne noSingularPointsStatement hV
  exact ⟨(isFixedVolumeMinimizer_iff_lebesgue V _ h.isOpen.measurableSet).mpr h.minimizer,
    h.bounded, hae, fun _ hν => h.slicing_inequality hν⟩

/-- **`lem:slicing-inequality`**, unconditional, for a Borel fixed-volume minimiser `Ω₀` at
volume `V > 0` (the convention of `def:minimizer`): the conclusions of
`slicing_inequality_of_isLebesgueFixedVolumeMinimizer` for the bounded representative
`densityOne Ω₀`. -/
theorem slicing_inequality_of_isFixedVolumeMinimizer {V : ℝ} {Ω₀ : Set AmbientSpace}
    (hV : 0 < V) (hΩ₀ : IsFixedVolumeMinimizer V Ω₀) :
    IsFixedVolumeMinimizer V (densityOne Ω₀) ∧ Bornology.IsBounded (densityOne Ω₀) ∧
      densityOne Ω₀ =ᵐ[volume] Ω₀ ∧
      ∀ ν : AmbientSpace, ‖ν‖ = 1 → ∀ᵐ ℓ : ℝ,
        perimeter (densityOne Ω₀ ∩ {x | ℓ < inner ℝ ν x}) +
            perimeter (densityOne Ω₀ ∩ {x | inner ℝ ν x < ℓ}) =
          perimeter (densityOne Ω₀) +
            2 * hausdorffMeasure2 3 (densityOne Ω₀ ∩ {x | inner ℝ ν x = ℓ}) ∧
        (∫⁻ x in densityOne Ω₀ ∩ {x | ℓ < inner ℝ ν x},
            ∫⁻ y in densityOne Ω₀ ∩ {y | inner ℝ ν y < ℓ}, ENNReal.ofReal (‖x - y‖⁻¹)) ≤
          2 * hausdorffMeasure2 3 (densityOne Ω₀ ∩ {x | inner ℝ ν x = ℓ}) :=
  slicing_inequality_of_isLebesgueFixedVolumeMinimizer hV hΩ₀.toLebesgue

/-- `prop:V-le-8` for every fixed-volume minimiser (Lebesgue-measurable convention), with the
boundedness hypothesis of `le_eight_of_isFixedVolumeMinimizer` discharged by the bounded
representative: `V ≤ 8`. -/
theorem le_eight_of_isLebesgueFixedVolumeMinimizer {V : ℝ} {Ω₀ : Set AmbientSpace}
    (hΩ₀ : IsLebesgueFixedVolumeMinimizer V Ω₀) : V ≤ 8 := by
  rcases le_or_gt V 0 with hV | hV
  · linarith
  · obtain ⟨hmin, hbdd, -, -⟩ := slicing_inequality_of_isLebesgueFixedVolumeMinimizer hV hΩ₀
    exact le_eight_of_isFixedVolumeMinimizer hmin hbdd

end LiquidDrop

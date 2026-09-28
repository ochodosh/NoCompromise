import NoCompromise.Cones.NoSingularExcess
import NoCompromise.Cones.NoSingularChart
import NoCompromise.Cones.NoSingularGlobal
import NoCompromise.Regularity.RepresentativeBounded

/-!
# `prop:no-singular-points`: every boundary point of an `ω`-minimal set is regular

Blueprint `prop:no-singular-points` (chapter 26).  Let `E ⊂ ℝ³` be `ω`-minimal with `|E| < ∞`
and `Ω = densityOne E`.  Then

* every point of `∂Ω` is regular (`IsRegularBoundaryPoint`: a one-sided `C^{1,1/2}` graph chart
  in a rotated, rescaled cylinder);
* `∂Ω` is compact, `Ω` has `C¹` boundary charts (`HasC1Boundary`) — together, `∂Ω` is a compact
  embedded `C^{1,1/2}` surface — and `∂Ω` has finitely many connected components;
* `Ω = int (closure Ω)` and `Per(Ω) = H²(∂Ω)` (`eq:omega-regular-closed`).

Route (blueprint): at `x ∈ ∂Ω` a tangent cone is a nontrivial minimising cone
(`lem:tangent-cone-minimizing`, `prop:tangent-is-cone`), hence a halfspace (`thm:cone-3d`), so the
cylindrical excess tends to zero along the tangent scales (`lem:fixed-normal-excess-convergence`;
`IsOmegaMinimal.tendsto_cylindricalExcess_halfspace`), and `thm:eps-regularity` gives the chart
(`IsOmegaMinimal.isRegularBoundaryPoint_of_tendsto_excess`).  Compactness is
`lem:bounded-representative`; the rest is `cor:smooth-perimeter` and point-set topology
(Cones/NoSingularGlobal.lean).
-/

noncomputable section
open MeasureTheory Set
open scoped ENNReal
namespace LiquidDrop

/-- Every boundary point of the density-one representative of an `ω`-minimal set is regular. -/
theorem IsOmegaMinimal.isRegularBoundaryPoint {E : Set AmbientSpace} {ω : ℝ}
    (hE : IsOmegaMinimal E ω) {x : AmbientSpace} (hx : x ∈ frontier (densityOne E)) :
    IsRegularBoundaryPoint (densityOne E) x := by
  obtain ⟨ν, hν, r, hr, hr0, hexc⟩ := hE.tendsto_cylindricalExcess_halfspace hx
  exact hE.isRegularBoundaryPoint_of_tendsto_excess hν hx hr hr0 hexc

/-- **Blueprint `prop:no-singular-points`.** -/
theorem no_singular_points {E : Set AmbientSpace} {ω : ℝ} (hE : IsOmegaMinimal E ω)
    (hV : volume E < ∞) :
    (∀ x ∈ frontier (densityOne E), IsRegularBoundaryPoint (densityOne E) x) ∧
    IsCompact (frontier (densityOne E)) ∧
    HasC1Boundary (densityOne E) ∧
    Finite (ConnectedComponents (frontier (densityOne E))) ∧
    densityOne E = interior (closure (densityOne E)) ∧
    perimeter (densityOne E) = hausdorffMeasure2 3 (frontier (densityOne E)) := by
  have hreg : ∀ x ∈ frontier (densityOne E), IsRegularBoundaryPoint (densityOne E) x :=
    fun x hx => hE.isRegularBoundaryPoint hx
  obtain ⟨hb, hc⟩ := quasiminimal_bounded_representative hE hV
  exact ⟨hreg, hc, hasC1Boundary_of_isRegularBoundaryPoint hreg,
    finite_connectedComponents_frontier_of_isRegularBoundaryPoint hb hreg,
    (interior_closure_eq_of_isRegularBoundaryPoint hE.isOpen_densityOne hreg).symm,
    perimeter_eq_of_isRegularBoundaryPoint hE.isOpen_densityOne hreg⟩

end LiquidDrop

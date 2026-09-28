import NoCompromise.Isoperimetric.SharpNeumann
import NoCompromise.Elliptic.NeumannChartC1Ambient

/-!
# The ABP Neumann problem to first order, and the sharp isoperimetric inequality

The local boundary ingredient `ABPNeumannLocalBoundaryC1Regularity` of `lem:abp-neumann` is
the constant-data instance of `IsWeakNeumannSolution.exists_boundary_c1_conormal`
(Elliptic/NeumannChartC1Ambient.lean): localization to a flat normal chart, the first assertion
of `thm:boundary-neumann` (`boundary_neumann_c1_holder_conormal`) for the transformed data, and
the transport of the flat conormal condition back to `∂_ν z = 1`. Together with the proved
interior regularity and the gluing in Isoperimetric/ABPNeumann.lean this gives C¹-up-to-the-
boundary classical ABP Neumann solutions (`ABPNeumannC1Solvable`), which is all the contact-set
argument consumes. Hence `prop:iso-smooth`, `cor:iso-smooth-components` and
`thm:sharp-isoperimetric` hold without hypotheses.

The full smooth-up-to-the-boundary assertion `ABPNeumannSolvable` of `lem:abp-neumann` needs
the higher-order boundary regularity of `thm:boundary-neumann` and is not claimed here.
-/

noncomputable section

open MeasureTheory Set
open scoped ENNReal

namespace LiquidDrop

namespace IsABPNeumannC1Solution

variable {G : Set AmbientSpace} {hG : HasC1Boundary G} {z : AmbientSpace → ℝ}

/-! The fields of a C¹ solution consumed by the contact-set argument, under the names of the
corresponding lemmas for `IsABPNeumannSolution`. -/

lemma contDiffOn_two (h : IsABPNeumannC1Solution G hG z) : ContDiffOn ℝ 2 z G := h.1

lemma continuousOn (h : IsABPNeumannC1Solution G hG z) : ContinuousOn z (closure G) :=
  h.2.1.continuousOn

lemma laplacian (h : IsABPNeumannC1Solution G hG z) :
    ∀ x ∈ G, laplacianTrace z x = (perimeter G).toReal / volume.real G := h.2.2.1

/-- A C¹ solution of the ABP Neumann problem satisfies `NeumannOne`. -/
lemma neumannOne (h : IsABPNeumannC1Solution G hG z) : NeumannOne G z :=
  hG.neumannOne h.2.1 h.2.2.2

end IsABPNeumannC1Solution

/-- The local boundary ingredient of `lem:abp-neumann`, proved: near every boundary point a
weak solution of the constant ABP data agrees a.e. with a C¹ function on an open
neighbourhood whose derivative along the classical outward normal is `1` on the boundary. -/
theorem abpNeumannLocalBoundaryC1Regularity : ABPNeumannLocalBoundaryC1Regularity := by
  intro G hGo hGb _hGc hGs z hz p hp
  exact hz.exists_boundary_c1_conormal hGs (abpNeumannForcing_ae G hGb)
    (abpNeumannFlux_ae G hGo hGb hGs) contDiff_const contDiff_const hp

/-- Every weak solution of the constant ABP data has a representative that is C² in `G`,
C¹ on `closure G`, with `Δ = Per(G)/|G|` in `G` and `∂_ν = 1` on `∂G`. -/
theorem abpNeumannBoundaryC1Regularity : ABPNeumannBoundaryC1Regularity :=
  abpNeumannBoundaryC1Regularity_of_localBoundary abpNeumannLocalBoundaryC1Regularity

/-- `lem:abp-neumann` to first order at the boundary: every bounded connected open set with
smooth boundary carries a function C² inside and C¹ up to the boundary with
`Δz = Per(G)/|G|` in `G` and `∂_ν z = 1` on `∂G`. -/
theorem abpNeumannC1Solvable : ABPNeumannC1Solvable :=
  abpNeumannC1Solvable_of_boundaryC1Regularity abpNeumannBoundaryC1Regularity

/-- Blueprint `prop:iso-smooth`, unconditionally: a bounded connected open set with smooth
boundary satisfies `Per(G)^3 ≥ 36π |G|^2`. -/
theorem iso_smooth_unconditional {G : Set AmbientSpace} (hGo : IsOpen G)
    (hGb : Bornology.IsBounded G) (hGc : IsConnected G) (hGs : HasSmoothBoundary G) :
    36 * Real.pi * volume.real G ^ 2 ≤ (perimeter G).toReal ^ 3 :=
  iso_smooth_of_c1Solvable abpNeumannC1Solvable hGo hGb hGc hGs

/-- Blueprint `cor:iso-smooth-components`, second inequality, unconditionally: every bounded
open set with smooth boundary. -/
theorem smoothIsoperimetric_holds : SmoothIsoperimetric :=
  smoothIsoperimetric_of_connected fun _ hGo hGb hGc hGs =>
    iso_smooth_unconditional hGo hGb hGc hGs

/-- Blueprint `thm:sharp-isoperimetric`, unconditionally. -/
theorem sharp_isoperimetric_unconditional {E : Set AmbientSpace}
    (hE : NullMeasurableSet E volume) (hfin : volume E < ∞) :
    ENNReal.ofReal ((36 * Real.pi) ^ (1 / (3 : ℝ)) * (volume E).toReal ^ (2 / (3 : ℝ)))
      ≤ perimeter E :=
  sharp_isoperimetric_of_smooth smoothIsoperimetric_holds hE hfin

/-- The named hypothesis `SharpIsoperimetric` of Chapters 17–18 holds. -/
theorem sharpIsoperimetric_holds : SharpIsoperimetric :=
  fun _ hE hfin => sharp_isoperimetric_unconditional hE hfin

end LiquidDrop

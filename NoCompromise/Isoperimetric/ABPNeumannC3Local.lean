module

public import NoCompromise.Isoperimetric.ABPNeumannC3
public import NoCompromise.Elliptic.NeumannChartC3Ambient

@[expose] public section

/-!
# The local boundary ingredient of `lem:abp-neumann` on domains with C³ boundary

`ABPNeumannLocalBoundaryC1RegularityC3` is the constant-data instance of
`IsWeakNeumannSolution.exists_boundary_c1_conormal_c3` (Elliptic/NeumannChartC3Ambient.lean):
localization to a flat normal chart of a C³ boundary chart (the chart map is C², the
coefficient and forcing C¹, the flat datum C², the face normal coefficient constant), the first
assertion of `thm:boundary-neumann` (`boundary_neumann_c1_holder_conormal`), and the transport of
the flat conormal condition back to `∂_ν z = 1`. Hence `ABPNeumannSolvableC3` holds, and with it
`prop:iso-smooth` for bounded connected open sets with C³ boundary.
-/

noncomputable section

open MeasureTheory Set

namespace LiquidDrop

/-- The local boundary ingredient of `lem:abp-neumann` for C³ domains, proved. -/
theorem abpNeumannLocalBoundaryC1RegularityC3 : ABPNeumannLocalBoundaryC1RegularityC3 := by
  intro G hGo hGb _hGc hG z hz p hp
  exact hz.exists_boundary_c1_conormal_c3 hG (abpNeumannForcing_ae G hGb)
    (abpNeumannFluxC1_ae G hGo hGb hG.hasC1Boundary) contDiff_const contDiff_const hp

/-- `lem:abp-neumann` in the C³ form consumed downstream, proved: every bounded connected open
set with C³ boundary carries `z`, C² in `G` and C¹ on `closure G`, with `Δz = Per(G)/|G|` in `G`
and `∂_ν z = 1` on `∂G`. -/
theorem abpNeumannSolvableC3 : ABPNeumannSolvableC3 :=
  abpNeumannSolvableC3_of_localBoundary abpNeumannLocalBoundaryC1RegularityC3

/-- Blueprint `prop:iso-smooth` for bounded connected open sets with C³ boundary, without
hypotheses. -/
theorem iso_C3_unconditional {G : Set AmbientSpace} (hGo : IsOpen G)
    (hGb : Bornology.IsBounded G) (hGc : IsConnected G) (hG : HasCkBoundary 3 G) :
    36 * Real.pi * volume.real G ^ 2 ≤ (perimeter G).toReal ^ 3 :=
  iso_C3 abpNeumannSolvableC3 hGo hGb hGc hG

end LiquidDrop

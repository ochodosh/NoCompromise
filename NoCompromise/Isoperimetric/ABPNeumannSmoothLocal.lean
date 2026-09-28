import NoCompromise.Isoperimetric.ABPNeumannSmooth
import NoCompromise.Elliptic.NeumannChartSmoothAmbient

/-!
# The local boundary ingredient of the smooth clause of `lem:abp-neumann`

`ABPNeumannLocalBoundarySmoothRegularity` is the constant-data instance of
`IsWeakNeumannSolution.exists_boundary_all_orders_conormal`
(Elliptic/NeumannChartSmoothAmbient.lean): localization to a flat normal chart of a smooth
boundary chart, regularity of every order for the flat inhomogeneous conormal problem with
smooth data (`boundary_neumann_inhom_all_orders`), and the transport of the flat conormal
condition back to `∂_ν z = 1`. Hence `ABPNeumannSolvable` holds: every bounded connected open
set with smooth boundary carries a solution smooth up to the boundary, and with it
`prop:iso-smooth` through `iso_smooth`.
-/

noncomputable section

open MeasureTheory Set

namespace LiquidDrop

/-- The local boundary ingredient of the smooth clause of `lem:abp-neumann`, proved: near every
boundary point and for every `k`, a weak solution of the constant ABP data agrees a.e. in `G`
with a `C^{k+1}` function on an open neighbourhood whose derivative along the classical outward
normal is `1` on the boundary. -/
theorem abpNeumannLocalBoundarySmoothRegularity : ABPNeumannLocalBoundarySmoothRegularity := by
  intro G hGo hGb _hGc hGs z hz p hp k
  obtain ⟨V, w, hV, hpV, hw, hzw, hν⟩ :=
    hz.exists_boundary_all_orders_conormal hGs (abpNeumannForcing_ae G hGb)
      (abpNeumannFlux_ae G hGo hGb hGs) contDiff_const contDiff_const hp k
  exact ⟨V, w, hV, hpV, by exact_mod_cast hw, hzw, hν⟩

/-- `lem:abp-neumann`, proved: every bounded connected open set with smooth boundary carries
`z`, smooth up to the boundary, with `Δz = Per(G)/|G|` in `G` and `∂_ν z = 1` on `∂G`. -/
theorem abpNeumannSolvable : ABPNeumannSolvable :=
  abpNeumannSolvable_of_localBoundarySmooth abpNeumannLocalBoundarySmoothRegularity

/-- Blueprint `prop:iso-smooth` through the smooth ABP Neumann solution of `lem:abp-neumann`,
without hypotheses. -/
theorem iso_smooth_of_abpNeumannSolvable_unconditional {G : Set AmbientSpace}
    (hGo : IsOpen G) (hGb : Bornology.IsBounded G) (hGc : IsConnected G)
    (hGs : HasSmoothBoundary G) :
    36 * Real.pi * volume.real G ^ 2 ≤ (perimeter G).toReal ^ 3 :=
  iso_smooth abpNeumannSolvable hGo hGb hGc hGs

end LiquidDrop

import NoCompromise.Isoperimetric.ABPNeumannC3
import NoCompromise.Isoperimetric.SharpNeumann

/-!
# `cor:iso-smooth-components` for domains with `C³` boundary

The component decomposition of `Isoperimetric/Components.lean` uses the smoothness of the
boundary only to restrict charts to a component; the same restriction keeps a `C^k` height.
With `iso_C3` this gives blueprint `cor:iso-smooth-components` for bounded open sets with `C³`
boundary, and with it `thm:sharp-isoperimetric` from `ABPNeumannSolvableC3`.
-/

noncomputable section

open MeasureTheory Set
open scoped ENNReal

namespace LiquidDrop

/-- A connected component of an open set with `C^k` boundary has `C^k` boundary. -/
theorem hasCkBoundary_connectedComponentIn {k : ℕ∞} {S : Set AmbientSpace} (hS : IsOpen S)
    (hSk : HasCkBoundary k S) (x : AmbientSpace) :
    HasCkBoundary k (connectedComponentIn S x) := by
  intro p hp
  have hpS := frontier_connectedComponentIn_subset hS x hp
  obtain ⟨c, hc, hpc, hck⟩ := hSk p hpS
  obtain ⟨W, hW, hpW, hSW⟩ := hSk.hasC1Boundary.exists_nhds_isPreconnected_inter hpS
  have heq := inter_eq_component_inter hW hpW hp.1 hSW
  let d : C1BoundaryChart :=
    { c with
      region := c.region ∩ W
      isOpen_region := c.isOpen_region.inter hW
      bounded_region := c.bounded_region.subset inter_subset_left }
  refine ⟨d, ?_, ⟨hpc, hpW⟩, hck⟩
  intro z hz
  change z ∈ connectedComponentIn S x ↔ c.placement.symm z ∈ smoothSubgraph c.height
  rw [← hc z hz.1]
  exact ⟨fun hzG => connectedComponentIn_subset S x hzG, fun hzS =>
    (show z ∈ connectedComponentIn S x ∩ W from heq ▸ ⟨hzS, hz.2⟩).1⟩

/-- The perimeter of an open set with `C^k` boundary is the sum over its components. -/
theorem perimeter_eq_tsum_openComponents_of_hasCkBoundary {k : ℕ∞} {S : Set AmbientSpace}
    (hS : IsOpen S) (hSk : HasCkBoundary k S) :
    perimeter S = ∑' G : openComponents S, perimeter (G : Set AmbientSpace) := by
  rw [hSk.hasC1Boundary.perimeter_eq_boundaryArea hS,
    frontier_eq_biUnion_openComponents hS hSk.hasC1Boundary,
    measure_biUnion (countable_openComponents hS)
      (pairwiseDisjoint_frontier_openComponents hS hSk.hasC1Boundary)
      (fun _ _ => isClosed_frontier.measurableSet)]
  apply tsum_congr
  rintro ⟨G, x, hx, rfl⟩
  exact (HasC1Boundary.perimeter_eq_boundaryArea
    (hasCkBoundary_connectedComponentIn hS hSk x).hasC1Boundary
    hS.connectedComponentIn).symm

/-- Blueprint `cor:iso-smooth-components` (both inequalities) for a bounded open set with `C³`
boundary, from `prop:iso-smooth` for connected sets with `C³` boundary. -/
theorem iso_C3_components
    (hconn : ∀ G : Set AmbientSpace, IsOpen G → Bornology.IsBounded G → IsConnected G →
      HasCkBoundary 3 G → 36 * Real.pi * volume.real G ^ 2 ≤ (perimeter G).toReal ^ 3)
    {S : Set AmbientSpace} (hS : IsOpen S) (hSb : Bornology.IsBounded S)
    (hSs : HasCkBoundary 3 S) :
    ENNReal.ofReal ((36 * Real.pi) ^ (1 / (3 : ℝ))) *
        ∑' G : openComponents S, volume (G : Set AmbientSpace) ^ (2 / (3 : ℝ))
          ≤ perimeter S ∧
      volume S ^ (2 / (3 : ℝ)) ≤
        ∑' G : openComponents S, volume (G : Set AmbientSpace) ^ (2 / (3 : ℝ)) := by
  constructor
  · rw [perimeter_eq_tsum_openComponents_of_hasCkBoundary hS hSs, ← ENNReal.tsum_mul_left]
    apply ENNReal.tsum_le_tsum
    rintro ⟨G, x, hx, rfl⟩
    have ho : IsOpen (connectedComponentIn S x) := hS.connectedComponentIn
    have hb := hSb.subset (connectedComponentIn_subset S x)
    have hs := hasCkBoundary_connectedComponentIn hS hSs x
    have hc := isConnected_connectedComponentIn_iff.mpr hx
    have hvfin : volume (connectedComponentIn S x) ≠ ∞ := hb.measure_lt_top.ne
    have hpfin : perimeter (connectedComponentIn S x) ≠ ∞ := by
      have hf := hs.hasC1Boundary.hasFinitePerimeter ho hb
      change perimeterN (connectedComponentIn S x) < ∞ at hf
      rw [perimeterN_eq_perimeter _ ho.measurableSet.nullMeasurableSet] at hf
      exact hf.ne
    have hr := isoperimetric_cube_root ENNReal.toReal_nonneg ENNReal.toReal_nonneg
      (hconn _ ho hb hc hs)
    have he := ENNReal.ofReal_le_ofReal hr
    rw [ENNReal.ofReal_mul (Real.rpow_nonneg (by positivity) _),
      ← ENNReal.ofReal_rpow_of_nonneg ENNReal.toReal_nonneg (by norm_num),
      ENNReal.ofReal_toReal hvfin, ENNReal.ofReal_toReal hpfin] at he
    exact he
  · rw [volume_eq_tsum_openComponents hS]
    exact ennreal_rpow_tsum_le _ (by norm_num) (by norm_num)

/-- Blueprint `cor:iso-smooth-components` for `C³` domains, given `ABPNeumannSolvableC3`. -/
theorem iso_C3_components_of_abpNeumannSolvableC3 (hN : ABPNeumannSolvableC3)
    {S : Set AmbientSpace} (hS : IsOpen S) (hSb : Bornology.IsBounded S)
    (hSs : HasCkBoundary 3 S) :
    ENNReal.ofReal ((36 * Real.pi) ^ (1 / (3 : ℝ))) *
        ∑' G : openComponents S, volume (G : Set AmbientSpace) ^ (2 / (3 : ℝ))
          ≤ perimeter S ∧
      volume S ^ (2 / (3 : ℝ)) ≤
        ∑' G : openComponents S, volume (G : Set AmbientSpace) ^ (2 / (3 : ℝ)) :=
  iso_C3_components (fun _ hGo hGb hGc hG => iso_C3 hN hGo hGb hGc hG) hS hSb hSs

/-- The isoperimetric inequality `Per(S) ≥ (36π)^{1/3} |S|^{2/3}` for every bounded open set
with `C³` boundary, given `ABPNeumannSolvableC3`. -/
theorem iso_C3_of_abpNeumannSolvableC3 (hN : ABPNeumannSolvableC3)
    {S : Set AmbientSpace} (hS : IsOpen S) (hSb : Bornology.IsBounded S)
    (hSs : HasCkBoundary 3 S) :
    ENNReal.ofReal ((36 * Real.pi) ^ (1 / (3 : ℝ)) * (volume S).toReal ^ (2 / (3 : ℝ)))
      ≤ perimeter S := by
  obtain ⟨hfirst, hsecond⟩ := iso_C3_components_of_abpNeumannSolvableC3 hN hS hSb hSs
  rw [ENNReal.ofReal_mul (Real.rpow_nonneg (by positivity) _),
    ← ENNReal.ofReal_rpow_of_nonneg ENNReal.toReal_nonneg (by norm_num),
    ENNReal.ofReal_toReal hSb.measure_lt_top.ne]
  exact (mul_le_mul_right hsecond _).trans hfirst

/-- `SmoothIsoperimetric` (the smooth case of `cor:iso-smooth-components`) from
`ABPNeumannSolvableC3`. -/
theorem smoothIsoperimetric_of_abpNeumannSolvableC3 (hN : ABPNeumannSolvableC3) :
    SmoothIsoperimetric :=
  smoothIsoperimetric_of_connected fun _ hGo hGb hGc hGs =>
    iso_smooth_of_abpNeumannSolvableC3 hN hGo hGb hGc hGs

/-- Blueprint `thm:sharp-isoperimetric`, given `ABPNeumannSolvableC3`. -/
theorem sharp_isoperimetric_of_abpNeumannSolvableC3 (hN : ABPNeumannSolvableC3)
    {E : Set AmbientSpace} (hE : NullMeasurableSet E volume) (hfin : volume E < ∞) :
    ENNReal.ofReal ((36 * Real.pi) ^ (1 / (3 : ℝ)) * (volume E).toReal ^ (2 / (3 : ℝ)))
      ≤ perimeter E :=
  sharp_isoperimetric_of_smooth (smoothIsoperimetric_of_abpNeumannSolvableC3 hN) hE hfin

/-- The named hypothesis `SharpIsoperimetric` of Chapters 17–18 from `ABPNeumannSolvableC3`. -/
theorem sharpIsoperimetric_of_abpNeumannSolvableC3 (hN : ABPNeumannSolvableC3) :
    SharpIsoperimetric :=
  fun _ hE hfin => sharp_isoperimetric_of_abpNeumannSolvableC3 hN hE hfin

end LiquidDrop

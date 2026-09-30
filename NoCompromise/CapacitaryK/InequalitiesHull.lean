module

public import NoCompromise.CapacitaryK.InequalitiesFinal
public import NoCompromise.Capacity.HullExistence

@[expose] public section

/-!
# `thm:capacitary-inequalities` for the filled hull of `Ω`

`K = filledHull Ω` for a bounded connected open `Ω ∋ 0` with `C²` boundary (`def:hull`,
`lem:hull-properties`) satisfies the standing hypotheses of
`capacitary_inequalities_of_C2_extension_final`, and its capacitary potential exists
(`exists_filledHull_capacitary_potential`). The mean curvature is taken in the charts of
`int K`, the form of `IsStationaryDomain.filledHull_boundary` (`cor:EL-pointwise` on `∂K`).
-/

noncomputable section
open Real Set Filter Metric MeasureTheory
open scoped Topology Gradient ENNReal

namespace LiquidDrop.CapacitaryK

/-- `thm:capacitary-inequalities` for the capacitary potential of the filled hull, modulo only
`thm:total-curvature-bound` and the `C²` extension of `u` across `∂K`. -/
theorem filledHull_capacitary_inequalities {Ω : Set E3} (ho : IsOpen Ω)
    (hbd : Bornology.IsBounded Ω) (hc : IsConnected Ω) (h2 : HasC2Boundary Ω)
    (h0 : (0 : E3) ∈ Ω)
    {u : E3 → ℝ} (hu : Continuous u)
    (hh : HasDistributionalLaplacianOn u (fun _ => 0) (filledHull Ω)ᶜ)
    (hb : ∀ x ∈ filledHull Ω, u x = 1) (hinf : Tendsto u (cocompact E3) (𝓝 0))
    {g : E3 → ℝ} (hg : ContDiff ℝ 2 g) (hug : EqOn u g (closure (filledHull Ω)ᶜ))
    (h_of_total_curvature_bound : ∀ (S : Set E3) (n : E3 → E3), IsCompact S → IsConnected S →
      IsSmoothEmbeddedSurface S → IsUnitNormalField S n →
      ∫ x in S, gaussCurvature S n x ∂(Measure.euclideanHausdorffMeasure 2) ≤ 4 * Real.pi)
    {H : E3 → ℝ} (hH : ∀ p ∈ frontier (filledHull Ω), ∀ c : C1BoundaryChart,
      c.IsChartFor (interior (filledHull Ω)) → p ∈ c.region → ContDiff ℝ 2 c.height →
        H p = meanCurvature (frontier (filledHull Ω)) c.outwardNormal p) :
    4 * π ≤ ∫ x in frontier (filledHull Ω), ‖gradient g x‖ ^ 2 ∂hausdorffMeasure2 3 ∧
      4 * (∫ x in frontier (filledHull Ω), ‖gradient g x‖ ^ 2 ∂hausdorffMeasure2 3) - 8 * π ≤
        ∫ x in frontier (filledHull Ω), H x * ‖gradient g x‖ ∂hausdorffMeasure2 3 :=
  capacitary_inequalities_of_C2_extension_final (filledHull_isCompact hbd)
    (filledHull_isConnected hc hbd) (filledHull_isConnected_compl hbd).isPreconnected
    (filledHull_eq_closure_interior ho) (filledHull_hasC2Boundary_interior ho h2)
    (filledHull_subset_interior ho h0) hu hh hb hinf hg hug h_of_total_curvature_bound hH

/-- The capacitary potential of the filled hull exists, and every `C²` extension of it across
`∂K` yields `eq:capacitary-inequalities` (given `thm:total-curvature-bound`). -/
theorem exists_filledHull_capacitary_potential_inequalities {Ω : Set E3} (ho : IsOpen Ω)
    (hbd : Bornology.IsBounded Ω) (hc : IsConnected Ω) (h2 : HasC2Boundary Ω)
    (h0 : (0 : E3) ∈ Ω)
    (h_of_total_curvature_bound : ∀ (S : Set E3) (n : E3 → E3), IsCompact S → IsConnected S →
      IsSmoothEmbeddedSurface S → IsUnitNormalField S n →
      ∫ x in S, gaussCurvature S n x ∂(Measure.euclideanHausdorffMeasure 2) ≤ 4 * Real.pi)
    {H : E3 → ℝ} (hH : ∀ p ∈ frontier (filledHull Ω), ∀ c : C1BoundaryChart,
      c.IsChartFor (interior (filledHull Ω)) → p ∈ c.region → ContDiff ℝ 2 c.height →
        H p = meanCurvature (frontier (filledHull Ω)) c.outwardNormal p) :
    ∃ u : E3 → ℝ, Continuous u ∧
      HasDistributionalLaplacianOn u (fun _ => 0) (filledHull Ω)ᶜ ∧
      (∀ x ∈ filledHull Ω, u x = 1) ∧ Tendsto u (cocompact E3) (𝓝 0) ∧
      (∀ x ∈ (filledHull Ω)ᶜ, 0 < u x ∧ u x < 1) ∧
      ∀ g : E3 → ℝ, ContDiff ℝ 2 g → EqOn u g (closure (filledHull Ω)ᶜ) →
        4 * π ≤ ∫ x in frontier (filledHull Ω), ‖gradient g x‖ ^ 2 ∂hausdorffMeasure2 3 ∧
          4 * (∫ x in frontier (filledHull Ω), ‖gradient g x‖ ^ 2 ∂hausdorffMeasure2 3) -
              8 * π ≤
            ∫ x in frontier (filledHull Ω), H x * ‖gradient g x‖ ∂hausdorffMeasure2 3 := by
  obtain ⟨u, hu, hh, -, hb, hinf, hsign⟩ := exists_filledHull_capacitary_potential ho hbd h2 h0
  exact ⟨u, hu, hh, hb, hinf, hsign, fun g hg hug => filledHull_capacitary_inequalities ho hbd hc
    h2 h0 hu hh hb hinf hg hug h_of_total_curvature_bound hH⟩

end LiquidDrop.CapacitaryK

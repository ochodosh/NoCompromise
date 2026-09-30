module

public import NoCompromise.CapacitaryK.InequalitiesHull
public import NoCompromise.Capacity.FluxIdentityHull
public import NoCompromise.Surface.TotalCurvatureBoundMain

@[expose] public section

/-!
# `thm:capacitary-inequalities` for the filled hull, unconditionally

`filledHull_capacitary_inequalities` (the filled-hull instance of
`capacitary_inequalities_of_C2_extension_final`) takes two inputs: `thm:total-curvature-bound`,
proved as `total_curvature_bound_forall`, and a `C²` extension `g` of `u` across `∂K`, supplied
by `hullPotentialBoundaryC2` (`thm:boundary-C2a` for the hull potential) when `Ω` has `C³`
boundary. With both fed in, `eq:capacitary-inequalities` holds for the capacitary potential of
the filled hull of every bounded connected open `Ω ∋ 0` with `C³` boundary, `∇u = ∇g` on `∂K`
and `H` any function equal on `∂K` to the mean curvature of `∂K` in the `C²` charts of `int K`.
-/

noncomputable section
open Real Set Filter Metric MeasureTheory
open scoped Topology Gradient ENNReal

namespace LiquidDrop.CapacitaryK

/-- Blueprint `thm:capacitary-inequalities` (`eq:capacitary-inequalities`) for the capacitary
potential `u` of the filled hull `K` of a bounded connected open `Ω ∋ 0` with `C³` boundary:
some `C²` function `g` with `u = g` on `closure Kᶜ` satisfies `4π ≤ ∫_{∂K} |∇g|²` and
`4 ∫_{∂K} |∇g|² - 8π ≤ ∫_{∂K} H |∇g|`. The conclusion after the extension is that of
`filledHull_capacitary_inequalities` (and of `capacitary_inequalities_of_C2_extension_final`
for `K = filledHull Ω`), with `thm:total-curvature-bound` discharged. -/
theorem filledHull_capacitary_inequalities_unconditional {Ω : Set E3} (ho : IsOpen Ω)
    (hbd : Bornology.IsBounded Ω) (hc : IsConnected Ω) (h3 : HasCkBoundary 3 Ω)
    (h0 : (0 : E3) ∈ Ω)
    {u : E3 → ℝ} (hu : Continuous u)
    (hh : HasDistributionalLaplacianOn u (fun _ => 0) (filledHull Ω)ᶜ)
    (hb : ∀ x ∈ filledHull Ω, u x = 1) (hinf : Tendsto u (cocompact E3) (𝓝 0))
    {H : E3 → ℝ} (hH : ∀ p ∈ frontier (filledHull Ω), ∀ c : C1BoundaryChart,
      c.IsChartFor (interior (filledHull Ω)) → p ∈ c.region → ContDiff ℝ 2 c.height →
        H p = meanCurvature (frontier (filledHull Ω)) c.outwardNormal p) :
    ∃ g : E3 → ℝ, ContDiff ℝ 2 g ∧ EqOn u g (closure (filledHull Ω)ᶜ) ∧
      4 * π ≤ ∫ x in frontier (filledHull Ω), ‖gradient g x‖ ^ 2 ∂hausdorffMeasure2 3 ∧
      4 * (∫ x in frontier (filledHull Ω), ‖gradient g x‖ ^ 2 ∂hausdorffMeasure2 3) - 8 * π ≤
        ∫ x in frontier (filledHull Ω), H x * ‖gradient g x‖ ∂hausdorffMeasure2 3 := by
  obtain ⟨g, hg, hug⟩ := hullPotentialBoundaryC2 Ω ho hbd h3 h0 u hu hh hb hinf
  exact ⟨g, hg, hug, filledHull_capacitary_inequalities ho hbd hc (h3.hasC2Boundary (by norm_num))
    h0 hu hh hb hinf hg hug total_curvature_bound_forall hH⟩

/-- The capacitary potential of the filled hull `K` of a bounded connected open `Ω ∋ 0` with
`C³` boundary exists, and it has a `C²` extension `g` across `∂K` satisfying
`eq:capacitary-inequalities` (`thm:capacitary-inequalities`, `thm:capacitary-potential`). The
conclusion is that of `exists_filledHull_capacitary_potential_inequalities` with the extension
supplied and `thm:total-curvature-bound` discharged. -/
theorem exists_filledHull_capacitary_potential_inequalities_unconditional {Ω : Set E3}
    (ho : IsOpen Ω) (hbd : Bornology.IsBounded Ω) (hc : IsConnected Ω) (h3 : HasCkBoundary 3 Ω)
    (h0 : (0 : E3) ∈ Ω)
    {H : E3 → ℝ} (hH : ∀ p ∈ frontier (filledHull Ω), ∀ c : C1BoundaryChart,
      c.IsChartFor (interior (filledHull Ω)) → p ∈ c.region → ContDiff ℝ 2 c.height →
        H p = meanCurvature (frontier (filledHull Ω)) c.outwardNormal p) :
    ∃ u : E3 → ℝ, Continuous u ∧
      HasDistributionalLaplacianOn u (fun _ => 0) (filledHull Ω)ᶜ ∧
      (∀ x ∈ filledHull Ω, u x = 1) ∧ Tendsto u (cocompact E3) (𝓝 0) ∧
      (∀ x ∈ (filledHull Ω)ᶜ, 0 < u x ∧ u x < 1) ∧
      ∃ g : E3 → ℝ, ContDiff ℝ 2 g ∧ EqOn u g (closure (filledHull Ω)ᶜ) ∧
        4 * π ≤ ∫ x in frontier (filledHull Ω), ‖gradient g x‖ ^ 2 ∂hausdorffMeasure2 3 ∧
          4 * (∫ x in frontier (filledHull Ω), ‖gradient g x‖ ^ 2 ∂hausdorffMeasure2 3) -
              8 * π ≤
            ∫ x in frontier (filledHull Ω), H x * ‖gradient g x‖ ∂hausdorffMeasure2 3 := by
  obtain ⟨u, hu, hh, -, hb, hinf, hsign⟩ :=
    exists_filledHull_capacitary_potential ho hbd (h3.hasC2Boundary (by norm_num)) h0
  exact ⟨u, hu, hh, hb, hinf, hsign,
    filledHull_capacitary_inequalities_unconditional ho hbd hc h3 h0 hu hh hb hinf hH⟩

end LiquidDrop.CapacitaryK

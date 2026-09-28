import NoCompromise.Surface.TotalCurvatureBoundMain
import NoCompromise.CapacitaryK.FromPotential

/-!
# `lem:K-gauss-bonnet-input` for the capacitary potential, unconditionally

`K_gauss_bonnet_input` (CapacitaryK/GaussBonnetInput.lean) took `lem:level-connected` and
`thm:total-curvature-bound` as the named hypotheses `h_of_level_connected` and
`h_of_total_curvature_bound`. Both are now proved:

* `h_of_total_curvature_bound` is `total_curvature_bound_forall`
  (Surface/TotalCurvatureBoundMain.lean);
* `h_of_level_connected` is `level_connected` (Capacity/LevelsMain.lean), whose inputs are
  properties of the capacitary potential: exterior smoothness
  (`capacitary_potential_contDiffOn`) and `0 < u < 1` off `K` (`capacitary_signs`, using that
  `Kᶜ` is connected).

The standing hypotheses of chapter 31 on `K` and `u` are those of
`capacitary_inequalities_of_potential`: `K` compact and connected, `Kᶜ` connected,
`0 ∈ int K`; `u` continuous, harmonic off `K` (distributionally), `u = 1` on `K`, `u → 0` at
infinity.
-/

noncomputable section
open Set Filter MeasureTheory Topology
open scoped Gradient

namespace LiquidDrop.CapacitaryK

/-- `lem:level-connected` for the capacitary potential, in the exact shape of the named
hypothesis `h_of_level_connected` of chapter 31: every regular level `{u = s}`, `0 < s < 1`, is
connected. -/
theorem capacitary_level_connected
    {K : Set E3} (hK : IsCompact K) (hKconn : IsConnected K) (hcompl : IsPreconnected Kᶜ)
    (hzero : (0 : E3) ∈ interior K)
    {u : E3 → ℝ} (hu : Continuous u)
    (hh : HasDistributionalLaplacianOn u (fun _ => 0) Kᶜ)
    (hb : ∀ x ∈ K, u x = 1) (hinf : Tendsto u (cocompact E3) (𝓝 0)) :
    ∀ s : ℝ, 0 < s → s < 1 → (∀ x ∈ u ⁻¹' {s}, gradient u x ≠ 0) →
      IsConnected (u ⁻¹' {s}) := by
  have hsmooth := capacitary_potential_contDiffOn hK hu hh
  have hsigns := capacitary_signs hK hzero hu hh hb hinf
  have hstrict : ∀ x ∉ K, 0 < u x ∧ u x < 1 :=
    fun x hx => ⟨(hsigns.1 x hx).1, hsigns.2 hcompl x hx⟩
  intro s hs hs1 hreg
  exact level_connected hK hKconn hu hb hh hsmooth hinf hstrict hs hs1 hreg

/-- **`lem:K-gauss-bonnet-input`** (`eq:K-gauss-bonnet-input`) for the capacitary potential `u`
of `K`, with no named hypothesis: for every regular value `t ∈ (0,1)`,
`∫_{u=t} κ dH² ≤ 4π`, where `κ = gaussCurvature {u = t} ν` is the Gauss curvature of the level
surface for the level-set normal `ν = -∇u/|∇u|` (`unitNormal u`). -/
theorem capacitary_K_gauss_bonnet_input
    {K : Set E3} (hK : IsCompact K) (hKconn : IsConnected K) (hcompl : IsPreconnected Kᶜ)
    (hzero : (0 : E3) ∈ interior K)
    {u : E3 → ℝ} (hu : Continuous u)
    (hh : HasDistributionalLaplacianOn u (fun _ => 0) Kᶜ)
    (hb : ∀ x ∈ K, u x = 1) (hinf : Tendsto u (cocompact E3) (𝓝 0))
    {t : ℝ} (ht0 : 0 < t) (ht1 : t < 1) (hreg : ∀ x ∈ u ⁻¹' {t}, gradient u x ≠ 0) :
    ∫ x in u ⁻¹' {t}, gaussCurvature (u ⁻¹' {t}) (unitNormal u) x
        ∂(Measure.euclideanHausdorffMeasure 2) ≤ 4 * Real.pi := by
  obtain ⟨hsub, hcompact, -⟩ :=
    capacitary_levels ⟨0, interior_subset hzero⟩ hu hb hinf t ht0 ht1
  exact K_gauss_bonnet_input_of_level_connected hK.isClosed.isOpen_compl
    (capacitary_potential_contDiffOn hK hu hh) ht0 ht1 hsub hreg hcompact
    (capacitary_level_connected hK hKconn hcompl hzero hu hh hb hinf)

end LiquidDrop.CapacitaryK

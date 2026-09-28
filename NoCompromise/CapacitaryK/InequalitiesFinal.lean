import NoCompromise.CapacitaryK.BoundaryMeanCurvature
import NoCompromise.CapacitaryK.MuMeasure

/-!
# `thm:capacitary-inequalities`, blueprint statement

For the capacitary potential `u` of a compact connected `K` with connected complement, `C²`
boundary and `0 ∈ int K`, given a `C²` extension `g` of `u` across `∂K` (the `thm:boundary-C2a`
stand-in) and `thm:total-curvature-bound`:
`∫_{∂K} |∇u|² ≥ 4π` and `∫_{∂K} H|∇u| ≥ 4 ∫_{∂K} |∇u|² - 8π`, where `∇u = ∇g` on `∂K` and `H`
is the mean curvature of `∂K` in the charts of `int K`. The measure `μ = Δ|∇u|` is supplied by
`K_mu_measure`, and the base level `t₀` is taken in the collar near `∂K`, where every level is
regular.
-/

noncomputable section
open Real Set Filter Metric MeasureTheory
open scoped Topology Gradient ENNReal

namespace LiquidDrop.CapacitaryK

/-- Blueprint `thm:capacitary-inequalities` (`eq:capacitary-inequalities`), modulo only
`thm:total-curvature-bound` and the `C²` extension `g` of `u` across `∂K`. -/
theorem capacitary_inequalities_of_C2_extension_final
    {K : Set E3} (hK : IsCompact K) (hKconn : IsConnected K) (hcompl : IsPreconnected Kᶜ)
    (hreg : K = closure (interior K)) (hC2 : HasC2Boundary (interior K))
    (hzero : (0 : E3) ∈ interior K)
    {u : E3 → ℝ} (hu : Continuous u)
    (hh : HasDistributionalLaplacianOn u (fun _ => 0) Kᶜ)
    (hb : ∀ x ∈ K, u x = 1) (hinf : Tendsto u (cocompact E3) (𝓝 0))
    {g : E3 → ℝ} (hg : ContDiff ℝ 2 g) (hug : EqOn u g (closure Kᶜ))
    (h_of_total_curvature_bound : ∀ (S : Set E3) (n : E3 → E3), IsCompact S → IsConnected S →
      IsSmoothEmbeddedSurface S → IsUnitNormalField S n →
      ∫ x in S, gaussCurvature S n x ∂(Measure.euclideanHausdorffMeasure 2) ≤ 4 * Real.pi)
    {H : E3 → ℝ} (hH : ∀ p ∈ frontier K, ∀ c : C1BoundaryChart, c.IsChartFor (interior K) →
      p ∈ c.region → ContDiff ℝ 2 c.height → H p = meanCurvature (frontier K) c.outwardNormal p) :
    4 * π ≤ ∫ x in frontier K, ‖gradient g x‖ ^ 2 ∂hausdorffMeasure2 3 ∧
      4 * (∫ x in frontier K, ‖gradient g x‖ ^ 2 ∂hausdorffMeasure2 3) - 8 * π ≤
        ∫ x in frontier K, H x * ‖gradient g x‖ ∂hausdorffMeasure2 3 := by
  have hC1 : HasC1Boundary (interior K) := hC2.hasC1Boundary
  obtain ⟨R, hR⟩ := hK.isBounded.subset_closedBall 0
  have hR₀ : (0 : ℝ) < max R 1 := lt_max_of_lt_right one_pos
  have hKR : K ⊆ closedBall 0 (max R 1) := hR.trans (closedBall_subset_closedBall (le_max_left _ _))
  have hU : IsOpen Kᶜ := hK.isClosed.isOpen_compl
  have hu3 : ContDiffOn ℝ 3 u Kᶜ := (capacitary_potential_contDiffOn hK hu hh).of_le (by norm_num)
  have hΔ := kelvin_laplacianN_eq_zero_of_distributional hU hu.continuousOn hh
  obtain ⟨μ, hμU, hμK, hμ⟩ := K_mu_measure hU hu3 hΔ
  obtain ⟨t₁, ht₁, c, hc, M, hcol⟩ := capacitary_collar_of_C2_extension hK hreg hC1 hR₀ hKR
    hzero hu hh hb hinf hg hug hC2 hcompl
  set t₀ : ℝ := (max t₁ 0 + 1) / 2 with ht₀def
  have hm : max t₁ 0 < 1 := max_lt ht₁ one_pos
  have ht₀ : t₀ ∈ Ioo (0 : ℝ) 1 := ⟨by linarith [le_max_right t₁ 0], by linarith⟩
  have ht₀R : ∀ x ∈ Kᶜ, u x = t₀ → gradient u x ≠ 0 := by
    intro x hx hxt hz
    have hw := (hcol x hx (by rw [hxt]; linarith [le_max_left t₁ 0])).1
    have : gradNorm u x = 0 := by rw [gradNorm, hz, norm_zero]
    linarith
  exact capacitary_inequalities_boundary_chart_of_C2_extension hK hKconn hcompl hreg hC1 hC2
    hR₀ hKR hzero hu hh hb hinf hg hug hμU hμK hμ h_of_total_curvature_bound ht₀ ht₀R hH

end LiquidDrop.CapacitaryK

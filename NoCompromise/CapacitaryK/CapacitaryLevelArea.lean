module

public import NoCompromise.CapacitaryK.CapacitaryLevelRadius
public import NoCompromise.CapacitaryK.RadialGraphAreaFormula

@[expose] public section

/-!
# `eq:K-dA` as an identity of measures on the small capacitary levels

Chapter 31, `lem:K-level-asymptotics`. For small `t > 0`, with `ρ_t` the zero-homogeneous level
radius about `z = (v 0)⁻¹ • ∇v(0)`, the two-dimensional Hausdorff measure of the level
`Kᶜ ∩ {u = t}` is the pushforward of `J_t(θ) dθ` under `θ ↦ ρ_t θ • θ + z`, where
`J_t = ρ_t √(ρ_t² + |∇_T ρ_t|²)` and, uniformly in `θ`,
`J_t(θ) = C²/t² + 2 Q(θ)/C + O(t)`, i.e. `dH²_t = (C²/t²)(1 + 2 Q t²/C³ + O(t³)) dθ`.
-/

noncomputable section

open Set Filter Metric InnerProductSpace MeasureTheory
open scoped Topology Gradient RealInnerProductSpace ENNReal

namespace LiquidDrop.CapacitaryK

/-- `lem:K-level-asymptotics`, `eq:K-dA`: area on the small capacitary levels in radial
coordinates, with the uniform expansion of the area element. -/
theorem capacitary_level_area_expansion
    {K : Set E3} (hK : IsCompact K) {R₀ : ℝ} (hR₀ : 0 < R₀)
    (hKR : K ⊆ Metric.closedBall 0 R₀) (hzero : (0 : E3) ∈ interior K)
    {u : E3 → ℝ} (hu : Continuous u)
    (hh : HasDistributionalLaplacianOn u (fun _ => 0) Kᶜ)
    (hb : ∀ x ∈ K, u x = 1) (hinf : Tendsto u (cocompact E3) (𝓝 0)) :
    ∃ (v : E3 → ℝ) (r : ℝ), 0 < r ∧ ContDiffOn ℝ (⊤ : ℕ∞) v (Metric.ball 0 r) ∧
      EqOn v (kelvinTransform u) (Metric.ball 0 r \ {0}) ∧ 0 < v 0 ∧
      ∃ A : ℝ, 0 ≤ A ∧ ∀ᶠ t in 𝓝[>] (0 : ℝ),
        (∃ ρ : E3 → ℝ, (∀ y : E3, y ≠ 0 → ρ y = ρ (‖y‖⁻¹ • y)) ∧
          ∀ θ : E3, ‖θ‖ = 1 → 0 < ρ θ ∧ u (ρ θ • θ + (v 0)⁻¹ • gradient v 0) = t) ∧
        ∀ ρ : E3 → ℝ, (∀ y : E3, y ≠ 0 → ρ y = ρ (‖y‖⁻¹ • y)) →
          (∀ θ : E3, ‖θ‖ = 1 → 0 < ρ θ ∧ u (ρ θ • θ + (v 0)⁻¹ • gradient v 0) = t) →
          (∀ q : E3 → ℝ≥0∞, Measurable q →
            ∫⁻ x in Kᶜ ∩ u ⁻¹' {t}, q x ∂(Measure.euclideanHausdorffMeasure 2) =
              ∫⁻ θ in sphere (0 : E3) 1, q (ρ θ • θ + (v 0)⁻¹ • gradient v 0) *
                ENNReal.ofReal (ρ θ * Real.sqrt (ρ θ ^ 2 +
                  ‖gradient ρ θ - ⟪gradient ρ θ, θ⟫ • θ‖ ^ 2))
                ∂(Measure.euclideanHausdorffMeasure 2)) ∧
          (∀ f : E3 → ℝ, Measurable f →
            ∫ x in Kᶜ ∩ u ⁻¹' {t}, f x ∂(Measure.euclideanHausdorffMeasure 2) =
              ∫ θ in sphere (0 : E3) 1, f (ρ θ • θ + (v 0)⁻¹ • gradient v 0) *
                (ρ θ * Real.sqrt (ρ θ ^ 2 + ‖gradient ρ θ - ⟪gradient ρ θ, θ⟫ • θ‖ ^ 2))
                ∂(Measure.euclideanHausdorffMeasure 2)) ∧
          ∀ θ : E3, ‖θ‖ = 1 →
            |ρ θ - (v 0 / t + t * kelvinTranslatedQuadrupole v θ / (v 0) ^ 2)| ≤ A * t ^ 2 ∧
            |ρ θ * Real.sqrt (ρ θ ^ 2 + ‖gradient ρ θ - ⟪gradient ρ θ, θ⟫ • θ‖ ^ 2) -
              ((v 0) ^ 2 / t ^ 2 + 2 * kelvinTranslatedQuadrupole v θ / v 0)| ≤ A * t := by
  obtain ⟨v, r, hr, hv, he, hv0, A, hA, hev⟩ :=
    capacitary_level_radius_smooth hK hR₀ hKR hzero hu hh hb hinf
  refine ⟨v, r, hr, hv, he, hv0, A, hA, ?_⟩
  filter_upwards [hev] with t ⟨hex, hall⟩
  refine ⟨hex, fun ρ hhom hroot => ?_⟩
  obtain ⟨hρs, hlevel, hbd⟩ := hall ρ hhom hroot
  have hρ1 : ContDiffOn ℝ 1 ρ {y : E3 | y ≠ 0} := hρs.of_le (by exact_mod_cast le_top)
  refine ⟨fun q hq => ?_, fun f hf => ?_, fun θ hθ => ⟨(hbd θ hθ).2.1, (hbd θ hθ).2.2⟩⟩
  · rw [hlevel]
    exact radial_graph_lintegral hρ1 (fun θ hθ => (hroot θ hθ).1) _ hq
  · rw [hlevel]
    exact radial_graph_integral_real hρ1 (fun θ hθ => (hroot θ hθ).1) _ hf

end LiquidDrop.CapacitaryK

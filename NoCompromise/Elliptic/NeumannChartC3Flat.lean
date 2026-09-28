import NoCompromise.Elliptic.NeumannChartC3Data
import NoCompromise.Elliptic.NeumannChartC1Flat

/-!
# C¹ flat representatives for C³ boundary charts
-/

noncomputable section

open Set Filter Metric InnerProductSpace MeasureTheory
open scoped Topology Gradient NNReal

namespace LiquidDrop

/-- C³ chart height and smooth data give the flat C¹ representative and conormal identity. -/
theorem neumannChartC3_flat_representative
    (c : C1BoundaryChart) (hψ : ContDiff ℝ 3 c.height)
    (a : EuclideanSpace ℝ (Fin 2)) {ρ : ℝ} (hρ : 0 < ρ)
    (hreg : ∀ y ∈ ball 0 2, (fderiv ℝ (neumannLocalizeMap c a ρ) y).IsInvertible)
    {f₀ h₀ : AmbientSpace → ℝ} (hf : ContDiff ℝ (⊤ : ℕ∞) f₀)
    (hh : ContDiff ℝ (⊤ : ℕ∞) h₀) {α : ℝ} (hα : 0 < α) (hα1 : α < 1)
    {z : AmbientSpace → ℝ} {F : AmbientSpace → AmbientSpace}
    (hz : HasH1GradientOn z F (boundaryHalfBall 1))
    (hweak : ∀ φ : AmbientSpace → ℝ, ContDiff ℝ 1 φ → HasCompactSupport φ →
      tsupport φ ⊆ ball 0 1 →
      (∫ y in boundaryHalfBall 1,
        inner ℝ (neumannLocalizeCoefficient (neumannLocalizeMap c a ρ) y (F y))
          (gradient φ y)) =
        -(∫ y in boundaryHalfBall 1,
          neumannChartC1Forcing (neumannLocalizeMap c a ρ) f₀ y * φ y) -
          ∫ t in ball (0 : EuclideanSpace ℝ (Fin 2)) 1,
            neumannChartC1BoundaryDatum c a ρ h₀ t * φ (graphBaseEmbedding t)) :
    ∃ u : AmbientSpace → ℝ,
      ContDiffOn ℝ 1 u (ball 0 (1 / 2 : ℝ)) ∧
      z =ᵐ[volume.restrict (boundaryHalfBall (1 / 2))] u ∧
      F =ᵐ[volume.restrict (boundaryHalfBall (1 / 2))] gradient u ∧
      (∃ C > 0,
        (∀ x ∈ ball 0 (1 / 2 : ℝ), ‖gradient u x‖ ≤ C) ∧
        (∀ x ∈ ball 0 (1 / 2 : ℝ), ∀ y ∈ ball 0 (1 / 2 : ℝ),
          ‖gradient u x - gradient u y‖ ≤ C * dist x y ^ α)) ∧
      ∀ t : EuclideanSpace ℝ (Fin 2), graphBaseEmbedding t ∈ ball 0 (1 / 2 : ℝ) →
        neumannLocalizeCoefficient (neumannLocalizeMap c a ρ) (graphBaseEmbedding t)
          (gradient u (graphBaseEmbedding t)) (Fin.last 2) =
            -(h₀ (neumannLocalizeMap c a ρ (graphBaseEmbedding t)) * ρ ^ 2 *
              Real.sqrt (1 + ‖gradient c.height (a + ρ • t)‖ ^ 2)) := by
  obtain ⟨lam, cap, HA, K, hlam, hcap, hHA, hK, hd⟩ :=
    neumannChartC3_exists_data c hψ a hρ hreg hf hh hα hα1
  exact hd.exists_representative hα hα1 hlam hcap hHA hK hz hweak

/-- The chart map is C², while the representative is C¹ with α-Hölder gradient. -/
theorem IsWeakNeumannSolution.exists_normal_chart_c1_conormal_c3
    {D : Set AmbientSpace} {hD : IsOpen D} {hbD : Bornology.IsBounded D}
    {hL : HasLipschitzBoundary D} {f : Lp ℝ 2 (volume.restrict D)}
    {h : Lp ℝ 2 ((hausdorffMeasure2 3).restrict (frontier D))} {z : H1Space D}
    (hz : IsWeakNeumannSolution hD hbD hL f h z)
    {f₀ h₀ : AmbientSpace → ℝ} (hf : ⇑f =ᵐ[volume.restrict D] f₀)
    (hh : ⇑h =ᵐ[(hausdorffMeasure2 3).restrict (frontier D)] h₀)
    (hfs : ContDiff ℝ (⊤ : ℕ∞) f₀) (hhs : ContDiff ℝ (⊤ : ℕ∞) h₀)
    {c : C1BoundaryChart} (hc : c.IsChartFor D)
    (hψ : ContDiff ℝ 3 c.height) {p : AmbientSpace}
    (hp : p ∈ frontier D) (hpc : p ∈ c.region)
    {α : ℝ} (hα : 0 < α) (hα1 : α < 1) :
    ∃ ρ > 0,
      let a := graphProjectionN 2 (c.placement.symm p)
      let Θ := neumannLocalizeMap c a ρ
      Θ 0 = p ∧ ContDiff ℝ 2 Θ ∧ InjOn Θ (ball 0 2) ∧
      (∀ y ∈ ball 0 2, (fderiv ℝ Θ y).IsInvertible) ∧
      Θ '' ball 0 2 ⊆ c.region ∧ Θ '' boundaryHalfBall 2 ⊆ D ∧
      Disjoint (Θ '' (ball 0 2 ∩ {y | y (Fin.last 2) < 0})) (closure D) ∧
      Θ '' (ball 0 2 ∩ {y | y (Fin.last 2) = 0}) ⊆ frontier D ∧
      IsOpen (Θ '' ball 0 2) ∧
      ∃ u : AmbientSpace → ℝ,
        ContDiffOn ℝ 1 u (ball 0 (1 / 2 : ℝ)) ∧
        (fun y => z (Θ y)) =ᵐ[volume.restrict (boundaryHalfBall (1 / 2))] u ∧
        (fun y => (fderiv ℝ Θ y).adjoint (z.gradientLp (Θ y)))
          =ᵐ[volume.restrict (boundaryHalfBall (1 / 2))] gradient u ∧
        (∃ C > 0,
          (∀ x ∈ ball 0 (1 / 2 : ℝ), ‖gradient u x‖ ≤ C) ∧
          (∀ x ∈ ball 0 (1 / 2 : ℝ), ∀ y ∈ ball 0 (1 / 2 : ℝ),
            ‖gradient u x - gradient u y‖ ≤ C * dist x y ^ α)) ∧
        ∀ t : EuclideanSpace ℝ (Fin 2), graphBaseEmbedding t ∈ ball 0 (1 / 2 : ℝ) →
          neumannLocalizeCoefficient Θ (graphBaseEmbedding t)
            (gradient u (graphBaseEmbedding t)) (Fin.last 2) =
              -(h₀ (Θ (graphBaseEmbedding t)) * ρ ^ 2 *
                Real.sqrt (1 + ‖gradient c.height (a + ρ • t)‖ ^ 2)) := by
  obtain ⟨ρ, hρ, h0, -, hinj, hreg, hregion, hupper, hlower, hface, hopen, hH1, hweak⟩ :=
    hz.exists_normal_chart_c2_of_c3 hf hh hc (hψ.of_le (by norm_num)) hp hpc
  refine ⟨ρ, hρ, h0, contDiff_neumannLocalizeMap_of_contDiff c hψ _ ρ, hinj, hreg,
    hregion, hupper, hlower, hface, hopen, ?_⟩
  exact neumannChartC3_flat_representative c hψ _ hρ hreg hfs hhs hα hα1 hH1 hweak

end LiquidDrop

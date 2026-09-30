module

public import NoCompromise.Elliptic.NeumannChartC1Data
public import NoCompromise.Elliptic.BoundaryNeumannC2InhomSmooth

@[expose] public section

/-!
# C² regularity up to the face in a smooth normal chart

Smooth data in a regular normal chart satisfy the hypotheses of
`boundary_neumann_c2_inhom_smooth_fixed`. The representative is C¹ on the
full radius-`1 / 2` ball and C² on the radius-`1 / 4 * (3 / 8)` half-ball,
with each Hessian entry extending continuously to its closure. The exact
conormal condition holds on the radius-`1 / 2` face.
-/

noncomputable section

open Set Filter Metric InnerProductSpace MeasureTheory
open scoped Topology Gradient

namespace LiquidDrop

/-- Smooth chart data and the localized weak equation give a C² representative
whose Hessian entries extend continuously to the closed smaller half-ball.
The auxiliary Hölder exponent is fixed internally to `1 / 2`. -/
theorem neumannChartC2_flat_representative
    (c : C1BoundaryChart) (hψ : ContDiff ℝ (⊤ : ℕ∞) c.height)
    (a : EuclideanSpace ℝ (Fin 2)) {ρ : ℝ} (hρ : 0 < ρ)
    (hreg : ∀ y ∈ ball 0 2, (fderiv ℝ (neumannLocalizeMap c a ρ) y).IsInvertible)
    {f₀ h₀ : AmbientSpace → ℝ} (hf : ContDiff ℝ (⊤ : ℕ∞) f₀)
    (hh : ContDiff ℝ (⊤ : ℕ∞) h₀)
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
      ContDiffOn ℝ 2 u (boundaryHalfBall (1 / 4 * (3 / 8))) ∧
      z =ᵐ[volume.restrict (boundaryHalfBall (1 / 4 * (3 / 8)))] u ∧
      F =ᵐ[volume.restrict (boundaryHalfBall (1 / 4 * (3 / 8)))] gradient u ∧
      (∀ i j : Fin 3, ∃ D : AmbientSpace → ℝ,
        ContinuousOn D (closure (boundaryHalfBall (1 / 4 * (3 / 8)))) ∧
        EqOn D (fun x => boundaryNeumannC2Entry u x i j)
          (boundaryHalfBall (1 / 4 * (3 / 8)))) ∧
      ∀ t : EuclideanSpace ℝ (Fin 2), graphBaseEmbedding t ∈ ball 0 (1 / 2 : ℝ) →
        neumannLocalizeCoefficient (neumannLocalizeMap c a ρ) (graphBaseEmbedding t)
          (gradient u (graphBaseEmbedding t)) (Fin.last 2) =
            -(h₀ (neumannLocalizeMap c a ρ (graphBaseEmbedding t)) * ρ ^ 2 *
              Real.sqrt (1 + ‖gradient c.height (a + ρ • t)‖ ^ 2)) := by
  have hα : (0 : ℝ) < 1 / 2 := by norm_num
  have hα1 : (1 / 2 : ℝ) < 1 := by norm_num
  obtain ⟨lam, cap, HA, K, hlam, -, -, -, hd⟩ :=
    neumannChartC1_exists_data c hψ a hρ hreg hf hh hα hα1
  obtain ⟨U, hU, hsub, -, -, hpos⟩ := hd.normal_neighborhood
  exact boundary_neumann_c2_inhom_smooth_fixed hα hα1 hlam isOpen_ball
    (closedBall_subset_ball (by norm_num : (1 : ℝ) < 2))
    (smoothOn_neumannLocalizeCoefficient_ball c hψ a ρ hreg)
    (smoothOn_neumannChartC1Forcing (smooth_neumannLocalizeMap c hψ a ρ) hf hreg)
    (smooth_neumannChartC1BoundaryDatum c hψ a ρ hh)
    hd.elliptic hd.cross_face ⟨U, hU, hsub, hpos⟩ hz hweak

/-- A weak Neumann solution with smooth volume and boundary representatives
admits a smooth normal chart and a C² representative up to its flat face in
the sense of continuous extensions of all Hessian entries. All geometric
chart properties of `IsWeakNeumannSolution.exists_normal_chart_c1_conormal`
are retained. -/
theorem IsWeakNeumannSolution.exists_normal_chart_c2
    {D : Set AmbientSpace} {hD : IsOpen D} {hbD : Bornology.IsBounded D}
    {hL : HasLipschitzBoundary D} {f : Lp ℝ 2 (volume.restrict D)}
    {h : Lp ℝ 2 ((hausdorffMeasure2 3).restrict (frontier D))} {z : H1Space D}
    (hz : IsWeakNeumannSolution hD hbD hL f h z)
    {f₀ h₀ : AmbientSpace → ℝ} (hf : ⇑f =ᵐ[volume.restrict D] f₀)
    (hh : ⇑h =ᵐ[(hausdorffMeasure2 3).restrict (frontier D)] h₀)
    (hfs : ContDiff ℝ (⊤ : ℕ∞) f₀) (hhs : ContDiff ℝ (⊤ : ℕ∞) h₀)
    {c : C1BoundaryChart} (hc : c.IsChartFor D)
    (hψ : ContDiff ℝ (⊤ : ℕ∞) c.height) {p : AmbientSpace}
    (hp : p ∈ frontier D) (hpc : p ∈ c.region) :
    ∃ ρ > 0,
      let a := graphProjectionN 2 (c.placement.symm p)
      let Θ := neumannLocalizeMap c a ρ
      Θ 0 = p ∧ ContDiff ℝ (⊤ : ℕ∞) Θ ∧ InjOn Θ (ball 0 2) ∧
      (∀ y ∈ ball 0 2, (fderiv ℝ Θ y).IsInvertible) ∧
      Θ '' ball 0 2 ⊆ c.region ∧ Θ '' boundaryHalfBall 2 ⊆ D ∧
      Disjoint (Θ '' (ball 0 2 ∩ {y | y (Fin.last 2) < 0})) (closure D) ∧
      Θ '' (ball 0 2 ∩ {y | y (Fin.last 2) = 0}) ⊆ frontier D ∧
      IsOpen (Θ '' ball 0 2) ∧
      ∃ u : AmbientSpace → ℝ,
        ContDiffOn ℝ 1 u (ball 0 (1 / 2 : ℝ)) ∧
        ContDiffOn ℝ 2 u (boundaryHalfBall (1 / 4 * (3 / 8))) ∧
        (fun y => z (Θ y))
          =ᵐ[volume.restrict (boundaryHalfBall (1 / 4 * (3 / 8)))] u ∧
        (fun y => (fderiv ℝ Θ y).adjoint (z.gradientLp (Θ y)))
          =ᵐ[volume.restrict (boundaryHalfBall (1 / 4 * (3 / 8)))] gradient u ∧
        (∀ i j : Fin 3, ∃ E : AmbientSpace → ℝ,
          ContinuousOn E (closure (boundaryHalfBall (1 / 4 * (3 / 8)))) ∧
          EqOn E (fun x => boundaryNeumannC2Entry u x i j)
            (boundaryHalfBall (1 / 4 * (3 / 8)))) ∧
        ∀ t : EuclideanSpace ℝ (Fin 2), graphBaseEmbedding t ∈ ball 0 (1 / 2 : ℝ) →
          neumannLocalizeCoefficient Θ (graphBaseEmbedding t)
            (gradient u (graphBaseEmbedding t)) (Fin.last 2) =
              -(h₀ (Θ (graphBaseEmbedding t)) * ρ ^ 2 *
                Real.sqrt (1 + ‖gradient c.height (a + ρ • t)‖ ^ 2)) := by
  obtain ⟨ρ, hρ, h0, -, hinj, hreg, hregion, hupper, hlower, hface, hopen, hH1, hweak⟩ :=
    hz.exists_normal_chart hf hh hc hψ hp hpc
  refine ⟨ρ, hρ, h0, smooth_neumannLocalizeMap c hψ _ ρ, hinj, hreg,
    hregion, hupper, hlower, hface, hopen, ?_⟩
  exact neumannChartC2_flat_representative c hψ _ hρ hreg hfs hhs hH1 hweak

end LiquidDrop

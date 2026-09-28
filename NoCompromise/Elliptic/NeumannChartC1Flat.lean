import NoCompromise.Elliptic.NeumannChartC1Data

/-!
# C¹ representatives and the classical conormal condition in a normal chart

The energy constant is the actual squared L² norm of the pullback gradient.
The data bounds are constructed from smooth representatives, so no additional
quantitative hypotheses are imposed on the original weak solution.
-/

noncomputable section

open Set Filter Metric InnerProductSpace MeasureTheory
open scoped Topology Gradient

namespace LiquidDrop

/-- Apply the flat theorem to the recorded data, choosing the energy constant
to be the energy of the given weak gradient. -/
theorem NeumannChartC1Data.exists_representative
    {A : AmbientSpace → AmbientSpace →L[ℝ] AmbientSpace}
    {f : AmbientSpace → ℝ} {h : EuclideanSpace ℝ (Fin 2) → ℝ}
    {α lam cap HA K : ℝ} (hd : NeumannChartC1Data A f h α lam cap HA K)
    (hα : 0 < α) (hα1 : α < 1) (hlam : 0 < lam) (hcap : 0 ≤ cap)
    (hHA : 0 ≤ HA) (hK : 0 ≤ K)
    {z : AmbientSpace → ℝ} {F : AmbientSpace → AmbientSpace}
    (hz : HasH1GradientOn z F (boundaryHalfBall 1))
    (hweak : ∀ φ : AmbientSpace → ℝ, ContDiff ℝ 1 φ → HasCompactSupport φ →
      tsupport φ ⊆ ball 0 1 →
      (∫ x in boundaryHalfBall 1, inner ℝ (A x (F x)) (gradient φ x)) =
        -(∫ x in boundaryHalfBall 1, f x * φ x) -
          ∫ t in ball (0 : EuclideanSpace ℝ (Fin 2)) 1,
            h t * φ (graphBaseEmbedding t)) :
    ∃ u : AmbientSpace → ℝ,
      ContDiffOn ℝ 1 u (ball 0 (1 / 2 : ℝ)) ∧
      z =ᵐ[volume.restrict (boundaryHalfBall (1 / 2))] u ∧
      F =ᵐ[volume.restrict (boundaryHalfBall (1 / 2))] gradient u ∧
      (∃ C > 0,
        (∀ x ∈ ball 0 (1 / 2 : ℝ), ‖gradient u x‖ ≤ C) ∧
        (∀ x ∈ ball 0 (1 / 2 : ℝ), ∀ y ∈ ball 0 (1 / 2 : ℝ),
          ‖gradient u x - gradient u y‖ ≤ C * dist x y ^ α)) ∧
      ∀ t : EuclideanSpace ℝ (Fin 2), graphBaseEmbedding t ∈ ball 0 (1 / 2 : ℝ) →
        A (graphBaseEmbedding t) (gradient u (graphBaseEmbedding t)) (Fin.last 2) = h t := by
  let M := ∫ x in boundaryHalfBall 1, ‖F x‖ ^ 2
  have hM : 0 ≤ M := integral_nonneg fun _ => sq_nonneg _
  obtain ⟨C, hC, hregularity⟩ :=
    boundary_neumann_c1_holder_conormal hα hα1 hlam hcap hHA hK hM
  obtain ⟨u, hu, hzu, hFu, hbu, hhu, hcon⟩ := hregularity A F z f h
    hd.continuous_coefficient hd.bound_coefficient hd.elliptic hd.holder_coefficient
    hd.cross_face hd.normal_neighborhood hd.bound_datum hd.bound_normal
    hd.bound_gradient_datum hd.bound_gradient_normal hd.holder_gradient_datum
    hd.holder_gradient_normal hd.continuous_forcing hd.bound_forcing hd.holder_forcing
    hz le_rfl hweak
  exact ⟨u, hu, hzu, hFu, ⟨C, hC, hbu, hhu⟩, hcon⟩

/-- Smooth data and the exact localized equation imply C¹ regularity and the
pointwise flat conormal condition. The pullback and its weak gradient are the
ones in `IsWeakNeumannSolution.exists_normal_chart`. -/
theorem neumannChartC1_flat_representative
    (c : C1BoundaryChart) (hψ : ContDiff ℝ (⊤ : ℕ∞) c.height)
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
    neumannChartC1_exists_data c hψ a hρ hreg hf hh hα hα1
  exact hd.exists_representative hα hα1 hlam hcap hHA hK hz hweak

/-- A weak Neumann solution with smooth volume and boundary representatives
has a C¹ representative in a normal chart, with the exact classical conormal
condition on the face. All original hypotheses of localization are retained. -/
theorem IsWeakNeumannSolution.exists_normal_chart_c1_conormal
    {D : Set AmbientSpace} {hD : IsOpen D} {hbD : Bornology.IsBounded D}
    {hL : HasLipschitzBoundary D} {f : Lp ℝ 2 (volume.restrict D)}
    {h : Lp ℝ 2 ((hausdorffMeasure2 3).restrict (frontier D))} {z : H1Space D}
    (hz : IsWeakNeumannSolution hD hbD hL f h z)
    {f₀ h₀ : AmbientSpace → ℝ} (hf : ⇑f =ᵐ[volume.restrict D] f₀)
    (hh : ⇑h =ᵐ[(hausdorffMeasure2 3).restrict (frontier D)] h₀)
    (hfs : ContDiff ℝ (⊤ : ℕ∞) f₀) (hhs : ContDiff ℝ (⊤ : ℕ∞) h₀)
    {c : C1BoundaryChart} (hc : c.IsChartFor D)
    (hψ : ContDiff ℝ (⊤ : ℕ∞) c.height) {p : AmbientSpace}
    (hp : p ∈ frontier D) (hpc : p ∈ c.region)
    {α : ℝ} (hα : 0 < α) (hα1 : α < 1) :
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
    hz.exists_normal_chart hf hh hc hψ hp hpc
  refine ⟨ρ, hρ, h0, smooth_neumannLocalizeMap c hψ _ ρ, hinj, hreg,
    hregion, hupper, hlower, hface, hopen, ?_⟩
  exact neumannChartC1_flat_representative c hψ _ hρ hreg hfs hhs hα hα1 hH1 hweak

end LiquidDrop

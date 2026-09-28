import NoCompromise.Regularity.OmegaMinimal
import NoCompromise.Regularity.FirstVariationScalar
import NoCompromise.Variation.Perimeter
import NoCompromise.Variation.SymmetricDifferenceFull

/-! # Bounded generalized first variation of a quasiminimizer -/

noncomputable section
open MeasureTheory Set Filter Metric
open scoped ENNReal Topology symmDiff
namespace LiquidDrop

lemma IsOmegaMinimal.eventually_perimeter_variation_comparison
    {E : Set AmbientSpace} {ω : ℝ} (hE : IsOmegaMinimal E ω)
    {X : AmbientSpace → AmbientSpace} (hX : ContDiff ℝ 1 X)
    (hcX : HasCompactSupport X) {x : AmbientSpace} (hXs : tsupport X ⊆ ball x 1) :
    ∀ᶠ t : ℝ in 𝓝 0,
      (perimeterIn E (ball x 1)).toReal ≤
        (perimeterIn (straightPerturbation X t '' E) (ball x 1)).toReal +
          ω * volume.real (E ∆ (straightPerturbation X t '' E)) := by
  have hsmall : ∀ᶠ t : ℝ in 𝓝 0, |t| * ‖straightDerivativeField hX hcX‖ < 1 :=
    (continuous_abs.mul_const _).continuousAt.eventually
      (gt_mem_nhds (by simp : |(0 : ℝ)| * ‖straightDerivativeField hX hcX‖ < 1))
  filter_upwards [hsmall] with t ht
  obtain ⟨Φ, heq, hΦ, hiΦ, _, _, _⟩ :=
    straightPerturbation_compactlySupported_diffeomorphism hX hcX ht
  have hcoe : (Φ : AmbientSpace → AmbientSpace) = straightPerturbation X t := funext heq
  have hpF := hasLocallyFinitePerimeter_image_of_C1_diffeomorphism Φ hΦ hiΦ
    E hE.locallyFinite hE.nullMeasurable
  have hmF := nullMeasurableSet_image_of_differentiable
    (hΦ.differentiable one_ne_zero) Φ.injective hE.nullMeasurable
  rw [hcoe] at hpF hmF
  have hs : E ∆ (straightPerturbation X t '' E) ⊆ tsupport X :=
    symmDiff_straightPerturbation_subset_tsupport
      (lipschitzWith_straightDerivativeField hX hcX) ht E
  have hcs : closure ((straightPerturbation X t '' E) ∆ E) ⊆ tsupport X := by
    rw [symmDiff_comm]
    exact closure_minimal hs (isClosed_tsupport X)
  have hc := hcX.of_isClosed_subset isClosed_closure hcs
  have hh := hE.comparison x 1 (by norm_num) (by simp) _ hmF hpF hc (hcs.trans hXs)
  have hpfin := hpF (ball x 1) isOpen_ball isBounded_ball.isCompact_closure
  have hvfin : volume (E ∆ (straightPerturbation X t '' E)) < ∞ :=
    (measure_mono hs).trans_lt hcX.measure_lt_top
  have hright : perimeterIn (straightPerturbation X t '' E) (ball x 1) +
      ENNReal.ofReal ω * volume (E ∆ (straightPerturbation X t '' E)) ≠ ∞ := by
    finiteness
  have htR := ENNReal.toReal_mono hright hh
  rw [ENNReal.toReal_add hpfin.ne (by finiteness), ENNReal.toReal_mul,
    ENNReal.toReal_ofReal hE.nonneg] at htR
  exact htR

/-- Blueprint `lem:bounded-H`. The full normal-flux bound is valid for every
compact C¹ field supported in any unit ball. -/
theorem IsOmegaMinimal.bounded_first_variation
    {E : Set AmbientSpace} {ω : ℝ} (hE : IsOmegaMinimal E ω)
    {X : AmbientSpace → AmbientSpace} (hX : ContDiff ℝ 1 X)
    (hcX : HasCompactSupport X) {x : AmbientSpace} (hXs : tsupport X ⊆ ball x 1) :
    |∫ z in reducedBoundary E hE.locallyFinite hE.nullMeasurable,
      tangentialDivergence X (reducedNormal E hE.locallyFinite hE.nullMeasurable) z
        ∂hausdorffMeasure2 3| ≤
      ω * ∫ z in reducedBoundary E hE.locallyFinite hE.nullMeasurable,
        |inner ℝ (X z) (reducedNormal E hE.locallyFinite hE.nullMeasurable z)|
          ∂hausdorffMeasure2 3 := by
  apply abs_derivative_le_of_variation_cost
    (first_variation_perimeter E hE.locallyFinite hE.nullMeasurable hX hcX
      isOpen_ball isBounded_ball hXs)
    (hE.locallyFinite.tendsto_symmDiff_straightPerturbation hE.nullMeasurable hX hcX)
  simpa only [straightPerturbation_zero, image_id] using
    hE.eventually_perimeter_variation_comparison hX hcX hXs

end LiquidDrop

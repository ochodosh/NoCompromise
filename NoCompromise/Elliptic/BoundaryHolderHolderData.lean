module

public import NoCompromise.Elliptic.BoundaryHolderData
public import NoCompromise.Elliptic.BoundaryHolderAverages

@[expose] public section

/-! The blueprint's actual Hölder coefficient and datum hypotheses imply the
radial equation data used in the boundary bootstrap. -/

noncomputable section
open MeasureTheory Filter Metric Set InnerProductSpace
open scoped ENNReal NNReal Topology Gradient RealInnerProductSpace
namespace LiquidDrop
set_option maxSynthPendingDepth 8

lemma zero_mem_closure_boundaryHalfBall {R : ℝ} (hR : 0 < R) :
    (0 : EuclideanSpace ℝ (Fin 3)) ∈ closure (boundaryHalfBall R) := by
  rw [Metric.mem_closure_iff]
  intro ε hε
  let t := min R ε / 2
  have ht : 0 < t := by dsimp [t]; positivity
  have htR : t < R := by have hh := min_le_left R ε; dsimp [t]; linarith
  have htε : t < ε := by have hh := min_le_right R ε; dsimp [t]; linarith
  refine ⟨EuclideanSpace.single (Fin.last 2) t, ⟨?_, ?_⟩, ?_⟩
  · change dist (EuclideanSpace.single (Fin.last 2) t) 0 < R
    simpa only [dist_zero_right, PiLp.norm_single, Real.norm_eq_abs, abs_of_pos ht] using htR
  · change 0 < EuclideanSpace.single (Fin.last 2) t (Fin.last 2)
    simpa only [PiLp.single_apply, ite_true] using ht
  · simpa only [dist_zero_left, PiLp.norm_single, Real.norm_eq_abs, abs_of_pos ht] using htε

/-- Full closed-half-ball Hölder data and the genuine weak solution give the
radial data without additional boundary regularity or gradient assumptions. -/
theorem boundary_radialData_of_holder {a lam cap HA HG R : ℝ}
    (ha : 0 ≤ a) (hHG : 0 ≤ HG) (hR : 0 < R)
    {u : EuclideanSpace ℝ (Fin 3) → ℝ}
    {F G : EuclideanSpace ℝ (Fin 3) → EuclideanSpace ℝ (Fin 3)}
    {A : EuclideanSpace ℝ (Fin 3) → EuclideanSpace ℝ (Fin 3) →L[ℝ]
      EuclideanSpace ℝ (Fin 3)}
    (hA : ContinuousOn A (closure (boundaryHalfBall R)))
    (hG : ContinuousOn G (closure (boundaryHalfBall R)))
    (hbA : ∀ x ∈ closure (boundaryHalfBall R), ‖A x‖ ≤ cap)
    (hell : ∀ x ∈ closure (boundaryHalfBall R), ∀ ξ,
      lam * ‖ξ‖ ^ 2 ≤ inner ℝ (A x ξ) ξ)
    (hHA : ∀ x ∈ closure (boundaryHalfBall R), ∀ y ∈ closure (boundaryHalfBall R),
      ‖A x - A y‖ ≤ HA * dist x y ^ a)
    (hHG' : ∀ x ∈ closure (boundaryHalfBall R), ∀ y ∈ closure (boundaryHalfBall R),
      ‖G x - G y‖ ≤ HG * dist x y ^ a)
    (hu : HasH1GradientOn u F (boundaryHalfBall R))
    (hT : HasZeroFlatTraceOn u F (ball 0 R))
    (hw : IsWeakDivergenceEquationOn A F G (boundaryHalfBall R)) :
    BoundaryHolderRadialData a lam cap HA HG R u F G A := by
  have h0 := zero_mem_closure_boundaryHalfBall hR
  have hmA := (hA.mono subset_closure).aestronglyMeasurable (μ := volume)
    (isOpen_boundaryHalfBall R).measurableSet
  have hmG := (hG.mono subset_closure).aestronglyMeasurable (μ := volume)
    (isOpen_boundaryHalfBall R).measurableSet
  have hoscA : ∀ᵐ x ∂volume.restrict (boundaryHalfBall R), ‖A x - A 0‖ ≤ HA * ‖x‖ ^ a := by
    filter_upwards [ae_restrict_mem (isOpen_boundaryHalfBall R).measurableSet] with x hx
    simpa only [dist_zero_right] using hHA x (subset_closure hx) 0 h0
  have hoscG : ∀ᵐ x ∂volume.restrict (boundaryHalfBall R), ‖G x - G 0‖ ≤ HG * ‖x‖ ^ a := by
    filter_upwards [ae_restrict_mem (isOpen_boundaryHalfBall R).measurableSet] with x hx
    simpa only [dist_zero_right] using hHG' x (subset_closure hx) 0 h0
  let : IsFiniteMeasure (volume.restrict (boundaryHalfBall R)) :=
    ⟨by simpa using boundaryHalfBall_volume_lt_top R⟩
  have hmemG : MemLp G 2 (volume.restrict (boundaryHalfBall R)) := by
    apply MemLp.of_bound hmG (HG * R ^ a + ‖G 0‖)
    filter_upwards [hoscG, ae_restrict_mem (isOpen_boundaryHalfBall R).measurableSet] with x hx hy
    have hyR : ‖x‖ ≤ R := (show ‖x‖ < R by
      simpa only [mem_ball, dist_zero_right] using hy.1).le
    have hp := mul_le_mul_of_nonneg_left (Real.rpow_le_rpow (norm_nonneg _) hyR ha) hHG
    have hn := norm_le_insert' (G x) (G 0)
    linarith
  refine ⟨hu, hT, hw, hmA, ?_, hmemG, hell 0 h0, hbA 0 h0, hoscA, hoscG⟩
  filter_upwards [ae_restrict_mem (isOpen_boundaryHalfBall R).measurableSet] with x hx
  exact hbA x (subset_closure hx)

end LiquidDrop

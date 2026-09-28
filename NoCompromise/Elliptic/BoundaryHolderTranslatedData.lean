import NoCompromise.Elliptic.BoundaryHolderTranslate
import NoCompromise.Elliptic.BoundaryHolderHolderData

/-! Uniform transfer of the actual boundary data to tangential centers safely
inside the original half-ball. -/

noncomputable section
open MeasureTheory Filter Metric Set InnerProductSpace
open scoped ENNReal NNReal Topology Gradient RealInnerProductSpace
namespace LiquidDrop
set_option maxSynthPendingDepth 8

lemma boundary_halfBall_translate_mem (z : EuclideanSpace ℝ (Fin 2))
    (x : EuclideanSpace ℝ (Fin 3)) (r : ℝ) :
    x + graphAppendN z 0 ∈ ball (graphAppendN z 0) r ∩ {y | 0 < y (Fin.last 2)} ↔
      x ∈ boundaryHalfBall r := by
  simp only [mem_inter_iff, mem_ball, dist_eq_norm, add_sub_cancel_right,
    mem_ofPred_eq, PiLp.add_apply, graphAppendN_last, add_zero, boundaryHalfBall, sub_zero]

lemma boundary_integral_halfBall_translate {E : Type*}
    [NormedAddCommGroup E] [NormedSpace ℝ E]
    (f : EuclideanSpace ℝ (Fin 3) → E) (z : EuclideanSpace ℝ (Fin 2)) (r : ℝ) :
    (∫ x in boundaryHalfBall r, f (x + graphAppendN z 0)) =
      ∫ x in ball (graphAppendN z 0) r ∩ {y | 0 < y (Fin.last 2)}, f x := by
  let D := ball (graphAppendN z 0) r ∩ {y | 0 < y (Fin.last 2)}
  have h := integral_add_right_eq_self (D.indicator f) (graphAppendN z 0) (μ := volume)
  have he : (fun x => D.indicator f (x + graphAppendN z 0)) =
      (boundaryHalfBall r).indicator (fun x => f (x + graphAppendN z 0)) := by
    funext x
    by_cases hx : x ∈ boundaryHalfBall r
    · have hxD : x + graphAppendN z 0 ∈ D := (boundary_halfBall_translate_mem z x r).mpr hx
      simp only [indicator_of_mem hxD, indicator_of_mem hx]
    · have hxD : x + graphAppendN z 0 ∉ D :=
        fun hh => hx ((boundary_halfBall_translate_mem z x r).mp hh)
      simp only [indicator_of_notMem hxD, indicator_of_notMem hx]
  rw [he, integral_indicator (isOpen_boundaryHalfBall r).measurableSet,
    integral_indicator (isOpen_ball.inter boundary_holder_open_upper).measurableSet] at h
  exact h

lemma boundary_small_translate_ball_subset {z : EuclideanSpace ℝ (Fin 2)}
    (hz : ‖graphAppendN z 0‖ < 3 / 4) {r : ℝ} (hr : r ≤ 1 / 8) :
    MapsTo (fun x : EuclideanSpace ℝ (Fin 3) => x + graphAppendN z 0) (ball 0 r) (ball 0 1) := by
  intro x hx
  have hx' : ‖x‖ < r := by simpa only [mem_ball, dist_zero_right] using hx
  have hh := norm_add_le x (graphAppendN z 0)
  change dist (x + graphAppendN z 0) 0 < 1
  rw [dist_zero_right]
  linarith

lemma boundary_small_translate_halfBall_subset {z : EuclideanSpace ℝ (Fin 2)}
    (hz : ‖graphAppendN z 0‖ < 3 / 4) {r : ℝ} (hr : r ≤ 1 / 8) :
    MapsTo (fun x : EuclideanSpace ℝ (Fin 3) => x + graphAppendN z 0)
      (boundaryHalfBall r) (boundaryHalfBall 1) := by
  intro x hx
  refine ⟨boundary_small_translate_ball_subset hz hr hx.1, ?_⟩
  simpa only [mem_ofPred_eq, PiLp.add_apply, graphAppendN_last, add_zero] using hx.2

/-- The original closed-half-ball Hölder data yield uniform radial data at each
interior tangential center, preserving the genuine weak trace. -/
theorem boundary_translated_radialData_of_holder {a lam cap HA HG R : ℝ}
    (ha : 0 ≤ a) (hHG : 0 ≤ HG) (hR : 0 < R) (hRsmall : R ≤ 1 / 8)
    (z : EuclideanSpace ℝ (Fin 2)) (hz : ‖graphAppendN z 0‖ < 3 / 4)
    {u : EuclideanSpace ℝ (Fin 3) → ℝ}
    {F G : EuclideanSpace ℝ (Fin 3) → EuclideanSpace ℝ (Fin 3)}
    {A : EuclideanSpace ℝ (Fin 3) → EuclideanSpace ℝ (Fin 3) →L[ℝ]
      EuclideanSpace ℝ (Fin 3)}
    (hA : ContinuousOn A (closure (boundaryHalfBall 1)))
    (hG : ContinuousOn G (closure (boundaryHalfBall 1)))
    (hbA : ∀ x ∈ closure (boundaryHalfBall 1), ‖A x‖ ≤ cap)
    (hell : ∀ x ∈ closure (boundaryHalfBall 1), ∀ ξ,
      lam * ‖ξ‖ ^ 2 ≤ inner ℝ (A x ξ) ξ)
    (hHA : ∀ x ∈ closure (boundaryHalfBall 1), ∀ y ∈ closure (boundaryHalfBall 1),
      ‖A x - A y‖ ≤ HA * dist x y ^ a)
    (hHG' : ∀ x ∈ closure (boundaryHalfBall 1), ∀ y ∈ closure (boundaryHalfBall 1),
      ‖G x - G y‖ ≤ HG * dist x y ^ a)
    (hu : HasH1GradientOn u F (boundaryHalfBall 1))
    (hT : HasZeroFlatTraceOn u F (ball 0 1))
    (hw : IsWeakDivergenceEquationOn A F G (boundaryHalfBall 1)) :
    BoundaryHolderRadialData a lam cap HA HG R
      (fun x => u (x + graphAppendN z 0)) (fun x => F (x + graphAppendN z 0))
      (fun x => G (x + graphAppendN z 0)) (fun x => A (x + graphAppendN z 0)) := by
  let c := graphAppendN z 0
  have hmap := boundary_small_translate_halfBall_subset hz hRsmall
  have hmapcl := hmap.closure_of_continuousOn
    (continuous_id.add continuous_const).continuousOn
  apply boundary_radialData_of_holder ha hHG hR
  · exact hA.comp (continuous_id.add continuous_const).continuousOn hmapcl
  · exact hG.comp (continuous_id.add continuous_const).continuousOn hmapcl
  · exact fun x hx => hbA _ (hmapcl hx)
  · exact fun x hx => hell _ (hmapcl hx)
  · intro x hx y hy
    simpa only [dist_add_right] using hHA _ (hmapcl hx) _ (hmapcl hy)
  · intro x hx y hy
    simpa only [dist_add_right] using hHG' _ (hmapcl hx) _ (hmapcl hy)
  · exact hu.translate (isOpen_boundaryHalfBall 1) (isOpen_boundaryHalfBall R) c
      (fun x hx => hmap hx)
  · exact hT.translate z (fun x hx => boundary_small_translate_ball_subset hz hRsmall hx)
  · exact hw.boundary_translate c (fun x hx => hmap hx)

end LiquidDrop

module

public import NoCompromise.Elliptic.BoundaryHolderComparisonBounds

@[expose] public section

/-! Genuine radial boundary equation data. These are weaker than full Hölder
hypotheses: only the coefficient and datum oscillations about the boundary
center are recorded, together with the actual H¹ solution and zero trace. -/

noncomputable section
open MeasureTheory Filter Metric Set InnerProductSpace
open scoped ENNReal NNReal Topology Gradient RealInnerProductSpace
namespace LiquidDrop

/-- All PDE and trace fields are the previously defined actual notions. -/
structure BoundaryHolderRadialData (a lam cap HA HG R : ℝ)
    (u : EuclideanSpace ℝ (Fin 3) → ℝ)
    (F G : EuclideanSpace ℝ (Fin 3) → EuclideanSpace ℝ (Fin 3))
    (A : EuclideanSpace ℝ (Fin 3) → EuclideanSpace ℝ (Fin 3) →L[ℝ]
      EuclideanSpace ℝ (Fin 3)) : Prop where
  h1 : HasH1GradientOn u F (boundaryHalfBall R)
  zero_trace : HasZeroFlatTraceOn u F (ball 0 R)
  equation : IsWeakDivergenceEquationOn A F G (boundaryHalfBall R)
  coefficient_measurable : AEStronglyMeasurable A (volume.restrict (boundaryHalfBall R))
  coefficient_bound : ∀ᵐ x ∂volume.restrict (boundaryHalfBall R), ‖A x‖ ≤ cap
  datum_memLp : MemLp G 2 (volume.restrict (boundaryHalfBall R))
  elliptic_at_zero : ∀ ξ, lam * ‖ξ‖ ^ 2 ≤ inner ℝ (A 0 ξ) ξ
  coefficient_bound_at_zero : ‖A 0‖ ≤ cap
  coefficient_modulus : ∀ᵐ x ∂volume.restrict (boundaryHalfBall R),
    ‖A x - A 0‖ ≤ HA * ‖x‖ ^ a
  datum_modulus : ∀ᵐ x ∂volume.restrict (boundaryHalfBall R), ‖G x - G 0‖ ≤ HG * ‖x‖ ^ a

namespace BoundaryHolderRadialData
variable {a lam cap HA HG R : ℝ}
variable {u : EuclideanSpace ℝ (Fin 3) → ℝ}
variable {F G : EuclideanSpace ℝ (Fin 3) → EuclideanSpace ℝ (Fin 3)}
variable {A : EuclideanSpace ℝ (Fin 3) → EuclideanSpace ℝ (Fin 3) →L[ℝ]
  EuclideanSpace ℝ (Fin 3)}

lemma mono (h : BoundaryHolderRadialData a lam cap HA HG R u F G A)
    {r : ℝ} (hr : r ≤ R) : BoundaryHolderRadialData a lam cap HA HG r u F G A := by
  have hs := boundaryHalfBall_mono hr
  have hm := Measure.restrict_mono hs (le_rfl (a := volume))
  exact ⟨h.h1.mono hs, h.zero_trace.mono (ball_subset_ball hr), h.equation.mono hs,
    h.coefficient_measurable.mono_measure hm, ae_mono hm h.coefficient_bound,
    h.datum_memLp.mono_measure hm, h.elliptic_at_zero, h.coefficient_bound_at_zero,
    ae_mono hm h.coefficient_modulus, ae_mono hm h.datum_modulus⟩

lemma oscillation_bounds (h : BoundaryHolderRadialData a lam cap HA HG R u F G A)
    (ha : 0 ≤ a) (hHA : 0 ≤ HA) (hHG : 0 ≤ HG) :
    (∀ᵐ x ∂volume.restrict (boundaryHalfBall R), ‖A x - A 0‖ ≤ HA * R ^ a) ∧
    (∀ᵐ x ∂volume.restrict (boundaryHalfBall R), ‖G x - G 0‖ ≤ HG * R ^ a) := by
  have hp : ∀ᵐ x ∂volume.restrict (boundaryHalfBall R), ‖x‖ ^ a ≤ R ^ a := by
    filter_upwards [ae_restrict_mem (isOpen_boundaryHalfBall R).measurableSet] with x hx
    apply Real.rpow_le_rpow (norm_nonneg _) _ ha
    exact (show ‖x‖ < R by simpa only [mem_ball, dist_zero_right] using hx.1).le
  constructor
  · filter_upwards [h.coefficient_modulus, hp] with x hx hy
    exact hx.trans (mul_le_mul_of_nonneg_left hy hHA)
  · filter_upwards [h.datum_modulus, hp] with x hx hy
    exact hx.trans (mul_le_mul_of_nonneg_left hy hHG)

lemma energy_mono (h : BoundaryHolderRadialData a lam cap HA HG R u F G A)
    {s r : ℝ} (hsr : s ≤ r) (hr : r ≤ R) :
    (∫ x in boundaryHalfBall s, ‖F x‖ ^ 2) ≤ ∫ x in boundaryHalfBall r, ‖F x‖ ^ 2 :=
  setIntegral_mono_set (h.mono hr).h1.memLp_gradient.norm.integrable_sq
    (Eventually.of_forall fun _ => sq_nonneg _)
    (Eventually.of_forall (boundaryHalfBall_mono hsr))

end BoundaryHolderRadialData
end LiquidDrop

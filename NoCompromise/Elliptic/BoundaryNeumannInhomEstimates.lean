module

public import NoCompromise.Elliptic.BoundaryNeumannInhomPrimitive
public import NoCompromise.Elliptic.BoundaryNeumannInhomSlicing

@[expose] public section

/-!
The corrected datum has a quantitative Hölder bound once the corresponding
bounds for the gradient of the explicit quotient lift have been supplied.
This is an auxiliary estimate, not an assumption-free construction of those bounds.
-/

noncomputable section
open MeasureTheory Filter Metric Set InnerProductSpace
open scoped ENNReal NNReal Topology Gradient RealInnerProductSpace
namespace LiquidDrop

lemma boundaryNeumannInhomDatum_holder {a cap HA Bf Hf Hh Bq Hq : ℝ}
    (ha : 0 ≤ a) (ha1 : a ≤ 1) (hcap : 0 ≤ cap) (hHA : 0 ≤ HA)
    (hBf : 0 ≤ Bf) (hHf : 0 ≤ Hf) (hHh : 0 ≤ Hh)
    {A : EuclideanSpace ℝ (Fin 3) → EuclideanSpace ℝ (Fin 3) →L[ℝ]
      EuclideanSpace ℝ (Fin 3)}
    {f : EuclideanSpace ℝ (Fin 3) → ℝ} {h : EuclideanSpace ℝ (Fin 2) → ℝ}
    (hbA : ∀ x ∈ closure (boundaryHalfBall 1), ‖A x‖ ≤ cap)
    (hhA : ∀ x ∈ closure (boundaryHalfBall 1), ∀ y ∈ closure (boundaryHalfBall 1),
      ‖A x - A y‖ ≤ HA * dist x y ^ a)
    (hf : ContinuousOn f (closure (boundaryHalfBall 1)))
    (hbf : ∀ x ∈ closure (boundaryHalfBall 1), ‖f x‖ ≤ Bf)
    (hhf : ∀ x ∈ closure (boundaryHalfBall 1), ∀ y ∈ closure (boundaryHalfBall 1),
      ‖f x - f y‖ ≤ Hf * dist x y ^ a)
    (hhh : ∀ x ∈ closedBall (0 : EuclideanSpace ℝ (Fin 2)) 1, ∀ y ∈ closedBall 0 1,
      ‖h x - h y‖ ≤ Hh * dist x y ^ a)
    (hbq : ∀ x ∈ closure (boundaryHalfBall 1),
      ‖gradient (boundaryNeumannLift h (boundaryNeumannNormalCoefficient A)) x‖ ≤ Bq)
    (hhq : ∀ x ∈ closure (boundaryHalfBall 1), ∀ y ∈ closure (boundaryHalfBall 1),
      ‖gradient (boundaryNeumannLift h (boundaryNeumannNormalCoefficient A)) x -
        gradient (boundaryNeumannLift h (boundaryNeumannNormalCoefficient A)) y‖ ≤
          Hq * dist x y ^ a)
    {x y : EuclideanSpace ℝ (Fin 3)} (hx : x ∈ closure (boundaryHalfBall 1))
    (hy : y ∈ closure (boundaryHalfBall 1)) :
    ‖boundaryNeumannInhomDatum A f h x - boundaryNeumannInhomDatum A f h y‖ ≤
      (Hf + 2 * Bf + Hh + cap * Hq + HA * Bq) * dist x y ^ a := by
  let Q := gradient (boundaryNeumannLift h (boundaryNeumannNormalCoefficient A))
  have hprod : ‖A x (Q x) - A y (Q y)‖ ≤
      (cap * Hq + HA * Bq) * dist x y ^ a := by
    have he : A x (Q x) - A y (Q y) =
        A x (Q x - Q y) + (A x - A y) (Q y) := by
      rw [map_sub, sub_apply]
      abel
    have h1 : ‖A x (Q x - Q y)‖ ≤ cap * (Hq * dist x y ^ a) :=
      ((A x).le_opNorm _).trans
        (mul_le_mul (hbA x hx) (hhq x hx y hy) (norm_nonneg _) hcap)
    have h2 : ‖(A x - A y) (Q y)‖ ≤ (HA * dist x y ^ a) * Bq :=
      ((A x - A y).le_opNorm _).trans
        (mul_le_mul (hhA x hx y hy) (hbq y hy) (norm_nonneg _) (by positivity))
    rw [he]
    exact (norm_add_le _ _).trans ((add_le_add h1 h2).trans_eq (by ring))
  have hp {z : EuclideanSpace ℝ (Fin 3)} (hz : z ∈ closure (boundaryHalfBall 1)) :
      graphProjectionN 2 z ∈ closedBall (0 : EuclideanSpace ℝ (Fin 2)) 1 := by
    simp only [mem_closedBall, dist_zero_right]
    exact (boundary_neumann_norm_projection_le z).trans (boundary_neumann_closed_norm_le hz)
  have hd : dist (graphProjectionN 2 x) (graphProjectionN 2 y) ≤ dist x y := by
    simpa only [dist_eq_norm, map_sub] using boundary_neumann_norm_projection_le (x - y)
  have hnormal : ‖(h (graphProjectionN 2 x) - h (graphProjectionN 2 y)) •
      EuclideanSpace.single (Fin.last 2) (1 : ℝ)‖ ≤ Hh * dist x y ^ a := by
    rw [norm_smul, PiLp.norm_single, norm_one, mul_one]
    exact (hhh _ (hp hx) _ (hp hy)).trans
      (mul_le_mul_of_nonneg_left (Real.rpow_le_rpow dist_nonneg hd ha) hHh)
  have he : boundaryNeumannInhomDatum A f h x - boundaryNeumannInhomDatum A f h y =
      (boundaryNeumannPrimitive f x - boundaryNeumannPrimitive f y) +
        (h (graphProjectionN 2 x) - h (graphProjectionN 2 y)) •
          EuclideanSpace.single (Fin.last 2) (1 : ℝ) - (A x (Q x) - A y (Q y)) := by
    simp only [boundaryNeumannInhomDatum, sub_smul, Q]
    abel
  rw [he]
  have hP := boundaryNeumannPrimitive_holder ha ha1 hBf hHf hf hbf hhf hx hy
  calc
    _ ≤ (‖boundaryNeumannPrimitive f x - boundaryNeumannPrimitive f y‖ +
        ‖(h (graphProjectionN 2 x) - h (graphProjectionN 2 y)) •
          EuclideanSpace.single (Fin.last 2) (1 : ℝ)‖) + ‖A x (Q x) - A y (Q y)‖ :=
      (norm_sub_le _ _).trans (add_le_add (norm_add_le _ _) le_rfl)
    _ ≤ _ := by nlinarith

end LiquidDrop

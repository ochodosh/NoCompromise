import NoCompromise.Elliptic.CkHolderAlgebra
import NoCompromise.Elliptic.BoundaryNeumannQuotient

/-!
# The levels of the smooth boundary Neumann iteration (`thm:boundary-neumann`)

`BoundaryNeumannCkLevel k` is the statement of the `k`-th level of the higher-regularity
iteration for the homogeneous flat conormal problem: a smooth coefficient `A` and a
`C^{k+1,α}` datum `H` and solution `w` on a neighbourhood of the closed half ball of radius
`R ≤ 1`, with vanishing cross coefficients, `H₃ = 0` and `∂₃w = 0` on the flat face, give
`w ∈ C^{k+2,α}` on the half ball of radius `(3/8) (1/2)ᵏ R`.
-/

noncomputable section
open MeasureTheory Filter Metric Set InnerProductSpace
open scoped ENNReal Topology Gradient RealInnerProductSpace
namespace LiquidDrop

/-- The `k`-th level of the smooth boundary Neumann iteration on flat half balls. -/
def BoundaryNeumannCkLevel (k : ℕ) : Prop :=
  ∀ {α lam cap R : ℝ}, 0 < α → α < 1 → 0 < lam → 0 < R → R ≤ 1 →
    ∀ {U : Set (EuclideanSpace ℝ (Fin 3))}, IsOpen U → closure (boundaryHalfBall R) ⊆ U →
    ∀ {A : EuclideanSpace ℝ (Fin 3) → EuclideanSpace ℝ (Fin 3) →L[ℝ] EuclideanSpace ℝ (Fin 3)}
      {H : EuclideanSpace ℝ (Fin 3) → EuclideanSpace ℝ (Fin 3)}
      {w : EuclideanSpace ℝ (Fin 3) → ℝ},
    ContDiffOn ℝ (⊤ : ℕ∞) A U →
    HasCkHolderOn (k + 1) α H U (closure (boundaryHalfBall R)) →
    HasCkHolderOn (k + 1) α w U (closure (boundaryHalfBall R)) →
    (∀ x ∈ closure (boundaryHalfBall R), ‖A x‖ ≤ cap) →
    (∀ x ∈ closure (boundaryHalfBall R), ∀ v, lam * ‖v‖ ^ 2 ≤ inner ℝ (A x v) v) →
    (∀ x ∈ closure (boundaryHalfBall R), x (Fin.last 2) = 0 →
      ∀ j : Fin 3, j ≠ Fin.last 2 →
        A x (EuclideanSpace.single j 1) (Fin.last 2) = 0 ∧
        A x (EuclideanSpace.single (Fin.last 2) 1) j = 0) →
    (∀ x ∈ closure (boundaryHalfBall R), x (Fin.last 2) = 0 → H x (Fin.last 2) = 0) →
    (∀ x ∈ closure (boundaryHalfBall R), x (Fin.last 2) = 0 →
      gradient w x (Fin.last 2) = 0) →
    IsBoundaryNeumannEquationOn A (gradient w) H R →
    HasCkHolderOn (k + 2) α w (boundaryHalfBall (3 / 8 * (1 / 2) ^ k * R))
      (boundaryHalfBall (3 / 8 * (1 / 2) ^ k * R))

end LiquidDrop

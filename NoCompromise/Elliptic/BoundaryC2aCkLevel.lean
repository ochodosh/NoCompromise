module

public import NoCompromise.Elliptic.CkHolderAlgebra
public import NoCompromise.Elliptic.BoundaryC2aDifferentiate

@[expose] public section

/-!
# The levels of the Dirichlet boundary higher-regularity iteration (`thm:boundary-C2a`)

`BoundaryDirichletCkLevel k` is the statement of the `k`-th level of the higher-regularity
iteration for the flat Dirichlet problem `div(A ∇u) = div G` in the half ball with `u = φ` on
the flat face: a smooth coefficient `A` and boundary datum `φ`, and a `C^{k+1,α}` datum `G`
and solution `u` on a neighbourhood of the closed half ball of radius `R ≤ 1`, give
`u ∈ C^{k+2,α}` on the half ball of radius `(3/8) (1/2)ᵏ R`.
-/

noncomputable section
open MeasureTheory Filter Metric Set InnerProductSpace
open scoped ENNReal Topology Gradient RealInnerProductSpace
namespace LiquidDrop

/-- The `k`-th level of the Dirichlet boundary higher-regularity iteration on flat half balls. -/
def BoundaryDirichletCkLevel (k : ℕ) : Prop :=
  ∀ {α lam cap R : ℝ}, 0 < α → α < 1 → 0 < lam → 0 < R → R ≤ 1 →
    ∀ {U : Set (EuclideanSpace ℝ (Fin 3))}, IsOpen U → closure (boundaryHalfBall R) ⊆ U →
    ∀ {A : EuclideanSpace ℝ (Fin 3) → EuclideanSpace ℝ (Fin 3) →L[ℝ] EuclideanSpace ℝ (Fin 3)}
      {G : EuclideanSpace ℝ (Fin 3) → EuclideanSpace ℝ (Fin 3)}
      {u φ : EuclideanSpace ℝ (Fin 3) → ℝ},
    ContDiffOn ℝ (⊤ : ℕ∞) A U → ContDiff ℝ (⊤ : ℕ∞) φ →
    HasCkHolderOn (k + 1) α G U (closure (boundaryHalfBall R)) →
    HasCkHolderOn (k + 1) α u U (closure (boundaryHalfBall R)) →
    (∀ x ∈ closure (boundaryHalfBall R), ‖A x‖ ≤ cap) →
    (∀ x ∈ closure (boundaryHalfBall R), ∀ v, lam * ‖v‖ ^ 2 ≤ inner ℝ (A x v) v) →
    (∀ x ∈ closure (boundaryHalfBall R), x (Fin.last 2) = 0 → u x = φ x) →
    IsWeakDivergenceEquationOn A (gradient u) G (boundaryHalfBall R) →
    HasCkHolderOn (k + 2) α u (boundaryHalfBall (3 / 8 * (1 / 2) ^ k * R))
      (boundaryHalfBall (3 / 8 * (1 / 2) ^ k * R))

end LiquidDrop

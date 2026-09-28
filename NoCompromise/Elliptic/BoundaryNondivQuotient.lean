import NoCompromise.Elliptic.NondivSchauderDifferenceEquation
import NoCompromise.Elliptic.BoundaryHolderDecayIntegrals

/-!
# Tangential difference quotients on the flat half ball

First analytic step of `thm:boundary-nondiv` (and of `thm:boundary-C2a`): for a
tangential direction `e_i` (`i ≠ 3`), translation by `h e_i` with `|h| ≤ R - r` maps
`B_r^+` into `B_R^+`, so the exact difference-quotient equation of the interior
nondivergence Schauder argument holds on the smaller half ball. Normal difference
quotients are not available (they would leave the half ball), which is why the
normal second derivative is recovered algebraically (`Elliptic/BoundaryC2.lean`).
-/

noncomputable section
open MeasureTheory Metric Set InnerProductSpace
namespace LiquidDrop

/-- Tangential translations by at most `R - r` map `B_r^+` into `B_R^+`. -/
lemma boundaryHalfBall_add_tangential {r R h : ℝ} {i : Fin 3} (hi : i ≠ Fin.last 2)
    (hh : |h| ≤ R - r) {x : EuclideanSpace ℝ (Fin 3)} (hx : x ∈ boundaryHalfBall r) :
    x + h • EuclideanSpace.single i (1 : ℝ) ∈ boundaryHalfBall R := by
  obtain ⟨hxb, hxl⟩ := hx
  refine ⟨?_, ?_⟩
  · rw [mem_ball_zero_iff] at hxb ⊢
    calc ‖x + h • EuclideanSpace.single i (1 : ℝ)‖
        ≤ ‖x‖ + ‖h • EuclideanSpace.single i (1 : ℝ)‖ := norm_add_le _ _
      _ = ‖x‖ + |h| := by
          rw [norm_smul, PiLp.norm_single, norm_one, mul_one, Real.norm_eq_abs]
      _ < r + (R - r) := add_lt_add_of_lt_of_le hxb hh
      _ = R := by ring
  · have hne : (2 : Fin 3) ≠ i := by
      intro h'
      apply hi
      rw [← h']
      rfl
    change 0 < (x + h • EuclideanSpace.single i (1 : ℝ)) (Fin.last 2)
    simpa [PiLp.add_apply, PiLp.smul_apply, PiLp.single_apply, hne] using hxl

/-- **Tangential difference quotients on the half ball.** If `div (A D) = g` weakly on
`B_R^+` with continuous `A`, `D`, `g`, then for every tangential direction `e_i` and
`|h| ≤ R - r` the difference quotients satisfy on `B_r^+` the exact equation
`div (A(· + h e_i) δ_h D + (δ_h A) D) = δ_h g`, tested against smooth compactly supported
functions in the open half ball. -/
theorem IsWeakScalarDivergenceEquationOn.boundary_tangentialDifferenceQuotient
    {A : EuclideanSpace ℝ (Fin 3) → EuclideanSpace ℝ (Fin 3) →L[ℝ] EuclideanSpace ℝ (Fin 3)}
    {D : EuclideanSpace ℝ (Fin 3) → EuclideanSpace ℝ (Fin 3)}
    {g : EuclideanSpace ℝ (Fin 3) → ℝ} {r R : ℝ}
    (he : IsWeakScalarDivergenceEquationOn A D g (boundaryHalfBall R))
    (hA : ContinuousOn A (boundaryHalfBall R)) (hD : ContinuousOn D (boundaryHalfBall R))
    (hg : ContinuousOn g (boundaryHalfBall R)) (hrR : r ≤ R)
    {i : Fin 3} (hi : i ≠ Fin.last 2) {h : ℝ} (hh : |h| ≤ R - r) :
    ∀ φ : EuclideanSpace ℝ (Fin 3) → ℝ, ContDiff ℝ (⊤ : ℕ∞) φ →
      HasCompactSupport φ → tsupport φ ⊆ boundaryHalfBall r →
      (∫ x, inner ℝ
        (A (x + h • EuclideanSpace.single i 1) (LiquidDrop.coordinateDifferenceQuotient i h D x) +
          LiquidDrop.coordinateDifferenceQuotient i h A x (D x)) (gradient φ x)) =
        -(∫ x, φ x * LiquidDrop.coordinateDifferenceQuotient i h g x) :=
  he.coordinateDifferenceQuotient (isOpen_boundaryHalfBall R) (isOpen_boundaryHalfBall r)
    hA hD hg (boundaryHalfBall_mono hrR) i h
    (fun _ hx => boundaryHalfBall_add_tangential hi hh hx)

end LiquidDrop

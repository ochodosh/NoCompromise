module

public import NoCompromise.Elliptic.QuasilinearCoordinate
public import NoCompromise.Elliptic.QuasilinearNorm
public import NoCompromise.Elliptic.NondivSchauderClassical

@[expose] public section

/-! Blueprint `thm:quasilinear-schauder`. The nonlinear flux has genuine C²
regularity, the initial solution is only C¹,α, and the equation is tested against
smooth compact functions. The estimates produce actual C²,α regularity. Bounds
on DA and D²A on the closed gradient ball make the dependence on the C² flux
norm explicit; no symmetry and no prior second derivative of f is assumed. -/

noncomputable section
open MeasureTheory Filter Metric Set InnerProductSpace
open scoped ENNReal NNReal Topology Gradient RealInnerProductSpace
namespace LiquidDrop
set_option maxSynthPendingDepth 8

/-- Full quasilinear Schauder, with constants fixed before all equation data.
This includes the planar blueprint and also the three-dimensional case. The
full sum norm retains coefficient one on the original essential uniform norm. -/
theorem quasilinear_schauder {n : ℕ} (hn0 : 0 < n) (hn : n < 4)
    {a lam cap M B N H : ℝ} (ha : 0 < a) (ha1 : a < 1)
    (hlam : 0 < lam) (hlamcap : lam ≤ cap)
    (hM : 0 ≤ M) (hB : 0 ≤ B) (hN : 0 ≤ N) (hH : 0 ≤ H) :
    ∃ C > 0, ∀ (A : EuclideanSpace ℝ (Fin n) → EuclideanSpace ℝ (Fin n))
      (f g : EuclideanSpace ℝ (Fin n) → ℝ),
      ContDiff ℝ 2 A → HasC1HolderOn a f (ball 0 1) →
      HasFiniteHolderNormOn a g (ball 0 1) → holderNorm a g (ball 0 1) ≤ N →
      (∀ x ∈ ball 0 (1 : ℝ), ‖gradient f x‖ ≤ M) →
      holderSeminorm a (gradient f) (ball 0 1) ≤ H →
      (∀ p ∈ closedBall (0 : EuclideanSpace ℝ (Fin n)) M, ‖fderiv ℝ A p‖ ≤ cap) →
      (∀ p ∈ closedBall (0 : EuclideanSpace ℝ (Fin n)) M,
        ‖fderiv ℝ (fderiv ℝ A) p‖ ≤ B) →
      (∀ p ∈ closedBall (0 : EuclideanSpace ℝ (Fin n)) M, ∀ ξ,
        lam * ‖ξ‖ ^ 2 ≤ inner ℝ (fderiv ℝ A p ξ) ξ) →
      IsWeakQuasilinearEquationOn A f g (ball 0 1) →
      HasC1HolderOn a (gradient f) (ball 0 (1 / 2)) ∧
        nondivC1HolderNorm a (gradient f) (ball 0 (1 / 2)) ≤ C ∧
        HasC2HolderOn a f (ball 0 (1 / 2)) ∧
        schauderC2HolderNorm a f (ball 0 (1 / 2)) ≤
          lpNorm f ∞ (volume.restrict (ball 0 1)) + C := by
  obtain ⟨L, hL, hcoordinate⟩ := quasilinear_coordinate_estimate hn0 hn ha ha1
    hlam hlamcap hM hB hN hH
  let K := (n : ℝ) * L
  have hK : 0 ≤ K := mul_nonneg (Nat.cast_nonneg _) hL.le
  refine ⟨2 * M + H + 2 * K + 1, by positivity, ?_⟩
  intro A f g hA hf hg hgN hfM hfH hcap hb hell he
  have hcoord := hcoordinate A f g hA hf hg hgN hfM hfH hcap hb hell he
  have hfsmall : ContDiffOn ℝ 1 f (ball 0 (1 / 2 : ℝ)) :=
    hf.contDiff.mono (ball_subset_ball (by norm_num : (1 / 2 : ℝ) ≤ 1))
  obtain ⟨hc, _, _, _, hessb, hessH⟩ := nondiv_hessian_holder_of_coordinate_derivatives hL.le
    isOpen_ball hfsmall (fun i => (hcoord i).1) (fun i => (hcoord i).2.1)
    (fun i x hx y hy => by simpa only [dist_eq_norm] using (hcoord i).2.2 x hx y hy)
  obtain ⟨hgrad, hgradb, hC2, hC2b⟩ := quasilinear_norm_bounds ha ha1 hM hH hK
    hf hc hfM hfH hessb
    (fun x hx y hy => by simpa only [dist_eq_norm] using hessH x hx y hy)
  refine ⟨hgrad, hgradb.trans ?_, hC2, hC2b.trans ?_⟩ <;> linarith

end LiquidDrop

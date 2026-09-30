module

public import NoCompromise.Elliptic.QuasilinearDifferentiated
public import NoCompromise.Elliptic.QuasilinearCampanatoInterior

@[expose] public section

/-! The proved Campanato estimate applies to the constructed derivative
equations. This gives actual C¹,α regularity of every coordinate derivative,
with constants fixed before the nonlinear flux and solution data. -/

noncomputable section
open MeasureTheory Filter Metric Set InnerProductSpace
open scoped ENNReal NNReal Topology Gradient RealInnerProductSpace
namespace LiquidDrop
set_option maxSynthPendingDepth 8

/-- Uniform actual C¹,α estimates for each first derivative of a quasilinear
solution, on the full half-radius ball. -/
theorem quasilinear_coordinate_estimate {n : ℕ} (hn0 : 0 < n) (hn : n < 4)
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
      ∀ i : Fin n,
        ContDiffOn ℝ 1 (fun x => fderiv ℝ f x (EuclideanSpace.single i 1))
          (ball 0 (1 / 2)) ∧
        (∀ x ∈ ball 0 (1 / 2 : ℝ),
          ‖gradient (fun y => fderiv ℝ f y (EuclideanSpace.single i 1)) x‖ ≤ C) ∧
        ∀ x ∈ ball 0 (1 / 2 : ℝ), ∀ y ∈ ball 0 (1 / 2 : ℝ),
          ‖gradient (fun z => fderiv ℝ f z (EuclideanSpace.single i 1)) x -
            gradient (fun z => fderiv ℝ f z (EuclideanSpace.single i 1)) y‖ ≤ C * dist x y ^ a := by
  obtain ⟨C₀, hC₀, hlinear⟩ := quasilinear_exists_coordinate_linearized
    (n := n) ha hlam hlamcap hM hB hN
  obtain ⟨C, hC, hcamp⟩ := quasilinear_campanato_interior hn0 hn ha ha1 hlam
    (hlam.le.trans hlamcap) (mul_nonneg hB hH) hN (sq_nonneg C₀)
  refine ⟨C, hC, ?_⟩
  intro A f g hA hf hg hgN hfM hfH hcap hb hell he i
  obtain ⟨G, hG, hGb, hEq⟩ := hlinear A f g hA hf hg hgN hfM hcap hb hell he i
  let V : Set (EuclideanSpace ℝ (Fin n)) := ball 0 (3 / 4)
  have hVU : V ⊆ ball 0 (1 : ℝ) := ball_subset_ball (by norm_num : (3 / 4 : ℝ) ≤ 1)
  have hFM : ∀ x ∈ ball 0 (1 : ℝ), gradient f x ∈ closedBall 0 M := by
    intro x hx
    simpa only [mem_closedBall, dist_zero_right] using hfM x hx
  have hFhold : ∀ x ∈ ball 0 (1 : ℝ), ∀ y ∈ ball 0 (1 : ℝ),
      ‖gradient f x - gradient f y‖ ≤ H * dist x y ^ a := by
    intro x hx y hy
    apply (hf.gradient_holder.1.nondiv_norm_sub_le hx hy).trans
    simpa only [dist_eq_norm] using
      mul_le_mul_of_nonneg_right hfH (Real.rpow_nonneg (norm_nonneg (x - y)) a)
  have hDAc : Continuous (fderiv ℝ A) :=
    (hA.of_le (by norm_num : (1 : WithTop ℕ∞) ≤ 2)).continuous_fderiv one_ne_zero
  have hAc : ContinuousOn (fun x => fderiv ℝ A (gradient f x)) V :=
    hDAc.comp_continuousOn
      ((continuousOn_gradient_of_contDiffOn isOpen_ball hf.contDiff).mono hVU)
  have hgc : ContinuousOn (fun x => g x • EuclideanSpace.single i (1 : ℝ)) V :=
    ((hg.nondiv_continuousOn ha).mono hVU).smul continuousOn_const
  have huc : ContinuousOn (fun x => fderiv ℝ f x (EuclideanSpace.single i 1)) V :=
    (hf.derivative_holder.nondiv_continuousOn ha).clm_apply continuousOn_const |>.mono hVU
  have hsemig : holderSeminorm a g (ball 0 1) ≤ N :=
    (le_add_of_nonneg_left (holderUniformNorm_nonneg hg.uniform_bounded)).trans hgN
  have hghold : ∀ x ∈ V, ∀ y ∈ V,
      ‖g x • EuclideanSpace.single i (1 : ℝ) - g y • EuclideanSpace.single i (1 : ℝ)‖ ≤
        N * dist x y ^ a := by
    intro x hx y hy
    rw [← sub_smul, norm_smul, PiLp.norm_single, norm_one, mul_one]
    apply (hg.nondiv_norm_sub_le (hVU hx) (hVU hy)).trans
    simpa only [dist_eq_norm] using
      mul_le_mul_of_nonneg_right hsemig (Real.rpow_nonneg (norm_nonneg (x - y)) a)
  have henergy : (∫ x in V, ‖G x‖ ^ 2) ≤ C₀ ^ 2 := by
    rw [← lpNorm_two_sq_eq_integral_norm_sq hG.memLp_gradient]
    exact pow_le_pow_left₀ lpNorm_nonneg hGb 2
  have hc := hcamp (fun x => fderiv ℝ A (gradient f x))
    (fun x => g x • EuclideanSpace.single i 1) G
    (fun x => fderiv ℝ f x (EuclideanSpace.single i 1)) hAc hgc huc
    (fun x hx => hcap _ (hFM x (hVU hx)))
    (fun x hx => hell _ (hFM x (hVU hx)))
    (fun x hx y hy => quasilinear_linearized_coefficient_holder hA hB hb hFM hFhold
      (hVU hx) (hVU hy)) hghold hG hEq henergy
  exact ⟨hc.1, hc.2.2.1, hc.2.2.2⟩

end LiquidDrop

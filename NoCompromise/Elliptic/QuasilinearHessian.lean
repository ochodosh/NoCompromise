import NoCompromise.Elliptic.QuasilinearQuotientBounds
import NoCompromise.Elliptic.NondivSchauderHessian

/-! Actual weak second derivatives of the quasilinear solution are constructed
by H¹ weak compactness and strong convergence of first difference quotients.
The weak integral pairings needed for the linearized equation are retained. -/

noncomputable section
open MeasureTheory Filter Metric Set InnerProductSpace
open scoped ENNReal NNReal Topology Gradient RealInnerProductSpace
namespace LiquidDrop
set_option maxSynthPendingDepth 8

/-- The genuine first derivative acquires a weak gradient, with a uniform bound
independent of the zeroth-order size of the solution. -/
theorem quasilinear_exists_coordinate_h1_gradient {n : ℕ} {a lam cap M B N : ℝ}
    (ha : 0 < a) (hlam : 0 < lam) (hlamcap : lam ≤ cap)
    (hM : 0 ≤ M) (hB : 0 ≤ B) (hN : 0 ≤ N) :
    ∃ C > 0, ∀ (A : EuclideanSpace ℝ (Fin n) → EuclideanSpace ℝ (Fin n))
      (f g : EuclideanSpace ℝ (Fin n) → ℝ),
      ContDiff ℝ 2 A → HasC1HolderOn a f (ball 0 1) →
      HasFiniteHolderNormOn a g (ball 0 1) → holderNorm a g (ball 0 1) ≤ N →
      (∀ x ∈ ball 0 (1 : ℝ), ‖gradient f x‖ ≤ M) →
      (∀ p ∈ closedBall (0 : EuclideanSpace ℝ (Fin n)) M, ‖fderiv ℝ A p‖ ≤ cap) →
      (∀ p ∈ closedBall (0 : EuclideanSpace ℝ (Fin n)) M,
        ‖fderiv ℝ (fderiv ℝ A) p‖ ≤ B) →
      (∀ p ∈ closedBall (0 : EuclideanSpace ℝ (Fin n)) M, ∀ ξ,
        lam * ‖ξ‖ ^ 2 ≤ inner ℝ (fderiv ℝ A p ξ) ξ) →
      IsWeakQuasilinearEquationOn A f g (ball 0 1) →
      ∀ i : Fin n, ∃ G : EuclideanSpace ℝ (Fin n) → EuclideanSpace ℝ (Fin n),
        HasH1GradientOn (fun x => fderiv ℝ f x (EuclideanSpace.single i 1)) G
          (ball 0 (3 / 4)) ∧
        lpNorm G 2 (volume.restrict (ball 0 (3 / 4))) ≤ C ∧
        ∃ σ : ℕ → ℕ, StrictMono σ ∧
          ∀ P : EuclideanSpace ℝ (Fin n) → EuclideanSpace ℝ (Fin n),
            MemLp P 2 (volume.restrict (ball 0 (3 / 4))) →
            Tendsto (fun j => ∫ x in ball 0 (3 / 4), inner ℝ (P x)
              (coordinateDifferenceQuotient i (nondivQuotientStep (σ j)) (gradient f) x))
              atTop (𝓝 (∫ x in ball 0 (3 / 4), inner ℝ (P x) (G x))) := by
  obtain ⟨C, hC, hbound⟩ := quasilinear_quotient_h1_bound (n := n) ha hlam hlamcap hM hB hN
  refine ⟨C, hC, ?_⟩
  intro A f g hA hf hg hgN hfM hcap hb hell he i
  let V : Set (EuclideanSpace ℝ (Fin n)) := ball 0 (3 / 4)
  have hVU : V ⊆ ball 0 (1 : ℝ) := ball_subset_ball (by norm_num : (3 / 4 : ℝ) ≤ 1)
  have hVW : V ⊆ ball 0 (7 / 8 : ℝ) := ball_subset_ball (by norm_num : (3 / 4 : ℝ) ≤ 7 / 8)
  have hq (j : ℕ) := hbound A f g hA hf hg hgN hfM hcap hb hell he i
    (nondivQuotientStep j) (nondivQuotientStep_pos j).ne' (nondivQuotientStep_small j)
  have hDcont : ContinuousOn (fun x => fderiv ℝ f x (EuclideanSpace.single i 1)) V :=
    (hf.derivative_holder.nondiv_continuousOn ha).clm_apply continuousOn_const |>.mono hVU
  let : IsFiniteMeasure (volume.restrict V) :=
    ⟨by rw [Measure.restrict_apply_univ]; exact isBounded_ball.measure_lt_top⟩
  have hmD : MemLp (fun x => fderiv ℝ f x (EuclideanSpace.single i 1))
      2 (volume.restrict V) := by
    apply MemLp.of_bound (hDcont.aestronglyMeasurable measurableSet_ball) M
    filter_upwards [ae_restrict_mem measurableSet_ball] with x hx
    have ht := (fderiv ℝ f x).le_opNorm (EuclideanSpace.single i 1)
    simp only [PiLp.norm_single, norm_one, mul_one] at ht
    apply ht.trans
    simpa only [gradient, LinearIsometryEquiv.norm_map] using hfM x (hVU hx)
  have ht := nondiv_tendsto_coordinateDifferenceQuotient_L2 ha isOpen_ball measurableSet_ball
    (ne_of_lt isBounded_ball.measure_lt_top) hf i
    (fun j => (nondivQuotientStep_pos j).ne') tendsto_nondivQuotientStep
    (fun j x hx t ht => nondiv_segment_mem_unitBall i (nondivQuotientStep_small j) (hVW hx) ht)
  obtain ⟨G, hG, hGb, σ, hσ, hweak⟩ :=
    nondiv_hasH1GradientOn_of_bounded_approximants (fun j => (hq j).1) hmD
      (fun j => (hq j).2) ht
  refine ⟨G, hG, hGb, σ, hσ, ?_⟩
  intro P hP
  exact nondiv_tendsto_integral_inner_of_weakLp (fun j => (hq (σ j)).1.memLp_gradient)
    hG.memLp_gradient hP hweak

end LiquidDrop

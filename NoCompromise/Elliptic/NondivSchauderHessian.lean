module

public import NoCompromise.Elliptic.NondivSchauderQuotientBounds
public import NoCompromise.Elliptic.NondivSchauderConvergence
public import NoCompromise.Elliptic.NondivSchauderWeakLimit

@[expose] public section

/-!
# Construction of actual weak second derivatives

Uniformly bounded genuine H¹ quotients converge strongly to each actual first
derivative. Hilbert weak compactness constructs its weak gradient and preserves
the uniform estimate. Weak integral pairings are retained for the differentiated
equation; no second derivative or H² premise is introduced.
-/

noncomputable section
open MeasureTheory Filter Metric Set InnerProductSpace
open scoped ENNReal Topology Gradient RealInnerProductSpace
namespace LiquidDrop
set_option maxSynthPendingDepth 8

/-- One fixed sequence of nonzero admissible signed-quotient steps. -/
def nondivQuotientStep (j : ℕ) : ℝ := (1 / 32) / ((j : ℝ) + 1)

lemma nondivQuotientStep_pos (j : ℕ) : 0 < nondivQuotientStep j := by
  dsimp [nondivQuotientStep]
  positivity

lemma nondivQuotientStep_small (j : ℕ) : |nondivQuotientStep j| < 1 / 16 := by
  rw [abs_of_pos (nondivQuotientStep_pos j)]
  exact (div_le_self (by norm_num : (0 : ℝ) ≤ 1 / 32)
    (by linarith [Nat.cast_nonneg (α := ℝ) j])).trans_lt (by norm_num)

lemma tendsto_nondivQuotientStep : Tendsto nondivQuotientStep atTop (𝓝 0) := by
  change Tendsto (fun j : ℕ => (1 / 32 : ℝ) / ((j : ℝ) + 1)) atTop (𝓝 0)
  simpa only [mul_one_div, mul_zero] using!
    (tendsto_one_div_add_atTop_nhds_zero_nat (𝕜 := ℝ)).const_mul (1 / 32 : ℝ)

/-- Every actual coordinate derivative acquires a genuine weak gradient on
B₃/₄, with a linear norm bound and convergence of all L² integral pairings. -/
theorem nondiv_exists_coordinate_h1_gradient {n : ℕ} {α lam cap M : ℝ}
    (hα : 0 < α) (hlam : 0 < lam) (hlamcap : lam ≤ cap) (hM : 0 ≤ M) :
    ∃ C > 0, ∀ (A : EuclideanSpace ℝ (Fin n) →
        EuclideanSpace ℝ (Fin n) →L[ℝ] EuclideanSpace ℝ (Fin n))
      (b : EuclideanSpace ℝ (Fin n) → EuclideanSpace ℝ (Fin n))
      (z f : EuclideanSpace ℝ (Fin n) → ℝ),
      HasC1HolderOn α A (ball 0 1) → HasFiniteHolderNormOn α b (ball 0 1) →
      HasC1HolderOn α z (ball 0 1) → HasFiniteHolderNormOn α f (ball 0 1) →
      nondivC1HolderNorm α A (ball 0 1) ≤ M → holderNorm α b (ball 0 1) ≤ M →
      (∀ x ∈ ball 0 (1 : ℝ), ‖A x‖ ≤ cap) →
      (∀ x ∈ ball 0 (1 : ℝ), ∀ v, lam * ‖v‖ ^ 2 ≤ inner ℝ v (A x v)) →
      IsWeakNondivergenceEquationOn A b z f (ball 0 1) →
      ∀ i : Fin n, ∃ G : EuclideanSpace ℝ (Fin n) → EuclideanSpace ℝ (Fin n),
        HasH1GradientOn (fun x => fderiv ℝ z x (EuclideanSpace.single i 1)) G
          (ball 0 (3 / 4)) ∧
        lpNorm G 2 (volume.restrict (ball 0 (3 / 4))) ≤
          C * (nondivC1HolderNorm α z (ball 0 1) + holderNorm α f (ball 0 1)) ∧
        ∃ σ : ℕ → ℕ, StrictMono σ ∧
          ∀ P : EuclideanSpace ℝ (Fin n) → EuclideanSpace ℝ (Fin n),
            MemLp P 2 (volume.restrict (ball 0 (3 / 4))) →
            Tendsto (fun j => ∫ x in ball 0 (3 / 4), inner ℝ (P x)
              (coordinateDifferenceQuotient i (nondivQuotientStep (σ j)) (gradient z) x))
              atTop (𝓝 (∫ x in ball 0 (3 / 4), inner ℝ (P x) (G x))) := by
  obtain ⟨C, hC, hbound⟩ := nondiv_quotient_h1_bound (n := n) hα hlam hlamcap hM
  refine ⟨C, hC, ?_⟩
  intro A b z f hA hb hz hf hbA hbb hcap hell he i
  let V : Set (EuclideanSpace ℝ (Fin n)) := ball 0 (3 / 4)
  have hVU : V ⊆ ball 0 (1 : ℝ) := ball_subset_ball (by norm_num : (3 / 4 : ℝ) ≤ 1)
  have hVW : V ⊆ ball 0 (7 / 8 : ℝ) := ball_subset_ball (by norm_num : (3 / 4 : ℝ) ≤ 7 / 8)
  have hq (j : ℕ) := hbound A b z f hA hb hz hf hbA hbb hcap hell he i
    (nondivQuotientStep j) (nondivQuotientStep_pos j).ne' (nondivQuotientStep_small j)
  have hDcont : ContinuousOn (fun x => fderiv ℝ z x (EuclideanSpace.single i 1)) V :=
    (hz.derivative_holder.nondiv_continuousOn hα).clm_apply
      continuousOn_const |>.mono hVU
  let : IsFiniteMeasure (volume.restrict V) :=
    ⟨by rw [Measure.restrict_apply_univ]; exact isBounded_ball.measure_lt_top⟩
  have hmD : MemLp (fun x => fderiv ℝ z x (EuclideanSpace.single i 1))
      2 (volume.restrict V) := by
    apply MemLp.of_bound (hDcont.aestronglyMeasurable measurableSet_ball)
      (holderNorm α (fderiv ℝ z) (ball 0 1))
    filter_upwards [ae_restrict_mem measurableSet_ball] with x hx
    have ht := (fderiv ℝ z x).le_opNorm (EuclideanSpace.single i 1)
    simp only [PiLp.norm_single, norm_one, mul_one] at ht
    exact ht.trans (hz.derivative_holder.nondiv_norm_le (hVU hx))
  have ht := nondiv_tendsto_coordinateDifferenceQuotient_L2 hα isOpen_ball measurableSet_ball
    (ne_of_lt isBounded_ball.measure_lt_top) hz i
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

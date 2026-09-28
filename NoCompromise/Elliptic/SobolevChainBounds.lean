import NoCompromise.Elliptic.SobolevChainNorm
import Mathlib.Analysis.Calculus.ContDiff.Bounds
import Mathlib.MeasureTheory.Measure.OpenPos

/-!
# Quantitative local Sobolev embedding

The norm below is the explicit finite sum of L² norms of genuine weak derivatives.
The conclusion bounds the operator norms of all classical iterated derivatives.
-/

noncomputable section
open MeasureTheory Filter Metric Set InnerProductSpace
open scoped NNReal ENNReal Topology Gradient
namespace LiquidDrop
lemma sobolevChain_euclidean_norm_le_sum {n : ℕ} (v : EuclideanSpace ℝ (Fin n)) :
    ‖v‖ ≤ ∑ i, ‖v i‖ := by
  have heq : v = ∑ i, EuclideanSpace.single i (v i) := by
    apply PiLp.ext
    intro i
    simp
  calc
    ‖v‖ = ‖∑ i, EuclideanSpace.single i (v i)‖ := congrArg norm heq
    _ ≤ ∑ i, ‖EuclideanSpace.single i (v i)‖ := norm_sum_le _ _
    _ = ∑ i, ‖v i‖ := by simp [EuclideanSpace.single, PiLp.norm_single]
lemma sobolevChain_norm_iteratedFDeriv_vector_le {n k j : ℕ}
    {W : EuclideanSpace ℝ (Fin n) → EuclideanSpace ℝ (Fin n)}
    (hW : ContDiff ℝ k W) (hj : j ≤ k) (x : EuclideanSpace ℝ (Fin n)) :
    ‖iteratedFDeriv ℝ j W x‖ ≤ ∑ i, ‖iteratedFDeriv ℝ j (fun y => W y i) x‖ := by
  apply ContinuousMultilinearMap.opNorm_le_bound (Finset.sum_nonneg fun _ _ => norm_nonneg _)
  intro v
  calc
    ‖iteratedFDeriv ℝ j W x v‖ ≤ ∑ i, ‖(iteratedFDeriv ℝ j W x v) i‖ :=
      sobolevChain_euclidean_norm_le_sum _
    _ = ∑ i, ‖iteratedFDeriv ℝ j (fun y => W y i) x v‖ := by
      apply Finset.sum_congr rfl
      intro i _
      have h := (EuclideanSpace.proj (𝕜 := ℝ) i).iteratedFDeriv_comp_left (x := x) hW.contDiffAt
        (by exact_mod_cast hj)
      exact congrArg (fun A => ‖A v‖) h.symm
    _ ≤ ∑ i, ‖iteratedFDeriv ℝ j (fun y => W y i) x‖ * ∏ l, ‖v l‖ :=
      Finset.sum_le_sum fun i _ => ContinuousMultilinearMap.le_opNorm _ _
    _ = (∑ i, ‖iteratedFDeriv ℝ j (fun y => W y i) x‖) * ∏ l, ‖v l‖ :=
      (Finset.sum_mul ..).symm
lemma sobolevChain_norm_iteratedFDeriv_gradient {n j : ℕ}
    (w : EuclideanSpace ℝ (Fin n) → ℝ) (x : EuclideanSpace ℝ (Fin n)) :
    ‖iteratedFDeriv ℝ j (gradient w) x‖ = ‖iteratedFDeriv ℝ (j + 1) w x‖ := by
  have heq : (toDual ℝ (EuclideanSpace ℝ (Fin n))) ∘ gradient w = fderiv ℝ w :=
    funext fun _ => toDual_gradient
  rw [← norm_iteratedFDeriv_fderiv, ← heq]
  exact ((toDual ℝ (EuclideanSpace ℝ (Fin n))).norm_iteratedFDeriv_comp_left
    (gradient w) x j).symm


/-- The H² estimate bounds any continuous representative on a smaller ball. -/
theorem sobolevChain_continuous_bound {n : ℕ} (hn : n < 4)
    (z : EuclideanSpace ℝ (Fin n)) {r R : ℝ} (hrR : r < R) :
    ∃ C : ℝ, 0 < C ∧ ∀ (m : ℕ) (u w : EuclideanSpace ℝ (Fin n) → ℝ)
      (d : SobolevDerivativeData (ball z R) (m + 2) u), Continuous w →
      w =ᵐ[volume.restrict (ball z R)] u → ∀ x ∈ ball z r, ‖w x‖ ≤ C * d.norm := by
  obtain ⟨C, hC, hb⟩ := interior_poisson_continuous hn z hrR
  refine ⟨C, hC, ?_⟩
  intro m u w d hw hweq
  obtain ⟨h, hf⟩ := d.hasH2DerivativesOn.hasDistributionalLaplacianOn
  obtain ⟨v, hv, hveq, hvb⟩ := hb u _ h d.memLp hf
  have hwEq : w =ᵐ[volume.restrict (ball z r)] u :=
    ae_restrict_of_ae_restrict_of_subset (ball_subset_ball hrR.le) hweq
  have hwveq := Measure.eqOn_open_of_ae_eq (hwEq.trans hveq.symm)
    isOpen_ball hw.continuousOn hv.continuousOn
  intro x hx
  rw [hwveq hx]
  exact (hvb x).trans (mul_le_mul_of_nonneg_left d.lpNorm_add_trace_le hC.le)

/-- The interior C^k bound for any global classical representative of the weak Sobolev data. -/
theorem sobolevChain_classical_derivative_bound {n k : ℕ} (hn : n < 4)
    (z : EuclideanSpace ℝ (Fin n)) {r R : ℝ} (hrR : r < R) :
    ∃ C : ℝ, 0 < C ∧ ∀ (u w : EuclideanSpace ℝ (Fin n) → ℝ)
      (d : SobolevDerivativeData (ball z R) (k + 2) u), ContDiff ℝ k w →
      w =ᵐ[volume.restrict (ball z R)] u →
      ∀ j ≤ k, ∀ x ∈ ball z r, ‖iteratedFDeriv ℝ j w x‖ ≤ C * d.norm := by
  induction k with
  | zero =>
    obtain ⟨C, hC, hb⟩ := sobolevChain_continuous_bound hn z hrR
    refine ⟨C, hC, ?_⟩
    intro u w d hw hweq j hj x hx
    have hj0 : j = 0 := by omega
    rw [hj0, norm_iteratedFDeriv_zero]
    exact hb 0 u w d hw.continuous hweq x hx
  | succ k ih =>
    obtain ⟨C₀, hC₀, hb₀⟩ := sobolevChain_continuous_bound hn z hrR
    obtain ⟨C₁, hC₁, hb₁⟩ := ih
    refine ⟨max C₀ C₁, lt_of_lt_of_le hC₀ (le_max_left _ _), ?_⟩
    intro u w d hw hweq j hj x hx
    cases j with
    | zero =>
      rw [norm_iteratedFDeriv_zero]
      exact (hb₀ (k + 1) u w d hw.continuous hweq x hx).trans
        (mul_le_mul_of_nonneg_right (le_max_left _ _) d.norm_nonneg)
    | succ j =>
      have hjk : j ≤ k := by omega
      have hW : ContDiff ℝ k (gradient w) := contDiff_gradient_of_contDiff_succ hw
      have heq : d.gradient =ᵐ[volume.restrict (ball z R)] gradient w :=
        (d.hasH1GradientOn.toHasWeakGradientOn.congr_ae hweq.symm EventuallyEq.rfl).unique
          isOpen_ball (hasWeakGradientOn_of_contDiffOn isOpen_ball
            (hw.of_le (by simp)).contDiffOn)
      have hbi (i : Fin n) :
          ‖iteratedFDeriv ℝ j (fun y => gradient w y i) x‖ ≤ C₁ * (d.tail i).norm :=
        hb₁ (fun y => d.gradient y i) (fun y => gradient w y i) (d.tail i)
          (contDiff_euclidean.mp hW i) (heq.symm.mono fun y hy => congrArg (fun v => v i) hy)
          j hjk x hx
      rw [← sobolevChain_norm_iteratedFDeriv_gradient]
      calc
        ‖iteratedFDeriv ℝ j (gradient w) x‖ ≤
            ∑ i, ‖iteratedFDeriv ℝ j (fun y => gradient w y i) x‖ :=
          sobolevChain_norm_iteratedFDeriv_vector_le hW hjk x
        _ ≤ ∑ i, C₁ * (d.tail i).norm := Finset.sum_le_sum fun i _ => hbi i
        _ = C₁ * ∑ i, (d.tail i).norm := (Finset.mul_sum ..).symm
        _ ≤ C₁ * d.norm := mul_le_mul_of_nonneg_left d.sum_tail_norm_le hC₁.le
        _ ≤ max C₀ C₁ * d.norm :=
          mul_le_mul_of_nonneg_right (le_max_right _ _) d.norm_nonneg

/-- Quantitative interior Sobolev embedding for actual weak derivatives. -/
theorem interior_sobolev_contDiff_bound {n k : ℕ} (hn : n < 4)
    (z : EuclideanSpace ℝ (Fin n)) {r R : ℝ} (hrR : r < R) :
    ∃ C : ℝ, 0 < C ∧ ∀ (u : EuclideanSpace ℝ (Fin n) → ℝ)
      (d : SobolevDerivativeData (ball z R) (k + 2) u),
      ∃ w : EuclideanSpace ℝ (Fin n) → ℝ, ContDiff ℝ k w ∧
        w =ᵐ[volume.restrict (ball z r)] u ∧
        ∀ j ≤ k, ∀ x ∈ ball z r, ‖iteratedFDeriv ℝ j w x‖ ≤ C * d.norm := by
  let s := (r + R) / 2
  have hrs : r < s := by dsimp [s]; linarith
  have hsR : s < R := by dsimp [s]; linarith
  obtain ⟨C, hC, hb⟩ := sobolevChain_classical_derivative_bound (k := k) hn z hrs
  refine ⟨C, hC, ?_⟩
  intro u d
  obtain ⟨w, hw, hweq⟩ := interior_sobolev_contDiff hn z hsR d.hasSobolevOrderOn
  refine ⟨w, hw, ae_restrict_of_ae_restrict_of_subset (ball_subset_ball hrs.le) hweq, ?_⟩
  intro j hj x hx
  exact (hb u w (d.mono (ball_subset_ball hsR.le)) hw hweq j hj x hx).trans
    (mul_le_mul_of_nonneg_left (d.norm_mono (ball_subset_ball hsR.le)) hC.le)

/-- Every higher Sobolev order also gives the same local C^k estimate. -/
theorem interior_sobolev_contDiff_bound_of_le {n k m : ℕ} (hn : n < 4)
    (z : EuclideanSpace ℝ (Fin n)) {r R : ℝ} (hrR : r < R) (hkm : k + 2 ≤ m) :
    ∃ C : ℝ, 0 < C ∧ ∀ (u : EuclideanSpace ℝ (Fin n) → ℝ)
      (d : SobolevDerivativeData (ball z R) m u),
      ∃ w : EuclideanSpace ℝ (Fin n) → ℝ, ContDiff ℝ k w ∧
        w =ᵐ[volume.restrict (ball z r)] u ∧
        ∀ j ≤ k, ∀ x ∈ ball z r, ‖iteratedFDeriv ℝ j w x‖ ≤ C * d.norm := by
  obtain ⟨C, hC, hb⟩ := interior_sobolev_contDiff_bound (k := k) hn z hrR
  refine ⟨C, hC, ?_⟩
  intro u d
  obtain ⟨e, he⟩ := d.exists_lower hkm
  obtain ⟨w, hw, hweq, hwb⟩ := hb u e
  exact ⟨w, hw, hweq, fun j hj x hx => (hwb j hj x hx).trans
    (mul_le_mul_of_nonneg_left he hC.le)⟩

end LiquidDrop

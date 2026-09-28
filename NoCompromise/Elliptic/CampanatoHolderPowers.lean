import NoCompromise.Elliptic.CampanatoHolderEmbedding

/-! Conversion between integral and averaged Campanato normalizations, retaining
uniform constants and the genuine almost-everywhere representative. -/

noncomputable section
open MeasureTheory Filter Metric Set InnerProductSpace
open scoped ENNReal NNReal Topology Gradient RealInnerProductSpace
namespace LiquidDrop
set_option maxSynthPendingDepth 8

lemma campanato_power_oscillation_normalization {n : ℕ} (hn : 0 < n)
    {K r γ : ℝ} (hK : 0 ≤ K) (hr : 0 < r) (c : EuclideanSpace ℝ (Fin n)) :
    K * r ^ ((n : ℝ) + 2 * γ) =
      (Real.sqrt (K / volume.real (ball (0 : EuclideanSpace ℝ (Fin n)) 1)) * r ^ γ) ^ 2 *
        volume.real (ball c r) := by
  have hV : 0 < volume.real (ball (0 : EuclideanSpace ℝ (Fin n)) 1) :=
    ENNReal.toReal_pos (measure_ball_pos volume 0 zero_lt_one).ne'
      (isBounded_ball (x := (0 : EuclideanSpace ℝ (Fin n))) (r := 1)).measure_lt_top.ne
  rw [frozen_real_volume_ball hn c hr.le, mul_pow,
    Real.sq_sqrt (div_nonneg hK hV.le), campanato_square_rpow hr.le γ,
    Real.rpow_add hr, Real.rpow_natCast]
  field_simp

/-- Integral power bounds imply a genuine bounded Hölder representative. -/
theorem campanato_holder_representative_of_power {n : ℕ} (hn : 0 < n)
    {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F] [CompleteSpace F]
    {K γ R M : ℝ} (hK : 0 ≤ K) (hγ : 0 < γ) (hR : 0 < R) :
    ∃ C P : ℝ, 0 < C ∧ 0 ≤ P ∧
      ∀ (f : EuclideanSpace ℝ (Fin n) → F) (U : Set (EuclideanSpace ℝ (Fin n))),
        MeasurableSet U → MemLp f 2 (volume.restrict (ball 0 1)) →
        (∫ x in ball 0 1, ‖f x‖ ^ 2) ≤ M →
        (∀ x ∈ U, ball x R ⊆ ball 0 1) →
        (∀ x ∈ U, ∀ r ∈ Ioc 0 R,
          (∫ y in ball x r, ‖f y - ⨍ z in ball x r, f z‖ ^ 2) ≤
            K * r ^ ((n : ℝ) + 2 * γ)) →
        ∃ g : EuclideanSpace ℝ (Fin n) → F,
          f =ᵐ[volume.restrict U] g ∧ ContinuousOn g U ∧
          (∀ x ∈ U, ‖g x‖ ≤ P) ∧
          ∀ x ∈ U, ∀ y ∈ U, ‖g x - g y‖ ≤ C * dist x y ^ γ := by
  obtain ⟨C, P, hC, hP, hb⟩ := campanato_holder_representative (F := F) hn
    (Real.sqrt_nonneg (K / volume.real (ball (0 : EuclideanSpace ℝ (Fin n)) 1))) hγ hR
    (M := M)
  refine ⟨C, P, hC, hP, ?_⟩
  intro f U hU hf hM hballs hosc
  apply hb f U hU hf hM hballs
  intro x hx r hr
  exact (hosc x hx r hr).trans_eq (campanato_power_oscillation_normalization hn hK hr.1 x)

end LiquidDrop

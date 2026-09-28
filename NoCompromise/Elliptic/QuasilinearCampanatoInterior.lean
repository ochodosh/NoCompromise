import NoCompromise.Elliptic.QuasilinearCampanatoScaling

/-! Uniform local Campanato applications fill the requested half-radius ball.
This retains the larger three-quarter-radius domain for the actual H¹ equation,
as supplied by difference-quotient energy estimates. -/

noncomputable section
open MeasureTheory Filter Metric Set InnerProductSpace
open scoped ENNReal NNReal Topology Gradient RealInnerProductSpace
namespace LiquidDrop
set_option maxSynthPendingDepth 8

/-- A continuous actual H¹ solution on B_(3/4) satisfies the full actual C¹,α
estimate on B_(1/2). The constant is uniform over all equation data. -/
theorem quasilinear_campanato_interior {n : ℕ} (hn0 : 0 < n) (hn : n < 4)
    {a lam cap HA HG M : ℝ} (ha : 0 < a) (ha1 : a < 1)
    (hlam : 0 < lam) (hcap : 0 ≤ cap) (hHA : 0 ≤ HA) (hHG : 0 ≤ HG) (hM : 0 ≤ M) :
    ∃ C : ℝ, 0 < C ∧
      ∀ (A : EuclideanSpace ℝ (Fin n) →
          EuclideanSpace ℝ (Fin n) →L[ℝ] EuclideanSpace ℝ (Fin n))
        (G F : EuclideanSpace ℝ (Fin n) → EuclideanSpace ℝ (Fin n))
        (u : EuclideanSpace ℝ (Fin n) → ℝ),
        ContinuousOn A (ball 0 (3 / 4 : ℝ)) → ContinuousOn G (ball 0 (3 / 4 : ℝ)) →
        ContinuousOn u (ball 0 (3 / 4 : ℝ)) →
        (∀ x ∈ ball 0 (3 / 4 : ℝ), ‖A x‖ ≤ cap) →
        (∀ x ∈ ball 0 (3 / 4 : ℝ), ∀ ξ, lam * ‖ξ‖ ^ 2 ≤ inner ℝ (A x ξ) ξ) →
        (∀ x ∈ ball 0 (3 / 4 : ℝ), ∀ y ∈ ball 0 (3 / 4 : ℝ),
          ‖A x - A y‖ ≤ HA * dist x y ^ a) →
        (∀ x ∈ ball 0 (3 / 4 : ℝ), ∀ y ∈ ball 0 (3 / 4 : ℝ),
          ‖G x - G y‖ ≤ HG * dist x y ^ a) →
        HasH1GradientOn u F (ball 0 (3 / 4 : ℝ)) →
        IsWeakDivergenceEquationOn A F G (ball 0 (3 / 4 : ℝ)) →
        (∫ x in ball 0 (3 / 4 : ℝ), ‖F x‖ ^ 2) ≤ M →
        ContDiffOn ℝ 1 u (ball 0 (1 / 2 : ℝ)) ∧
          F =ᵐ[volume.restrict (ball 0 (1 / 2 : ℝ))] gradient u ∧
          (∀ x ∈ ball 0 (1 / 2 : ℝ), ‖gradient u x‖ ≤ C) ∧
          ∀ x ∈ ball 0 (1 / 2 : ℝ), ∀ y ∈ ball 0 (1 / 2 : ℝ),
            ‖gradient u x - gradient u y‖ ≤ C * dist x y ^ a := by
  obtain ⟨L, hL, hball⟩ := quasilinear_campanato_on_ball hn0 hn ha ha1
    hlam hcap hHA hHG hM (by norm_num : (0 : ℝ) < 1 / 8)
  let C := max L (2 * L / (1 / 16 : ℝ) ^ a) + 1
  have hC : 0 < C := by
    have hh := le_max_left L (2 * L / (1 / 16 : ℝ) ^ a)
    dsimp [C]
    linarith only [hh, hL]
  have hLC : L ≤ C := (le_max_left _ _).trans (le_add_of_nonneg_right zero_le_one)
  have hLfar : 2 * L / (1 / 16 : ℝ) ^ a ≤ C :=
    (le_max_right _ _).trans (le_add_of_nonneg_right zero_le_one)
  refine ⟨C, hC, ?_⟩
  intro A G F u hA hG huc hbA hell hAhold hGhold hu hw henergy
  have hi : IntegrableOn (fun x => ‖F x‖ ^ 2) (ball 0 (3 / 4 : ℝ)) :=
    hu.memLp_gradient.integrable_norm_pow (by norm_num)
  have hlocal (c : EuclideanSpace ℝ (Fin n)) (hc : c ∈ ball 0 (1 / 2 : ℝ)) :
      ContDiffOn ℝ 1 u (ball c (1 / 16 : ℝ)) ∧
        (∀ x ∈ ball c (1 / 16 : ℝ), ‖gradient u x‖ ≤ L) ∧
        ∀ x ∈ ball c (1 / 16 : ℝ), ∀ y ∈ ball c (1 / 16 : ℝ),
          ‖gradient u x - gradient u y‖ ≤ L * dist x y ^ a := by
    have hs : ball c (1 / 8 : ℝ) ⊆ ball 0 (3 / 4 : ℝ) :=
      campanato_inner_ball_subset hc (by norm_num)
    have he : (∫ x in ball c (1 / 8 : ℝ), ‖F x‖ ^ 2) ≤ M :=
      (setIntegral_mono_set hi (Eventually.of_forall (fun _ => sq_nonneg _))
        (Eventually.of_forall hs)).trans henergy
    simpa only [show (1 / 8 : ℝ) / 2 = 1 / 16 by norm_num] using
      hball c A G F u (hA.mono hs) (hG.mono hs) (huc.mono hs)
        (fun x hx => hbA x (hs hx)) (fun x hx => hell x (hs hx))
        (fun x hx y hy => hAhold x (hs hx) y (hs hy))
        (fun x hx y hy => hGhold x (hs hx) y (hs hy))
        (hu.mono hs) (hw.mono hs) he
  have huC : ContDiffOn ℝ 1 u (ball 0 (1 / 2 : ℝ)) := by
    intro x hx
    exact ((hlocal x hx).1.contDiffAt
      (isOpen_ball.mem_nhds (mem_ball_self (by norm_num : (0 : ℝ) < 1 / 16)))).contDiffWithinAt
  have hnorm (x) (hx : x ∈ ball 0 (1 / 2 : ℝ)) : ‖gradient u x‖ ≤ L :=
    (hlocal x hx).2.1 x (mem_ball_self (by norm_num))
  refine ⟨huC, ?_, fun x hx => (hnorm x hx).trans hLC, ?_⟩
  · exact HasWeakGradientOn.unique isOpen_ball
      (hu.mono (ball_subset_ball (by norm_num : (1 / 2 : ℝ) ≤ 3 / 4))).toHasWeakGradientOn
      (hasWeakGradientOn_of_contDiffOn isOpen_ball huC)
  · intro x hx y hy
    by_cases hnear : dist x y < 1 / 16
    · have hyx : y ∈ ball x (1 / 16 : ℝ) := by
        simpa only [mem_ball, dist_comm y x] using hnear
      exact ((hlocal x hx).2.2 x (mem_ball_self (by norm_num)) y hyx).trans
        (mul_le_mul_of_nonneg_right hLC (Real.rpow_nonneg dist_nonneg a))
    · have hp : (1 / 16 : ℝ) ^ a ≤ dist x y ^ a :=
        Real.rpow_le_rpow (by norm_num) (le_of_not_gt hnear) ha.le
      have hpos : 0 < (1 / 16 : ℝ) ^ a := Real.rpow_pos_of_pos (by norm_num) a
      calc
        _ ≤ ‖gradient u x‖ + ‖gradient u y‖ := norm_sub_le _ _
        _ ≤ 2 * L := by linarith only [hnorm x hx, hnorm y hy]
        _ = (2 * L / (1 / 16 : ℝ) ^ a) * (1 / 16 : ℝ) ^ a :=
          (div_mul_cancel₀ (2 * L) hpos.ne').symm
        _ ≤ (2 * L / (1 / 16 : ℝ) ^ a) * dist x y ^ a :=
          mul_le_mul_of_nonneg_left hp (div_nonneg (by positivity) hpos.le)
        _ ≤ C * dist x y ^ a :=
          mul_le_mul_of_nonneg_right hLfar (Real.rpow_nonneg dist_nonneg a)

end LiquidDrop

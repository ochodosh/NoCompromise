module

public import NoCompromise.Elliptic.CampanatoGrowth

@[expose] public section

/-! The centered oscillation recurrence follows from the actual frozen replacement
and its proved decay. The gradient-energy error remains explicit for bootstrapping. -/

noncomputable section
open MeasureTheory Filter Metric Set InnerProductSpace
open scoped ENNReal NNReal Topology Gradient RealInnerProductSpace
namespace LiquidDrop
set_option maxSynthPendingDepth 8

lemma campanato_integral_oscillation_le_twice {X F : Type*}
    [MeasurableSpace X] [NormedAddCommGroup F] [InnerProductSpace ℝ F] [CompleteSpace F]
    {μ : Measure X} [IsFiniteMeasure μ] {f g : X → F}
    (hf : MemLp f 2 μ) (hg : MemLp g 2 μ) :
    (∫ x, ‖f x - ⨍ y, f y ∂μ‖ ^ 2 ∂μ) ≤
      2 * (∫ x, ‖f x - g x‖ ^ 2 ∂μ) +
        2 * (∫ x, ‖g x - ⨍ y, g y ∂μ‖ ^ 2 ∂μ) := by
  have hmin := frozen_integral_norm_sub_average_le hf (⨍ y, g y ∂μ)
  have ht := campanato_integral_norm_sq_le_twice
    (hf.sub (memLp_const (⨍ y, g y ∂μ))) (hg.sub (memLp_const (⨍ y, g y ∂μ)))
  simp only [Pi.sub_apply, sub_sub_sub_cancel_right] at ht
  exact hmin.trans ht

lemma campanato_oscillation_mono_radius {n : ℕ}
    {F : EuclideanSpace ℝ (Fin n) → EuclideanSpace ℝ (Fin n)}
    {c : EuclideanSpace ℝ (Fin n)} {r R : ℝ}
    (hF : MemLp F 2 (volume.restrict (ball c R))) (hrR : r ≤ R) :
    (∫ x in ball c r, ‖F x - ⨍ y in ball c r, F y‖ ^ 2) ≤
      ∫ x in ball c R, ‖F x - ⨍ y in ball c R, F y‖ ^ 2 := by
  let : IsFiniteMeasure (volume.restrict (ball c r)) :=
    ⟨by simpa using (isBounded_ball (x := c) (r := r)).measure_lt_top⟩
  let : IsFiniteMeasure (volume.restrict (ball c R)) :=
    ⟨by simpa using (isBounded_ball (x := c) (r := R)).measure_lt_top⟩
  have hs : ball c r ⊆ ball c R := ball_subset_ball hrR
  have hg := hF.sub (memLp_const (⨍ y in ball c R, F y))
  exact (frozen_integral_norm_sub_average_le
    (hF.mono_measure (Measure.restrict_mono hs le_rfl)) (⨍ y in ball c R, F y)).trans
      (setIntegral_mono_set ((memLp_two_iff_integrable_sq_norm hg.aestronglyMeasurable).mp hg)
        (Filter.Eventually.of_forall (fun _ => sq_nonneg _)) (Filter.Eventually.of_forall hs))

lemma campanato_transfer_oscillation_decay {n : ℕ}
    {F H : EuclideanSpace ℝ (Fin n) → EuclideanSpace ℝ (Fin n)}
    {c : EuclideanSpace ℝ (Fin n)} {r θ C : ℝ}
    (hF : MemLp F 2 (volume.restrict (ball c r)))
    (hH : MemLp H 2 (volume.restrict (ball c r)))
    (hr : 0 < r) (hθ : 0 < θ) (hθ1 : θ < 1) (hC : 0 ≤ C)
    (hdec : (∫ x in ball c (θ * r), ‖H x - ⨍ y in ball c (θ * r), H y‖ ^ 2) ≤
      C * θ ^ (n + 2) * ∫ x in ball c r, ‖H x - ⨍ y in ball c r, H y‖ ^ 2) :
    (∫ x in ball c (θ * r), ‖F x - ⨍ y in ball c (θ * r), F y‖ ^ 2) ≤
      (2 + 4 * C) * (∫ x in ball c r, ‖F x - H x‖ ^ 2) +
        4 * C * θ ^ (n + 2) * ∫ x in ball c r, ‖F x - ⨍ y in ball c r, F y‖ ^ 2 := by
  let : IsFiniteMeasure (volume.restrict (ball c r)) :=
    ⟨by simpa using (isBounded_ball (x := c) (r := r)).measure_lt_top⟩
  let : IsFiniteMeasure (volume.restrict (ball c (θ * r))) :=
    ⟨by simpa using (isBounded_ball (x := c) (r := θ * r)).measure_lt_top⟩
  have hs : ball c (θ * r) ⊆ ball c r := ball_subset_ball (by nlinarith)
  have hμ := Measure.restrict_mono hs (le_rfl (a := volume))
  have hsmall := campanato_integral_oscillation_le_twice
    (hF.mono_measure hμ) (hH.mono_measure hμ)
  have hlarge := campanato_integral_oscillation_le_twice hH hF
  have heq : (∫ x in ball c r, ‖H x - F x‖ ^ 2) =
      ∫ x in ball c r, ‖F x - H x‖ ^ 2 := by
    simp only [norm_sub_rev]
  rw [heq] at hlarge
  have hmono : (∫ x in ball c (θ * r), ‖F x - H x‖ ^ 2) ≤
      ∫ x in ball c r, ‖F x - H x‖ ^ 2 :=
    setIntegral_mono_set ((memLp_two_iff_integrable_sq_norm (hF.sub hH).aestronglyMeasurable).mp (hF.sub hH))
      (Filter.Eventually.of_forall (fun _ => sq_nonneg _)) (Filter.Eventually.of_forall hs)
  have hscaled := mul_le_mul_of_nonneg_left hlarge
    (show 0 ≤ 2 * C * θ ^ (n + 2) by positivity)
  have hfirst : (∫ x in ball c (θ * r), ‖F x - ⨍ y in ball c (θ * r), F y‖ ^ 2) ≤
      (2 + 4 * C * θ ^ (n + 2)) * (∫ x in ball c r, ‖F x - H x‖ ^ 2) +
        4 * C * θ ^ (n + 2) * ∫ x in ball c r, ‖F x - ⨍ y in ball c r, F y‖ ^ 2 := by
    nlinarith only [hsmall, hmono, hdec, hscaled]
  have hcoeff : 2 + 4 * C * θ ^ (n + 2) ≤ 2 + 4 * C := by
    have ht := mul_le_mul_of_nonneg_left (pow_le_one₀ hθ.le hθ1.le (n := n + 2))
      (show 0 ≤ 4 * C by positivity)
    linarith only [ht]
  exact hfirst.trans (add_le_add
    (mul_le_mul_of_nonneg_right hcoeff (integral_nonneg (fun _ => sq_nonneg _))) le_rfl)

/-- Constants are selected before the coefficient field, solution, center,
radius, Hölder exponent, and shrinking factor. The weak equation is genuine. -/
theorem campanato_oscillation_recurrence_constants {n : ℕ} (hn0 : 0 < n) (hn : n < 4)
    {lam cap HA HG : ℝ} (hlam : 0 < lam) (hcap : 0 ≤ cap)
    (hHA : 0 ≤ HA) (hHG : 0 ≤ HG) :
    ∃ C : ℝ, 0 < C ∧ ∃ D : ℝ, 0 ≤ D ∧
      ∀ (a : ℝ) (c : EuclideanSpace ℝ (Fin n)) (r : ℝ), 0 < r →
      ∀ (u : EuclideanSpace ℝ (Fin n) → ℝ)
        (F G : EuclideanSpace ℝ (Fin n) → EuclideanSpace ℝ (Fin n))
        (A : EuclideanSpace ℝ (Fin n) →
          EuclideanSpace ℝ (Fin n) →L[ℝ] EuclideanSpace ℝ (Fin n)),
        HasH1GradientOn u F (ball c r) → IsWeakDivergenceEquationOn A F G (ball c r) →
        AEStronglyMeasurable A (volume.restrict (ball c r)) →
        (∀ᵐ x ∂volume.restrict (ball c r), ‖A x‖ ≤ cap) →
        MemLp G 2 (volume.restrict (ball c r)) →
        (∀ ξ, lam * ‖ξ‖ ^ 2 ≤ inner ℝ (A c ξ) ξ) → ‖A c‖ ≤ cap →
        (∀ᵐ x ∂volume.restrict (ball c r), ‖A x - A c‖ ≤ HA * r ^ a) →
        (∀ᵐ x ∂volume.restrict (ball c r), ‖G x - G c‖ ≤ HG * r ^ a) →
        ∀ θ : ℝ, 0 < θ → θ < 1 →
          (∫ x in ball c (θ * r), ‖F x - ⨍ y in ball c (θ * r), F y‖ ^ 2) ≤
            C * θ ^ ((n : ℝ) + 2) *
                (∫ x in ball c r, ‖F x - ⨍ y in ball c r, F y‖ ^ 2) +
              C * r ^ (2 * a) * (∫ x in ball c r, ‖F x‖ ^ 2) +
                D * r ^ ((n : ℝ) + 2 * a) := by
  obtain ⟨K, hK, hfrozen⟩ := frozen_decay_h1Space hn0 hn hlam hcap
  let P := (2 + 4 * K) * (2 / lam ^ 2)
  let V := volume.real (ball (0 : EuclideanSpace ℝ (Fin n)) 1)
  let C := 4 * K + P * HA ^ 2 + 1
  let D := P * HG ^ 2 * V
  have hP : 0 ≤ P := by dsimp [P]; positivity
  have hC : 0 < C := by dsimp [C]; positivity
  have hD : 0 ≤ D := by dsimp [D, V]; positivity
  refine ⟨C, hC, D, hD, ?_⟩
  intro a c r hr u F G A hu hw hA hbA hG hell hAc hBA hQG θ hθ hθ1
  obtain ⟨h, hh, herr⟩ := exists_campanato_comparison_bounded_oscillation hn0 c r hu hw
    hA hbA hG hlam hell (mul_nonneg hHA (Real.rpow_nonneg hr.le a))
      (mul_nonneg hHG (Real.rpow_nonneg hr.le a)) hBA hQG
  have hdec := (hfrozen (A c) c r hr h hh hell hAc θ hθ hθ1).1
  have ht := campanato_transfer_oscillation_decay hu.memLp_gradient h.hasH1GradientOn.memLp_gradient
    hr hθ hθ1 hK.le hdec
  have herror := mul_le_mul_of_nonneg_left herr (show 0 ≤ 2 + 4 * K by positivity)
  have hvolume : volume.real (ball c r) = r ^ n * V := frozen_real_volume_ball hn0 c hr.le
  have hpower : r ^ (2 * a) * r ^ n = r ^ ((n : ℝ) + 2 * a) := by
    rw [Real.rpow_add hr, Real.rpow_natCast]
    ring
  have hraw : (∫ x in ball c (θ * r), ‖F x - ⨍ y in ball c (θ * r), F y‖ ^ 2) ≤
      4 * K * θ ^ (n + 2) * (∫ x in ball c r, ‖F x - ⨍ y in ball c r, F y‖ ^ 2) +
        P * HA ^ 2 * r ^ (2 * a) * (∫ x in ball c r, ‖F x‖ ^ 2) +
          D * r ^ ((n : ℝ) + 2 * a) := by
    calc
      _ ≤ (2 + 4 * K) * ((2 / lam ^ 2) *
          ((HA * r ^ a) ^ 2 * (∫ x in ball c r, ‖F x‖ ^ 2) +
            (HG * r ^ a) ^ 2 * volume.real (ball c r))) +
            4 * K * θ ^ (n + 2) *
              ∫ x in ball c r, ‖F x - ⨍ y in ball c r, F y‖ ^ 2 :=
        ht.trans (add_le_add herror le_rfl)
      _ = _ := by
        rw [hvolume, mul_pow, mul_pow, campanato_square_rpow hr.le a]
        dsimp [P, D]
        rw [← hpower]
        ring
  have hc₁ : 4 * K ≤ C := by
    have hp : 0 ≤ P * HA ^ 2 := by positivity
    dsimp [C]
    linarith only [hp]
  have hc₂ : P * HA ^ 2 ≤ C := by dsimp [C]; linarith only [hK]
  refine hraw.trans (add_le_add (add_le_add ?_ ?_) le_rfl)
  · rw [show (n : ℝ) + 2 = ((n + 2 : ℕ) : ℝ) by simp, Real.rpow_natCast]
    exact mul_le_mul_of_nonneg_right
      (mul_le_mul_of_nonneg_right hc₁ (pow_nonneg hθ.le (n + 2)))
      (integral_nonneg (fun _ => sq_nonneg _))
  · exact mul_le_mul_of_nonneg_right
      (mul_le_mul_of_nonneg_right hc₂ (Real.rpow_nonneg hr.le (2 * a)))
      (integral_nonneg (fun _ => sq_nonneg _))

end LiquidDrop

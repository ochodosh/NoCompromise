import NoCompromise.Elliptic.CampanatoHolderBootstrap
import NoCompromise.Elliptic.CampanatoHolderPrimitive

/-!
# The divergence-form C¹,α estimate

Blueprint `thm:campanato` is proved for genuine H¹ solutions in dimensions two
and three (also one). Coefficients need not be symmetric. The representative,
its classical gradient, and both displayed estimates are constructed from the
weak equation. Constants are chosen before all coefficient and solution data.
-/

noncomputable section
open MeasureTheory Filter Metric Set InnerProductSpace
open scoped ENNReal NNReal Topology Gradient RealInnerProductSpace
namespace LiquidDrop
set_option maxSynthPendingDepth 8

lemma campanato_average_oscillation_of_holder {n : ℕ}
    {F H : EuclideanSpace ℝ (Fin n) → EuclideanSpace ℝ (Fin n)}
    {U : Set (EuclideanSpace ℝ (Fin n))} {C a : ℝ} (hC : 0 ≤ C) (ha : 0 ≤ a)
    (hF : MemLp F 2 (volume.restrict U)) (he : F =ᵐ[volume.restrict U] H)
    (hholder : ∀ x ∈ U, ∀ y ∈ U, ‖H x - H y‖ ≤ C * dist x y ^ a)
    {c : EuclideanSpace ℝ (Fin n)} {r : ℝ} (hr : 0 < r) (hs : ball c r ⊆ U) :
    (⨍ x in ball c r, ‖F x - ⨍ y in ball c r, F y‖ ^ 2) ≤ C ^ 2 * r ^ (2 * a) := by
  let : IsFiniteMeasure (volume.restrict (ball c r)) :=
    ⟨by simpa using (isBounded_ball (x := c) (r := r)).measure_lt_top⟩
  have hf := hF.mono_measure (Measure.restrict_mono hs le_rfl)
  have hc : c ∈ U := hs (mem_ball_self hr)
  have he' := ae_restrict_of_ae_restrict_of_subset hs he
  have hb : ∀ᵐ x ∂volume.restrict (ball c r), ‖F x - H c‖ ≤ C * r ^ a := by
    filter_upwards [he', ae_restrict_mem measurableSet_ball] with x hx hxr
    rw [hx]
    exact (hholder x (hs hxr) c hc).trans (mul_le_mul_of_nonneg_left
      (Real.rpow_le_rpow dist_nonneg (le_of_lt hxr) ha) hC)
  have hmin := frozen_integral_norm_sub_average_le hf (H c)
  have hbound := campanato_integral_sq_le_measure (hf.sub (memLp_const (H c)))
    (mul_nonneg hC (Real.rpow_nonneg hr.le a)) hb
  simp only [Pi.sub_apply, Measure.real, Measure.restrict_apply_univ] at hbound
  have hV : 0 < volume.real (ball c r) :=
    ENNReal.toReal_pos (measure_ball_pos volume c hr).ne'
      (isBounded_ball (x := c) (r := r)).measure_lt_top.ne
  rw [average_eq]
  simp only [Measure.real, Measure.restrict_apply_univ, smul_eq_mul]
  have hh := mul_le_mul_of_nonneg_left (hmin.trans hbound) (inv_nonneg.mpr hV.le)
  change (volume.real (ball c r))⁻¹ * _ ≤ _
  calc
    _ ≤ (volume.real (ball c r))⁻¹ *
        ((C * r ^ a) ^ 2 * volume.real (ball c r)) := hh
    _ = C ^ 2 * r ^ (2 * a) := by
      rw [mul_pow, campanato_square_rpow hr.le a]
      field_simp

/-- Full blueprint Campanato theorem, with positive uniform ellipticity and
0 < α < 1. The only solution-size parameter is the squared L² gradient bound. -/
theorem campanato_c1_holder {n : ℕ} (hn0 : 0 < n) (hn : n < 4)
    {a lam cap HA HG M : ℝ} (ha : 0 < a) (ha1 : a < 1)
    (hlam : 0 < lam) (hcap : 0 ≤ cap) (hHA : 0 ≤ HA) (hHG : 0 ≤ HG) (hM : 0 ≤ M) :
    ∃ C : ℝ, 0 < C ∧
      ∀ (A : EuclideanSpace ℝ (Fin n) →
          EuclideanSpace ℝ (Fin n) →L[ℝ] EuclideanSpace ℝ (Fin n))
        (G F : EuclideanSpace ℝ (Fin n) → EuclideanSpace ℝ (Fin n))
        (u : EuclideanSpace ℝ (Fin n) → ℝ),
        ContinuousOn A (ball 0 1) → ContinuousOn G (ball 0 1) →
        (∀ x ∈ ball 0 1, ‖A x‖ ≤ cap) →
        (∀ x ∈ ball 0 1, ∀ ξ, lam * ‖ξ‖ ^ 2 ≤ inner ℝ (A x ξ) ξ) →
        (∀ x ∈ ball 0 1, ∀ y ∈ ball 0 1, ‖A x - A y‖ ≤ HA * dist x y ^ a) →
        (∀ x ∈ ball 0 1, ∀ y ∈ ball 0 1, ‖G x - G y‖ ≤ HG * dist x y ^ a) →
        HasH1GradientOn u F (ball 0 1) → IsWeakDivergenceEquationOn A F G (ball 0 1) →
        (∫ x in ball 0 1, ‖F x‖ ^ 2) ≤ M →
        ∃ v : EuclideanSpace ℝ (Fin n) → ℝ,
          ContDiffOn ℝ 1 v (ball 0 (1 / 2 : ℝ)) ∧
          u =ᵐ[volume.restrict (ball 0 (1 / 2 : ℝ))] v ∧
          F =ᵐ[volume.restrict (ball 0 (1 / 2 : ℝ))] gradient v ∧
          (∀ x ∈ ball 0 (1 / 2 : ℝ), ‖gradient v x‖ ≤ C) ∧
          (∀ x ∈ ball 0 (1 / 2 : ℝ), ∀ y ∈ ball 0 (1 / 2 : ℝ),
            ‖gradient v x - gradient v y‖ ≤ C * dist x y ^ a) ∧
          ∀ (c : EuclideanSpace ℝ (Fin n)) (r : ℝ), 0 < r →
            ball c r ⊆ ball 0 (1 / 2 : ℝ) →
            (⨍ x in ball c r,
              ‖gradient v x - ⨍ y in ball c r, gradient v y‖ ^ 2) ≤ C * r ^ (2 * a) := by
  obtain ⟨L, P, hL, hP, hb⟩ :=
    campanato_gradient_holder hn0 hn ha ha1 hlam hcap hHA hHG hM
  let C := max P (max L (L ^ 2)) + 1
  have hC : 0 < C := by
    have hh := le_max_left P (max L (L ^ 2))
    dsimp [C]
    linarith only [hh, hP]
  have hPC : P ≤ C := (le_max_left _ _).trans (le_add_of_nonneg_right zero_le_one)
  have hLC : L ≤ C := ((le_max_left _ _).trans (le_max_right _ _)).trans
    (le_add_of_nonneg_right zero_le_one)
  have hL2C : L ^ 2 ≤ C := ((le_max_right _ _).trans (le_max_right _ _)).trans
    (le_add_of_nonneg_right zero_le_one)
  refine ⟨C, hC, ?_⟩
  intro A G F u hA hG hbA hell hHA' hHG' hu hw hM'
  obtain ⟨H, he, hH, hnorm, hholder⟩ := hb A G F u hA hG hbA hell hHA' hHG' hu hw hM'
  have hu' := (hu.mono (ball_subset_ball (by norm_num : (3 / 5 : ℝ) ≤ 1)))
    |>.toHasWeakGradientOn.congr_ae Filter.EventuallyEq.rfl he
  obtain ⟨v, hv, huv, hgrad⟩ := campanato_c1_representative_of_continuous_weak_gradient
    (by norm_num : (0 : ℝ) < 1 / 2) (by norm_num : (1 / 2 : ℝ) < 3 / 5) hu' hH
  have hs : ball (0 : EuclideanSpace ℝ (Fin n)) (1 / 2 : ℝ) ⊆ ball 0 (3 / 5 : ℝ) :=
    ball_subset_ball (by norm_num)
  have hegrad : F =ᵐ[volume.restrict (ball 0 (1 / 2 : ℝ))] gradient v := by
    filter_upwards [ae_restrict_of_ae_restrict_of_subset hs he,
      ae_restrict_mem measurableSet_ball] with x hx hxr
    exact hx.trans (hgrad x hxr).symm
  have hh : ∀ x ∈ ball 0 (1 / 2 : ℝ), ∀ y ∈ ball 0 (1 / 2 : ℝ),
      ‖gradient v x - gradient v y‖ ≤ L * dist x y ^ a := by
    intro x hx y hy
    rw [hgrad x hx, hgrad y hy]
    exact hholder x (hs hx) y (hs hy)
  refine ⟨v, hv, huv, hegrad, ?_, ?_, ?_⟩
  · intro x hx
    rw [hgrad x hx]
    exact (hnorm x (hs hx)).trans hPC
  · intro x hx y hy
    exact (hh x hx y hy).trans
      (mul_le_mul_of_nonneg_right hLC (Real.rpow_nonneg dist_nonneg a))
  · intro c r hr hball
    have hvLp := (hu.memLp_gradient.mono_measure
      (Measure.restrict_mono (ball_subset_ball (by norm_num : (1 / 2 : ℝ) ≤ 1)) le_rfl))
      |>.ae_eq hegrad
    exact (campanato_average_oscillation_of_holder hL.le ha.le hvLp
      Filter.EventuallyEq.rfl hh hr hball).trans
        (mul_le_mul_of_nonneg_right hL2C (Real.rpow_nonneg hr.le (2 * a)))

end LiquidDrop

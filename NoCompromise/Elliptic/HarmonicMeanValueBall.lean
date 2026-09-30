module

public import NoCompromise.Elliptic.HarmonicMeanValueTests
public import Mathlib.Analysis.Calculus.ParametricIntegral

@[expose] public section

/-!
# Classical harmonic ball mean values

Differentiation of scaled unit-ball integrals and the compact radial-test
identity show that every C² function with zero Laplacian on a ball equals
its average there. The proof works in every Euclidean dimension and requires
no harmonicity outside the ball.
-/

noncomputable section
open MeasureTheory Filter Metric Set InnerProductSpace
open scoped ENNReal NNReal Topology Gradient RealInnerProductSpace
namespace LiquidDrop
set_option maxSynthPendingDepth 8

lemma integral_unitBall_comp_affine_scale {n : ℕ}
    (f : EuclideanSpace ℝ (Fin n) → ℝ) (c : EuclideanSpace ℝ (Fin n))
    {r : ℝ} (hr : 0 < r) :
    (∫ x in ball (0 : EuclideanSpace ℝ (Fin n)) 1, f (c + r • x)) =
      (r ^ n)⁻¹ * ∫ x in ball c r, f x := by
  have h := Measure.integral_comp_smul_of_nonneg volume
    (fun x => (ball c r).indicator f (c + x)) r (hR := hr.le)
  have he : (fun x => (ball c r).indicator f (c + r • x)) =
      (ball (0 : EuclideanSpace ℝ (Fin n)) 1).indicator (fun x => f (c + r • x)) := by
    funext x
    have hm : c + r • x ∈ ball c r ↔ x ∈ ball (0 : EuclideanSpace ℝ (Fin n)) 1 := by
      simp only [mem_ball, dist_eq_norm, add_sub_cancel_left, sub_zero, norm_smul,
        Real.norm_eq_abs, abs_of_pos hr]
      constructor <;> intro hx <;> nlinarith [norm_nonneg x]
    simp only [Set.indicator]
    split_ifs with hx hx' hx'
    · rfl
    · exact False.elim (hx' (hm.mp hx))
    · exact False.elim (hx (hm.mpr hx'))
    · rfl
  rw [he, integral_indicator measurableSet_ball,
    integral_add_left_eq_self, integral_indicator measurableSet_ball] at h
  simpa only [Module.finrank_fin_fun, finrank_euclideanSpace, Fintype.card_fin, smul_eq_mul] using h

set_option maxHeartbeats 400000 in
-- Derivative-under-the-integral elaboration carries several restricted measures.
lemma hasDerivAt_integral_unitBall_affine_scale {n : ℕ}
    {u : EuclideanSpace ℝ (Fin n) → ℝ} (hu : ContDiff ℝ 1 u)
    (c : EuclideanSpace ℝ (Fin n)) (r : ℝ) :
    HasDerivAt (fun s : ℝ => ∫ x in ball (0 : EuclideanSpace ℝ (Fin n)) 1, u (c + s • x))
      (∫ x in ball (0 : EuclideanSpace ℝ (Fin n)) 1, inner ℝ (gradient u (c + r • x)) x) r := by
  have hG : Continuous (gradient u) := continuous_gradient_of_contDiff hu
  have hc (s : ℝ) : Continuous (fun x : EuclideanSpace ℝ (Fin n) => c + s • x) :=
    continuous_const.add (continuous_id.const_smul s)
  have hF (s : ℝ) : Continuous (fun x : EuclideanSpace ℝ (Fin n) => u (c + s • x)) :=
    hu.continuous.comp (hc s)
  have hFder (s : ℝ) : Continuous (fun x : EuclideanSpace ℝ (Fin n) =>
      inner ℝ (gradient u (c + s • x)) x) := (hG.comp (hc s)).inner continuous_id
  obtain ⟨C, hC⟩ := ((isCompact_closedBall c (|r| + 1)).image hG).isBounded.exists_norm_le
  have hb (x : EuclideanSpace ℝ (Fin n)) (hx : x ∈ ball 0 1)
      (s : ℝ) (hs : s ∈ ball r 1) : c + s • x ∈ closedBall c (|r| + 1) := by
    have hx' : ‖x‖ < 1 := by simpa only [mem_ball, dist_zero_right] using hx
    have hs' : |s - r| < 1 := by simpa only [mem_ball, Real.dist_eq] using hs
    have hsr : |s| ≤ |r| + 1 := by
      have h := abs_add_le (s - r) r
      simpa only [sub_add_cancel] using h.trans (by linarith)
    simp only [mem_closedBall, dist_eq_norm, add_sub_cancel_left, norm_smul, Real.norm_eq_abs]
    nlinarith [abs_nonneg s, norm_nonneg x]
  have hi : IntegrableOn (fun x : EuclideanSpace ℝ (Fin n) => u (c + r • x)) (ball 0 1) :=
    ((hF r).continuousOn.integrableOn_compact
      (isCompact_closedBall 0 1)).mono_set ball_subset_closedBall
  let : IsFiniteMeasure (volume.restrict (ball (0 : EuclideanSpace ℝ (Fin n)) 1)) :=
    ⟨by rw [Measure.restrict_apply_univ]; exact isBounded_ball.measure_lt_top⟩
  refine (hasDerivAt_integral_of_dominated_loc_of_deriv_le (ball_mem_nhds r zero_lt_one)
    (μ := volume.restrict (ball (0 : EuclideanSpace ℝ (Fin n)) 1))
    (F := fun s x => u (c + s • x))
    (F' := fun s x => inner ℝ (gradient u (c + s • x)) x)
    (bound := fun _ => C) ?_ hi ?_ ?_ (integrable_const C) ?_).2
  · exact Eventually.of_forall fun s => (hF s).aestronglyMeasurable
  · exact (hFder r).aestronglyMeasurable
  · filter_upwards [ae_restrict_mem measurableSet_ball] with x hx
    intro s hs
    have hg := hC _ ⟨c + s • x, hb x hx s hs, rfl⟩
    have hx' : ‖x‖ ≤ 1 := le_of_lt (by simpa only [mem_ball, dist_zero_right] using hx)
    exact (norm_inner_le_norm _ _).trans (by nlinarith [norm_nonneg (gradient u (c + s • x))])
  · filter_upwards [] with x
    intro s _
    have hd := ((hu.differentiable one_ne_zero (c + s • x)).hasFDerivAt).comp_hasDerivAt s
      ((hasDerivAt_id s).smul_const x |>.const_add c)
    convert! hd using 1
    simp [← inner_gradient_left]

lemma hasDerivAt_integral_unitBall_affine_scale_zero {n : ℕ}
    {u : EuclideanSpace ℝ (Fin n) → ℝ} (hu : ContDiff ℝ 2 u)
    (c : EuclideanSpace ℝ (Fin n)) {r : ℝ} (hr : 0 < r)
    (hh : ∀ x ∈ ball c r, laplacianN u x = 0) :
    HasDerivAt (fun s : ℝ => ∫ x in ball (0 : EuclideanSpace ℝ (Fin n)) 1, u (c + s • x))
      0 r := by
  have hi := integral_unitBall_comp_affine_scale
    (fun x => inner ℝ (gradient u x) (x - c)) c hr
  rw [integral_ball_inner_gradient_sub_eq_zero hu c hr hh, mul_zero] at hi
  simp only [add_sub_cancel_left, inner_smul_right, integral_const_mul] at hi
  have hz : (∫ x in ball (0 : EuclideanSpace ℝ (Fin n)) 1,
      inner ℝ (gradient u (c + r • x)) x) = 0 := (mul_eq_zero.mp hi).resolve_left hr.ne'
  rw [← hz]
  exact hasDerivAt_integral_unitBall_affine_scale (hu.of_le (by norm_num)) c r

/-- The classical ball mean-value identity, proved by differentiating scaled
ball integrals and the compact radial-test identity. -/
theorem integral_ball_eq_measure_mul_of_laplacianN_eq_zero {n : ℕ}
    {u : EuclideanSpace ℝ (Fin n) → ℝ} (hu : ContDiff ℝ 2 u)
    (c : EuclideanSpace ℝ (Fin n)) {r : ℝ} (hr : 0 < r)
    (hh : ∀ x ∈ ball c r, laplacianN u x = 0) :
    (∫ x in ball c r, u x) = volume.real (ball c r) * u c := by
  let M : ℝ → ℝ := fun s => ∫ x in ball (0 : EuclideanSpace ℝ (Fin n)) 1, u (c + s • x)
  have hd (s : ℝ) : DifferentiableAt ℝ M s :=
    (hasDerivAt_integral_unitBall_affine_scale (hu.of_le (by norm_num)) c s).differentiableAt
  have hz (s : ℝ) (hs : s ∈ Ioo 0 r) : deriv M s = 0 :=
    (hasDerivAt_integral_unitBall_affine_scale_zero hu c hs.1
      (fun x hx => hh x ((ball_subset_ball hs.2.le) hx))).deriv
  have he : EqOn M (fun _ => M (r / 2)) (Ioo 0 r) := by
    intro s hs
    exact isOpen_Ioo.is_const_of_deriv_eq_zero (convex_Ioo (0 : ℝ) r).isPreconnected
      (fun t _ => (hd t).differentiableWithinAt) (fun t ht => hz t ht) hs
      ⟨by linarith, by linarith⟩
  have hec := he.closure (show Differentiable ℝ M from hd).continuous continuous_const
  rw [closure_Ioo hr.ne] at hec
  have he0 := hec (show (0 : ℝ) ∈ Icc 0 r from ⟨le_rfl, hr.le⟩)
  have her := hec (show r ∈ Icc (0 : ℝ) r from ⟨hr.le, le_rfl⟩)
  have hm : M r = M 0 := her.trans he0.symm
  dsimp only [M] at hm
  simp only [zero_smul, add_zero, integral_const, Measure.real,
    Measure.restrict_apply_univ, smul_eq_mul] at hm
  rw [integral_unitBall_comp_affine_scale u c hr] at hm
  have hvol := integral_unitBall_comp_affine_scale (fun _ => (1 : ℝ)) c hr
  simp only [integral_const, Measure.real, Measure.restrict_apply_univ,
    smul_eq_mul, mul_one] at hvol
  rw [hvol] at hm
  have hne : (r ^ n)⁻¹ ≠ 0 := inv_ne_zero (pow_ne_zero _ hr.ne')
  exact (mul_left_cancel₀ hne (by simpa only [Measure.real, mul_assoc] using hm))

/-- A classical harmonic function equals its average on every ball. -/
theorem average_ball_eq_of_laplacianN_eq_zero {n : ℕ}
    {u : EuclideanSpace ℝ (Fin n) → ℝ} (hu : ContDiff ℝ 2 u)
    (c : EuclideanSpace ℝ (Fin n)) {r : ℝ} (hr : 0 < r)
    (hh : ∀ x ∈ ball c r, laplacianN u x = 0) :
    (⨍ x in ball c r, u x) = u c := by
  rw [average_eq, integral_ball_eq_measure_mul_of_laplacianN_eq_zero hu c hr hh]
  have hv : volume.real (ball c r) ≠ 0 := ENNReal.toReal_ne_zero.mpr
    ⟨(measure_ball_pos volume c hr).ne', isBounded_ball.measure_lt_top.ne⟩
  simp only [Measure.real, Measure.restrict_apply_univ, smul_eq_mul]
  change (volume.real (ball c r))⁻¹ * (volume.real (ball c r) * u c) = u c
  field_simp

end LiquidDrop

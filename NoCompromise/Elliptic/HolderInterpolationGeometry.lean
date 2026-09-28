import Mathlib.Analysis.Calculus.MeanValue
import Mathlib.Analysis.Calculus.ContDiff.Basic
import Mathlib.Analysis.InnerProductSpace.PiL2

/-!
# Same-ball finite-difference estimates

A controlled inward displacement leaves room for a finite difference without
requiring values on any larger domain.
-/

noncomputable section
open Metric Set
open scoped Topology

namespace LiquidDrop

/-- A uniform classical Hessian bound controls derivative differences on a ball. -/
lemma holderInterpolation_fderiv_sub_le {n : ℕ}
    {u : EuclideanSpace ℝ (Fin n) → ℝ} {c : EuclideanSpace ℝ (Fin n)} {R M : ℝ}
    (hu : ContDiffOn ℝ 2 u (ball c R))
    (hM : ∀ x ∈ ball c R, ‖fderiv ℝ (fderiv ℝ u) x‖ ≤ M)
    {x y : EuclideanSpace ℝ (Fin n)} (hx : x ∈ ball c R) (hy : y ∈ ball c R) :
    ‖fderiv ℝ u y - fderiv ℝ u x‖ ≤ M * ‖y - x‖ := by
  have hd : ContDiffOn ℝ 1 (fderiv ℝ u) (ball c R) :=
    hu.fderiv_of_isOpen isOpen_ball (by norm_num)
  exact (convex_ball c R).norm_image_sub_le_of_norm_fderiv_le
    (fun z hz => ((hd z hz).contDiffAt (isOpen_ball.mem_nhds hz)).differentiableAt one_ne_zero)
    hM hx hy

/-- An interior finite difference bounds the derivative by the value and Hessian bounds. -/
lemma holderInterpolation_fderiv_le_of_ball_subset {n : ℕ}
    {u : EuclideanSpace ℝ (Fin n) → ℝ} {c y : EuclideanSpace ℝ (Fin n)} {R s M M₀ : ℝ}
    (hu : ContDiffOn ℝ 2 u (ball c R)) (hs : 0 < s) (hM0 : 0 ≤ M) (hM₀ : 0 ≤ M₀)
    (hval : ∀ x ∈ ball c R, ‖u x‖ ≤ M₀)
    (hM : ∀ x ∈ ball c R, ‖fderiv ℝ (fderiv ℝ u) x‖ ≤ M)
    (hsub : ball y s ⊆ ball c R) :
    ‖fderiv ℝ u y‖ ≤ (4 / s) * M₀ + s * M := by
  apply ContinuousLinearMap.opNorm_le_of_unit_norm (by positivity)
  intro v hv
  let p := y + (s / 2) • v
  have hyp : y ∈ ball y s := mem_ball_self hs
  have hp : p ∈ ball y s := by
    rw [mem_ball, dist_eq_norm]
    dsimp [p]
    rw [add_sub_cancel_left, norm_smul, Real.norm_eq_abs, abs_of_pos (half_pos hs), hv, mul_one]
    exact half_lt_self hs
  have hd (z) (hz : z ∈ ball y s) : DifferentiableAt ℝ u z :=
    ((hu z (hsub hz)).contDiffAt (isOpen_ball.mem_nhds (hsub hz))).differentiableAt (by norm_num)
  have hb (z) (hz : z ∈ ball y s) : ‖fderiv ℝ u z - fderiv ℝ u y‖ ≤ M * s :=
    (holderInterpolation_fderiv_sub_le hu hM (hsub hyp) (hsub hz)).trans
      (mul_le_mul_of_nonneg_left (mem_ball_iff_norm.mp hz).le hM0)
  have ht := (convex_ball y s).norm_image_sub_le_of_norm_fderiv_le' hd hb hyp hp
  have hvp : ‖u p - u y‖ ≤ 2 * M₀ :=
    (norm_sub_le _ _).trans (by linarith [hval p (hsub hp), hval y (hsub hyp)])
  have hn : ‖fderiv ℝ u y (p - y)‖ ≤ 2 * M₀ + (M * s) * ‖p - y‖ := by
    calc
      ‖fderiv ℝ u y (p - y)‖ =
          ‖(u p - u y) - (u p - u y - fderiv ℝ u y (p - y))‖ := by congr 1; ring
      _ ≤ ‖u p - u y‖ + ‖u p - u y - fderiv ℝ u y (p - y)‖ := norm_sub_le _ _
      _ ≤ 2 * M₀ + (M * s) * ‖p - y‖ := add_le_add hvp ht
  have he : p - y = (s / 2) • v := by dsimp [p]; module
  simp only [he, map_smul, norm_smul, Real.norm_of_nonneg (half_pos hs).le, hv, mul_one] at hn
  have hsne : s ≠ 0 := hs.ne'
  have hc : ((4 / s) * M₀ + s * M) * (s / 2) = 2 * M₀ + (M * s) * (s / 2) := by
    field_simp [hsne]
    ring
  nlinarith

/-- An inward displacement creates a prescribed ball while moving by at most its radius. -/
lemma holderInterpolation_exists_inward_ball {n : ℕ}
    {c x : EuclideanSpace ℝ (Fin n)} {R s : ℝ} (hx : x ∈ ball c R)
    (hs : 0 < s) (hsR : s < R) :
    ∃ y : EuclideanSpace ℝ (Fin n), y ∈ ball c R ∧ ‖y - x‖ ≤ s ∧ ball y s ⊆ ball c R := by
  have hR : 0 < R := hs.trans hsR
  have ha : 0 < 1 - s / R := sub_pos.mpr ((div_lt_one hR).mpr hsR)
  let y := c + (1 - s / R) • (x - c)
  have hyc : y - c = (1 - s / R) • (x - c) := by dsimp [y]; module
  have hxy : x - y = (s / R) • (x - c) := by dsimp [y]; module
  have hn : ‖x - c‖ < R := mem_ball_iff_norm.mp hx
  have hd : dist y c < R - s := by
    rw [dist_eq_norm, hyc, norm_smul, Real.norm_eq_abs, abs_of_pos ha]
    calc
      (1 - s / R) * ‖x - c‖ < (1 - s / R) * R := mul_lt_mul_of_pos_left hn ha
      _ = R - s := by field_simp [hR.ne']
  have hb : ball y s ⊆ ball c R := ball_subset_ball' (by linarith)
  refine ⟨y, hb (mem_ball_self hs), ?_, hb⟩
  rw [norm_sub_rev, hxy, norm_smul, Real.norm_eq_abs, abs_of_nonneg (div_nonneg hs.le hR.le)]
  calc
    s / R * ‖x - c‖ ≤ s / R * R := mul_le_mul_of_nonneg_left hn.le (div_nonneg hs.le hR.le)
    _ = s := div_mul_cancel₀ _ hR.ne'

/-- Same-ball first-derivative interpolation, with a freely chosen positive difference scale. -/
theorem holderInterpolation_fderiv_le {n : ℕ}
    {u : EuclideanSpace ℝ (Fin n) → ℝ} {c : EuclideanSpace ℝ (Fin n)} {R s M M₀ : ℝ}
    (hu : ContDiffOn ℝ 2 u (ball c R)) (hs : 0 < s) (hsR : s < R)
    (hM0 : 0 ≤ M) (hM₀ : 0 ≤ M₀) (hval : ∀ x ∈ ball c R, ‖u x‖ ≤ M₀)
    (hM : ∀ x ∈ ball c R, ‖fderiv ℝ (fderiv ℝ u) x‖ ≤ M)
    {x : EuclideanSpace ℝ (Fin n)} (hx : x ∈ ball c R) :
    ‖fderiv ℝ u x‖ ≤ (4 / s) * M₀ + (2 * s) * M := by
  obtain ⟨y, hy, hdist, hball⟩ := holderInterpolation_exists_inward_ball hx hs hsR
  have hd := holderInterpolation_fderiv_sub_le hu hM hy hx
  have hyb := holderInterpolation_fderiv_le_of_ball_subset hu hs hM0 hM₀ hval hM hball
  have hdist' : ‖x - y‖ ≤ s := by simpa only [norm_sub_rev] using hdist
  have hd' := hd.trans (mul_le_mul_of_nonneg_left hdist' hM0)
  have hh := norm_le_norm_sub_add (fderiv ℝ u x) (fderiv ℝ u y)
  linarith

end LiquidDrop

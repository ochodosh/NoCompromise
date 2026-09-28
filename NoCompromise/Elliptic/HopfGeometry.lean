import NoCompromise.Elliptic.Hopf
import Mathlib.Analysis.Calculus.ContDiff.RCLike

/-!
# Local geometry for the exterior Hopf sign

Quadratic error bounds for genuine C² defining functions and the elementary
inner-product inequality for a ball tangent in a prescribed unit direction.
-/

noncomputable section
open Set Filter Metric InnerProductSpace
open scoped Topology RealInnerProductSpace
namespace LiquidDrop

theorem exists_quadratic_fderiv_error {n : ℕ}
    {F : EuclideanSpace ℝ (Fin n) → ℝ} (hF : ContDiff ℝ 2 F)
    (p : EuclideanSpace ℝ (Fin n)) :
    ∃ K δ : ℝ, 0 ≤ K ∧ 0 < δ ∧ ∀ y ∈ ball p δ,
      ‖F y - F p - fderiv ℝ F p (y - p)‖ ≤ K * ‖y - p‖ ^ 2 := by
  have hd : ContDiff ℝ 1 (fderiv ℝ F) := hF.fderiv_right (by norm_num)
  obtain ⟨K, V, hV, hLip⟩ := hd.contDiffAt.exists_lipschitzOnWith (x := p)
  obtain ⟨δ, hδ, hball⟩ := Metric.mem_nhds_iff.mp hV
  refine ⟨K, δ, K.coe_nonneg, hδ, ?_⟩
  intro y hy
  have hsub : closedBall p ‖y - p‖ ⊆ ball p δ :=
    closedBall_subset_ball (mem_ball_iff_norm.mp hy)
  have hbound : ∀ z ∈ closedBall p ‖y - p‖,
      ‖fderiv ℝ F z - fderiv ℝ F p‖ ≤ (K : ℝ) * ‖y - p‖ := by
    intro z hz
    have hb : ‖fderiv ℝ F z - fderiv ℝ F p‖ ≤ (K : ℝ) * ‖z - p‖ := by
      simpa only [dist_eq_norm] using hLip.dist_le_mul z (hball (hsub hz))
        p (hball (mem_ball_self hδ))
    exact hb.trans (mul_le_mul_of_nonneg_left (mem_closedBall_iff_norm.mp hz) K.coe_nonneg)
  have ht := (convex_closedBall p ‖y - p‖).norm_image_sub_le_of_norm_fderiv_le'
    (x := p) (y := y)
    (fun z _ => hF.differentiable (by norm_num) z) hbound
    (mem_closedBall_self (norm_nonneg _)) (by simp only [mem_closedBall, dist_eq_norm, le_refl])
  simpa only [pow_two, mul_assoc] using ht

lemma inner_pos_of_mem_tangent_ball {n : ℕ} {p ν y : EuclideanSpace ℝ (Fin n)}
    {R : ℝ} (hR : 0 < R) (hν : ‖ν‖ = 1) (hy : y ∈ ball (p + R • ν) R) :
    ‖y - p‖ ^ 2 < 2 * R * inner ℝ ν (y - p) := by
  have hn : ‖y - p - R • ν‖ < R := by
    simpa only [mem_ball, dist_eq_norm, sub_add_eq_sub_sub] using hy
  have hsq := (sq_lt_sq₀ (norm_nonneg _) hR.le).mpr hn
  rw [norm_sub_sq_real, real_inner_smul_right, real_inner_comm ν (y - p),
    norm_smul, Real.norm_eq_abs, abs_of_pos hR, hν, mul_one] at hsq
  nlinarith

theorem exists_tangent_ball_of_contDiff {n : ℕ}
    {F : EuclideanSpace ℝ (Fin n) → ℝ} (hF : ContDiff ℝ 2 F)
    {p ν : EuclideanSpace ℝ (Fin n)} (hFp : F p = 0) (hν : ‖ν‖ = 1)
    {a : ℝ} (ha : 0 < a) (hder : ∀ v, fderiv ℝ F p v = a * inner ℝ ν v)
    {W : Set (EuclideanSpace ℝ (Fin n))} (hW : IsOpen W) (hpW : p ∈ W) :
    ∃ R : ℝ, 0 < R ∧ ball (p + R • ν) R ⊆ W ∩ {y | 0 < F y} ∧
      p ∈ sphere (p + R • ν) R := by
  obtain ⟨K, δ, hK, hδ, hTaylor⟩ := exists_quadratic_fderiv_error hF p
  obtain ⟨d, hd, hdb⟩ := Metric.mem_nhds_iff.mp (hW.mem_nhds hpW)
  let R := min (min δ d / 4) (a / (4 * (K + 1)))
  have hR : 0 < R := lt_min (by positivity) (by positivity)
  have hsmall : 2 * R < min δ d := by
    have he : R ≤ min δ d / 4 := min_le_left _ _
    have hm : 0 < min δ d := lt_min hδ hd
    dsimp only [R] at he
    change 2 * min (min δ d / 4) (a / (4 * (K + 1))) < min δ d
    linarith
  have hcoef : 2 * R * K < a := by
    have he : R ≤ a / (4 * (K + 1)) := min_le_right _ _
    have hh := (le_div_iff₀ (show 0 < 4 * (K + 1) by positivity)).mp he
    nlinarith [mul_nonneg hR.le hK]
  have hcenter : dist (p + R • ν) p = R := by
    simp [dist_eq_norm, norm_smul, abs_of_pos hR, hν]
  refine ⟨R, hR, ?_, ?_⟩
  · intro y hy
    have hyd : dist y p < min δ d :=
      (dist_triangle y (p + R • ν) p).trans_lt (by
        rw [hcenter]
        have hh : dist y (p + R • ν) < R := hy
        linarith)
    have hyδ : y ∈ ball p δ := hyd.trans_le (min_le_left _ _)
    have hyW : y ∈ W := hdb (hyd.trans_le (min_le_right _ _))
    refine ⟨hyW, ?_⟩
    have he := hTaylor y hyδ
    rw [hFp, sub_zero, hder] at he
    have he' := (neg_le_of_abs_le (by simpa only [Real.norm_eq_abs] using he))
    have hi := inner_pos_of_mem_tangent_ball hR hν hy
    have hi' := mul_lt_mul_of_pos_left hi ha
    have hK' := mul_le_mul_of_nonneg_right hcoef.le (sq_nonneg ‖y - p‖)
    have he'' := mul_le_mul_of_nonneg_left he' (show 0 ≤ 2 * R by positivity)
    have hprod : 0 < (2 * R) * F y := by nlinarith only [hi', hK', he'']
    exact (mul_pos_iff_of_pos_left (by positivity : 0 < 2 * R)).mp hprod
  · change dist p (p + R • ν) = R
    rw [dist_comm]
    exact hcenter

end LiquidDrop

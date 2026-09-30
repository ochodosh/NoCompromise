module

public import NoCompromise.Elliptic.NondivSchauderNorm

@[expose] public section

/-! The quasilinear derivative estimate and full sum norm use genuine operator
norms. The only zeroth-order contribution is the original essential uniform
norm, with coefficient one. -/

noncomputable section
open MeasureTheory Filter Metric Set InnerProductSpace
open scoped ENNReal NNReal Topology Gradient RealInnerProductSpace
namespace LiquidDrop
set_option maxSynthPendingDepth 8

lemma quasilinear_holder_of_modulus {E F : Type*} [NormedAddCommGroup E]
    [NormedAddCommGroup F] {a M H : ℝ} (hM : 0 ≤ M) (hH : 0 ≤ H)
    {f : E → F} {U : Set E} (hb : ∀ x ∈ U, ‖f x‖ ≤ M)
    (hh : ∀ x ∈ U, ∀ y ∈ U, ‖f x - f y‖ ≤ H * dist x y ^ a) :
    HasFiniteHolderNormOn a f U ∧ holderNorm a f U ≤ M + H := by
  have hq : ∀ x ∈ U, ∀ y ∈ U, ‖f x - f y‖ / ‖x - y‖ ^ a ≤ H := by
    intro x hx y hy
    by_cases he : x = y
    · subst y
      simpa only [sub_self, norm_zero, zero_div] using hH
    · apply (div_le_iff₀ (Real.rpow_pos_of_pos
        (norm_pos_iff.mpr (sub_ne_zero.mpr he)) a)).mpr
      simpa only [dist_eq_norm] using hh x hx y hy
  exact ⟨HasFiniteHolderNormOn.of_bounds hM hH hb hq, holderNorm_le hM hH hb hq⟩

/-- Classical second-derivative bounds yield the precise gradient C¹,α estimate
and the full scalar sum norm with no additive-constant loss. -/
theorem quasilinear_norm_bounds {n : ℕ} {a M H K : ℝ}
    (ha : 0 < a) (ha1 : a < 1) (hM : 0 ≤ M) (hH : 0 ≤ H) (hK : 0 ≤ K)
    {f : EuclideanSpace ℝ (Fin n) → ℝ}
    (hf : HasC1HolderOn a f (ball 0 1))
    (hc : ContDiffOn ℝ 2 f (ball 0 (1 / 2 : ℝ)))
    (hfM : ∀ x ∈ ball 0 (1 : ℝ), ‖gradient f x‖ ≤ M)
    (hfH : holderSeminorm a (gradient f) (ball 0 1) ≤ H)
    (hb : ∀ x ∈ ball 0 (1 / 2 : ℝ), ‖fderiv ℝ (fderiv ℝ f) x‖ ≤ K)
    (hh : ∀ x ∈ ball 0 (1 / 2 : ℝ), ∀ y ∈ ball 0 (1 / 2 : ℝ),
      ‖fderiv ℝ (fderiv ℝ f) x - fderiv ℝ (fderiv ℝ f) y‖ ≤ K * dist x y ^ a) :
    HasC1HolderOn a (gradient f) (ball 0 (1 / 2)) ∧
      nondivC1HolderNorm a (gradient f) (ball 0 (1 / 2)) ≤ M + H + 2 * K ∧
      HasC2HolderOn a f (ball 0 (1 / 2)) ∧
      schauderC2HolderNorm a f (ball 0 (1 / 2)) ≤
        lpNorm f ∞ (volume.restrict (ball 0 1)) + (2 * M + H + 2 * K) := by
  let U : Set (EuclideanSpace ℝ (Fin n)) := ball 0 (1 / 2)
  have hU1 : U ⊆ ball 0 (1 : ℝ) := ball_subset_ball (by norm_num : (1 / 2 : ℝ) ≤ 1)
  have hgradb : ∀ x ∈ U, ‖gradient f x‖ ≤ M := fun x hx => hfM x (hU1 hx)
  have hgradH : ∀ x ∈ U, ∀ y ∈ U,
      ‖gradient f x - gradient f y‖ ≤ H * dist x y ^ a := by
    intro x hx y hy
    apply (hf.gradient_holder.1.nondiv_norm_sub_le (hU1 hx) (hU1 hy)).trans
    simpa only [dist_eq_norm] using
      mul_le_mul_of_nonneg_right hfH (Real.rpow_nonneg (norm_nonneg (x - y)) a)
  obtain ⟨hgradh, hgradNb⟩ := quasilinear_holder_of_modulus hM hH hgradb hgradH
  have hDb : ∀ x ∈ U, ‖fderiv ℝ f x‖ ≤ M := by
    intro x hx
    simpa only [gradient, LinearIsometryEquiv.norm_map] using hgradb x hx
  have hDH : ∀ x ∈ U, ∀ y ∈ U,
      ‖fderiv ℝ f x - fderiv ℝ f y‖ ≤ H * dist x y ^ a := by
    intro x hx y hy
    simpa only [gradient, ← map_sub, LinearIsometryEquiv.norm_map] using hgradH x hx y hy
  obtain ⟨hDh, hDNb⟩ := quasilinear_holder_of_modulus hM hH hDb hDH
  obtain ⟨hHh, hHNb⟩ := quasilinear_holder_of_modulus hK hK hb hh
  have hcD : ContDiffOn ℝ 1 (fderiv ℝ f) U :=
    hc.fderiv_of_isOpen isOpen_ball (by norm_num)
  let L := (toDual ℝ (EuclideanSpace ℝ (Fin n))).symm.toContinuousLinearEquiv.toContinuousLinearMap
  have hL : ‖L‖ ≤ 1 := by
    apply ContinuousLinearMap.opNorm_le_bound _ zero_le_one
    intro v
    change ‖(toDual ℝ (EuclideanSpace ℝ (Fin n))).symm v‖ ≤ 1 * ‖v‖
    rw [LinearIsometryEquiv.norm_map, one_mul]
  have hcgrad : ContDiffOn ℝ 1 (gradient f) U := L.contDiff.comp_contDiffOn hcD
  have hDG (x) (hx : x ∈ U) :
      fderiv ℝ (gradient f) x = L.comp (fderiv ℝ (fderiv ℝ f) x) := by
    have hd := ((hcD.contDiffAt (isOpen_ball.mem_nhds hx)).differentiableAt one_ne_zero).hasFDerivAt
    exact (L.hasFDerivAt.comp x hd).fderiv
  have hDGb (x) (hx : x ∈ U) : ‖fderiv ℝ (gradient f) x‖ ≤ K := by
    rw [hDG x hx]
    apply (ContinuousLinearMap.opNorm_comp_le _ _).trans
    exact (mul_le_mul hL (hb x hx) (norm_nonneg _) zero_le_one).trans_eq (one_mul _)
  have hDGH (x) (hx : x ∈ U) (y) (hy : y ∈ U) :
      ‖fderiv ℝ (gradient f) x - fderiv ℝ (gradient f) y‖ ≤ K * dist x y ^ a := by
    rw [hDG x hx, hDG y hy, ← ContinuousLinearMap.comp_sub]
    apply (ContinuousLinearMap.opNorm_comp_le _ _).trans
    exact (mul_le_mul hL (hh x hx y hy) (norm_nonneg _) zero_le_one).trans_eq (one_mul _)
  obtain ⟨hDGh, hDGNb⟩ := quasilinear_holder_of_modulus hK hK hDGb hDGH
  have hm := hf.memLp_top isOpen_ball
  let Z := lpNorm f ∞ (volume.restrict (ball 0 1))
  have hZ : 0 ≤ Z := lpNorm_nonneg
  have hfb (x) (hx : x ∈ U) : ‖f x‖ ≤ Z :=
    holderInterpolation_norm_le_lpNorm_top isOpen_ball hf.contDiff.continuousOn hm x (hU1 hx)
  have hfHsmall (x) (hx : x ∈ U) (y) (hy : y ∈ U) :
      ‖f x - f y‖ ≤ M * dist x y ^ a := by
    have hconv := convex_ball (0 : EuclideanSpace ℝ (Fin n)) (1 / 2 : ℝ)
    have hlip := hconv.norm_image_sub_le_of_norm_fderiv_le
        (fun z hz => (hc.contDiffAt (isOpen_ball.mem_nhds hz)).differentiableAt (by norm_num))
        hDb hy hx
    have hd : dist x y ≤ 1 := by
      have hx' : ‖x‖ < 1 / 2 := mem_ball_zero_iff.mp hx
      have hy' : ‖y‖ < 1 / 2 := mem_ball_zero_iff.mp hy
      rw [dist_eq_norm]
      exact (norm_sub_le _ _).trans (by linarith)
    have hp : dist x y ≤ dist x y ^ a := by
      simpa only [Real.rpow_one] using
        Real.rpow_le_rpow_of_exponent_ge' dist_nonneg hd ha.le ha1.le
    exact hlip.trans (by simpa only [dist_eq_norm] using mul_le_mul_of_nonneg_left hp hM)
  obtain ⟨hfh, hfNb⟩ := quasilinear_holder_of_modulus hZ hM hfb hfHsmall
  refine ⟨⟨hcgrad, hgradh, hDGh⟩, ?_, ⟨hc, hfh, hDh, hHh⟩, ?_⟩
  · change holderNorm a (gradient f) U + holderNorm a (fderiv ℝ (gradient f)) U ≤ _
    linarith only [hgradNb, hDGNb]
  · change holderNorm a f U + holderNorm a (fderiv ℝ f) U +
      holderNorm a (fderiv ℝ (fderiv ℝ f)) U ≤ Z + _
    linarith only [hfNb, hDNb, hHNb]

end LiquidDrop

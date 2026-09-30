module

public import NoCompromise.Elliptic.NondivSchauderData
public import NoCompromise.Sobolev.H1DifferenceQuotient

@[expose] public section

/-!
# Uniform Hölder bounds for coefficient difference quotients

Parallel-segment mean-value estimates give the C⁰,α bound for δₕA directly
from the genuine C⁰,α norm of DA. The bound is independent of h and is valid
for positive or negative nonzero steps. No derivative of order two is used.
-/

noncomputable section
open MeasureTheory Filter Metric Set InnerProductSpace
open scoped ENNReal Topology Gradient
namespace LiquidDrop
set_option maxSynthPendingDepth 8

lemma nondiv_hasDerivAt_segment {E F : Type*}
    [NormedAddCommGroup E] [NormedSpace ℝ E]
    [NormedAddCommGroup F] [NormedSpace ℝ F]
    {f : E → F} {U : Set E} (hU : IsOpen U) (hf : ContDiffOn ℝ 1 f U)
    (x v : E) {t : ℝ} (ht : x + t • v ∈ U) :
    HasDerivAt (fun s : ℝ => f (x + s • v)) (fderiv ℝ f (x + t • v) v) t := by
  have hd := ((hf.contDiffAt (hU.mem_nhds ht)).differentiableAt one_ne_zero).hasFDerivAt
  have hp : HasDerivAt (fun s : ℝ => x + s • v) v t := by
    simpa only [one_smul, id_eq] using ((hasDerivAt_id t).smul_const v).const_add x
  exact hd.comp_hasDerivAt t hp

lemma nondiv_norm_segment_increment_le {E F : Type*}
    [NormedAddCommGroup E] [NormedSpace ℝ E]
    [NormedAddCommGroup F] [NormedSpace ℝ F]
    {f : E → F} {U : Set E} (hU : IsOpen U) (hf : ContDiffOn ℝ 1 f U)
    {M : ℝ} (hb : ∀ x ∈ U, ‖fderiv ℝ f x‖ ≤ M)
    (x v : E) (hseg : ∀ t ∈ Icc (0 : ℝ) 1, x + t • v ∈ U) :
    ‖f (x + v) - f x‖ ≤ M * ‖v‖ := by
  have h := norm_image_sub_le_of_norm_deriv_le_segment_01'
    (fun t ht => (nondiv_hasDerivAt_segment hU hf x v (hseg t ht)).hasDerivWithinAt)
    (fun t ht => ((fderiv ℝ f (x + t • v)).le_opNorm v).trans
      (mul_le_mul_of_nonneg_right (hb _ (hseg t (Ico_subset_Icc_self ht))) (norm_nonneg v)))
  simpa only [one_smul, zero_smul, add_zero] using h

/-- The mixed increment is controlled by the Hölder modulus of the derivative,
using only the two parallel displacement segments. -/
lemma nondiv_norm_parallel_increment_le {E F : Type*}
    [NormedAddCommGroup E] [NormedSpace ℝ E]
    [NormedAddCommGroup F] [NormedSpace ℝ F]
    {α : ℝ} {f : E → F} {U : Set E} (hU : IsOpen U) (hf : HasC1HolderOn α f U)
    (x y v : E)
    (hx : ∀ t ∈ Icc (0 : ℝ) 1, x + t • v ∈ U)
    (hy : ∀ t ∈ Icc (0 : ℝ) 1, y + t • v ∈ U) :
    ‖(f (x + v) - f x) - (f (y + v) - f y)‖ ≤
      holderSeminorm α (fderiv ℝ f) U * ‖x - y‖ ^ α * ‖v‖ := by
  have hder (t : ℝ) (ht : t ∈ Icc (0 : ℝ) 1) :
      HasDerivWithinAt (fun s : ℝ => f (x + s • v) - f (y + s • v))
        ((fderiv ℝ f (x + t • v) - fderiv ℝ f (y + t • v)) v) (Icc (0 : ℝ) 1) t := by
    simpa only [sub_apply] using!
      ((nondiv_hasDerivAt_segment hU hf.contDiff x v (hx t ht)).sub
        (nondiv_hasDerivAt_segment hU hf.contDiff y v (hy t ht))).hasDerivWithinAt
  have hb (t : ℝ) (ht : t ∈ Ico (0 : ℝ) 1) :
      ‖(fderiv ℝ f (x + t • v) - fderiv ℝ f (y + t • v)) v‖ ≤
        holderSeminorm α (fderiv ℝ f) U * ‖x - y‖ ^ α * ‖v‖ := by
    apply (ContinuousLinearMap.le_opNorm _ v).trans
    apply mul_le_mul_of_nonneg_right _ (norm_nonneg v)
    have h := hf.derivative_holder.nondiv_norm_sub_le
      (hx t (Ico_subset_Icc_self ht)) (hy t (Ico_subset_Icc_self ht))
    simpa only [add_sub_add_right_eq_sub] using h
  have h := norm_image_sub_le_of_norm_deriv_le_segment_01' hder hb
  simp only [one_smul, zero_smul, add_zero] at h
  convert h using 1
  congr 1
  abel

/-- The exact derivative Hölder norm bounds every coordinate difference quotient
on any set whose displacement segments stay inside the C¹,α domain. -/
theorem nondiv_coordinateDifferenceQuotient_holder {n : ℕ} {F : Type*}
    [NormedAddCommGroup F] [NormedSpace ℝ F]
    {α : ℝ} {f : EuclideanSpace ℝ (Fin n) → F}
    {U V : Set (EuclideanSpace ℝ (Fin n))} (hU : IsOpen U) (hf : HasC1HolderOn α f U)
    (i : Fin n) {h : ℝ} (hh : h ≠ 0)
    (hseg : ∀ x ∈ V, ∀ t ∈ Icc (0 : ℝ) 1, x + t • (h • EuclideanSpace.single i 1) ∈ U) :
    HasFiniteHolderNormOn α (coordinateDifferenceQuotient i h f) V ∧
      holderNorm α (coordinateDifferenceQuotient i h f) V ≤ holderNorm α (fderiv ℝ f) U := by
  have hn : ‖h⁻¹‖ * ‖h • EuclideanSpace.single i (1 : ℝ)‖ = 1 := by
    simp only [norm_smul, PiLp.norm_single, norm_one, mul_one, norm_inv]
    exact inv_mul_cancel₀ (norm_ne_zero_iff.mpr hh)
  have hA := holderUniformNorm_nonneg hf.derivative_holder.uniform_bounded
  have hB := hf.derivative_holder.seminorm_nonneg
  have hv : ∀ x ∈ V, ‖coordinateDifferenceQuotient i h f x‖ ≤
      holderUniformNorm (fderiv ℝ f) U := by
    intro x hx
    have ht := nondiv_norm_segment_increment_le hU hf.contDiff
      (fun y hy => norm_le_holderUniformNorm hf.derivative_holder.uniform_bounded hy)
      x (h • EuclideanSpace.single i 1) (hseg x hx)
    change ‖h⁻¹ • (f (x + h • EuclideanSpace.single i 1) - f x)‖ ≤ _
    rw [norm_smul]
    apply (mul_le_mul_of_nonneg_left ht (norm_nonneg _)).trans_eq
    calc
      _ = (‖h⁻¹‖ * ‖h • EuclideanSpace.single i (1 : ℝ)‖) *
          holderUniformNorm (fderiv ℝ f) U := by ring
      _ = _ := by rw [hn, one_mul]
  have hi : ∀ x ∈ V, ∀ y ∈ V,
      ‖coordinateDifferenceQuotient i h f x - coordinateDifferenceQuotient i h f y‖ ≤
        holderSeminorm α (fderiv ℝ f) U * ‖x - y‖ ^ α := by
    intro x hx y hy
    have hb := nondiv_norm_parallel_increment_le hU hf x y
      (h • EuclideanSpace.single i 1) (hseg x hx) (hseg y hy)
    simp only [coordinateDifferenceQuotient, ← smul_sub, norm_smul]
    apply (mul_le_mul_of_nonneg_left hb (norm_nonneg _)).trans_eq
    calc
      _ = (‖h⁻¹‖ * ‖h • EuclideanSpace.single i (1 : ℝ)‖) *
          (holderSeminorm α (fderiv ℝ f) U * ‖x - y‖ ^ α) := by ring
      _ = _ := by rw [hn, one_mul]
  have hq : ∀ x ∈ V, ∀ y ∈ V,
      ‖coordinateDifferenceQuotient i h f x - coordinateDifferenceQuotient i h f y‖ /
        ‖x - y‖ ^ α ≤ holderSeminorm α (fderiv ℝ f) U := by
    intro x hx y hy
    by_cases he : x = y
    · subst y
      simp only [sub_self, norm_zero, zero_div]
      exact hB
    · exact (div_le_iff₀ (Real.rpow_pos_of_pos
        (norm_pos_iff.mpr (sub_ne_zero.mpr he)) α)).mpr (hi x hx y hy)
  exact ⟨HasFiniteHolderNormOn.of_bounds hA hB hv hq, holderNorm_le hA hB hv hq⟩

/-- The actual difference quotient remains C¹ on the translated interior domain. -/
lemma nondiv_coordinateDifferenceQuotient_contDiffOn {n : ℕ} {F : Type*}
    [NormedAddCommGroup F] [NormedSpace ℝ F]
    {f : EuclideanSpace ℝ (Fin n) → F} {U V : Set (EuclideanSpace ℝ (Fin n))}
    (hf : ContDiffOn ℝ 1 f U) (hVU : V ⊆ U) (i : Fin n) (h : ℝ)
    (hmap : ∀ x ∈ V, x + h • EuclideanSpace.single i 1 ∈ U) :
    ContDiffOn ℝ 1 (coordinateDifferenceQuotient i h f) V :=
  contDiffOn_const.smul
    ((hf.comp (contDiff_id.add contDiff_const).contDiffOn hmap).sub (hf.mono hVU))

end LiquidDrop

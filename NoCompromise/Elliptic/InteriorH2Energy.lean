module

public import NoCompromise.Elliptic.InteriorH2Mollification
public import NoCompromise.Elliptic.Caccioppoli

@[expose] public section

/-!
# Cutoff energy estimates for smooth Poisson solutions

These estimates apply to the smooth interior convolutions of distributional L²
solutions and do not impose an H¹ assumption on the original solution.
-/

noncomputable section

open MeasureTheory Filter Metric Set InnerProductSpace
open scoped NNReal ENNReal Topology Gradient Convolution

namespace LiquidDrop

set_option maxSynthPendingDepth 8

lemma contDiff_gradient_of_contDiff_succ {n : ℕ} {r : WithTop ℕ∞}
    {u : EuclideanSpace ℝ (Fin n) → ℝ} (hu : ContDiff ℝ (r + 1) u) :
    ContDiff ℝ r (gradient u) :=
  (toDual ℝ (EuclideanSpace ℝ (Fin n))).symm.contDiff.comp (hu.fderiv_right le_rfl)

lemma continuous_laplacianN {n : ℕ} {u : EuclideanSpace ℝ (Fin n) → ℝ}
    (hu : ContDiff ℝ 2 u) : Continuous (laplacianN u) := by
  classical
  apply continuous_finsetSum
  intro i _
  exact (ContDiff.poissonCoordinateDerivative (r := 0)
    (ContDiff.poissonCoordinateDerivative (r := 1) hu i) i).continuous

/-- Classical integration by parts against a compact C¹ scalar test. -/
lemma integral_mul_poissonCoordinateDerivative {n : ℕ}
    {u φ : EuclideanSpace ℝ (Fin n) → ℝ}
    (hu : ContDiff ℝ 1 u) (hφ : ContDiff ℝ 1 φ) (hcφ : HasCompactSupport φ) (i : Fin n) :
    (∫ x, u x * poissonCoordinateDerivative i φ x) =
      -(∫ x, φ x * poissonCoordinateDerivative i u x) := by
  have h := (hasWeakGradientOn_of_contDiffOn isOpen_univ hu.contDiffOn).test_eq
    i φ hφ hcφ (subset_univ _)
  simp only [setIntegral_univ, ← poissonCoordinateDerivative_eq_gradient] at h
  exact (neg_eq_iff_eq_neg.mp h)

/-- Green's identity requires compact support only for the scalar test. -/
lemma integral_mul_laplacianN {n : ℕ}
    {u φ : EuclideanSpace ℝ (Fin n) → ℝ}
    (hu : ContDiff ℝ 2 u) (hφ : ContDiff ℝ 1 φ) (hcφ : HasCompactSupport φ) :
    (∫ x, φ x * laplacianN u x) = -(∫ x, inner ℝ (gradient φ x) (gradient u x)) := by
  classical
  have hdu (i : Fin n) : ContDiff ℝ 1 (poissonCoordinateDerivative i u) :=
    ContDiff.poissonCoordinateDerivative (r := 1) hu i
  have hid (i : Fin n) : Integrable
      (fun x => φ x * poissonCoordinateDerivative i (poissonCoordinateDerivative i u) x) :=
    (hφ.continuous.mul
      (ContDiff.poissonCoordinateDerivative (r := 0) (hdu i) i).continuous
    ).integrable_of_hasCompactSupport
       hcφ.mul_right
  have hip (i : Fin n) : Integrable
      (fun x => poissonCoordinateDerivative i φ x * poissonCoordinateDerivative i u x) :=
    ((ContDiff.poissonCoordinateDerivative (r := 0) hφ i).continuous.mul
      (hdu i).continuous).integrable_of_hasCompactSupport
       (HasCompactSupport.poissonCoordinateDerivative hcφ i).mul_right
  have he (i : Fin n) :
      (∫ x, φ x * poissonCoordinateDerivative i (poissonCoordinateDerivative i u) x) =
      -(∫ x, poissonCoordinateDerivative i φ x * poissonCoordinateDerivative i u x) := by
    have h := integral_mul_poissonCoordinateDerivative (hdu i) hφ hcφ i
    simp_rw [mul_comm (poissonCoordinateDerivative i u _)] at h
    linarith
  simp only [laplacianN, Finset.mul_sum, PiLp.inner_apply, Real.inner_apply,
    ← poissonCoordinateDerivative_eq_gradient]
  rw [integral_finsetSum _ (fun i _ => hid i), integral_finsetSum _ (fun i _ => hip i)]
  simp_rw [he]
  exact Finset.sum_neg_distrib _

set_option maxHeartbeats 400000 in
-- Expanded product-gradient identities require additional elaboration fuel.
/-- The exact cutoff energy identity underlying the local L²-to-H¹ estimate.
The expanded product-gradient identities require additional elaboration fuel. -/
lemma integral_cutoff_gradient_sq {n : ℕ}
    {u η : EuclideanSpace ℝ (Fin n) → ℝ}
    (hu : ContDiff ℝ 2 u) (hη : ContDiff ℝ 1 η) (hcη : HasCompactSupport η) :
    (∫ x, η x ^ 2 * ‖gradient u x‖ ^ 2) =
      -(∫ x, η x ^ 2 * u x * laplacianN u x) -
        2 * ∫ x, η x * u x * inner ℝ (gradient η x) (gradient u x) := by
  have hu1 := hu.of_le (by norm_num : (1 : WithTop ℕ∞) ≤ 2)
  have hφ : ContDiff ℝ 1 (fun x => η x ^ 2 * u x) := (hη.pow 2).mul hu1
  have hcφ : HasCompactSupport (fun x => η x ^ 2 * u x) := by
    have ht : HasCompactSupport (fun x => η x * η x * u x) := hcη.mul_right.mul_right
    simpa only [pow_two] using ht
  have he := integral_mul_laplacianN hu hφ hcφ
  have hgrad (x : EuclideanSpace ℝ (Fin n)) :
      gradient (fun y => η y ^ 2 * u y) x =
        η x ^ 2 • gradient u x + (2 * η x * u x) • gradient η x := by
    rw [gradient_mul (hη.pow 2) hu1]
    have hηgrad : gradient (fun y => η y ^ 2) x = (2 * η x) • gradient η x := by
      simpa only [pow_two, two_mul, add_smul] using gradient_mul hη hη x
    rw [hηgrad, smul_smul]
    rw [show u x * (2 * η x) = 2 * η x * u x by ring]
  have hi1 : Integrable (fun x => η x ^ 2 * ‖gradient u x‖ ^ 2) :=
    ((hη.continuous.pow 2).mul
      ((continuous_gradient_of_contDiff hu1).norm.pow 2)).integrable_of_hasCompactSupport
      (by
        change HasCompactSupport (fun x => η x ^ 2 * ‖gradient u x‖ ^ 2)
        have ht : HasCompactSupport (fun x => η x * η x * ‖gradient u x‖ ^ 2) :=
          hcη.mul_right.mul_right
        simpa only [pow_two] using ht)
  have hi2 : Integrable (fun x => η x * u x * inner ℝ (gradient η x) (gradient u x)) :=
    ((hη.continuous.mul hu.continuous).mul
      ((continuous_gradient_of_contDiff hη).inner
        (continuous_gradient_of_contDiff hu1))).integrable_of_hasCompactSupport
      hcη.mul_right.mul_right
  simp_rw [hgrad, inner_add_left, real_inner_smul_left, real_inner_self_eq_norm_sq] at he
  have hp (x : EuclideanSpace ℝ (Fin n)) :
      (2 * η x * u x) * inner ℝ (gradient η x) (gradient u x) =
        2 * (η x * u x * inner ℝ (gradient η x) (gradient u x)) := by ring
  simp_rw [hp] at he
  rw [integral_add hi1 (hi2.const_mul 2), integral_const_mul] at he
  linarith

/-- The pointwise completion of squares used for the Poisson cutoff estimate. -/
lemma poisson_cutoff_pointwise {F : Type*} [NormedAddCommGroup F] [InnerProductSpace ℝ F]
    (a b : ℝ) (v w : F) :
    ‖v‖ ^ 2 ≤ a ^ 2 + b ^ 2 + 4 * ‖w‖ ^ 2 +
      2 * (a * b + ‖v‖ ^ 2 + 2 * inner ℝ v w) := by
  have h := sq_nonneg ‖v + (2 : ℝ) • w‖
  rw [norm_add_sq_real, norm_smul, inner_smul_right] at h
  norm_num at h
  nlinarith [sq_nonneg (a + b)]

/-- Integrated completion of squares for L² data. -/
lemma poisson_integral_energy {α F : Type*} [MeasurableSpace α]
    [NormedAddCommGroup F] [InnerProductSpace ℝ F]
    {μ : Measure α} {a b : α → ℝ} {v w : α → F}
    (ha : MemLp a 2 μ) (hb : MemLp b 2 μ) (hv : MemLp v 2 μ) (hw : MemLp w 2 μ)
    (htest : (∫ x, a x * b x ∂μ) + (∫ x, ‖v x‖ ^ 2 ∂μ) +
      2 * ∫ x, inner ℝ (v x) (w x) ∂μ = 0) :
    (∫ x, ‖v x‖ ^ 2 ∂μ) ≤ (∫ x, ‖a x‖ ^ 2 ∂μ) +
      (∫ x, ‖b x‖ ^ 2 ∂μ) + 4 * ∫ x, ‖w x‖ ^ 2 ∂μ := by
  have hiV : Integrable (fun x => ‖v x‖ ^ 2) μ := hv.integrable_norm_pow (by norm_num)
  have hiW : Integrable (fun x => ‖w x‖ ^ 2) μ := hw.integrable_norm_pow (by norm_num)
  have hiA : Integrable (fun x => ‖a x‖ ^ 2) μ := ha.integrable_norm_pow (by norm_num)
  have hiB : Integrable (fun x => ‖b x‖ ^ 2) μ := hb.integrable_norm_pow (by norm_num)
  have hiAB : Integrable (fun x => a x * b x) μ := ha.integrable_mul hb
  have hiVW := integrable_inner_of_memLp_two hv hw
  have hpoint (x : α) :
      ‖v x‖ ^ 2 ≤ ‖a x‖ ^ 2 + ‖b x‖ ^ 2 + 4 * ‖w x‖ ^ 2 +
        2 * (a x * b x + ‖v x‖ ^ 2 + 2 * inner ℝ (v x) (w x)) := by
    simpa only [Real.norm_eq_abs, sq_abs] using
      poisson_cutoff_pointwise (a x) (b x) (v x) (w x)
  have hiR := ((hiA.add hiB).add (hiW.const_mul 4)).add
    (((hiAB.add hiV).add (hiVW.const_mul 2)).const_mul 2)
  have h := integral_mono hiV hiR hpoint
  change (∫ x, ‖v x‖ ^ 2 ∂μ) ≤ ∫ x,
    ‖a x‖ ^ 2 + ‖b x‖ ^ 2 + 4 * ‖w x‖ ^ 2 +
      2 * (a x * b x + ‖v x‖ ^ 2 + 2 * inner ℝ (v x) (w x)) ∂μ at h
  rw [integral_add (f := fun x => ‖a x‖ ^ 2 + ‖b x‖ ^ 2 + 4 * ‖w x‖ ^ 2)
    (g := fun x => 2 * (a x * b x + ‖v x‖ ^ 2 + 2 * inner ℝ (v x) (w x)))
    ((hiA.add hiB).add (hiW.const_mul 4))
    (((hiAB.add hiV).add (hiVW.const_mul 2)).const_mul 2)] at h
  rw [integral_add (f := fun x => ‖a x‖ ^ 2 + ‖b x‖ ^ 2)
    (g := fun x => 4 * ‖w x‖ ^ 2) (hiA.add hiB) (hiW.const_mul 4),
    integral_add hiA hiB, integral_const_mul, integral_const_mul,
    integral_add (f := fun x => a x * b x + ‖v x‖ ^ 2)
      (g := fun x => 2 * inner ℝ (v x) (w x)) (hiAB.add hiV) (hiVW.const_mul 2),
    integral_add hiAB hiV, integral_const_mul] at h
  rw [htest, mul_zero, add_zero] at h
  exact h

/-- A local energy estimate for smooth functions with scalar Poisson forcing.
All integrals are finite because the cutoff is compactly supported. -/
theorem smooth_poisson_cutoff_energy {n : ℕ}
    {u η : EuclideanSpace ℝ (Fin n) → ℝ}
    (hu : ContDiff ℝ 2 u) (hη : ContDiff ℝ 1 η) (hcη : HasCompactSupport η) :
    (∫ x, η x ^ 2 * ‖gradient u x‖ ^ 2) ≤
      (∫ x, η x ^ 2 * u x ^ 2) + (∫ x, η x ^ 2 * laplacianN u x ^ 2) +
        4 * ∫ x, u x ^ 2 * ‖gradient η x‖ ^ 2 := by
  let v (x : EuclideanSpace ℝ (Fin n)) : EuclideanSpace ℝ (Fin n) := η x • gradient u x
  let w (x : EuclideanSpace ℝ (Fin n)) : EuclideanSpace ℝ (Fin n) := u x • gradient η x
  let a (x : EuclideanSpace ℝ (Fin n)) := η x * u x
  let b (x : EuclideanSpace ℝ (Fin n)) := η x * laplacianN u x
  have hu1 := hu.of_le (by norm_num : (1 : WithTop ℕ∞) ≤ 2)
  have hcv : HasCompactSupport v := hcη.smul_right
  have hcgrad : HasCompactSupport (gradient η) :=
    hcη.of_isClosed_subset (isClosed_tsupport _) (tsupport_gradient_subset η)
  have hcw : HasCompactSupport w := HasCompactSupport.smul_left (f := u) hcgrad
  have hv : MemLp v 2 volume :=
    (hη.continuous.smul (continuous_gradient_of_contDiff hu1)).memLp_of_hasCompactSupport hcv
  have hw : MemLp w 2 volume :=
    (hu.continuous.smul (continuous_gradient_of_contDiff hη)).memLp_of_hasCompactSupport hcw
  have ha : MemLp a 2 volume :=
    (hη.continuous.mul hu.continuous).memLp_of_hasCompactSupport hcη.mul_right
  have hb : MemLp b 2 volume :=
    (hη.continuous.mul (continuous_laplacianN hu)).memLp_of_hasCompactSupport hcη.mul_right
  have htest : (∫ x, a x * b x) + (∫ x, ‖v x‖ ^ 2) +
      2 * ∫ x, inner ℝ (v x) (w x) = 0 := by
    have he := integral_cutoff_gradient_sq hu hη hcη
    have heq (x : EuclideanSpace ℝ (Fin n)) : a x * b x =
        η x ^ 2 * u x * laplacianN u x := by dsimp [a, b]; ring
    have heV (x : EuclideanSpace ℝ (Fin n)) :
        ‖v x‖ ^ 2 = η x ^ 2 * ‖gradient u x‖ ^ 2 := by
      simp only [v, norm_smul, mul_pow, Real.norm_eq_abs, sq_abs]
    have heVW (x : EuclideanSpace ℝ (Fin n)) :
        inner ℝ (v x) (w x) =
          η x * u x * inner ℝ (gradient η x) (gradient u x) := by
      simp only [v, w, real_inner_smul_left, inner_smul_right]
      rw [real_inner_comm (gradient u x)]
      ring
    simp_rw [heq, heV, heVW]
    linarith only [he]
  have h := poisson_integral_energy ha hb hv hw htest
  simpa only [v, w, a, b, norm_smul, Real.norm_eq_abs, mul_pow, sq_abs,
    norm_mul] using h

/-- The cutoff energy estimate expressed in ordinary L² norms. -/
theorem smooth_poisson_cutoff_lpNorm {n : ℕ}
    {u η : EuclideanSpace ℝ (Fin n) → ℝ}
    (hu : ContDiff ℝ 2 u) (hη : ContDiff ℝ 1 η) (hcη : HasCompactSupport η) :
    lpNorm (fun x => η x • gradient u x) 2 volume ≤
      lpNorm (fun x => η x * u x) 2 volume +
      lpNorm (fun x => η x * laplacianN u x) 2 volume +
      2 * lpNorm (fun x => u x • gradient η x) 2 volume := by
  let v (x : EuclideanSpace ℝ (Fin n)) : EuclideanSpace ℝ (Fin n) := η x • gradient u x
  let w (x : EuclideanSpace ℝ (Fin n)) : EuclideanSpace ℝ (Fin n) := u x • gradient η x
  let a (x : EuclideanSpace ℝ (Fin n)) := η x * u x
  let b (x : EuclideanSpace ℝ (Fin n)) := η x * laplacianN u x
  have hu1 := hu.of_le (by norm_num : (1 : WithTop ℕ∞) ≤ 2)
  have hcgrad : HasCompactSupport (gradient η) :=
    hcη.of_isClosed_subset (isClosed_tsupport _) (tsupport_gradient_subset η)
  have hv : MemLp v 2 volume :=
    (hη.continuous.smul (continuous_gradient_of_contDiff hu1)).memLp_of_hasCompactSupport
      (hcη.smul_right (f' := gradient u))
  have hw : MemLp w 2 volume :=
    (hu.continuous.smul (continuous_gradient_of_contDiff hη)).memLp_of_hasCompactSupport
      (hcgrad.smul_left (f := u))
  have ha : MemLp a 2 volume :=
    (hη.continuous.mul hu.continuous).memLp_of_hasCompactSupport hcη.mul_right
  have hb : MemLp b 2 volume :=
    (hη.continuous.mul (continuous_laplacianN hu)).memLp_of_hasCompactSupport hcη.mul_right
  have he := smooth_poisson_cutoff_energy hu hη hcη
  have hsq : lpNorm v 2 volume ^ 2 ≤ lpNorm a 2 volume ^ 2 +
      lpNorm b 2 volume ^ 2 + 4 * lpNorm w 2 volume ^ 2 := by
    rw [lpNorm_two_sq_eq_integral_norm_sq hv, lpNorm_two_sq_eq_integral_norm_sq ha,
      lpNorm_two_sq_eq_integral_norm_sq hb, lpNorm_two_sq_eq_integral_norm_sq hw]
    simpa only [v, a, b, w, norm_smul, norm_mul, mul_pow, Real.norm_eq_abs, sq_abs] using he
  have h0v : 0 ≤ lpNorm v 2 volume := lpNorm_nonneg
  have h0a : 0 ≤ lpNorm a 2 volume := lpNorm_nonneg
  have h0b : 0 ≤ lpNorm b 2 volume := lpNorm_nonneg
  have h0w : 0 ≤ lpNorm w 2 volume := lpNorm_nonneg
  change lpNorm v 2 volume ≤ lpNorm a 2 volume + lpNorm b 2 volume + 2 * lpNorm w 2 volume
  nlinarith [mul_nonneg h0a h0b, mul_nonneg h0a h0w, mul_nonneg h0b h0w]

end LiquidDrop

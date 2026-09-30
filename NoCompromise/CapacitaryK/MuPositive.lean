module

public import NoCompromise.CapacitaryK.Bochner
public import NoCompromise.Elliptic.InteriorH2Energy

@[expose] public section

/-!
# Positivity of the distributional Laplacian of the gradient length

The regularized Bochner identity is localized by a compact cutoff. The uniform
bound on the regularization error then passes positivity to the gradient length.
-/

noncomputable section
open MeasureTheory Filter Set InnerProductSpace
open scoped Topology Gradient ContDiff RealInnerProductSpace

namespace LiquidDrop.CapacitaryK

/-- `|w_ε - w| ≤ |ε|` (pure algebra). -/
theorem abs_gradNormEps_sub_gradNorm_le (ε : ℝ) (u : E3 → ℝ) (x : E3) :
    |gradNormEps ε u x - gradNorm u x| ≤ |ε| := by
  have hw := gradNorm_nonneg u x
  have hl : gradNorm u x ≤ gradNormEps ε u x :=
    Real.le_sqrt_of_sq_le (le_add_of_nonneg_right (sq_nonneg ε))
  have hr : gradNormEps ε u x ≤ gradNorm u x + |ε| := by
    apply (Real.sqrt_le_left (add_nonneg hw (abs_nonneg ε))).mpr
    nlinarith [sq_abs ε, mul_nonneg hw (abs_nonneg ε)]
  exact abs_le.mpr ⟨by linarith [abs_nonneg ε], by linarith⟩

/-- For `ε ≠ 0`, `Δw_ε ≥ 0` wherever `u` is `C³` and harmonic nearby. -/
theorem laplacianN_gradNormEps_nonneg {u : E3 → ℝ} {x : E3} {ε : ℝ} (hε : ε ≠ 0)
    (hu : ContDiffAt ℝ 3 u x) (hΔ : ∀ᶠ y in 𝓝 x, laplacianN u y = 0) :
    0 ≤ laplacianN (gradNormEps ε u) x := by
  have hp : 0 < gradNorm u x ^ 2 + ε ^ 2 :=
    add_pos_of_nonneg_of_pos (sq_nonneg _) (sq_pos_of_ne_zero hε)
  rw [laplacianN_gradNormEps hu hΔ hp]
  exact (bochner_rhs_ge u x hp).2.trans (bochner_rhs_ge u x hp).1

lemma regularized_contDiffAt {u : E3 → ℝ} {x : E3} {ε : ℝ}
    (hu : ContDiffAt ℝ 3 u x) (hε : ε ≠ 0) :
    ContDiffAt ℝ 2 (gradNormEps ε u) x := by
  have hcoord (i : Fin 3) : ContDiffAt ℝ 2 (fun y => gradient u y i) x := by
    simpa only [← poissonCoordinateDerivative_eq_gradient, poissonCoordinateDerivative] using
      (hu.fderiv_right (show (2 : ℕ∞ω) + 1 ≤ 3 by norm_num)).clm_apply
        (contDiffAt_const (c := basisVec i))
  have hs : ContDiffAt ℝ 2 (fun y => gradNorm u y ^ 2) x := by
    simp only [gradNorm_sq]
    exact ContDiffAt.sum fun i _ => (hcoord i).pow 2
  exact (hs.add contDiffAt_const).sqrt (ne_of_gt
    (add_pos_of_nonneg_of_pos (sq_nonneg _) (sq_pos_of_ne_zero hε)))

lemma gradient_length_continuousAt {u : E3 → ℝ} {x : E3}
    (hu : ContDiffAt ℝ 3 u x) : ContinuousAt (gradNorm u) x := by
  have hgrad : ContinuousAt (gradient u) x :=
    (toDual ℝ E3).symm.continuous.continuousAt.comp
      (hu.fderiv_right (show (2 : ℕ∞ω) + 1 ≤ 3 by norm_num)).continuousAt
  exact hgrad.norm

lemma laplacian_congr_near {f g : E3 → ℝ} {x : E3}
    (h : f =ᶠ[𝓝 x] g) : laplacianN f x = laplacianN g x := by
  unfold laplacianN
  apply Finset.sum_congr rfl
  intro i _
  have hc : poissonCoordinateDerivative i f =ᶠ[𝓝 x] poissonCoordinateDerivative i g := by
    filter_upwards [h.fderiv (𝕜 := ℝ)] with y hy
    exact congrArg (fun L => L (basisVec i)) hy
  exact congrArg (fun L => L (basisVec i)) (hc.fderiv_eq (𝕜 := ℝ))

lemma laplacian_support (f : E3 → ℝ) :
    tsupport (laplacianN f) ⊆ tsupport f := by
  apply closure_minimal _ (isClosed_tsupport f)
  intro x hx
  by_contra hn
  apply hx
  apply Finset.sum_eq_zero
  intro i _
  exact image_eq_zero_of_notMem_tsupport (fun h => hn
    ((tsupport_poissonCoordinateDerivative_subset i f)
      ((tsupport_poissonCoordinateDerivative_subset i (poissonCoordinateDerivative i f)) h)))

lemma integrable_mul_laplacian {U : Set E3} (hU : IsOpen U)
    {f φ : E3 → ℝ} (hf : ContinuousOn f U) (hφ : ContDiff ℝ 2 φ)
    (hcφ : HasCompactSupport φ) (hsφ : tsupport φ ⊆ U) :
    Integrable (fun x => f x * laplacianN φ x) := by
  have hcΔ : HasCompactSupport (laplacianN φ) :=
    hcφ.of_isClosed_subset (isClosed_tsupport _) (laplacian_support φ)
  apply Continuous.integrable_of_hasCompactSupport _ hcΔ.mul_left
  exact (hf.mul (continuous_laplacianN hφ).continuousOn).continuous_of_tsupport_subset
    hU (tsupport_mul_subset_right.trans ((laplacian_support φ).trans hsφ))

private lemma integral_regularized_nonneg {U : Set E3} (hU : IsOpen U)
    {u : E3 → ℝ} (hu : ContDiffOn ℝ 3 u U)
    (hΔ : ∀ x ∈ U, laplacianN u x = 0) {ε : ℝ} (hε : ε ≠ 0)
    {φ : E3 → ℝ} (hφ : ContDiff ℝ (⊤ : ℕ∞) φ)
    (hcφ : HasCompactSupport φ) (hsφ : tsupport φ ⊆ U) (hφ0 : ∀ x, 0 ≤ φ x) :
    0 ≤ ∫ x, gradNormEps ε u x * laplacianN φ x := by
  obtain ⟨χ, hχ, hcχ, hsχ, hone, _⟩ :=
    exists_smooth_cutoff_one_near_compact hcφ hU hsφ
  let v : E3 → ℝ := fun x => χ x * gradNormEps ε u x
  have hv : ContDiff ℝ 2 v := by
    apply contDiff_iff_contDiffAt.mpr
    intro x
    by_cases hx : x ∈ U
    · exact (hχ.of_le (by simp)).contDiffAt.mul
        (regularized_contDiffAt (hu.contDiffAt (hU.mem_nhds hx)) hε)
    · have hxt : x ∉ tsupport χ := fun ht => hx (hsχ ht)
      apply (contDiffAt_const (c := (0 : ℝ))).congr_of_eventuallyEq
      filter_upwards [(isClosed_tsupport χ).isOpen_compl.mem_nhds hxt] with y hy
      simp only [v, image_eq_zero_of_notMem_tsupport hy, zero_mul]
  have hcv : HasCompactSupport v := hcχ.mul_right
  have hnear (x : E3) (hx : x ∈ tsupport φ) : v =ᶠ[𝓝 x] gradNormEps ε u := by
    filter_upwards [hone.filter_mono (nhds_le_nhdsSet hx)] with y hy
    simp only [v, hy, one_mul]
  have heq : (fun x => gradNormEps ε u x * laplacianN φ x) =
      (fun x => v x * laplacianN φ x) := by
    funext x
    by_cases hx : x ∈ tsupport φ
    · rw [(hnear x hx).self_of_nhds]
    · have hz : laplacianN φ x = 0 := image_eq_zero_of_notMem_tsupport
        (fun ht => hx (laplacian_support φ ht))
      simp only [hz, mul_zero]
  have hgreen : (∫ x, v x * laplacianN φ x) = ∫ x, φ x * laplacianN v x := by
    rw [integral_mul_laplacianN (hφ.of_le (by simp)) (hv.of_le (by norm_num)) hcv,
      integral_mul_laplacianN hv (hφ.of_le (by simp)) hcφ]
    congr 1
    apply integral_congr_ae
    filter_upwards with x
    exact real_inner_comm _ _
  rw [heq, hgreen]
  apply integral_nonneg
  intro x
  by_cases hx : x ∈ tsupport φ
  · apply mul_nonneg (hφ0 x)
    rw [laplacian_congr_near (hnear x hx)]
    apply laplacianN_gradNormEps_nonneg hε (hu.contDiffAt (hU.mem_nhds (hsφ hx)))
    filter_upwards [hU.mem_nhds (hsφ hx)] with y hy
    exact hΔ y hy
  · simp only [image_eq_zero_of_notMem_tsupport hx, zero_mul, Pi.zero_apply, le_refl]

/-- `prop:K-mu`, positivity half: `Δw` is a positive distribution on the open set `U`
where `u` is `C³` and harmonic. -/
theorem integral_gradNorm_mul_laplacianN_nonneg {U : Set E3} (hU : IsOpen U) {u : E3 → ℝ}
    (hu : ContDiffOn ℝ 3 u U) (hΔ : ∀ x ∈ U, laplacianN u x = 0)
    {φ : E3 → ℝ} (hφ : ContDiff ℝ (⊤ : ℕ∞) φ) (hcφ : HasCompactSupport φ) (hsφ : tsupport φ ⊆ U)
    (hφ0 : ∀ x, 0 ≤ φ x) :
    0 ≤ ∫ x, gradNorm u x * laplacianN φ x := by
  have hw : ContinuousOn (gradNorm u) U := by
    intro x hx
    exact (gradient_length_continuousAt (hu.contDiffAt (hU.mem_nhds hx))).continuousWithinAt
  have hiw := integrable_mul_laplacian hU hw (hφ.of_le (by simp)) hcφ hsφ
  have hiε (ε : ℝ) : Integrable (fun x => gradNormEps ε u x * laplacianN φ x) :=
    integrable_mul_laplacian hU ((hw.pow 2).add continuousOn_const).sqrt
      (hφ.of_le (by simp)) hcφ hsφ
  have hiΔ : Integrable (fun x => |laplacianN φ x|) :=
    ((continuous_laplacianN (hφ.of_le (by simp))).integrable_of_hasCompactSupport
      (hcφ.of_isClosed_subset (isClosed_tsupport _) (laplacian_support φ))).abs
  let C : ℝ := ∫ x, |laplacianN φ x|
  have hC : 0 ≤ C := integral_nonneg fun _ => abs_nonneg _
  apply le_of_forall_pos_le_add
  intro δ hδ
  let ε : ℝ := δ / (C + 1)
  have hε : 0 < ε := div_pos hδ (by linarith)
  have hbound : ε * C ≤ δ := by
    have heq : ε * (C + 1) = δ := div_mul_cancel₀ δ (by linarith)
    nlinarith
  have hmono : (∫ x, gradNormEps ε u x * laplacianN φ x) ≤
      (∫ x, gradNorm u x * laplacianN φ x) + ε * C := by
    calc
      _ ≤ ∫ x, (gradNorm u x * laplacianN φ x + ε * |laplacianN φ x|) := by
        apply integral_mono (hiε ε) (hiw.add (hiΔ.const_mul ε))
        intro x
        change gradNormEps ε u x * laplacianN φ x ≤
          gradNorm u x * laplacianN φ x + ε * |laplacianN φ x|
        have hb := abs_gradNormEps_sub_gradNorm_le ε u x
        rw [abs_of_pos hε] at hb
        have hb' : (gradNormEps ε u x - gradNorm u x) * laplacianN φ x ≤
            ε * |laplacianN φ x| :=
          (le_abs_self _).trans (by
            rw [abs_mul]
            exact mul_le_mul_of_nonneg_right hb (abs_nonneg _))
        nlinarith
      _ = _ := by rw [integral_add hiw (hiΔ.const_mul ε), integral_const_mul]
  have hpos := integral_regularized_nonneg hU hu hΔ (ne_of_gt hε) hφ hcφ hsφ hφ0
  linarith

end LiquidDrop.CapacitaryK

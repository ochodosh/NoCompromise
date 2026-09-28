import NoCompromise.Sobolev.H1PositivePartPoincare
import NoCompromise.Elliptic.InteriorH2Hessian

/-!
# The positive-part energy argument for the weak maximum principle

The nonlinear positive part, its trace, nonnegative H¹₀ test approximation,
and bounded-domain coercivity are proved prerequisites. This module isolates
the remaining trace-kernel identification as an explicit input; it does not
claim that identification as an axiom or a definition of zero trace.
-/

noncomputable section
open MeasureTheory Filter Set InnerProductSpace
open scoped ENNReal NNReal Topology Gradient RealInnerProductSpace
namespace LiquidDrop
set_option maxSynthPendingDepth 8

/-- Weak first derivatives identify the two standard distributional Laplacian
pairings, without any second derivative assumption on the function. -/
lemma HasWeakGradientOn.integral_mul_laplacianN {n : ℕ}
    {D : Set (EuclideanSpace ℝ (Fin n))}
    {f : EuclideanSpace ℝ (Fin n) → ℝ}
    {G : EuclideanSpace ℝ (Fin n) → EuclideanSpace ℝ (Fin n)}
    (hf : HasWeakGradientOn f G D)
    {φ : EuclideanSpace ℝ (Fin n) → ℝ} (hφ : ContDiff ℝ 2 φ)
    (hcφ : HasCompactSupport φ) (hsφ : tsupport φ ⊆ D) :
    (∫ x in D, f x * laplacianN φ x) =
      -(∫ x in D, inner ℝ (G x) (gradient φ x)) := by
  have hg : ContDiff ℝ 1 (gradient φ) := contDiff_gradient_of_contDiff_succ hφ
  have hcg : HasCompactSupport (gradient φ) :=
    hcφ.of_isClosed_subset (isClosed_tsupport _) (tsupport_gradient_subset _)
  have h := hf.integral_divergence_eq hg hcg ((tsupport_gradient_subset _).trans hsφ)
  simp_rw [← laplacianN_eq_divergenceN_gradient hφ, real_inner_comm] at h
  exact neg_eq_iff_eq_neg.mp h

/-- The energy argument for the weak maximum principle, with the trace-kernel
identification kept explicit. The actual identification on Lipschitz domains
is proved separately. -/
theorem weak_maximum_of_trace_kernel {n : ℕ} (hn : 0 < n)
    {D : Set (EuclideanSpace ℝ (Fin n))} (hD : IsOpen D)
    (hbD : Bornology.IsBounded D) (hL : HasLipschitzBoundary D)
    {μ : Measure (EuclideanSpace ℝ (Fin n))}
    (T : H1Space D →L[ℝ] Lp ℝ 2 μ)
    (hT : ∀ f G (hf : HasH1GradientOn f G D), Continuous f →
      ⇑(T (H1Space.ofFunction f G hf)) =ᵐ[μ] f)
    (hker : ∀ v : H1Space D, T v = 0 → v ∈ h1ZeroSubmodule hD)
    (u : H1Space D)
    (hu : ∀ φ : EuclideanSpace ℝ (Fin n) → ℝ,
      ContDiff ℝ (⊤ : ℕ∞) φ → HasCompactSupport φ → tsupport φ ⊆ D →
      (∀ x, 0 ≤ φ x) → (∫ x in D, inner ℝ (u.gradientLp x) (gradient φ x)) ≤ 0)
    (hb : ∀ᵐ x ∂μ, T u x ≤ 0) : ∀ᵐ x ∂volume.restrict D, u x ≤ 0 := by
  obtain ⟨v, hv, ht, he⟩ := H1Space.exists_positivePart_of_trace hD hbD hL T hT u
  have htv : T v = 0 := by
    apply Lp.ext
    filter_upwards [ht, hb, Lp.coeFn_zero (E := ℝ) (p := 2) (μ := μ)] with x hx hb hz
    rw [hx, max_eq_right hb]
    exact hz.symm
  let w : H1ZeroSpace hD := ⟨v, hker v htv⟩
  have hw : ∀ᵐ x ∂volume.restrict D, 0 ≤ w.val x := by
    filter_upwards [hv] with x hx
    exact hx.symm ▸ le_max_right (u x) 0
  have hi := H1ZeroSpace.inner_gradient_le_zero_of_smooth_tests hD hbD.measure_lt_top u hu w hw
  have hg : ‖v.gradientLp‖ = 0 := by
    change inner ℝ u.gradientLp v.gradientLp ≤ 0 at hi
    nlinarith only [he, hi, norm_nonneg v.gradientLp]
  obtain ⟨C, _, hC⟩ := H1ZeroSpace.poincare_bounded hn hD hbD
  have hf : v.toLp = 0 := by
    apply norm_eq_zero.mp
    have h := hC w
    change ‖v.toLp‖ ≤ C * ‖v.gradientLp‖ at h
    rw [hg, mul_zero] at h
    exact le_antisymm h (norm_nonneg _)
  have hz : ∀ᵐ x ∂volume.restrict D, v x = 0 := by
    change ∀ᵐ x ∂volume.restrict D, v.toLp x = 0
    rw [hf]
    exact Lp.coeFn_zero ℝ 2 (volume.restrict D)
  filter_upwards [hv, hz] with x hx hx0
  have hm : max (u x) 0 = 0 := hx.symm.trans hx0
  exact (le_max_left (u x) 0).trans_eq hm

/-- The same maximum principle with the raw scalar distributional inequality
`∫ u Δφ ≥ 0` for every nonnegative smooth interior test. -/
theorem weak_maximum_distributional_of_trace_kernel {n : ℕ} (hn : 0 < n)
    {D : Set (EuclideanSpace ℝ (Fin n))} (hD : IsOpen D)
    (hbD : Bornology.IsBounded D) (hL : HasLipschitzBoundary D)
    {μ : Measure (EuclideanSpace ℝ (Fin n))}
    (T : H1Space D →L[ℝ] Lp ℝ 2 μ)
    (hT : ∀ f G (hf : HasH1GradientOn f G D), Continuous f →
      ⇑(T (H1Space.ofFunction f G hf)) =ᵐ[μ] f)
    (hker : ∀ v : H1Space D, T v = 0 → v ∈ h1ZeroSubmodule hD)
    (u : H1Space D)
    (hu : ∀ φ : EuclideanSpace ℝ (Fin n) → ℝ,
      ContDiff ℝ (⊤ : ℕ∞) φ → HasCompactSupport φ → tsupport φ ⊆ D →
      (∀ x, 0 ≤ φ x) → 0 ≤ ∫ x in D, u x * laplacianN φ x)
    (hb : ∀ᵐ x ∂μ, T u x ≤ 0) : ∀ᵐ x ∂volume.restrict D, u x ≤ 0 := by
  apply weak_maximum_of_trace_kernel hn hD hbD hL T hT hker u ?_ hb
  intro φ hφ hcφ hsφ hnonneg
  have he := u.hasH1GradientOn.toHasWeakGradientOn.integral_mul_laplacianN
    (hφ.of_le (by simp)) hcφ hsφ
  have hh := hu φ hφ hcφ hsφ hnonneg
  rw [he] at hh
  linarith

end LiquidDrop

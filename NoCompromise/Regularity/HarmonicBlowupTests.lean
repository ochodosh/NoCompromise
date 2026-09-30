module

public import NoCompromise.Sobolev.Rellich
public import NoCompromise.Elliptic.WeakMaximumCore

@[expose] public section

/-!
# Actual harmonic test equations under weak H¹ convergence

The gradient-test pairing is a continuous linear functional on the constructed
Hilbert space. Consequently vanishing compact-test residuals imply the genuine
distributional Laplace equation for the weak limit.
-/

noncomputable section
open MeasureTheory Set Filter Metric InnerProductSpace
open scoped Topology ENNReal NNReal Gradient
namespace LiquidDrop

/-- Weak H¹ convergence implies convergence of the actual gradient pairing
against any L² vector field, without a compact-support restriction. -/
theorem harmonicBlowup_tendsto_gradient_pairing {n : ℕ}
    {U : Set (EuclideanSpace ℝ (Fin n))} {u : ℕ → H1Space U} {v : H1Space U}
    (hw : ∀ ℓ : H1Space U →L[ℝ] ℝ,
      Tendsto (fun j => ℓ (u j)) atTop (𝓝 (ℓ v)))
    {P : EuclideanSpace ℝ (Fin n) → EuclideanSpace ℝ (Fin n)}
    (hP : MemLp P 2 (volume.restrict U)) :
    Tendsto (fun j => ∫ x in U, inner ℝ ((u j).gradientLp x) (P x)) atTop
      (𝓝 (∫ x in U, inner ℝ (v.gradientLp x) (P x))) := by
  let ℓ := (innerSL ℝ (hP.toLp P)).comp (H1Space.gradientCLM (U := U))
  have he (w : H1Space U) : ℓ w = ∫ x in U, inner ℝ (w.gradientLp x) (P x) := by
    change (∫ x in U, inner ℝ (hP.toLp P x) (w.gradientLp x)) = _
    apply integral_congr_ae
    filter_upwards [MemLp.coeFn_toLp hP] with x hx
    rw [hx, real_inner_comm]
  simpa only [he] using hw ℓ

/-- Compact C¹ tests have L² gradients on every measurable domain. -/
lemma harmonicBlowup_memLp_gradient_test {n : ℕ}
    {U : Set (EuclideanSpace ℝ (Fin n))}
    {φ : EuclideanSpace ℝ (Fin n) → ℝ} (hφ : ContDiff ℝ 1 φ)
    (hcφ : HasCompactSupport φ) : MemLp (gradient φ) 2 (volume.restrict U) :=
  (continuous_gradient_of_contDiff hφ).memLp_of_hasCompactSupport
    (hcφ.of_isClosed_subset (isClosed_tsupport _) (tsupport_gradient_subset _))

/-- A weak H¹ limit with vanishing actual C¹ compact-test residuals is
harmonic in the distributional sense. -/
theorem harmonicBlowup_distributional_limit {n : ℕ}
    {U : Set (EuclideanSpace ℝ (Fin n))} {u : ℕ → H1Space U} {v : H1Space U}
    (hw : ∀ ℓ : H1Space U →L[ℝ] ℝ,
      Tendsto (fun j => ℓ (u j)) atTop (𝓝 (ℓ v)))
    (hr : ∀ φ : EuclideanSpace ℝ (Fin n) → ℝ,
      ContDiff ℝ 1 φ → HasCompactSupport φ → tsupport φ ⊆ U →
      Tendsto (fun j => ∫ x in U, inner ℝ ((u j).gradientLp x) (gradient φ x))
        atTop (𝓝 0)) :
    HasDistributionalLaplacianOn v (fun _ => 0) U := by
  refine ⟨v.hasH1GradientOn.locallyIntegrable_function,
    (continuous_const.locallyIntegrable).locallyIntegrableOn U, ?_⟩
  intro φ hφ hcφ hsφ
  have hφ1 : ContDiff ℝ 1 φ := hφ.of_le (by simp)
  have ht := harmonicBlowup_tendsto_gradient_pairing hw
    (harmonicBlowup_memLp_gradient_test hφ1 hcφ)
  have hz := tendsto_nhds_unique ht (hr φ hφ1 hcφ hsφ)
  rw [v.hasH1GradientOn.toHasWeakGradientOn.integral_mul_laplacianN
    (hφ.of_le (by simp)) hcφ hsφ, hz]
  simp

/-- A common residual coefficient tending to zero supplies the testwise
convergence needed in the compactness theorem. -/
theorem harmonicBlowup_test_residual_tendsto {n : ℕ}
    {U : Set (EuclideanSpace ℝ (Fin n))} (u : ℕ → H1Space U)
    {a : ℕ → ℝ} (ha : Tendsto a atTop (𝓝 0))
    (hb : ∀ j (φ : EuclideanSpace ℝ (Fin n) → ℝ),
      ContDiff ℝ 1 φ → HasCompactSupport φ → tsupport φ ⊆ U →
      ∀ M : ℝ, 0 ≤ M → (∀ x, ‖gradient φ x‖ ≤ M) →
        |∫ x in U, inner ℝ ((u j).gradientLp x) (gradient φ x)| ≤ a j * M)
    {φ : EuclideanSpace ℝ (Fin n) → ℝ} (hφ : ContDiff ℝ 1 φ)
    (hcφ : HasCompactSupport φ) (hsφ : tsupport φ ⊆ U) :
    Tendsto (fun j => ∫ x in U, inner ℝ ((u j).gradientLp x) (gradient φ x))
      atTop (𝓝 0) := by
  have hcg : HasCompactSupport (gradient φ) :=
    hcφ.of_isClosed_subset (isClosed_tsupport _) (tsupport_gradient_subset _)
  obtain ⟨M, hM⟩ := hcg.exists_bound_of_continuous (continuous_gradient_of_contDiff hφ)
  have hM0 : 0 ≤ M := (norm_nonneg (gradient φ 0)).trans (hM 0)
  apply tendsto_zero_iff_norm_tendsto_zero.mpr
  apply squeeze_zero (fun _ => norm_nonneg _)
    (fun j => by simpa only [Real.norm_eq_abs] using hb j φ hφ hcφ hsφ M hM0 hM)
  simpa only [zero_mul] using ha.mul_const M

end LiquidDrop

import NoCompromise.Elliptic.NondivSchauderEquation
import NoCompromise.Elliptic.CampanatoComparisonTests
import NoCompromise.Sobolev.H1TraceKernelApprox

/-!
# From distributional tests to the C¹ energy test interface

A locally supported C¹ test is a genuine H¹₀ element by the previously proved
smooth approximation theorem. Thus an L² flux annihilating C∞ gradients also
annihilates C¹ compact gradients; no stronger weak-equation premise is added.
-/

noncomputable section
open MeasureTheory Filter Metric Set InnerProductSpace
open scoped ENNReal Topology Gradient RealInnerProductSpace
namespace LiquidDrop
set_option maxSynthPendingDepth 8

lemma nondiv_hasH1GradientOn_compact_test {n : ℕ}
    {φ : EuclideanSpace ℝ (Fin n) → ℝ} (hφ : ContDiff ℝ 1 φ)
    (hcφ : HasCompactSupport φ) : HasH1GradientOn φ (gradient φ) univ :=
  ⟨hasWeakGradientOn_of_contDiffOn isOpen_univ hφ.contDiffOn,
    hφ.continuous.memLp_of_hasCompactSupport hcφ,
    (continuous_gradient_of_contDiff hφ).memLp_of_hasCompactSupport
      (hcφ.of_isClosed_subset (isClosed_tsupport _) (tsupport_gradient_subset φ))⟩

/-- Genuine C∞ distributional tests suffice for the C¹ test interface used by Caccioppoli. -/
theorem nondiv_integral_flux_eq_zero_of_smooth_tests {n : ℕ}
    {U : Set (EuclideanSpace ℝ (Fin n))} (hU : IsOpen U)
    {F : EuclideanSpace ℝ (Fin n) → EuclideanSpace ℝ (Fin n)}
    (hF : MemLp F 2 (volume.restrict U))
    (he : ∀ φ : EuclideanSpace ℝ (Fin n) → ℝ, ContDiff ℝ (⊤ : ℕ∞) φ →
      HasCompactSupport φ → tsupport φ ⊆ U →
      (∫ x, inner ℝ (F x) (gradient φ x)) = 0)
    {φ : EuclideanSpace ℝ (Fin n) → ℝ} (hφ : ContDiff ℝ 1 φ)
    (hcφ : HasCompactSupport φ) (hsφ : tsupport φ ⊆ U) :
    (∫ x, inner ℝ (F x) (gradient φ x)) = 0 := by
  have hzero {ψ : EuclideanSpace ℝ (Fin n) → ℝ} (hsψ : tsupport ψ ⊆ U)
      (x : EuclideanSpace ℝ (Fin n)) (hx : x ∉ U) :
      inner ℝ (F x) (gradient ψ x) = 0 := by
    rw [gradient_eq_zero_of_notMem_tsupport (fun h => hx (hsψ h)), inner_zero_right]
  have hp := nondiv_hasH1GradientOn_compact_test hφ hcφ
  let v : H1ZeroSpace hU :=
    ⟨H1Space.ofFunction φ (gradient φ) (hp.mono (subset_univ U)),
      hp.mem_h1Zero_of_compact_support hU hcφ hsφ⟩
  have ht := campanato_integral_inner_gradient_eq_zero_of_smooth_tests hU hF
    (fun ψ hψ hcψ hsψ => by
      rw [setIntegral_eq_integral_of_forall_compl_eq_zero (hzero hsψ)]
      exact he ψ hψ hcψ hsψ) v
  rw [← setIntegral_eq_integral_of_forall_compl_eq_zero (hzero hsφ)]
  rw [← ht]
  apply integral_congr_ae
  filter_upwards [H1Space.gradientLp_ofFunction φ (gradient φ) (hp.mono (subset_univ U))]
    with x hx
  exact congrArg (fun y => inner ℝ (F x) y) hx.symm

/-- The standard weak divergence interface follows from the original smooth tests. -/
theorem nondiv_weakDivergenceEquationOn_of_smooth_tests {n : ℕ}
    {U : Set (EuclideanSpace ℝ (Fin n))} (hU : IsOpen U)
    {A : EuclideanSpace ℝ (Fin n) →
      EuclideanSpace ℝ (Fin n) →L[ℝ] EuclideanSpace ℝ (Fin n)}
    {D G : EuclideanSpace ℝ (Fin n) → EuclideanSpace ℝ (Fin n)}
    (hF : MemLp (fun x => A x (D x) - G x) 2 (volume.restrict U))
    (he : ∀ φ : EuclideanSpace ℝ (Fin n) → ℝ, ContDiff ℝ (⊤ : ℕ∞) φ →
      HasCompactSupport φ → tsupport φ ⊆ U →
      (∫ x, inner ℝ (A x (D x) - G x) (gradient φ x)) = 0) :
    IsWeakDivergenceEquationOn A D G U :=
  fun _ hφ hcφ hsφ => nondiv_integral_flux_eq_zero_of_smooth_tests hU hF he hφ hcφ hsφ

end LiquidDrop

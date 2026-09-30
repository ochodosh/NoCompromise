module

public import NoCompromise.Elliptic.NeumannLocalizeTests
public import NoCompromise.Elliptic.WeakMaximumCore
public import NoCompromise.Elliptic.HarmonicAlgebra
public import NoCompromise.Elliptic.NeumannInteriorLaplacian

@[expose] public section

/-!
# Interior regularity for weak Neumann solutions

The boundary flux is arbitrary L² data. Compact interior tests remove the
boundary term, giving the distributional equation with convention `Δz = f`.
For constant volume data, subtracting the explicit quadratic gives a harmonic
function and hence a smooth interior representative.
-/

noncomputable section

open MeasureTheory Set Filter Metric InnerProductSpace
open scoped ENNReal Topology Gradient

namespace LiquidDrop

/-- Interior tests eliminate the boundary term for any L² boundary flux. -/
theorem IsWeakNeumannSolution.hasDistributionalLaplacianOn
    {D : Set AmbientSpace} {hD : IsOpen D} {hbD : Bornology.IsBounded D}
    {hL : HasLipschitzBoundary D} {f : Lp ℝ 2 (volume.restrict D)}
    {h : Lp ℝ 2 ((hausdorffMeasure2 3).restrict (frontier D))} {z : H1Space D}
    (hz : IsWeakNeumannSolution hD hbD hL f h z)
    {f₀ : AmbientSpace → ℝ} (hf : ⇑f =ᵐ[volume.restrict D] f₀) :
    HasDistributionalLaplacianOn z f₀ D := by
  refine ⟨z.hasH1GradientOn.locallyIntegrable_function,
    locallyIntegrableOn_of_locallyIntegrable_restrict
      (((Lp.memLp f).ae_eq hf).locallyIntegrable (by norm_num)), ?_⟩
  intro φ hφ hcφ hsφ
  have hb : (∫ x, h x * φ x ∂(hausdorffMeasure2 3).restrict (frontier D)) = 0 := by
    apply integral_eq_zero_of_ae
    filter_upwards [ae_restrict_mem isClosed_frontier.measurableSet] with x hx
    have hnot : x ∉ D := by
      have hx' : x ∈ closure D \ D := by simpa only [hD.frontier_eq] using hx
      exact hx'.2
    rw [image_eq_zero_of_notMem_tsupport (fun ht => hnot (hsφ ht)), mul_zero]
    rfl
  rw [z.hasH1GradientOn.toHasWeakGradientOn.integral_mul_laplacianN
    (hφ.of_le (by simp)) hcφ hsφ,
    hz.ambient_test_eq hf EventuallyEq.rfl (hφ.of_le (by simp)) hcφ,
    hb, add_zero, neg_neg]

/-- The quadratic correction solves the constant-source equation on every set. -/
theorem hasDistributionalLaplacianOn_neumannQuadratic (D : Set AmbientSpace) (c : ℝ) :
    HasDistributionalLaplacianOn (fun x : AmbientSpace => c * ‖x‖ ^ 2 / 6)
      (fun _ => c) D := by
  refine ⟨(contDiff_neumannQuadratic c).continuous.locallyIntegrable.locallyIntegrableOn D,
    locallyIntegrableOn_const c, ?_⟩
  intro φ hφ hcφ hsφ
  rw [setIntegral_eq_integral_of_forall_compl_eq_zero (fun x hx => by
    rw [image_eq_zero_of_notMem_tsupport
      (fun ht => hx (hsφ (tsupport_laplacianN_subset φ ht))), mul_zero])]
  rw [sobolevChain_integral_laplacianN_comm
    ((contDiff_neumannQuadratic c).of_le (by simp)) hφ hcφ]
  simp_rw [laplacianN_neumannQuadratic]
  rw [setIntegral_eq_integral_of_forall_compl_eq_zero (fun x hx => by
    rw [image_eq_zero_of_notMem_tsupport (fun ht => hx (hsφ ht)), mul_zero])]
  simp only [mul_comm]

/-- Subtracting `c * ‖x‖² / 6` from a weak solution with source `c` gives a
distributionally harmonic function. No condition on the boundary flux is added. -/
theorem IsWeakNeumannSolution.sub_quadratic_harmonic
    {D : Set AmbientSpace} {hD : IsOpen D} {hbD : Bornology.IsBounded D}
    {hL : HasLipschitzBoundary D} {f : Lp ℝ 2 (volume.restrict D)}
    {h : Lp ℝ 2 ((hausdorffMeasure2 3).restrict (frontier D))} {z : H1Space D}
    (hz : IsWeakNeumannSolution hD hbD hL f h z)
    {c : ℝ} (hf : ⇑f =ᵐ[volume.restrict D] fun _ => c) :
    HasDistributionalLaplacianOn (fun x => z x - c * ‖x‖ ^ 2 / 6) (fun _ => 0) D := by
  simpa only [sub_self] using
    (hz.hasDistributionalLaplacianOn hf).sub (hasDistributionalLaplacianOn_neumannQuadratic D c)

end LiquidDrop

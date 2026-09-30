module

public import NoCompromise.Elliptic.WeakSolutions
public import NoCompromise.Elliptic.NondivSchauderTests

@[expose] public section

/-!
# Ambient tests for the weak Neumann equation

The sign convention is `Δz = f`, with outward normal derivative `h`.
An ambient compactly supported C¹ test belongs to H¹ on the domain, and its
constructed boundary trace is its restriction to the topological boundary.
-/

noncomputable section

open MeasureTheory Set Filter InnerProductSpace
open scoped ENNReal Topology Gradient

namespace LiquidDrop

/-- The global weak Neumann identity for ambient C¹ compact tests, written
using specified almost-everywhere representatives of the volume and flux data.
Continuity of these representatives is not needed for this identity. -/
theorem IsWeakNeumannSolution.ambient_test_eq
    {D : Set AmbientSpace} {hD : IsOpen D} {hbD : Bornology.IsBounded D}
    {hL : HasLipschitzBoundary D} {f : Lp ℝ 2 (volume.restrict D)}
    {h : Lp ℝ 2 ((hausdorffMeasure2 3).restrict (frontier D))} {z : H1Space D}
    (hz : IsWeakNeumannSolution hD hbD hL f h z)
    {f₀ h₀ : AmbientSpace → ℝ} (hf : ⇑f =ᵐ[volume.restrict D] f₀)
    (hh : ⇑h =ᵐ[(hausdorffMeasure2 3).restrict (frontier D)] h₀)
    {φ : AmbientSpace → ℝ} (hφ : ContDiff ℝ 1 φ) (hcφ : HasCompactSupport φ) :
    (∫ x in D, inner ℝ (z.gradientLp x) (gradient φ x)) =
      -(∫ x in D, f₀ x * φ x) +
        ∫ x, h₀ x * φ x ∂(hausdorffMeasure2 3).restrict (frontier D) := by
  have hp : HasH1GradientOn φ (gradient φ) D :=
    (nondiv_hasH1GradientOn_compact_test hφ hcφ).mono (subset_univ D)
  let v : H1Space D := H1Space.ofFunction φ (gradient φ) hp
  have hg : (∫ x in D, inner ℝ (z.gradientLp x) (v.gradientLp x)) =
      ∫ x in D, inner ℝ (z.gradientLp x) (gradient φ x) := by
    apply integral_congr_ae
    filter_upwards [H1Space.gradientLp_ofFunction φ (gradient φ) hp] with x hx
    exact congrArg (fun G => inner ℝ (z.gradientLp x) G) hx
  have hv : (∫ x in D, f x * v x) = ∫ x in D, f₀ x * φ x := by
    apply integral_congr_ae
    filter_upwards [hf, H1Space.coeFn_ofFunction φ (gradient φ) hp] with x hfx hvx
    exact congrArg₂ (· * ·) hfx hvx
  have ht : (∫ x, h x * h1BoundaryTrace hD hbD hL v x
      ∂(hausdorffMeasure2 3).restrict (frontier D)) =
      ∫ x, h₀ x * φ x ∂(hausdorffMeasure2 3).restrict (frontier D) := by
    apply integral_congr_ae
    filter_upwards [hh, h1BoundaryTrace_eq_restrict hD hbD hL φ (gradient φ) hp
      hφ.continuous] with x hhx htx
    exact congrArg₂ (· * ·) hhx htx
  simpa only [hg, hv, ht] using hz.test_eq v

end LiquidDrop

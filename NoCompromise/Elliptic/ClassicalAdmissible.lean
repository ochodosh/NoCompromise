module

public import NoCompromise.Elliptic.ClassicalCalculus
public import NoCompromise.Elliptic.ClassicalCubeAffine

@[expose] public section

/-! # Classical Gauss–Green for all admissible domain classes -/

noncomputable section
open MeasureTheory Set
namespace LiquidDrop

/-- The classical W¹,¹ trace and divergence identity, with the actual normal
field specified as part of the geometric domain data. -/
def HasClassicalW11GaussGreen (D : Set AmbientSpace) (ν : AmbientSpace → AmbientSpace) : Prop :=
  ∃ T : W11Space D →L[ℝ] Lp ℝ 1 ((hausdorffMeasure2 3).restrict (frontier D)),
    ∃ C : ℝ, 0 ≤ C ∧ ‖T‖ ≤ C ∧
      (∀ f G (hf : HasW11GradientOn f G D), Continuous f →
        ⇑(T (W11Space.ofFunction f G hf)) =ᵐ[
          (hausdorffMeasure2 3).restrict (frontier D)] f) ∧
      ∀ Z J (hZ : HasW11VectorGradientOn Z J D),
        (∫ x in D, w11Divergence J x) =
          ∫ x, inner ℝ (w11VectorTrace T hZ x) (ν x)
            ∂(hausdorffMeasure2 3).restrict (frontier D)

/-- Bounded open C¹ domains, including balls and smooth annuli. -/
theorem classical_w11_gauss_green_C1 {D : Set AmbientSpace}
    (hD : IsOpen D) (hbD : Bornology.IsBounded D) (hC1 : HasC1Boundary D) :
    HasClassicalW11GaussGreen D hC1.outwardNormal :=
  exists_w11_gauss_green hD hbD hC1

/-- Arbitrarily translated and rotated cubes, whose edges have zero boundary
area. The normal is the actual transported face normal. -/
theorem classical_w11_gauss_green_cube
    (a : AmbientSpace ≃ᵃⁱ[ℝ] AmbientSpace) {R : ℝ} (hR : 0 < R) :
    HasClassicalW11GaussGreen (placedCoordinateCube a R) (placedCubeOutwardNormal a R) :=
  exists_w11_gauss_green_placedCube a hR

end LiquidDrop

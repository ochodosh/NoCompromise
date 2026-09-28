import NoCompromise.Sobolev.W11TraceVector
import NoCompromise.Sobolev.C1Domain

/-!
# The blueprint L¹ trace theorem

Bounded Lipschitz domains include all the admissible domain classes. The actual
constructed vector trace obeys the L¹ estimate with the Euclidean operator norm
of the weak derivative matrix. No boundary estimate is assumed.
-/

noncomputable section
open MeasureTheory Set Filter
open scoped ENNReal Topology
namespace LiquidDrop

theorem w11_trace_L1 {D : Set AmbientSpace} (hD : IsOpen D)
    (hbD : Bornology.IsBounded D) (hL : HasLipschitzBoundary D) :
    ∃ T : W11Space D →L[ℝ]
      Lp ℝ 1 ((hausdorffMeasure2 3).restrict (frontier D)),
    ∃ C : ℝ, 0 ≤ C ∧ ∀ Z J (hZ : HasW11VectorGradientOn Z J D),
      Integrable (w11VectorTrace T hZ)
        ((hausdorffMeasure2 3).restrict (frontier D)) ∧
      (∫ x, ‖w11VectorTrace T hZ x‖
        ∂(hausdorffMeasure2 3).restrict (frontier D)) ≤
        C * ((∫ x in D, ‖Z x‖) + ∫ x in D, ‖J x‖) ∧
      (Continuous Z → w11VectorTrace T hZ =ᵐ[
        (hausdorffMeasure2 3).restrict (frontier D)] Z) :=
  exists_w11_vector_trace hD hbD hL

theorem w11_trace_L1_c1_domain {D : Set AmbientSpace} (hD : IsOpen D)
    (hbD : Bornology.IsBounded D) (hC1 : HasC1Boundary D) :
    ∃ T : W11Space D →L[ℝ]
      Lp ℝ 1 ((hausdorffMeasure2 3).restrict (frontier D)),
    ∃ C : ℝ, 0 ≤ C ∧ ∀ Z J (hZ : HasW11VectorGradientOn Z J D),
      Integrable (w11VectorTrace T hZ)
        ((hausdorffMeasure2 3).restrict (frontier D)) ∧
      (∫ x, ‖w11VectorTrace T hZ x‖
        ∂(hausdorffMeasure2 3).restrict (frontier D)) ≤
        C * ((∫ x in D, ‖Z x‖) + ∫ x in D, ‖J x‖) ∧
      (Continuous Z → w11VectorTrace T hZ =ᵐ[
        (hausdorffMeasure2 3).restrict (frontier D)] Z) :=
  w11_trace_L1 hD hbD hC1.hasLipschitzBoundary

end LiquidDrop

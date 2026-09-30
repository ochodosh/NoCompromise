module

public import NoCompromise.Sobolev.W11VectorData

@[expose] public section

/-!
# Classical C¹ fields on bounded domains as W¹,¹ data
-/

noncomputable section
open MeasureTheory Set Filter InnerProductSpace
open scoped ENNReal Topology Gradient
namespace LiquidDrop

lemma gradient_component_eq_adjoint {n : ℕ}
    {Z : EuclideanSpace ℝ (Fin n) → EuclideanSpace ℝ (Fin n)}
    {x : EuclideanSpace ℝ (Fin n)} (hZ : DifferentiableAt ℝ Z x) (i : Fin n) :
    gradient (fun y => Z y i) x =
      (fderiv ℝ Z x).adjoint (EuclideanSpace.single i 1) := by
  apply ext_inner_right ℝ
  intro v
  rw [inner_gradient_left, ContinuousLinearMap.adjoint_inner_left]
  have hh := (EuclideanSpace.proj i).hasFDerivAt.comp x hZ.hasFDerivAt
  change HasFDerivAt (fun y => Z y i) _ x at hh
  rw [hh.fderiv]
  simp only [ContinuousLinearMap.comp_apply, EuclideanSpace.inner_single_left, map_one, one_mul]
  rfl

theorem hasW11VectorGradientOn_of_contDiff {n : ℕ}
    {D : Set (EuclideanSpace ℝ (Fin n))} (hD : IsOpen D)
    (hbD : Bornology.IsBounded D)
    {Z : EuclideanSpace ℝ (Fin n) → EuclideanSpace ℝ (Fin n)} (hZ : ContDiff ℝ 1 Z) :
    HasW11VectorGradientOn Z (fderiv ℝ Z) D := by
  refine ⟨hZ.continuous.continuousOn.integrableOn_compact hbD.isCompact_closure |>.mono_set
    subset_closure, (hZ.continuous_fderiv one_ne_zero).continuousOn.integrableOn_compact
    hbD.isCompact_closure |>.mono_set subset_closure, fun i => ?_⟩
  have hc : ContDiff ℝ 1 (fun x => Z x i) := by
    exact (EuclideanSpace.proj i).contDiff.comp hZ
  have hw := hasWeakGradientOn_of_contDiffOn hD hc.contDiffOn
  exact hw.congr_ae EventuallyEq.rfl (Eventually.of_forall fun x =>
    gradient_component_eq_adjoint (hZ.differentiable one_ne_zero x) i)

end LiquidDrop

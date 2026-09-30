module

public import NoCompromise.Elliptic.BoundaryNormalChartCoefficient
public import Mathlib.MeasureTheory.Function.Jacobian

@[expose] public section

/-!
# Change of variables for the Dirichlet form

On an injective normal chart with invertible derivative, the coefficient from
the preceding file gives the exact pullback of the Dirichlet form.
-/

noncomputable section

open Set Filter Metric InnerProductSpace MeasureTheory
open scoped Topology Gradient

namespace LiquidDrop

/-- A normal chart maps open subsets of its regular set to open sets. -/
theorem boundaryNormalChart_isOpen_image
    {ψ : EuclideanSpace ℝ (Fin 2) → ℝ} (hψ : ContDiff ℝ 2 ψ)
    {V : Set (EuclideanSpace ℝ (Fin 3))} (hV : IsOpen V)
    (hreg : ∀ x ∈ V, (fderiv ℝ (boundaryNormalChart ψ) x).IsInvertible) :
    IsOpen (boundaryNormalChart ψ '' V) := by
  apply isOpen_iff_mem_nhds.mpr
  rintro y ⟨x, hx, rfl⟩
  obtain ⟨L, hL⟩ := hreg x hx
  have hc : ContDiff ℝ 1 (boundaryNormalChart ψ) := contDiff_boundaryNormalChart hψ
  have hd : HasFDerivAt (boundaryNormalChart ψ)
      (L : EuclideanSpace ℝ (Fin 3) →L[ℝ] EuclideanSpace ℝ (Fin 3)) x := by
    rw [hL]
    exact (hc.differentiable one_ne_zero x).hasFDerivAt
  rw [← (hc.contDiffAt.hasStrictFDerivAt' hd one_ne_zero).map_nhds_eq_of_equiv]
  exact Filter.image_mem_map (hV.mem_nhds hx)

/-- The ordinary gradient chain rule in the normal chart. -/
lemma boundaryNormalChart_gradient_comp
    {ψ : EuclideanSpace ℝ (Fin 2) → ℝ} (hψ : ContDiff ℝ 2 ψ)
    {u : EuclideanSpace ℝ (Fin 3) → ℝ} {x : EuclideanSpace ℝ (Fin 3)}
    (hu : DifferentiableAt ℝ u (boundaryNormalChart ψ x)) :
    gradient (u ∘ boundaryNormalChart ψ) x =
      (fderiv ℝ (boundaryNormalChart ψ) x).adjoint (gradient u (boundaryNormalChart ψ x)) := by
  have hc := (contDiff_boundaryNormalChart (r := 1) hψ).differentiable one_ne_zero x
  apply ext_inner_right ℝ
  intro v
  rw [inner_gradient_left, ContinuousLinearMap.adjoint_inner_left, inner_gradient_left,
    fderiv_comp x hu hc, ContinuousLinearMap.comp_apply]

/-- The pointwise Dirichlet pairing transforms by the normal coefficient. -/
theorem boundaryNormalChart_dirichlet_pairing
    {ψ : EuclideanSpace ℝ (Fin 2) → ℝ} (hψ : ContDiff ℝ 2 ψ)
    {u φ : EuclideanSpace ℝ (Fin 3) → ℝ} {x : EuclideanSpace ℝ (Fin 3)}
    (hu : DifferentiableAt ℝ u (boundaryNormalChart ψ x))
    (hφ : DifferentiableAt ℝ φ (boundaryNormalChart ψ x))
    (hx : (fderiv ℝ (boundaryNormalChart ψ) x).IsInvertible) :
    inner ℝ (boundaryNormalCoefficient ψ x (gradient (u ∘ boundaryNormalChart ψ) x))
      (gradient (φ ∘ boundaryNormalChart ψ) x) =
        |(fderiv ℝ (boundaryNormalChart ψ) x).det| *
          inner ℝ (gradient u (boundaryNormalChart ψ x))
            (gradient φ (boundaryNormalChart ψ x)) := by
  let L := fderiv ℝ (boundaryNormalChart ψ) x
  have hstar : L.inverse.adjoint.comp L.adjoint = ContinuousLinearMap.id ℝ _ := by
    rw [← ContinuousLinearMap.adjoint_comp, hx.self_comp_inverse,
      ContinuousLinearMap.adjoint_id]
  have hs (v : EuclideanSpace ℝ (Fin 3)) : L.inverse.adjoint (L.adjoint v) = v :=
    congrArg (fun A : EuclideanSpace ℝ (Fin 3) →L[ℝ] EuclideanSpace ℝ (Fin 3) => A v) hstar
  rw [boundaryNormalChart_gradient_comp hψ hu, boundaryNormalChart_gradient_comp hψ hφ]
  change inner ℝ (|L.det| • L.inverse
    (L.inverse.adjoint (L.adjoint (gradient u (boundaryNormalChart ψ x)))))
      (L.adjoint (gradient φ (boundaryNormalChart ψ x))) = _
  rw [hs, real_inner_smul_left, ContinuousLinearMap.adjoint_inner_right, hx.self_apply_inverse]

/-- Exact change of variables for C¹ functions on the chart image. The integrals
are the usual totalized Bochner integrals; no finiteness assumption is required
by the change-of-variables theorem. -/
theorem boundaryNormalChart_dirichlet_integral
    {ψ : EuclideanSpace ℝ (Fin 2) → ℝ} (hψ : ContDiff ℝ 2 ψ)
    {V : Set (EuclideanSpace ℝ (Fin 3))} (hV : IsOpen V)
    (hinj : InjOn (boundaryNormalChart ψ) V)
    (hreg : ∀ x ∈ V, (fderiv ℝ (boundaryNormalChart ψ) x).IsInvertible)
    {u φ : EuclideanSpace ℝ (Fin 3) → ℝ}
    (hu : ContDiffOn ℝ 1 u (boundaryNormalChart ψ '' V))
    (hφ : ContDiffOn ℝ 1 φ (boundaryNormalChart ψ '' V)) :
    (∫ y in boundaryNormalChart ψ '' V, inner ℝ (gradient u y) (gradient φ y)) =
      ∫ x in V, inner ℝ (boundaryNormalCoefficient ψ x (gradient (u ∘ boundaryNormalChart ψ) x))
        (gradient (φ ∘ boundaryNormalChart ψ) x) := by
  have hc := (contDiff_boundaryNormalChart (r := 1) hψ).differentiable one_ne_zero
  rw [integral_image_eq_integral_abs_det_fderiv_smul volume hV.measurableSet
    (fun x _ => (hc x).hasFDerivAt.hasFDerivWithinAt) hinj]
  apply setIntegral_congr_fun hV.measurableSet
  intro x hx
  have him : boundaryNormalChart ψ x ∈ boundaryNormalChart ψ '' V := mem_image_of_mem _ hx
  have hnhds := (boundaryNormalChart_isOpen_image hψ hV hreg).mem_nhds him
  exact (boundaryNormalChart_dirichlet_pairing hψ
    ((hu.differentiableOn one_ne_zero _ him).differentiableAt hnhds)
    ((hφ.differentiableOn one_ne_zero _ him).differentiableAt hnhds) (hreg x hx)).symm

end LiquidDrop

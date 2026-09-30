module

public import NoCompromise.Conventions
public import NoCompromise.BV.Defs
public import Mathlib.Analysis.Calculus.ContDiff.Operations
public import Mathlib.Topology.OpenPartialHomeomorph.Basic
public import Mathlib.MeasureTheory.Function.Jacobian
public import Mathlib.Analysis.Calculus.InverseFunctionTheorem.ApproximatesLinearOn

@[expose] public section

/-!
# Derivatives of a C¹ diffeomorphism between open sets

For `Φ : U → V` a C¹ diffeomorphism between open subsets of the ambient space
(an open partial homeomorphism, C¹ on its source, with C¹ inverse on its target),
the derivative at every source point is a continuous linear equivalence whose inverse
is the derivative of `Φ⁻¹` at the image point. This is the input of the local
extension step of blueprint `thm:transport-perimeter`.
-/

noncomputable section
open MeasureTheory Set Filter Metric
open scoped Topology
namespace LiquidDrop

/-- The derivative of a C¹ diffeomorphism between open sets is invertible, with inverse
the derivative of the inverse map. -/
theorem exists_fderiv_equiv_of_C1_diffeomorphism_on
    (Φ : OpenPartialHomeomorph AmbientSpace AmbientSpace)
    (hΦ : ContDiffOn ℝ 1 Φ Φ.source) (hΦi : ContDiffOn ℝ 1 Φ.symm Φ.target)
    {x : AmbientSpace} (hx : x ∈ Φ.source) :
    ∃ L : AmbientSpace ≃L[ℝ] AmbientSpace,
      (L : AmbientSpace →L[ℝ] AmbientSpace) = fderiv ℝ Φ x ∧
      (L.symm : AmbientSpace →L[ℝ] AmbientSpace) = fderiv ℝ Φ.symm (Φ x) := by
  have hy : Φ x ∈ Φ.target := Φ.map_source hx
  have hd : HasFDerivAt Φ (fderiv ℝ Φ x) x :=
    ((hΦ.contDiffAt (Φ.open_source.mem_nhds hx)).differentiableAt one_ne_zero).hasFDerivAt
  have hdi : HasFDerivAt Φ.symm (fderiv ℝ Φ.symm (Φ x)) (Φ x) :=
    ((hΦi.contDiffAt (Φ.open_target.mem_nhds hy)).differentiableAt one_ne_zero).hasFDerivAt
  have h1 : (fderiv ℝ Φ.symm (Φ x)).comp (fderiv ℝ Φ x) = ContinuousLinearMap.id ℝ _ := by
    have hc : HasFDerivAt (Φ.symm ∘ Φ) ((fderiv ℝ Φ.symm (Φ x)).comp (fderiv ℝ Φ x)) x :=
      hdi.comp x hd
    have hid : HasFDerivAt (Φ.symm ∘ Φ) (ContinuousLinearMap.id ℝ AmbientSpace) x :=
      (hasFDerivAt_id x).congr_of_eventuallyEq (Φ.eventually_left_inverse hx)
    exact hc.unique hid
  have h2 : (fderiv ℝ Φ x).comp (fderiv ℝ Φ.symm (Φ x)) = ContinuousLinearMap.id ℝ _ := by
    have hd' : HasFDerivAt Φ (fderiv ℝ Φ x) (Φ.symm (Φ x)) := by
      rw [Φ.left_inv hx]
      exact hd
    have hc : HasFDerivAt (Φ ∘ Φ.symm) ((fderiv ℝ Φ x).comp (fderiv ℝ Φ.symm (Φ x))) (Φ x) :=
      hd'.comp (Φ x) hdi
    have hid : HasFDerivAt (Φ ∘ Φ.symm) (ContinuousLinearMap.id ℝ AmbientSpace) (Φ x) :=
      (hasFDerivAt_id (Φ x)).congr_of_eventuallyEq (Φ.eventually_right_inverse hy)
    exact hc.unique hid
  refine ⟨ContinuousLinearEquiv.equivOfInverse (fderiv ℝ Φ x) (fderiv ℝ Φ.symm (Φ x))
    (fun v => by simpa using congrArg (fun T => T v) h1)
    (fun v => by simpa using congrArg (fun T => T v) h2), rfl, rfl⟩

/-- The image of a null-measurable subset of the source under a C¹ diffeomorphism between
open sets is null-measurable. -/
theorem nullMeasurableSet_image_of_C1_diffeomorphism_on
    (Φ : OpenPartialHomeomorph AmbientSpace AmbientSpace)
    (hΦ : ContDiffOn ℝ 1 Φ Φ.source) {E : Set AmbientSpace} (hEU : E ⊆ Φ.source)
    (hmE : NullMeasurableSet E volume) : NullMeasurableSet (Φ '' E) volume := by
  obtain ⟨E₀, hsub, hE₀, hae⟩ := hmE.exists_measurable_subset_ae_eq
  have h0 : MeasurableSet (Φ '' E₀) := by
    rw [Φ.image_eq_target_inter_inv_preimage (hsub.trans hEU),
      ← Subtype.image_preimage_coe]
    have hc : Continuous (Φ.target.domRestrict Φ.symm) := Φ.continuousOn_symm.domRestrict
    exact Φ.open_target.measurableSet.subtype_image (hc.measurable hE₀)
  have hnull : volume (E \ E₀) = 0 := (ae_eq_set.mp hae).2
  have hdiff : DifferentiableOn ℝ Φ (E \ E₀) :=
    (hΦ.differentiableOn one_ne_zero).mono (sdiff_subset.trans hEU)
  have himg : volume (Φ '' (E \ E₀)) = 0 :=
    addHaar_image_eq_zero_of_differentiableOn_of_addHaar_eq_zero volume hdiff hnull
  have hsplit : Φ '' E = Φ '' E₀ ∪ Φ '' (E \ E₀) := by
    rw [← image_union, union_sdiff_cancel hsub]
  rw [hsplit]
  exact h0.nullMeasurableSet.union (NullMeasurableSet.of_null himg)

/-- A global C¹ map that approximates an invertible linear map on the whole space, with
constant below the inverse norm bound, is a homeomorphism with C¹ inverse. This is the
final step of the local extension in blueprint `thm:transport-perimeter`. -/
theorem exists_C1_homeomorph_of_approximatesLinearOn_univ {Ψ : AmbientSpace → AmbientSpace}
    (A : AmbientSpace ≃L[ℝ] AmbientSpace) {c : NNReal} (hΨ : ContDiff ℝ 1 Ψ)
    (hA : ApproximatesLinearOn Ψ (A : AmbientSpace →L[ℝ] AmbientSpace) univ c)
    (hc : c < ‖(A.symm : AmbientSpace →L[ℝ] AmbientSpace)‖₊⁻¹) :
    ∃ e : AmbientSpace ≃ₜ AmbientSpace, (e : AmbientSpace → AmbientSpace) = Ψ ∧
      ContDiff ℝ 1 e ∧ ContDiff ℝ 1 e.symm := by
  let e : AmbientSpace ≃ₜ AmbientSpace := hA.toHomeomorph Ψ (Or.inr hc)
  have he : (e : AmbientSpace → AmbientSpace) = Ψ := rfl
  have hLip : LipschitzWith c (Ψ - ⇑(A : AmbientSpace →L[ℝ] AmbientSpace)) :=
    lipschitzOnWith_univ.mp (ApproximatesLinearOn.approximatesLinearOn_iff_lipschitzOnWith.mp hA)
  have hnear : ∀ a, ‖fderiv ℝ Ψ a - ((A.toUnit : (AmbientSpace →L[ℝ] AmbientSpace)ˣ) :
      AmbientSpace →L[ℝ] AmbientSpace)‖ <
      ‖((A.toUnit⁻¹ : (AmbientSpace →L[ℝ] AmbientSpace)ˣ) :
        AmbientSpace →L[ℝ] AmbientSpace)‖⁻¹ := by
    intro a
    have hd : HasFDerivAt Ψ (fderiv ℝ Ψ a) a :=
      ((hΨ.contDiffAt).differentiableAt one_ne_zero).hasFDerivAt
    have hsub : HasFDerivAt (Ψ - ⇑(A : AmbientSpace →L[ℝ] AmbientSpace))
        (fderiv ℝ Ψ a - (A : AmbientSpace →L[ℝ] AmbientSpace)) a :=
      hd.sub (A : AmbientSpace →L[ℝ] AmbientSpace).hasFDerivAt
    have hle := hsub.le_of_lipschitz hLip
    have hc' : (c : ℝ) < ‖(A.symm : AmbientSpace →L[ℝ] AmbientSpace)‖⁻¹ := by
      have := NNReal.coe_lt_coe.mpr hc
      simpa using this
    exact hle.trans_lt hc'
  let L : AmbientSpace → AmbientSpace ≃L[ℝ] AmbientSpace := fun a =>
    ContinuousLinearEquiv.unitsEquiv ℝ AmbientSpace (Units.ofNearby _ _ (hnear a))
  have hL : ∀ a, HasFDerivAt e (L a : AmbientSpace →L[ℝ] AmbientSpace) a := by
    intro a
    have hcoe : (L a : AmbientSpace →L[ℝ] AmbientSpace) = fderiv ℝ Ψ a := by
      ext v
      simp [L, ContinuousLinearEquiv.unitsEquiv_apply]
    rw [hcoe, he]
    exact ((hΨ.contDiffAt).differentiableAt one_ne_zero).hasFDerivAt
  exact ⟨e, he, he ▸ hΨ, e.contDiff_symm hL (he ▸ hΨ)⟩

end LiquidDrop

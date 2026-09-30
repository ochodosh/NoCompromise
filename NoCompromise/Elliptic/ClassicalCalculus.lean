module

public import NoCompromise.Elliptic.ClassicalGaussGreenW11
public import NoCompromise.Elliptic.ClassicalNormal
public import NoCompromise.Sobolev.W11Classical

@[expose] public section

/-!
# W¹,¹ Gauss–Green with the classical outward normal

The normal comes from the one-sided C¹ charts, and the trace is the actual
bounded extension of restriction. All geometric and analytic prerequisites
are proved by graph calculus and smooth approximation.
-/

noncomputable section
open MeasureTheory Set Filter InnerProductSpace
open scoped ENNReal Topology Gradient
namespace LiquidDrop
set_option maxSynthPendingDepth 8

/-- The C¹-domain W¹,¹ divergence theorem for any realization of the
unique bounded trace and the actual classical outward unit normal. -/
theorem w11_gauss_green {D : Set AmbientSpace}
    (hD : IsOpen D) (hbD : Bornology.IsBounded D) (hC1 : HasC1Boundary D)
    (T : W11Space D →L[ℝ] Lp ℝ 1 ((hausdorffMeasure2 3).restrict (frontier D)))
    (hT : ∀ f G (hf : HasW11GradientOn f G D), Continuous f →
      ⇑(T (W11Space.ofFunction f G hf)) =ᵐ[(hausdorffMeasure2 3).restrict (frontier D)] f)
    {Z : AmbientSpace → AmbientSpace} {J : AmbientSpace → AmbientSpace →L[ℝ] AmbientSpace}
    (hZ : HasW11VectorGradientOn Z J D) :
    (∫ x in D, w11Divergence J x) =
      ∫ x, inner ℝ (w11VectorTrace T hZ x) (hC1.outwardNormal x)
        ∂(hausdorffMeasure2 3).restrict (frontier D) :=
  w11_vector_gauss_green hD hbD hC1 (hC1.aestronglyMeasurable_outwardNormal _)
    (Eventually.of_forall hC1.norm_outwardNormal_le)
    (fun _ hc => hC1.outwardNormal_eq_chart_ae hc) T hT hZ

/-- The trace operator and its bound are constructed before any vector field
is specified, and Gauss–Green holds for every genuine W¹,¹ field. -/
theorem exists_w11_gauss_green {D : Set AmbientSpace}
    (hD : IsOpen D) (hbD : Bornology.IsBounded D) (hC1 : HasC1Boundary D) :
    ∃ T : W11Space D →L[ℝ] Lp ℝ 1 ((hausdorffMeasure2 3).restrict (frontier D)),
    ∃ C : ℝ, 0 ≤ C ∧ ‖T‖ ≤ C ∧
      (∀ f G (hf : HasW11GradientOn f G D), Continuous f →
        ⇑(T (W11Space.ofFunction f G hf)) =ᵐ[
          (hausdorffMeasure2 3).restrict (frontier D)] f) ∧
      ∀ Z J (hZ : HasW11VectorGradientOn Z J D),
        (∫ x in D, w11Divergence J x) =
          ∫ x, inner ℝ (w11VectorTrace T hZ x) (hC1.outwardNormal x)
            ∂(hausdorffMeasure2 3).restrict (frontier D) := by
  obtain ⟨T, C, hC, hTC, hT⟩ := exists_w11_trace_operator hD hbD hC1.hasLipschitzBoundary
  exact ⟨T, C, hC, hTC, hT, fun _ _ hZ => w11_gauss_green hD hbD hC1 T hT hZ⟩

theorem classical_gauss_green {D : Set AmbientSpace}
    (hD : IsOpen D) (hbD : Bornology.IsBounded D) (hC1 : HasC1Boundary D)
    {Z : AmbientSpace → AmbientSpace} (hZ : ContDiff ℝ 1 Z) :
    (∫ x in D, divergence Z x) =
      ∫ x, inner ℝ (Z x) (hC1.outwardNormal x)
        ∂(hausdorffMeasure2 3).restrict (frontier D) := by
  obtain ⟨T, _, _, _, hT, hGG⟩ := exists_w11_gauss_green hD hbD hC1
  let hW := hasW11VectorGradientOn_of_contDiff hD hbD hZ
  have ht : w11VectorTrace T hW =ᵐ[(hausdorffMeasure2 3).restrict (frontier D)] Z := by
    have hi (i : Fin 3) := hT (fun x => Z x i)
      (fun x => (fderiv ℝ Z x).adjoint (EuclideanSpace.single i 1)) (hW.component i)
      ((EuclideanSpace.proj i).continuous.comp hZ.continuous)
    filter_upwards [ae_all_iff.mpr hi] with x hx
    exact PiLp.ext fun i => hx i
  calc
    _ = ∫ x, inner ℝ (w11VectorTrace T hW x) (hC1.outwardNormal x)
        ∂(hausdorffMeasure2 3).restrict (frontier D) := hGG Z (fderiv ℝ Z) hW
    _ = _ := integral_congr_ae (ht.mono fun x hx =>
      congrArg (fun z => inner ℝ z (hC1.outwardNormal x)) hx)

/-- The classical flux of the position field is exactly three times volume. -/
theorem integral_position_normal_eq_three_volume {D : Set AmbientSpace}
    (hD : IsOpen D) (hbD : Bornology.IsBounded D) (hC1 : HasC1Boundary D) :
    (∫ x, inner ℝ x (hC1.outwardNormal x)
      ∂(hausdorffMeasure2 3).restrict (frontier D)) = 3 * volume.real D := by
  have h := classical_gauss_green hD hbD hC1 (Z := id) contDiff_id
  simp only [id_eq] at h
  rw [← h]
  have hd (x : AmbientSpace) : divergence id x = 3 := by
    simp [divergence, fderiv_id]
  simp only [hd, setIntegral_const, smul_eq_mul, mul_comm]

end LiquidDrop

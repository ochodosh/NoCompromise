import NoCompromise.Elliptic.BoundaryNeumannInhomPrimitive
import NoCompromise.Elliptic.BoundaryNeumannInhomGeometry
import NoCompromise.Elliptic.BoundaryNeumannInhomSlicing
import NoCompromise.Elliptic.BoundaryNeumannInhomEstimates

/-!
# Source identities for the inhomogeneous conormal reduction

These are intermediate results for the first assertion of blueprint
`thm:boundary-neumann`. They establish the two source identities and the
homogeneous weak equation for the explicit corrected flux. The quantitative
regularity theorem `boundary_neumann_c1_holder` is not established here.
-/

noncomputable section
open MeasureTheory Filter Metric Set InnerProductSpace
open scoped ENNReal NNReal Topology Gradient RealInnerProductSpace
namespace LiquidDrop

lemma boundary_neumann_isCompact_closure : IsCompact (closure (boundaryHalfBall 1)) :=
  (isCompact_closedBall (0 : EuclideanSpace ℝ (Fin 3)) 1).of_isClosed_subset
    isClosed_closure (fun x hx => by
      simpa only [mem_closedBall, dist_zero_right] using boundary_neumann_closed_norm_le hx)

lemma boundary_neumann_integrableOn_of_continuousOn
    {g : EuclideanSpace ℝ (Fin 3) → ℝ}
    (hg : ContinuousOn g (closure (boundaryHalfBall 1))) :
    IntegrableOn g (boundaryHalfBall 1) :=
  (hg.integrableOn_compact boundary_neumann_isCompact_closure).mono_set subset_closure

/-- The interior source is the divergence of its explicit vertical primitive.
All hypotheses concern the original scalar datum on the closed half-ball. -/
theorem boundary_neumann_interior_source_identity {a Bf Hf : ℝ}
    (ha : 0 < a) (ha1 : a ≤ 1) (hBf : 0 ≤ Bf) (hHf : 0 ≤ Hf)
    {f : EuclideanSpace ℝ (Fin 3) → ℝ}
    (hf : ContinuousOn f (closure (boundaryHalfBall 1)))
    (hb : ∀ x ∈ closure (boundaryHalfBall 1), ‖f x‖ ≤ Bf)
    (hh : ∀ x ∈ closure (boundaryHalfBall 1), ∀ y ∈ closure (boundaryHalfBall 1),
      ‖f x - f y‖ ≤ Hf * dist x y ^ a)
    {φ : EuclideanSpace ℝ (Fin 3) → ℝ} (hφ : ContDiff ℝ 1 φ)
    (hsφ : tsupport φ ⊆ ball 0 1) :
    (∫ x in boundaryHalfBall 1, inner ℝ (boundaryNeumannPrimitive f x) (gradient φ x)) =
      -(∫ x in boundaryHalfBall 1, f x * φ x) := by
  have hP := boundaryNeumannPrimitive_continuousOn ha ha1 hBf hHf hf hb hh
  have hiP := boundary_neumann_integrableOn_of_continuousOn
    (hP.inner (continuous_gradient_of_contDiff hφ).continuousOn)
  have hif : IntegrableOn (fun x => f x * φ x) (boundaryHalfBall 1) :=
    boundary_neumann_integrableOn_of_continuousOn (hf.mul hφ.continuous.continuousOn)
  rw [boundary_neumann_integral_halfBall_slices hiP,
    boundary_neumann_integral_halfBall_slices hif, ← integral_neg]
  apply setIntegral_congr_fun measurableSet_ball
  intro y hy
  have hT := boundary_neumann_slice_height_pos hy
  have hfc : ContinuousOn (fun t => f (graphAppendN y t))
      (Icc 0 (Real.sqrt (1 - ‖y‖ ^ 2))) :=
    hf.comp (continuous_const.add (continuous_id.smul continuous_const)).continuousOn
      (fun _ ht => boundary_neumann_closed_slice hy ht)
  simp only [boundaryNeumannPrimitive, graphProjectionN_append, graphAppendN_last,
    real_inner_smul_left, EuclideanSpace.inner_single_left, map_one, one_mul]
  rw [← integral_Ioc_eq_integral_Ioo, ← integral_Ioc_eq_integral_Ioo,
    ← intervalIntegral.integral_of_le hT.le, ← intervalIntegral.integral_of_le hT.le]
  exact boundary_neumann_primitive_slice hT.le hfc hφ y
    (boundary_neumann_test_zero_at_slice_top hsφ hy)

/-- The inhomogeneous weak formulation implies exactly the homogeneous test
identity required by Layer 1, for the explicit lift and corrected datum.
This statement concerns the equation only, without claiming regularity of the lift. -/
theorem boundary_neumann_inhomogeneous_weak_reduction {a cap Bf Hf : ℝ}
    (ha : 0 < a) (ha1 : a ≤ 1) (hBf : 0 ≤ Bf) (hHf : 0 ≤ Hf)
    {A : EuclideanSpace ℝ (Fin 3) → EuclideanSpace ℝ (Fin 3) →L[ℝ]
      EuclideanSpace ℝ (Fin 3)}
    {F : EuclideanSpace ℝ (Fin 3) → EuclideanSpace ℝ (Fin 3)}
    {f : EuclideanSpace ℝ (Fin 3) → ℝ} {h : EuclideanSpace ℝ (Fin 2) → ℝ}
    (hA : ContinuousOn A (closure (boundaryHalfBall 1)))
    (hbA : ∀ x ∈ closure (boundaryHalfBall 1), ‖A x‖ ≤ cap)
    (hF : MemLp F 2 (volume.restrict (boundaryHalfBall 1)))
    (hf : ContinuousOn f (closure (boundaryHalfBall 1)))
    (hbf : ∀ x ∈ closure (boundaryHalfBall 1), ‖f x‖ ≤ Bf)
    (hhf : ∀ x ∈ closure (boundaryHalfBall 1), ∀ y ∈ closure (boundaryHalfBall 1),
      ‖f x - f y‖ ≤ Hf * dist x y ^ a)
    (hh : ContinuousOn h (closedBall 0 1))
    (hweak : ∀ φ : EuclideanSpace ℝ (Fin 3) → ℝ, ContDiff ℝ 1 φ → HasCompactSupport φ →
      tsupport φ ⊆ ball 0 1 →
      (∫ x in boundaryHalfBall 1, inner ℝ (A x (F x)) (gradient φ x)) =
        -(∫ x in boundaryHalfBall 1, f x * φ x) -
          ∫ y in ball (0 : EuclideanSpace ℝ (Fin 2)) 1, h y * φ (graphBaseEmbedding y)) :
    ∀ φ : EuclideanSpace ℝ (Fin 3) → ℝ, ContDiff ℝ 1 φ → HasCompactSupport φ →
      tsupport φ ⊆ ball 0 1 →
      (∫ x in boundaryHalfBall 1,
        inner ℝ (A x (F x - gradient (boundaryNeumannLift h
          (boundaryNeumannNormalCoefficient A)) x) - boundaryNeumannInhomDatum A f h x)
            (gradient φ x)) = 0 := by
  intro φ hφ hcφ hsφ
  have hAF : MemLp (fun x => A x (F x)) 2 (volume.restrict (boundaryHalfBall 1)) := by
    have he := boundary_neumann_flux_memLp (a := a) (HH := 0) (H := fun _ => 0)
      ha.le le_rfl hA continuousOn_const hbA (by simp) hF
    simpa only [sub_zero] using he
  have hg : MemLp (gradient φ) 2 volume :=
    (continuous_gradient_of_contDiff hφ).memLp_of_hasCompactSupport
      (hcφ.of_isClosed_subset (isClosed_tsupport _) (tsupport_gradient_subset φ))
  have hiAF := integrable_inner_of_memLp_two hAF (hg.restrict (boundaryHalfBall 1))
  have hP := boundaryNeumannPrimitive_continuousOn ha ha1 hBf hHf hf hbf hhf
  have hiP := boundary_neumann_integrableOn_of_continuousOn
    (hP.inner (continuous_gradient_of_contDiff hφ).continuousOn)
  have hp : MapsTo (graphProjectionN 2) (closure (boundaryHalfBall 1)) (closedBall 0 1) := by
    intro x hx
    simp only [mem_closedBall, dist_zero_right]
    exact (boundary_neumann_norm_projection_le x).trans (boundary_neumann_closed_norm_le hx)
  have hih : IntegrableOn
      (fun x => h (graphProjectionN 2 x) * gradient φ x (Fin.last 2)) (boundaryHalfBall 1) :=
    boundary_neumann_integrableOn_of_continuousOn
      ((hh.comp (graphProjectionN 2).continuous.continuousOn hp).mul
        ((EuclideanSpace.proj (Fin.last 2)).continuous.comp
          (continuous_gradient_of_contDiff hφ)).continuousOn)
  have hiD : IntegrableOn (fun x => inner ℝ (A x (F x)) (gradient φ x) -
      inner ℝ (boundaryNeumannPrimitive f x) (gradient φ x)) (boundaryHalfBall 1) :=
    hiAF.sub hiP
  simp_rw [boundaryNeumannInhomDatum_flux, inner_sub_left, real_inner_smul_left,
    EuclideanSpace.inner_single_left, map_one, one_mul]
  rw [integral_sub hiD hih, integral_sub hiAF hiP,
    hweak φ hφ hcφ hsφ,
    boundary_neumann_interior_source_identity ha ha1 hBf hHf hf hbf hhf hφ hsφ,
    boundary_neumann_boundary_source_identity hh hφ hcφ hsφ]
  ring

end LiquidDrop

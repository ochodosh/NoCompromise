module

public import NoCompromise.Elliptic.BoundaryNeumannC2Tangential
public import NoCompromise.Elliptic.NondivSchauderClassical

@[expose] public section

/-!
# The classical divergence identity for the homogeneous Neumann problem

Interior C² regularity is an explicit hypothesis in the pointwise theorem below.
It is not asserted to follow from the closed data in this file.
-/

noncomputable section
open MeasureTheory Filter Metric Set InnerProductSpace
open scoped ENNReal NNReal Topology Gradient RealInnerProductSpace
namespace LiquidDrop

lemma boundary_neumann_c2_continuousOn_divergence {n : ℕ}
    {U : Set (EuclideanSpace ℝ (Fin n))} (hU : IsOpen U)
    {F : EuclideanSpace ℝ (Fin n) → EuclideanSpace ℝ (Fin n)}
    (hF : ContDiffOn ℝ 1 F U) : ContinuousOn (divergenceN F) U := by
  unfold divergenceN
  apply continuousOn_finsetSum
  intro i _
  exact (EuclideanSpace.proj i).continuous.comp_continuousOn
    ((hF.continuousOn_fderiv_of_isOpen hU le_rfl).clm_apply continuousOn_const)

/-- Local C¹ integration by parts for a vector field and a compactly supported
scalar test. The vector field need only be regular on the open domain. -/
theorem boundary_neumann_c2_integral_divergence {n : ℕ}
    {U : Set (EuclideanSpace ℝ (Fin n))} (hU : IsOpen U)
    {F : EuclideanSpace ℝ (Fin n) → EuclideanSpace ℝ (Fin n)}
    (hF : ContDiffOn ℝ 1 F U)
    {φ : EuclideanSpace ℝ (Fin n) → ℝ} (hφ : ContDiff ℝ 1 φ)
    (hcφ : HasCompactSupport φ) (hsφ : tsupport φ ⊆ U) :
    (∫ x, inner ℝ (F x) (gradient φ x)) = -(∫ x, φ x * divergenceN F x) := by
  have hprod : ContDiff ℝ 1 (fun x => φ x • F x) := by
    apply contDiff_iff_contDiffAt.mpr
    intro x
    by_cases hx : x ∈ U
    · exact hφ.contDiffAt.smul (hF.contDiffAt (hU.mem_nhds hx))
    · have hxφ : x ∉ tsupport φ := fun ht => hx (hsφ ht)
      apply (contDiffAt_const (c := (0 : EuclideanSpace ℝ (Fin n)))).congr_of_eventuallyEq
      filter_upwards [(isClosed_tsupport φ).isOpen_compl.mem_nhds hxφ] with y hy
      simp only [image_eq_zero_of_notMem_tsupport hy, zero_smul]
  have hcprod : HasCompactSupport (fun x => φ x • F x) := hcφ.smul_right
  have hi₁ := integrable_mul_compact_factor_on
    ((boundary_neumann_c2_continuousOn_divergence hU hF).locallyIntegrableOn hU.measurableSet)
    hφ.continuous hcφ hsφ
  have hi₂ : Integrable (fun x => inner ℝ (F x) (gradient φ x)) := by
    simpa only [real_inner_comm] using integrable_inner_compact_factor_on
      (hF.continuousOn.locallyIntegrableOn hU.measurableSet)
      (continuous_gradient_of_contDiff hφ)
      (hcφ.of_isClosed_subset (isClosed_tsupport _) (tsupport_gradient_subset φ))
      ((tsupport_gradient_subset φ).trans hsφ)
  have heq : divergenceN (fun x => φ x • F x) =
      fun x => φ x * divergenceN F x + inner ℝ (F x) (gradient φ x) := by
    funext x
    by_cases hx : x ∈ U
    · simpa only [real_inner_comm] using divergenceN_smul_of_differentiableAt
        (hφ.differentiable one_ne_zero x)
        ((hF.contDiffAt (hU.mem_nhds hx)).differentiableAt one_ne_zero)
    · have hxφ : x ∉ tsupport φ := fun ht => hx (hsφ ht)
      rw [divergenceN_eq_zero_of_notMem_tsupport
        (fun ht => hxφ (tsupport_smul_subset_left φ F ht)),
        image_eq_zero_of_notMem_tsupport hxφ, gradient_eq_zero_of_notMem_tsupport hxφ,
        zero_mul, inner_zero_right, add_zero]
  have hz := integral_divergenceN_eq_zero hprod hcprod
  rw [heq, integral_add hi₁ hi₂] at hz
  linarith

/-- A C¹ flux whose weak divergence vanishes has zero classical divergence. -/
theorem boundary_neumann_c2_divergence_eq_zero {n : ℕ}
    {U : Set (EuclideanSpace ℝ (Fin n))} (hU : IsOpen U)
    {F : EuclideanSpace ℝ (Fin n) → EuclideanSpace ℝ (Fin n)}
    (hF : ContDiffOn ℝ 1 F U)
    (he : ∀ φ : EuclideanSpace ℝ (Fin n) → ℝ,
      ContDiff ℝ 1 φ → HasCompactSupport φ → tsupport φ ⊆ U →
        (∫ x, inner ℝ (F x) (gradient φ x)) = 0) :
    EqOn (divergenceN F) (fun _ => 0) U := by
  have hc := boundary_neumann_c2_continuousOn_divergence hU hF
  have hz : ∀ᵐ x ∂volume, x ∈ U → divergenceN F x = 0 := by
    apply hU.ae_eq_zero_of_integral_contDiff_smul_eq_zero
      (hc.locallyIntegrableOn hU.measurableSet)
    intro φ hφ hcφ hsφ
    have hφ1 : ContDiff ℝ 1 φ := hφ.of_le (by simp)
    have hh := boundary_neumann_c2_integral_divergence hU hF hφ1 hcφ hsφ
    rw [he φ hφ1 hcφ hsφ] at hh
    change (∫ x, φ x * divergenceN F x) = 0
    linarith
  exact Measure.eqOn_open_of_ae_eq ((ae_restrict_iff' hU.measurableSet).mpr hz)
    hU hc continuousOn_const

/-- The precise interior regularity required when extracting a classical equation
from the conormal identity. `boundary_neumann_interior_c2` in
`BoundaryNeumannC2Interior` proves this from the original closed data. -/
def BoundaryNeumannInteriorC2 (w : EuclideanSpace ℝ (Fin 3) → ℝ) : Prop :=
  ContDiffOn ℝ 2 w (boundaryHalfBall 1)

/-- With explicitly supplied interior C² regularity, the homogeneous weak
Neumann equation is a classical zero-divergence equation for `A ∇w - H`. -/
theorem boundary_neumann_c2_pointwise_flux {α lam cap M N : ℝ}
    {A : EuclideanSpace ℝ (Fin 3) → EuclideanSpace ℝ (Fin 3) →L[ℝ]
      EuclideanSpace ℝ (Fin 3)}
    {H : EuclideanSpace ℝ (Fin 3) → EuclideanSpace ℝ (Fin 3)}
    {w : EuclideanSpace ℝ (Fin 3) → ℝ}
    (d : BoundaryNeumannClosedData α lam cap M N A H w)
    (hinteriorC2 : BoundaryNeumannInteriorC2 w) :
    ∀ x ∈ boundaryHalfBall 1,
      divergenceN (fun y => A y (gradient w y) - H y) x = 0 := by
  have hU := isOpen_boundaryHalfBall (1 : ℝ)
  have hDw : ContDiffOn ℝ 1 (fderiv ℝ w) (boundaryHalfBall 1) :=
    hinteriorC2.fderiv_of_isOpen hU (by norm_num)
  have hGw : ContDiffOn ℝ 1 (gradient w) (boundaryHalfBall 1) :=
    (toDual ℝ (EuclideanSpace ℝ (Fin 3))).symm.toContinuousLinearEquiv.contDiff
      |>.comp_contDiffOn hDw
  have hF : ContDiffOn ℝ 1 (fun y => A y (gradient w y) - H y) (boundaryHalfBall 1) :=
    ((d.coefficient.contDiff.mono subset_closure).clm_apply hGw).sub
      (d.source.contDiff.mono subset_closure)
  apply boundary_neumann_c2_divergence_eq_zero hU hF
  intro φ hφ hcφ hsφ
  rw [← setIntegral_eq_integral_of_forall_compl_eq_zero (s := boundaryHalfBall 1)
    (fun x hx => by
      rw [gradient_eq_zero_of_notMem_tsupport (fun ht => hx (hsφ ht)), inner_zero_right])]
  exact d.equation φ hφ hcφ (hsφ.trans inter_subset_left)

lemma boundary_neumann_c2_divergence_product
    {A : EuclideanSpace ℝ (Fin 3) → EuclideanSpace ℝ (Fin 3) →L[ℝ]
      EuclideanSpace ℝ (Fin 3)}
    {G H : EuclideanSpace ℝ (Fin 3) → EuclideanSpace ℝ (Fin 3)}
    {x : EuclideanSpace ℝ (Fin 3)}
    (hA : DifferentiableAt ℝ A x) (hG : DifferentiableAt ℝ G x)
    (hH : DifferentiableAt ℝ H x) :
    divergenceN (fun y => A y (G y) - H y) x =
      (∑ i, ∑ j, A x (EuclideanSpace.single j 1) i *
        fderiv ℝ G x (EuclideanSpace.single i 1) j) +
      (∑ i, ∑ j, fderiv ℝ A x (EuclideanSpace.single i 1)
        (EuclideanSpace.single j 1) i * G x j) - divergenceN H x := by
  have hd : HasFDerivAt (fun y => A y (G y) - H y)
      ((A x).comp (fderiv ℝ G x) + (fderiv ℝ A x).flip (G x) - fderiv ℝ H x) x :=
    (hA.hasFDerivAt.clm_apply hG.hasFDerivAt).sub hH.hasFDerivAt
  simp only [divergenceN, hd.fderiv, sub_apply, add_apply,
    ContinuousLinearMap.flip_apply, ContinuousLinearMap.comp_apply,
    PiLp.sub_apply, PiLp.add_apply, Finset.sum_sub_distrib, Finset.sum_add_distrib]
  congr 2
  · apply Finset.sum_congr rfl
    intro i _
    rw [frozen_linear_component_eq_sum]
    apply Finset.sum_congr rfl
    intro j _
    exact mul_comm _ _
  · apply Finset.sum_congr rfl
    intro i _
    rw [frozen_linear_component_eq_sum]
    apply Finset.sum_congr rfl
    intro j _
    exact mul_comm _ _

/-- The expanded pointwise equation, with row-column convention
`Aᵢⱼ = (A eⱼ)ᵢ`. The second derivative displayed is `∂ᵢ(∂ⱼw)`.
Interior C² is an explicit additional hypothesis. -/
theorem boundary_neumann_c2_pointwise_equation {α lam cap M N : ℝ}
    {A : EuclideanSpace ℝ (Fin 3) → EuclideanSpace ℝ (Fin 3) →L[ℝ]
      EuclideanSpace ℝ (Fin 3)}
    {H : EuclideanSpace ℝ (Fin 3) → EuclideanSpace ℝ (Fin 3)}
    {w : EuclideanSpace ℝ (Fin 3) → ℝ}
    (d : BoundaryNeumannClosedData α lam cap M N A H w)
    (hinteriorC2 : BoundaryNeumannInteriorC2 w) :
    ∀ x ∈ boundaryHalfBall 1,
      (∑ i, ∑ j, A x (EuclideanSpace.single j 1) i *
        fderiv ℝ (fun y => fderiv ℝ w y (EuclideanSpace.single j 1)) x
          (EuclideanSpace.single i 1)) +
      (∑ i, ∑ j, fderiv ℝ A x (EuclideanSpace.single i 1)
        (EuclideanSpace.single j 1) i * fderiv ℝ w x (EuclideanSpace.single j 1)) =
      divergenceN H x := by
  intro x hx
  have hU := isOpen_boundaryHalfBall (1 : ℝ)
  have hDw : ContDiffOn ℝ 1 (fderiv ℝ w) (boundaryHalfBall 1) :=
    hinteriorC2.fderiv_of_isOpen hU (by norm_num)
  have hGw : ContDiffOn ℝ 1 (gradient w) (boundaryHalfBall 1) :=
    (toDual ℝ (EuclideanSpace ℝ (Fin 3))).symm.toContinuousLinearEquiv.contDiff
      |>.comp_contDiffOn hDw
  have hdG := (hGw.contDiffAt (hU.mem_nhds hx)).differentiableAt one_ne_zero
  have hpartial (i j : Fin 3) :
      fderiv ℝ (gradient w) x (EuclideanSpace.single i 1) j =
        fderiv ℝ (fun y => fderiv ℝ w y (EuclideanSpace.single j 1)) x
          (EuclideanSpace.single i 1) := by
    have he : (fun y => fderiv ℝ w y (EuclideanSpace.single j 1)) =
        fun y => gradient w y j := funext fun y => (gradient_apply_eq_fderiv_single w y j).symm
    rw [he]
    change _ = fderiv ℝ ((EuclideanSpace.proj j) ∘ gradient w) x _
    rw [((EuclideanSpace.proj j).hasFDerivAt.comp x hdG.hasFDerivAt).fderiv]
    rfl
  have hdA := ((d.coefficient.contDiff.mono subset_closure).contDiffAt
    (hU.mem_nhds hx)).differentiableAt one_ne_zero
  have hdH := ((d.source.contDiff.mono subset_closure).contDiffAt
    (hU.mem_nhds hx)).differentiableAt one_ne_zero
  have hp := boundary_neumann_c2_divergence_product hdA hdG hdH
  rw [boundary_neumann_c2_pointwise_flux d hinteriorC2 x hx] at hp
  simp only [hpartial, gradient_apply_eq_fderiv_single] at hp
  linarith

end LiquidDrop

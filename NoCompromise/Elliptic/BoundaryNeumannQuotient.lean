import NoCompromise.Elliptic.BoundaryNondivHolder
import NoCompromise.Elliptic.BoundaryNeumann

/-!
# Tangential quotients of the homogeneous conormal equation

Tests are C¹ functions supported in the ambient ball and may meet the flat face.
The principal coefficient is unshifted; consequently the correction uses the
translated gradient. No symmetry of the coefficient is assumed.
-/

noncomputable section
open MeasureTheory Filter Metric Set InnerProductSpace
open scoped ENNReal Topology Gradient RealInnerProductSpace
namespace LiquidDrop

/-- The conormal identity, including tests meeting the flat face. -/
def IsBoundaryNeumannEquationOn
    (A : EuclideanSpace ℝ (Fin 3) → EuclideanSpace ℝ (Fin 3) →L[ℝ]
      EuclideanSpace ℝ (Fin 3))
    (F H : EuclideanSpace ℝ (Fin 3) → EuclideanSpace ℝ (Fin 3)) (r : ℝ) : Prop :=
  ∀ φ : EuclideanSpace ℝ (Fin 3) → ℝ, ContDiff ℝ 1 φ → HasCompactSupport φ →
    tsupport φ ⊆ ball 0 r →
    (∫ x in boundaryHalfBall r, inner ℝ (A x (F x) - H x) (gradient φ x)) = 0

/-- The exact datum for the unshifted principal coefficient. -/
def boundaryNeumannQuotientDatum
    (A : EuclideanSpace ℝ (Fin 3) → EuclideanSpace ℝ (Fin 3) →L[ℝ]
      EuclideanSpace ℝ (Fin 3))
    (F H : EuclideanSpace ℝ (Fin 3) → EuclideanSpace ℝ (Fin 3))
    (i : Fin 3) (s : ℝ) (x : EuclideanSpace ℝ (Fin 3)) : EuclideanSpace ℝ (Fin 3) :=
  coordinateDifferenceQuotient i s H x -
    coordinateDifferenceQuotient i s A x (F (x + s • EuclideanSpace.single i 1))

lemma boundary_neumann_tangential_last {i : Fin 3} (hi : i ≠ Fin.last 2)
    (s : ℝ) (x : EuclideanSpace ℝ (Fin 3)) :
    (x + s • EuclideanSpace.single i (1 : ℝ)) (Fin.last 2) = x (Fin.last 2) := by
  simp only [PiLp.add_apply, PiLp.smul_apply, PiLp.single_apply, Ne.symm hi,
    ite_false, smul_zero, add_zero]

lemma boundary_neumann_integral_upper_eq {r : ℝ}
    (f : EuclideanSpace ℝ (Fin 3) → ℝ)
    (hf : ∀ x ∉ ball (0 : EuclideanSpace ℝ (Fin 3)) r, f x = 0) :
    (∫ x in {x : EuclideanSpace ℝ (Fin 3) | 0 < x (Fin.last 2)}, f x) =
      ∫ x in boundaryHalfBall r, f x := by
  have h := setIntegral_eq_integral_of_forall_compl_eq_zero
    (μ := volume.restrict {x : EuclideanSpace ℝ (Fin 3) | 0 < x (Fin.last 2)})
    (s := ball 0 r) hf
  rw [Measure.restrict_restrict measurableSet_ball] at h
  exact h.symm

lemma boundary_neumann_integral_upper_translate
    (f : EuclideanSpace ℝ (Fin 3) → ℝ) {i : Fin 3} (hi : i ≠ Fin.last 2) (s : ℝ) :
    (∫ x in {x : EuclideanSpace ℝ (Fin 3) | 0 < x (Fin.last 2)},
      f (x + s • EuclideanSpace.single i 1)) =
      ∫ x in {x : EuclideanSpace ℝ (Fin 3) | 0 < x (Fin.last 2)}, f x := by
  let U := {x : EuclideanSpace ℝ (Fin 3) | 0 < x (Fin.last 2)}
  have hm : MeasurableSet U := boundary_holder_open_upper.measurableSet
  rw [← integral_indicator hm, ← integral_indicator hm]
  have he : U.indicator (fun x => f (x + s • EuclideanSpace.single i 1)) =
      fun x => U.indicator f (x + s • EuclideanSpace.single i 1) := by
    funext x
    have hx : x + s • EuclideanSpace.single i 1 ∈ U ↔ x ∈ U := by
      simp only [U, mem_ofPred_eq, boundary_neumann_tangential_last hi]
    by_cases h : x ∈ U
    · simp only [indicator_of_mem h, indicator_of_mem (hx.mpr h)]
    · simp only [indicator_of_notMem h, indicator_of_notMem (mt hx.mp h)]
  rw [he, integral_add_right_eq_self]

/-- Translation of the original flux identity, with C¹ ambient tests. -/
lemma boundary_neumann_flux_translate {R r s : ℝ} {i : Fin 3}
    (hi : i ≠ Fin.last 2) (hs : |s| ≤ R - r)
    {V : EuclideanSpace ℝ (Fin 3) → EuclideanSpace ℝ (Fin 3)}
    (he : ∀ φ : EuclideanSpace ℝ (Fin 3) → ℝ, ContDiff ℝ 1 φ →
      HasCompactSupport φ → tsupport φ ⊆ ball 0 R →
      (∫ x in boundaryHalfBall R, inner ℝ (V x) (gradient φ x)) = 0)
    {φ : EuclideanSpace ℝ (Fin 3) → ℝ} (hφ : ContDiff ℝ 1 φ)
    (hcφ : HasCompactSupport φ) (hsφ : tsupport φ ⊆ ball 0 r) :
    (∫ x in boundaryHalfBall r,
      inner ℝ (V (x + s • EuclideanSpace.single i 1)) (gradient φ x)) = 0 := by
  let a := s • EuclideanSpace.single i (1 : ℝ)
  let ψ := fun x => φ (x + -a)
  have hψ : ContDiff ℝ 1 ψ := hφ.comp (contDiff_id.add contDiff_const)
  have hcψ : HasCompactSupport ψ := hcφ.comp_homeomorph (Homeomorph.addRight (-a))
  have hsψ : tsupport ψ ⊆ ball 0 R := by
    intro x hx
    change x ∈ tsupport (φ ∘ Homeomorph.addRight (-a)) at hx
    rw [tsupport_comp_eq_preimage] at hx
    have hxb := hsφ hx
    rw [mem_ball_zero_iff] at hxb ⊢
    have hn : ‖a‖ = |s| := by simp [a, norm_smul, Real.norm_eq_abs]
    have ht := norm_add_le (x + -a) a
    simp only [add_assoc, neg_add_cancel, add_zero, hn] at ht
    change ‖x + -a‖ < r at hxb
    linarith
  have ht := he ψ hψ hcψ hsψ
  rw [← boundary_neumann_integral_upper_eq _ (fun x hx => by
    rw [gradient_eq_zero_of_notMem_tsupport (fun h => hx (hsψ h)), inner_zero_right])] at ht
  rw [← boundary_neumann_integral_upper_eq _ (fun x hx => by
    rw [gradient_eq_zero_of_notMem_tsupport (fun h => hx (hsφ h)), inner_zero_right])]
  rw [← boundary_neumann_integral_upper_translate _ hi s] at ht
  simpa only [ψ, nondiv_gradient_addRight, a, add_neg_cancel_right] using ht

lemma boundary_neumann_flux_quotient {R r s : ℝ} {i : Fin 3}
    (hi : i ≠ Fin.last 2) (hs : |s| ≤ R - r)
    {V : EuclideanSpace ℝ (Fin 3) → EuclideanSpace ℝ (Fin 3)}
    (hV : ContinuousOn V (closure (boundaryHalfBall R)))
    (he : ∀ φ : EuclideanSpace ℝ (Fin 3) → ℝ, ContDiff ℝ 1 φ →
      HasCompactSupport φ → tsupport φ ⊆ ball 0 R →
      (∫ x in boundaryHalfBall R, inner ℝ (V x) (gradient φ x)) = 0) :
    ∀ φ : EuclideanSpace ℝ (Fin 3) → ℝ, ContDiff ℝ 1 φ → HasCompactSupport φ →
      tsupport φ ⊆ ball 0 r →
      (∫ x in boundaryHalfBall r,
        inner ℝ (coordinateDifferenceQuotient i s V x) (gradient φ x)) = 0 := by
  intro φ hφ hcφ hsφ
  have hrR : r ≤ R := by linarith [abs_nonneg s]
  have hmap : MapsTo (fun x => x + s • EuclideanSpace.single i (1 : ℝ))
      (closure (boundaryHalfBall r)) (closure (boundaryHalfBall R)) :=
    (show MapsTo (fun x => x + s • EuclideanSpace.single i (1 : ℝ))
      (boundaryHalfBall r) (boundaryHalfBall R) from
      fun _ hx => boundaryHalfBall_add_tangential hi hs hx).closure
        (continuous_id.add continuous_const)
  have hc : IsCompact (closure (boundaryHalfBall r)) :=
    (isBounded_ball.subset (inter_subset_left : boundaryHalfBall r ⊆ ball 0 r)).isCompact_closure
  have hi0 : Integrable (fun x => inner ℝ (V x) (gradient φ x))
      (volume.restrict (boundaryHalfBall r)) :=
    (((hV.mono (closure_mono (boundaryHalfBall_mono hrR))).inner (𝕜 := ℝ)
      (continuous_gradient_of_contDiff hφ).continuousOn).integrableOn_compact hc).mono_set
        subset_closure
  have hi1 : Integrable (fun x => inner ℝ (V (x + s • EuclideanSpace.single i 1)) (gradient φ x))
      (volume.restrict (boundaryHalfBall r)) :=
    (((hV.comp (continuous_id.add continuous_const).continuousOn hmap).inner (𝕜 := ℝ)
      (continuous_gradient_of_contDiff hφ).continuousOn).integrableOn_compact hc).mono_set
        subset_closure
  have ht1 := boundary_neumann_flux_translate hi hs he hφ hcφ hsφ
  have ht0 := boundary_neumann_flux_translate hi
    (show |(0 : ℝ)| ≤ R - r by simpa using sub_nonneg.mpr hrR) he hφ hcφ hsφ
  simp only [zero_smul, add_zero] at ht0
  simp only [coordinateDifferenceQuotient, real_inner_smul_left, inner_sub_left]
  rw [integral_const_mul, integral_sub hi1 hi0, ht1, ht0, sub_self, mul_zero]

lemma boundary_neumann_normal_apply_zero
    {A : EuclideanSpace ℝ (Fin 3) →L[ℝ] EuclideanSpace ℝ (Fin 3)}
    (hA : ∀ j : Fin 3, j ≠ Fin.last 2 → A (EuclideanSpace.single j 1) (Fin.last 2) = 0)
    {v : EuclideanSpace ℝ (Fin 3)} (hv : v (Fin.last 2) = 0) :
    A v (Fin.last 2) = 0 := by
  change (EuclideanSpace.proj (Fin.last 2)) (A v) = 0
  conv_lhs => rw [← (EuclideanSpace.basisFun (Fin 3) ℝ).sum_repr v]
  simp only [map_sum, map_smul, EuclideanSpace.basisFun_apply]
  change (∑ j : Fin 3, (EuclideanSpace.basisFun (Fin 3) ℝ).repr v j •
    A (EuclideanSpace.single j 1) (Fin.last 2)) = 0
  apply Finset.sum_eq_zero
  intro j _
  by_cases hj : j = Fin.last 2
  · subst j
    change v (Fin.last 2) • A (EuclideanSpace.single (Fin.last 2) 1) (Fin.last 2) = 0
    rw [hv, zero_smul]
  · rw [hA j hj, smul_zero]

/-- Exact quotient equation and vanishing normal datum. Both cross rows of the
original coefficient are preserved because the principal coefficient is unshifted.
The equation itself is valid even for the zero step under the quotient convention. -/
theorem boundary_neumann_quotient_equation {R r s : ℝ} {i : Fin 3}
    (hi : i ≠ Fin.last 2) (hs : |s| ≤ R - r)
    {A : EuclideanSpace ℝ (Fin 3) → EuclideanSpace ℝ (Fin 3) →L[ℝ]
      EuclideanSpace ℝ (Fin 3)}
    {F H : EuclideanSpace ℝ (Fin 3) → EuclideanSpace ℝ (Fin 3)}
    (hA : ContinuousOn A (closure (boundaryHalfBall R)))
    (hF : ContinuousOn F (closure (boundaryHalfBall R)))
    (hH : ContinuousOn H (closure (boundaryHalfBall R)))
    (he : IsBoundaryNeumannEquationOn A F H R)
    (hcross : ∀ x ∈ closure (boundaryHalfBall R), x (Fin.last 2) = 0 →
      ∀ j : Fin 3, j ≠ Fin.last 2 → A x (EuclideanSpace.single j 1) (Fin.last 2) = 0)
    (hHzero : ∀ x ∈ closure (boundaryHalfBall R), x (Fin.last 2) = 0 → H x (Fin.last 2) = 0)
    (hFzero : ∀ x ∈ closure (boundaryHalfBall R), x (Fin.last 2) = 0 → F x (Fin.last 2) = 0) :
    IsBoundaryNeumannEquationOn A (coordinateDifferenceQuotient i s F)
      (boundaryNeumannQuotientDatum A F H i s) r ∧
    ∀ x ∈ closure (boundaryHalfBall r), x (Fin.last 2) = 0 →
      boundaryNeumannQuotientDatum A F H i s x (Fin.last 2) = 0 := by
  constructor
  · have ht := boundary_neumann_flux_quotient hi hs ((hA.clm_apply hF).sub hH) he
    have hp (x) : A x (coordinateDifferenceQuotient i s F x) -
        boundaryNeumannQuotientDatum A F H i s x =
        coordinateDifferenceQuotient i s (fun y => A y (F y) - H y) x := by
      simp only [boundaryNeumannQuotientDatum, coordinateDifferenceQuotient,
        map_smul, map_sub, smul_apply, sub_apply]
      module
    intro φ hφ hcφ hsφ
    simp_rw [hp]
    exact ht φ hφ hcφ hsφ
  · intro x hx hflat
    have hrR : r ≤ R := by linarith [abs_nonneg s]
    have hx0 := closure_mono (boundaryHalfBall_mono hrR) hx
    have hx1 : x + s • EuclideanSpace.single i 1 ∈ closure (boundaryHalfBall R) := by
      simpa only [one_smul] using boundary_nondiv_closed_segment hi hs hx (t := 1) (by simp)
    have hf1 := (boundary_neumann_tangential_last hi s x).trans hflat
    have ha0 := boundary_neumann_normal_apply_zero (hcross x hx0 hflat) (hFzero _ hx1 hf1)
    have ha1 := boundary_neumann_normal_apply_zero (hcross _ hx1 hf1) (hFzero _ hx1 hf1)
    simp only [boundaryNeumannQuotientDatum, coordinateDifferenceQuotient, smul_apply,
      sub_apply, PiLp.sub_apply, PiLp.smul_apply, hHzero _ hx1 hf1,
      hHzero x hx0 hflat, ha0, ha1, sub_self, smul_zero]

end LiquidDrop

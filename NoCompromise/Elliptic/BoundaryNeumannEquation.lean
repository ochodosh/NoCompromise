import NoCompromise.Elliptic.BoundaryNeumannReflection
import NoCompromise.Elliptic.BoundaryNeumannCoefficients
import NoCompromise.Elliptic.BoundaryHolderOddWeak

/-! The homogeneous conormal test identity implies the full reflected equation. -/

noncomputable section
open MeasureTheory Filter Metric Set InnerProductSpace
open scoped ENNReal NNReal Topology Gradient RealInnerProductSpace
namespace LiquidDrop

lemma boundary_neumann_gradient_reflection {φ : EuclideanSpace ℝ (Fin 3) → ℝ}
    (hφ : ContDiff ℝ 1 φ) (x : EuclideanSpace ℝ (Fin 3)) :
    gradient (φ ∘ coordinateReflection (Fin.last 2)) x =
      coordinateReflection (Fin.last 2) (gradient φ (coordinateReflection (Fin.last 2) x)) := by
  have hh := frozen_gradient_comp_linear
    (coordinateReflection (Fin.last 2)).toContinuousLinearEquiv
    (hφ.differentiable one_ne_zero) x
  simpa only [boundary_reflection_adjoint, ContinuousLinearEquiv.coe_coe,
    LinearIsometryEquiv.coe_toContinuousLinearEquiv] using hh

lemma boundary_neumann_gradient_add {f g : EuclideanSpace ℝ (Fin 3) → ℝ}
    (hf : ContDiff ℝ 1 f) (hg : ContDiff ℝ 1 g) (x : EuclideanSpace ℝ (Fin 3)) :
    gradient (fun y => f y + g y) x = gradient f x + gradient g x := by
  ext i
  simp only [gradient_apply_eq_fderiv_single, PiLp.add_apply,
    fderiv_fun_add (hf.differentiable one_ne_zero x) (hg.differentiable one_ne_zero x),
    add_apply]

lemma boundary_neumann_reflected_pairing
    (V : EuclideanSpace ℝ (Fin 3) → EuclideanSpace ℝ (Fin 3))
    {φ : EuclideanSpace ℝ (Fin 3) → ℝ} (hφ : ContDiff ℝ 1 φ) :
    (∫ x, inner ℝ (coordinateReflection (Fin.last 2)
        (V (coordinateReflection (Fin.last 2) x))) (gradient φ x)) =
      ∫ x, inner ℝ (V x) (gradient (φ ∘ coordinateReflection (Fin.last 2)) x) := by
  let R := coordinateReflection (Fin.last 2)
  have hm := R.measurePreserving.integral_comp R.toHomeomorph.measurableEmbedding
    (fun x => inner ℝ (R (V (R x))) (gradient φ x))
  rw [← hm]
  apply integral_congr_ae
  apply Eventually.of_forall
  intro x
  change inner ℝ (R (V (R (R x)))) (gradient φ (R x)) =
    inner ℝ (V x) (gradient (φ ∘ coordinateReflection (Fin.last 2)) x)
  rw [boundary_reflection_twice, boundary_neumann_gradient_reflection hφ]
  have hh := R.inner_map_map (V x) (R (gradient φ (R x)))
  dsimp only [R] at hh
  simpa only [boundary_reflection_twice] using hh

lemma boundaryEvenField_pairing
    {V : EuclideanSpace ℝ (Fin 3) → EuclideanSpace ℝ (Fin 3)}
    (hV : MemLp V 2 (volume.restrict (boundaryHalfBall 1)))
    {φ : EuclideanSpace ℝ (Fin 3) → ℝ}
    (hφ : ContDiff ℝ 1 φ) (hcφ : HasCompactSupport φ) :
    (∫ x, inner ℝ (boundaryEvenField V x) (gradient φ x)) =
      ∫ x in boundaryHalfBall 1, inner ℝ (V x)
        (gradient (fun y => φ y + φ (coordinateReflection (Fin.last 2) y)) x) := by
  let Z := (boundaryHalfBall 1).indicator V
  let R := coordinateReflection (Fin.last 2)
  have hZ : MemLp Z 2 volume :=
    (memLp_indicator_iff_restrict (isOpen_boundaryHalfBall 1).measurableSet).mpr hV
  have hRZ := R.toContinuousLinearEquiv.toContinuousLinearMap.comp_memLp'
    (hZ.comp_measurePreserving R.measurePreserving)
  have hφR : ContDiff ℝ 1 (φ ∘ R) := hφ.comp R.toContinuousLinearEquiv.contDiff
  have hcφR := hcφ.comp_homeomorph R.toHomeomorph
  have hgr : MemLp (gradient φ) 2 volume :=
    (continuous_gradient_of_contDiff hφ).memLp_of_hasCompactSupport
      (hcφ.of_isClosed_subset (isClosed_tsupport _) (tsupport_gradient_subset φ))
  have hgrR : MemLp (gradient (φ ∘ R)) 2 volume :=
    (continuous_gradient_of_contDiff hφR).memLp_of_hasCompactSupport
      (hcφR.of_isClosed_subset (isClosed_tsupport _) (tsupport_gradient_subset (φ ∘ R)))
  have hi1 := integrable_inner_of_memLp_two hZ hgr
  have hi2 := integrable_inner_of_memLp_two hRZ hgr
  have hi3 := integrable_inner_of_memLp_two hZ hgrR
  change Integrable (fun x => inner ℝ (R (Z (R x))) (gradient φ x)) at hi2
  have hp := boundary_neumann_reflected_pairing Z hφ
  change (∫ x, inner ℝ (R (Z (R x))) (gradient φ x)) =
    ∫ x, inner ℝ (Z x) (gradient (φ ∘ R) x) at hp
  have hind (W : EuclideanSpace ℝ (Fin 3) → EuclideanSpace ℝ (Fin 3)) :
      (∫ x, inner ℝ (Z x) (W x)) = ∫ x in boundaryHalfBall 1, inner ℝ (V x) (W x) := by
    have he : (fun x => inner ℝ (Z x) (W x)) =
        (boundaryHalfBall 1).indicator (fun x => inner ℝ (V x) (W x)) := by
      funext x
      by_cases hx : x ∈ boundaryHalfBall 1 <;> simp [Z, hx]
    rw [he, integral_indicator (isOpen_boundaryHalfBall 1).measurableSet]
  change (∫ x, inner ℝ (Z x + R (Z (R x))) (gradient φ x)) = _
  simp_rw [inner_add_left]
  rw [integral_add hi1 hi2, hp, ← integral_add hi1 hi3]
  calc
    _ = ∫ x, inner ℝ (Z x) (gradient (fun y => φ y + φ (R y)) x) := by
      apply integral_congr_ae
      apply Eventually.of_forall
      intro x
      change inner ℝ (Z x) (gradient φ x) + inner ℝ (Z x) (gradient (φ ∘ R) x) =
        inner ℝ (Z x) (gradient (fun y => φ y + (φ ∘ R) y) x)
      rw [boundary_neumann_gradient_add hφ hφR, inner_add_right]
    _ = _ := hind _

lemma boundaryEvenField_eq_lower (F : EuclideanSpace ℝ (Fin 3) → EuclideanSpace ℝ (Fin 3))
    {x : EuclideanSpace ℝ (Fin 3)} (hx : x ∈ ball 0 1) (hn : x (Fin.last 2) < 0) :
    boundaryEvenField F x =
      coordinateReflection (Fin.last 2) (F (coordinateReflection (Fin.last 2) x)) := by
  have hRx : coordinateReflection (Fin.last 2) x ∈ boundaryHalfBall 1 := by
    refine ⟨?_, ?_⟩
    · simpa only [mem_ball, dist_zero_right, (coordinateReflection (Fin.last 2)).norm_map]
        using hx
    · change 0 < coordinateReflection (Fin.last 2) x (Fin.last 2)
      rw [boundary_reflection_last]
      linarith
  have he := boundaryEvenField_reflect F (coordinateReflection (Fin.last 2) x)
  simpa only [boundary_reflection_twice, boundaryEvenField_eq_upper F hRx] using he

lemma boundary_neumann_flux_ae
    (A : EuclideanSpace ℝ (Fin 3) → EuclideanSpace ℝ (Fin 3) →L[ℝ]
      EuclideanSpace ℝ (Fin 3))
    (F H : EuclideanSpace ℝ (Fin 3) → EuclideanSpace ℝ (Fin 3)) :
    (fun x => boundaryNeumannCoefficient A x (boundaryEvenField F x) - boundaryNeumannDatum H x)
      =ᵐ[volume.restrict (ball 0 1)] boundaryEvenField (fun x => A x (F x) - H x) := by
  filter_upwards [ae_restrict_of_ae (ae_coordinate_ne_zero (Fin.last 2)),
    ae_restrict_mem measurableSet_ball] with x hn hx
  rcases lt_or_gt_of_ne hn with hneg | hpos
  · rw [boundaryNeumannCoefficient, boundaryNeumannDatum, ite_eq_right (not_le.mpr hneg),
      boundaryEvenField_eq_lower F hx hneg, boundaryNeumannConjugate_apply,
      boundary_reflection_twice, boundaryEvenField_eq_lower _ hx hneg, map_sub,
      ite_eq_right (not_le.mpr hneg)]
  · rw [boundaryNeumannCoefficient_eq_upper A hpos.le, boundaryNeumannDatum_eq_upper H hpos.le,
      boundaryEvenField_eq_upper F ⟨hx, hpos⟩, boundaryEvenField_eq_upper _ ⟨hx, hpos⟩]

/-- Reflection of the actual conormal weak equation. No assertion about the
weak gradient of the scalar extension is required for this separate step. -/
theorem boundary_neumann_even_weak_equation
    (A : EuclideanSpace ℝ (Fin 3) → EuclideanSpace ℝ (Fin 3) →L[ℝ]
      EuclideanSpace ℝ (Fin 3))
    (F H : EuclideanSpace ℝ (Fin 3) → EuclideanSpace ℝ (Fin 3))
    (hV : MemLp (fun x => A x (F x) - H x) 2 (volume.restrict (boundaryHalfBall 1)))
    (hw : ∀ φ : EuclideanSpace ℝ (Fin 3) → ℝ, ContDiff ℝ 1 φ → HasCompactSupport φ →
      tsupport φ ⊆ ball 0 1 →
        (∫ x in boundaryHalfBall 1, inner ℝ (A x (F x) - H x) (gradient φ x)) = 0) :
    IsWeakDivergenceEquationOn (boundaryNeumannCoefficient A) (boundaryEvenField F)
      (boundaryNeumannDatum H) (ball 0 1) := by
  intro φ hφ hcφ hsφ
  let R := coordinateReflection (Fin.last 2)
  have hφR : ContDiff ℝ 1 (φ ∘ R) := hφ.comp R.toContinuousLinearEquiv.contDiff
  have hsR : R ⁻¹' tsupport φ ⊆ ball 0 1 := by
    intro x hx
    have hh := hsφ hx
    simpa only [mem_ball, dist_zero_right, R.norm_map] using hh
  have hsψ : tsupport (fun x => φ x + φ (R x)) ⊆ ball 0 1 :=
    (tsupport_add _ _).trans (union_subset hsφ
      ((tsupport_comp_subset_preimage φ R.continuous).trans hsR))
  have he : (∫ x, inner ℝ
      (boundaryNeumannCoefficient A x (boundaryEvenField F x) - boundaryNeumannDatum H x)
        (gradient φ x)) =
      ∫ x, inner ℝ (boundaryEvenField (fun y => A y (F y) - H y) x) (gradient φ x) := by
    have hzero (V : EuclideanSpace ℝ (Fin 3) → EuclideanSpace ℝ (Fin 3)) :=
      setIntegral_eq_integral_of_forall_compl_eq_zero (μ := volume) (s := ball 0 1)
        (f := fun x => inner ℝ (V x) (gradient φ x)) (fun x hx => by
          rw [gradient_eq_zero_of_notMem_tsupport (fun ht => hx (hsφ ht)), inner_zero_right])
    rw [← hzero, ← hzero]
    apply integral_congr_ae
    filter_upwards [boundary_neumann_flux_ae A F H] with x hx
    rw [hx]
  rw [he, boundaryEvenField_pairing hV hφ hcφ]
  exact hw _ (hφ.add hφR) (hcφ.add (hcφ.comp_homeomorph R.toHomeomorph)) hsψ

end LiquidDrop

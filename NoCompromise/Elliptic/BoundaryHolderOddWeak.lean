import NoCompromise.Elliptic.BoundaryHolderOddField
import NoCompromise.Elliptic.BoundaryHolderLocalization

/-! Actual H¹ reflection from the original zero weak trace. The explicitly
reflected field agrees with the constructed weak gradient near the flat face. -/

noncomputable section
open MeasureTheory Filter Metric Set InnerProductSpace
open scoped ENNReal NNReal Topology Gradient RealInnerProductSpace
namespace LiquidDrop
set_option maxSynthPendingDepth 8

def boundaryOddFunction (u : EuclideanSpace ℝ (Fin 3) → ℝ)
    (x : EuclideanSpace ℝ (Fin 3)) : ℝ :=
  boundaryHolderZeroFunction u x -
    boundaryHolderZeroFunction u (coordinateReflection (Fin.last 2) x)

lemma boundary_reflection_adjoint :
    ((coordinateReflection (Fin.last 2)).toContinuousLinearEquiv.toContinuousLinearMap).adjoint =
      (coordinateReflection (Fin.last 2)).toContinuousLinearEquiv.toContinuousLinearMap := by
  rw [LinearIsometryEquiv.adjoint_eq_symm]
  apply ContinuousLinearMap.ext
  intro x
  apply (coordinateReflection (Fin.last 2)).injective
  simp only [ContinuousLinearEquiv.coe_coe, LinearIsometryEquiv.coe_toContinuousLinearEquiv,
    LinearIsometryEquiv.apply_symm_apply, boundary_reflection_twice]

lemma boundaryOddFunction_reflect (u : EuclideanSpace ℝ (Fin 3) → ℝ)
    (x : EuclideanSpace ℝ (Fin 3)) :
    boundaryOddFunction u (coordinateReflection (Fin.last 2) x) = -boundaryOddFunction u x := by
  simp only [boundaryOddFunction, boundary_reflection_twice, neg_sub]

lemma boundaryOddFunction_eq_upper (u : EuclideanSpace ℝ (Fin 3) → ℝ)
    {x : EuclideanSpace ℝ (Fin 3)} (hx : x ∈ boundaryHalfBall (1 / 64 : ℝ)) :
    boundaryOddFunction u x = u x := by
  have hn : ¬0 < coordinateReflection (Fin.last 2) x (Fin.last 2) := by
    rw [boundary_reflection_last]
    have hp : 0 < x (Fin.last 2) := hx.2
    linarith
  rw [boundaryOddFunction, boundaryHolderZeroFunction_eq u hx.1 hx.2]
  have hn' : coordinateReflection (Fin.last 2) x ∉
      {x : EuclideanSpace ℝ (Fin 3) | 0 < x (Fin.last 2)} := hn
  simp only [boundaryHolderZeroFunction, indicator_of_notMem hn', sub_zero]

lemma boundary_zeroGradient_eq_indicator {u : EuclideanSpace ℝ (Fin 3) → ℝ}
    {F : EuclideanSpace ℝ (Fin 3) → EuclideanSpace ℝ (Fin 3)}
    {x : EuclideanSpace ℝ (Fin 3)} (hx : x ∈ ball 0 (1 / 64 : ℝ)) :
    boundaryHolderZeroGradient u F x = (boundaryHalfBall 1).indicator F x := by
  by_cases hp : 0 < x (Fin.last 2)
  · rw [boundaryHolderZeroGradient_eq u F hx hp,
      indicator_of_mem (show x ∈ boundaryHalfBall 1 from
        ⟨ball_subset_ball (by norm_num) hx, hp⟩)]
  · have hn : x ∉ boundaryHalfBall 1 := fun hh => hp hh.2
    rw [boundaryHolderZeroGradient_eq_zero u F (le_of_not_gt hp), indicator_of_notMem hn]

/-- This weak-gradient conclusion is derived from the actual zero trace,
not supplied as an extension premise. -/
theorem HasH1GradientOn.boundary_odd_weak_gradient
    {u : EuclideanSpace ℝ (Fin 3) → ℝ}
    {F : EuclideanSpace ℝ (Fin 3) → EuclideanSpace ℝ (Fin 3)}
    (hu : HasH1GradientOn u F (boundaryHalfBall 1))
    (hT : HasZeroFlatTraceOn u F (ball 0 1)) :
    HasWeakGradientOn (boundaryOddFunction u) (boundaryOddField F)
      (ball 0 (1 / 64 : ℝ)) := by
  let R := coordinateReflection (Fin.last 2)
  let u₀ := boundaryHolderZeroFunction u
  let F₀ := boundaryHolderZeroGradient u F
  have hzero : HasH1GradientOn u₀ F₀ univ := hu.boundary_zero_extension_ball hT
  have hc := (hzero.comp_homeomorph R.toHomeomorph R.lipschitz R.symm.lipschitz).1
  change HasH1GradientOn (u₀ ∘ R)
    (fun x => (fderiv ℝ R x).adjoint (F₀ (R x))) univ at hc
  have hfder (x) : fderiv ℝ R x = R.toContinuousLinearEquiv.toContinuousLinearMap :=
    R.toContinuousLinearEquiv.fderiv
  have hadj : R.toContinuousLinearEquiv.toContinuousLinearMap.adjoint =
      R.toContinuousLinearEquiv.toContinuousLinearMap := boundary_reflection_adjoint
  have hc' : HasH1GradientOn (fun x => u₀ (R x)) (fun x => R (F₀ (R x))) univ := by
    simpa only [Function.comp_def, hfder, hadj, ContinuousLinearEquiv.coe_coe,
      LinearIsometryEquiv.coe_toContinuousLinearEquiv] using hc
  have hg := (hzero.sub hc').mono (subset_univ (ball (0 : EuclideanSpace ℝ (Fin 3)) (1 / 64)))
  apply hg.toHasWeakGradientOn.congr_ae EventuallyEq.rfl
  filter_upwards [ae_restrict_mem measurableSet_ball] with x hx
  have hRx : R x ∈ ball (0 : EuclideanSpace ℝ (Fin 3)) (1 / 64 : ℝ) := by
    simpa only [mem_ball, dist_zero_right, R.norm_map] using hx
  change F₀ x - R (F₀ (R x)) = boundaryOddField F x
  dsimp only [F₀]
  rw [boundary_zeroGradient_eq_indicator hx, boundary_zeroGradient_eq_indicator hRx]
  rfl

end LiquidDrop

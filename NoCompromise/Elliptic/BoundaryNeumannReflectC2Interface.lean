import NoCompromise.Elliptic.BoundaryNeumannTangential
import Mathlib.Analysis.Calculus.FDeriv.Extend

/-!
# C¹ gluing across the flat Neumann face

The derivative extension is specified as a continuous linear map. No ambient
regularity of the original function on the lower half ball is assumed.
-/

noncomputable section
open Filter Metric Set InnerProductSpace
open scoped Topology Gradient
namespace LiquidDrop

/-- Continuous derivatives on two convex open sets glue across their common
interface when the function and the proposed derivative are continuous on the
union of the closures. -/
theorem boundary_neumann_c1_glue
    {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [NormedAddCommGroup F] [NormedSpace ℝ F]
    {s t U : Set E} (hs : IsOpen s) (ht : IsOpen t)
    (hsc : Convex ℝ s) (htc : Convex ℝ t) (hU : IsOpen U)
    (hsub : U ⊆ closure s ∪ closure t)
    {f : E → F} {D : E → E →L[ℝ] F}
    (hf : ContinuousOn f (closure s ∪ closure t))
    (hD : ContinuousOn D (closure s ∪ closure t))
    (hd : ∀ x ∈ s ∪ t, HasFDerivAt f (D x) x) :
    ContDiffOn ℝ 1 f U ∧ ∀ x ∈ U, HasFDerivAt f (D x) x := by
  have hext (v : Set E) (hv : IsOpen v) (hvc : Convex ℝ v)
      (hvsub : v ⊆ s ∪ t) (hcsub : closure v ⊆ closure s ∪ closure t)
      (x : E) : HasFDerivWithinAt f (D x) (closure v) x := by
    by_cases hx : x ∈ closure v
    · apply hasFDerivWithinAt_closure_of_tendsto_fderiv
        (fun y hy => (hd y (hvsub hy)).differentiableAt.differentiableWithinAt) hvc hv
        (fun y hy => (hf y (hcsub hy)).mono (subset_closure.trans hcsub))
      apply ((hD x (hcsub hx)).mono (subset_closure.trans hcsub)).congr'
      filter_upwards [self_mem_nhdsWithin] with y hy
      exact (hd y (hvsub hy)).fderiv.symm
    · apply HasFDerivWithinAt.of_notMem_closure
      simpa only [closure_closure] using hx
  have hder (x : E) (hx : x ∈ U) : HasFDerivAt f (D x) x := by
    apply ((hext s hs hsc subset_union_left subset_union_left x).union
      (hext t ht htc subset_union_right subset_union_right x)).hasFDerivAt
    exact mem_of_superset (hU.mem_nhds hx) hsub
  refine ⟨?_, hder⟩
  change ContDiffOn ℝ (0 + 1) f U
  apply (contDiffOn_succ_iff_hasFDerivWithinAt_of_uniqueDiffOn hU.uniqueDiffOn).mpr
  exact ⟨by simp, D, (contDiffOn_zero).mpr (hD.mono hsub),
    fun x hx => (hder x hx).hasFDerivWithinAt⟩

/-- Interior points of the closed upper half space lie in the closure of the
open half ball; the radius is arbitrary. -/
lemma boundary_neumann_reflect_mem_closure {r : ℝ} {x : EuclideanSpace ℝ (Fin 3)}
    (hx : x ∈ ball 0 r) (hp : 0 ≤ x (Fin.last 2)) :
    x ∈ closure (boundaryHalfBall r) := by
  by_cases hh : 0 < x (Fin.last 2)
  · exact subset_closure ⟨hx, hh⟩
  have hz : x (Fin.last 2) = 0 := le_antisymm (le_of_not_gt hh) hp
  have hnorm : ‖x‖ < r := by simpa only [mem_ball, dist_zero_right] using hx
  rw [Metric.mem_closure_iff]
  intro ε hε
  let a := min (r - ‖x‖) ε / 2
  have ha : 0 < a := by dsimp [a]; positivity
  have har : a < r - ‖x‖ := by
    have := min_le_left (r - ‖x‖) ε
    dsimp [a]
    linarith
  have haε : a < ε := by
    have := min_le_right (r - ‖x‖) ε
    dsimp [a]
    linarith
  have hn : ‖EuclideanSpace.single (Fin.last 2) a‖ = a := by
    simp only [PiLp.norm_single, Real.norm_eq_abs, abs_of_pos ha]
  refine ⟨x + EuclideanSpace.single (Fin.last 2) a, ⟨?_, ?_⟩, ?_⟩
  · simp only [mem_ball, dist_zero_right]
    have := norm_add_le x (EuclideanSpace.single (Fin.last 2) a)
    rw [hn] at this
    linarith
  · change 0 < (x + EuclideanSpace.single (Fin.last 2) a) (Fin.last 2)
    simpa only [PiLp.add_apply, PiLp.single_apply, ite_true, hz, zero_add] using ha
  · simpa only [dist_self_add_right, hn] using haε

lemma boundary_neumann_reflect_closure_nonneg {r : ℝ}
    {x : EuclideanSpace ℝ (Fin 3)} (hx : x ∈ closure (boundaryHalfBall r)) :
    0 ≤ x (Fin.last 2) := by
  apply closure_minimal (s := boundaryHalfBall r)
    (t := {x : EuclideanSpace ℝ (Fin 3) | 0 ≤ x (Fin.last 2)})
    (fun y hy => (show 0 ≤ y (Fin.last 2) from le_of_lt hy.2)) _ hx
  exact isClosed_le continuous_const (EuclideanSpace.proj (Fin.last 2)).continuous

/-- A linear functional with zero normal component is unchanged by reflection
in the normal coordinate. This also holds for vector-valued linear maps. -/
lemma boundary_neumann_reflect_linear_eq {F : Type*}
    [NormedAddCommGroup F] [NormedSpace ℝ F]
    (L : EuclideanSpace ℝ (Fin 3) →L[ℝ] F)
    (hL : L (EuclideanSpace.single (Fin.last 2) 1) = 0) :
    L.comp (coordinateReflection (Fin.last 2)).toContinuousLinearEquiv.toContinuousLinearMap =
      L := by
  ext x
  have he : coordinateReflection (Fin.last 2) x =
      x - (2 * x (Fin.last 2)) • EuclideanSpace.single (Fin.last 2) 1 := by
    ext i
    by_cases hi : i = Fin.last 2
    · subst i
      simp [coordinateReflection_apply, PiLp.sub_apply, PiLp.smul_apply]
      ring
    · have hi2 : i ≠ (2 : Fin 3) := hi
      simp [coordinateReflection_apply, PiLp.sub_apply, PiLp.smul_apply, hi2]
  change L (coordinateReflection (Fin.last 2) x) = L x
  rw [he, map_sub, map_smul, hL, smul_zero, sub_zero]

/-- On the reflected closed half ball the branch on the face agrees with the
lower branch precisely when the prescribed boundary values are fixed by `T`. -/
lemma boundary_neumann_reflect_eq_lower {F : Type*} {r : ℝ}
    {f : EuclideanSpace ℝ (Fin 3) → F} {T : F → F}
    (hfix : ∀ x ∈ closure (boundaryHalfBall r), x (Fin.last 2) = 0 → T (f x) = f x)
    {x : EuclideanSpace ℝ (Fin 3)}
    (hx : coordinateReflection (Fin.last 2) x ∈ closure (boundaryHalfBall r)) :
    boundaryNeumannReflect f T x = T (f (coordinateReflection (Fin.last 2) x)) := by
  by_cases hp : 0 ≤ x (Fin.last 2)
  · have hn := boundary_neumann_reflect_closure_nonneg hx
    rw [boundary_reflection_last] at hn
    have hz : x (Fin.last 2) = 0 := by linarith
    have hr := boundary_neumann_reflection_fixed hz
    rw [hr] at hx ⊢
    simp only [boundaryNeumannReflect, ite_eq_left hp, hfix x hx hz]
  · simp only [boundaryNeumannReflect, ite_eq_right hp]

/-- Continuity of a reflected function on the two closed half balls, with the
specified matching condition on the flat face. -/
lemma boundary_neumann_reflect_continuous {F : Type*} [TopologicalSpace F] {r : ℝ}
    {f : EuclideanSpace ℝ (Fin 3) → F} {T : F → F}
    (hf : ContinuousOn f (closure (boundaryHalfBall r))) (hT : Continuous T)
    (hfix : ∀ x ∈ closure (boundaryHalfBall r), x (Fin.last 2) = 0 → T (f x) = f x) :
    ContinuousOn (boundaryNeumannReflect f T)
      (closure (boundaryHalfBall r) ∪
        coordinateReflection (Fin.last 2) ⁻¹' closure (boundaryHalfBall r)) := by
  have hu : ContinuousOn (boundaryNeumannReflect f T) (closure (boundaryHalfBall r)) :=
    hf.congr (fun x hx => by
      simp only [boundaryNeumannReflect, ite_eq_left (boundary_neumann_reflect_closure_nonneg hx)])
  have hl : ContinuousOn (boundaryNeumannReflect f T)
      (coordinateReflection (Fin.last 2) ⁻¹' closure (boundaryHalfBall r)) :=
    (hT.comp_continuousOn (hf.comp
      (coordinateReflection (Fin.last 2)).continuous.continuousOn (fun _ hx => hx))).congr
        (fun _ hx => boundary_neumann_reflect_eq_lower hfix hx)
  exact hu.union_of_isClosed hl isClosed_closure
    (isClosed_closure.preimage (coordinateReflection (Fin.last 2)).continuous)

/-- C¹ reflection with a linear action on the range. The value and derivative
matching hypotheses are imposed only on the flat face. This includes both even
and odd reflection. -/
theorem boundary_neumann_reflect_c1 {F : Type*}
    [NormedAddCommGroup F] [NormedSpace ℝ F] {r : ℝ}
    {f : EuclideanSpace ℝ (Fin 3) → F}
    {D : EuclideanSpace ℝ (Fin 3) → EuclideanSpace ℝ (Fin 3) →L[ℝ] F}
    (T : F →L[ℝ] F)
    (hf : ContinuousOn f (closure (boundaryHalfBall r)))
    (hD : ContinuousOn D (closure (boundaryHalfBall r)))
    (hd : ∀ x ∈ boundaryHalfBall r, HasFDerivAt f (D x) x)
    (hfix : ∀ x ∈ closure (boundaryHalfBall r), x (Fin.last 2) = 0 → T (f x) = f x)
    (hmatch : ∀ x ∈ closure (boundaryHalfBall r), x (Fin.last 2) = 0 →
      T.comp ((D x).comp
        (coordinateReflection (Fin.last 2)).toContinuousLinearEquiv.toContinuousLinearMap) = D x) :
    ContDiffOn ℝ 1 (boundaryNeumannReflect f T) (ball 0 r) ∧
    ∀ x ∈ ball 0 r, HasFDerivAt (boundaryNeumannReflect f T)
      (boundaryNeumannReflect D (fun L => T.comp (L.comp
        (coordinateReflection (Fin.last 2)).toContinuousLinearEquiv.toContinuousLinearMap)) x) x :=
    by
  let R := coordinateReflection (Fin.last 2)
  let S := R.toContinuousLinearEquiv.toContinuousLinearMap
  let V := R ⁻¹' boundaryHalfBall r
  let B := fun L : EuclideanSpace ℝ (Fin 3) →L[ℝ] F => T.comp (L.comp S)
  have hcl : closure V = R ⁻¹' closure (boundaryHalfBall r) :=
    (R.toHomeomorph.preimage_closure _).symm
  have hB : Continuous B := continuous_const.clm_comp
    (continuous_id.clm_comp continuous_const)
  have hc := boundary_neumann_reflect_continuous hf T.continuous hfix
  have hcD := boundary_neumann_reflect_continuous hD hB hmatch
  rw [← hcl] at hc hcD
  refine boundary_neumann_c1_glue (isOpen_boundaryHalfBall r)
    ((isOpen_boundaryHalfBall r).preimage R.continuous)
    (convex_boundaryHalfBall r) ((convex_boundaryHalfBall r).linear_preimage R.toLinearMap)
    isOpen_ball ?_ hc hcD ?_
  · intro x hx
    by_cases hp : 0 ≤ x (Fin.last 2)
    · exact Or.inl (boundary_neumann_reflect_mem_closure hx hp)
    · apply Or.inr
      rw [hcl]
      apply boundary_neumann_reflect_mem_closure
      · simpa only [mem_ball, dist_zero_right, R.norm_map] using hx
      · change 0 ≤ coordinateReflection (Fin.last 2) x (Fin.last 2)
        rw [boundary_reflection_last]
        exact neg_nonneg.mpr (le_of_not_ge hp)
  · intro x hx
    rcases hx with hx | hx
    · have hp : 0 ≤ x (Fin.last 2) := le_of_lt hx.2
      change HasFDerivAt (boundaryNeumannReflect f T) (boundaryNeumannReflect D B x) x
      rw [boundaryNeumannReflect, ite_eq_left hp]
      apply (hd x hx).congr_of_eventuallyEq
      filter_upwards [(isOpen_boundaryHalfBall r).mem_nhds hx] with y hy
      have hy0 : 0 ≤ y (Fin.last 2) := le_of_lt hy.2
      simp only [boundaryNeumannReflect, ite_eq_left hy0]
    · have hp : ¬ 0 ≤ x (Fin.last 2) := by
        have hy : 0 < R x (Fin.last 2) := hx.2
        change 0 < coordinateReflection (Fin.last 2) x (Fin.last 2) at hy
        rw [boundary_reflection_last] at hy
        linarith
      change HasFDerivAt (boundaryNeumannReflect f T) (boundaryNeumannReflect D B x) x
      rw [boundaryNeumannReflect, ite_eq_right hp]
      apply ((T.hasFDerivAt).comp x ((hd (R x) hx).comp x
        S.hasFDerivAt)).congr_of_eventuallyEq
      filter_upwards [((isOpen_boundaryHalfBall r).preimage R.continuous).mem_nhds hx] with y hy
      have hn : ¬ 0 ≤ y (Fin.last 2) := by
        have hz : 0 < R y (Fin.last 2) := hy.2
        change 0 < coordinateReflection (Fin.last 2) y (Fin.last 2) at hz
        rw [boundary_reflection_last] at hz
        linarith
      simp only [boundaryNeumannReflect, ite_eq_right hn]
      rfl

/-- Milestone 1: the even reflection is C¹ when the function and its derivative
extend continuously to the closed upper half ball and the extended normal
derivative is zero on its flat face. -/
theorem boundary_neumann_even_reflect_c1 {F : Type*}
    [NormedAddCommGroup F] [NormedSpace ℝ F] {r : ℝ}
    {f : EuclideanSpace ℝ (Fin 3) → F}
    {D : EuclideanSpace ℝ (Fin 3) → EuclideanSpace ℝ (Fin 3) →L[ℝ] F}
    (hf : ContinuousOn f (closure (boundaryHalfBall r)))
    (hD : ContinuousOn D (closure (boundaryHalfBall r)))
    (hd : ∀ x ∈ boundaryHalfBall r, HasFDerivAt f (D x) x)
    (hnormal : ∀ x ∈ closure (boundaryHalfBall r), x (Fin.last 2) = 0 →
      D x (EuclideanSpace.single (Fin.last 2) 1) = 0) :
    ContDiffOn ℝ 1 (fun x => f (coordinateFold (Fin.last 2) x)) (ball 0 r) ∧
    ∀ x ∈ ball 0 r, 0 ≤ x (Fin.last 2) →
      HasFDerivAt (fun y => f (coordinateFold (Fin.last 2) y)) (D x) x := by
  have he : boundaryNeumannReflect f (ContinuousLinearMap.id ℝ F) =
      fun x => f (coordinateFold (Fin.last 2) x) := by
    funext x
    by_cases hx : 0 ≤ x (Fin.last 2)
    · simp only [boundaryNeumannReflect, ite_eq_left hx, coordinateFold_eq_self hx]
    · simp only [boundaryNeumannReflect, ite_eq_right hx,
        coordinateFold_eq_reflection (le_of_not_ge hx), ContinuousLinearMap.id_apply]
  have hm (x) (hx : x ∈ closure (boundaryHalfBall r)) (hz : x (Fin.last 2) = 0) :
      (ContinuousLinearMap.id ℝ F).comp ((D x).comp
        (coordinateReflection (Fin.last 2)).toContinuousLinearEquiv.toContinuousLinearMap) = D x :=
      by
    rw [ContinuousLinearMap.id_comp]
    exact boundary_neumann_reflect_linear_eq _ (hnormal x hx hz)
  obtain ⟨hc, hder⟩ := boundary_neumann_reflect_c1 (ContinuousLinearMap.id ℝ F)
    hf hD hd (fun _ _ _ => rfl) hm
  rw [he] at hc hder
  refine ⟨hc, fun x hx hp => ?_⟩
  simpa only [boundaryNeumannReflect, ite_eq_left hp] using hder x hx

/-- The scalar version of milestone 1, stated with an independently prescribed
continuous extension of the gradient. -/
theorem boundary_neumann_even_reflect_c1_gradient {r : ℝ}
    {f : EuclideanSpace ℝ (Fin 3) → ℝ}
    {G : EuclideanSpace ℝ (Fin 3) → EuclideanSpace ℝ (Fin 3)}
    (hf : ContDiffOn ℝ 1 f (boundaryHalfBall r))
    (hc : ContinuousOn f (closure (boundaryHalfBall r)))
    (hG : ContinuousOn G (closure (boundaryHalfBall r)))
    (heq : EqOn G (gradient f) (boundaryHalfBall r))
    (hnormal : ∀ x ∈ closure (boundaryHalfBall r), x (Fin.last 2) = 0 →
      G x (Fin.last 2) = 0) :
    ContDiffOn ℝ 1 (fun x => f (coordinateFold (Fin.last 2) x)) (ball 0 r) ∧
    ∀ x ∈ ball 0 r, 0 ≤ x (Fin.last 2) →
      gradient (fun y => f (coordinateFold (Fin.last 2) y)) x = G x := by
  obtain ⟨hW, hder⟩ := boundary_neumann_even_reflect_c1 hc
    ((toDual ℝ (EuclideanSpace ℝ (Fin 3))).continuous.comp_continuousOn hG)
    (fun x hx => by
      dsimp only [Function.comp_apply]
      rw [heq hx, toDual_gradient]
      exact ((hf.contDiffAt ((isOpen_boundaryHalfBall r).mem_nhds hx)).differentiableAt
        one_ne_zero).hasFDerivAt)
    (fun x hx hz => by
      simpa only [Function.comp_apply, toDual_apply_apply, EuclideanSpace.inner_single_right,
        conj_trivial, one_mul] using hnormal x hx hz)
  refine ⟨hW, fun x hx hp => ?_⟩
  apply (toDual ℝ (EuclideanSpace ℝ (Fin 3))).injective
  rw [toDual_gradient, (hder x hx hp).fderiv]
  rfl

/-- Closed Neumann data already give a C¹ ambient representative by even
reflection, agreeing with both the function and its actual gradient on the
closed upper half ball inside the open unit ball. No ellipticity is needed. -/
theorem BoundaryNeumannClosedData.even_reflect_c1
    {α lam cap M N : ℝ} (hα : 0 < α)
    {A : EuclideanSpace ℝ (Fin 3) → EuclideanSpace ℝ (Fin 3) →L[ℝ]
      EuclideanSpace ℝ (Fin 3)}
    {H : EuclideanSpace ℝ (Fin 3) → EuclideanSpace ℝ (Fin 3)}
    {w : EuclideanSpace ℝ (Fin 3) → ℝ}
    (d : BoundaryNeumannClosedData α lam cap M N A H w) :
    ContDiffOn ℝ 1 (fun x => w (coordinateFold (Fin.last 2) x)) (ball 0 1) ∧
    ∀ x ∈ closure (boundaryHalfBall 1), x ∈ ball 0 1 →
      w (coordinateFold (Fin.last 2) x) = w x ∧
      gradient (fun y => w (coordinateFold (Fin.last 2) y)) x = gradient w x := by
  obtain ⟨hc, hG⟩ := boundary_neumann_even_reflect_c1_gradient
    (d.solution.contDiff.mono subset_closure) d.solution.contDiff.continuousOn
    (d.solution.gradient_holder.1.nondiv_continuousOn hα) (fun _ _ => rfl)
    d.solution_normal_zero
  refine ⟨hc, fun x hx hb => ?_⟩
  have hp := boundary_neumann_reflect_closure_nonneg hx
  exact ⟨by rw [coordinateFold_eq_self hp], hG x hb hp⟩

end LiquidDrop

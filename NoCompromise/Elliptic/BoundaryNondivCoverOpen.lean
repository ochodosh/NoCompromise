import NoCompromise.Elliptic.BoundaryNondivCover
import NoCompromise.Elliptic.BoundaryC2aReflection
import NoCompromise.Elliptic.BoundaryNondivHolder

/-!
# `thm:boundary-nondiv` on `B⁺_{1/2}` with C¹,α data on the open half ball

The TeX hypothesis `z ∈ C^{1,α}(closure B⁺_1)` is read literally: `z` is C¹,α on the open half
ball (where `fderiv` is the genuine derivative) and continuous on its closure. The three-term
reflection `boundaryReflectGlue` of `z` across the flat face is C¹ on the unit ball, agrees with
`z` on the closed half ball, and is C¹,α on `closure B⁺_1 ∩ B_1` with the same norm. The covering
argument of `BoundaryNondivCover.lean` only uses the solution on that set.
-/

noncomputable section
open MeasureTheory Filter Metric Set InnerProductSpace
open scoped ENNReal NNReal Topology Gradient RealInnerProductSpace
namespace LiquidDrop
set_option maxSynthPendingDepth 8

/-- Hölder bounds of a function continuous on the closure pass to the closure. -/
lemma boundary_nondiv_open_holder_closure {E F : Type*} [NormedAddCommGroup E]
    [NormedAddCommGroup F] {α : ℝ} (hα : 0 ≤ α) {g : E → F} {U : Set E}
    (hg : HasFiniteHolderNormOn α g U) (hc : ContinuousOn g (closure U)) :
    HasFiniteHolderNormOn α g (closure U) ∧ holderNorm α g (closure U) ≤ holderNorm α g U := by
  have h := boundary_c2a_holder_of_bounds (holderUniformNorm_nonneg hg.uniform_bounded)
    hg.seminorm_nonneg (U := closure U) (f := g) (α := α) ?_ ?_
  · exact ⟨h.1, h.2.trans_eq rfl⟩
  · intro x hx
    exact le_on_closure (f := fun x => ‖g x‖) (g := fun _ => holderUniformNorm g U)
      (fun y hy => norm_le_holderUniformNorm hg.uniform_bounded hy) hc.norm continuousOn_const hx
  · intro x hx y hy
    have := boundary_nondiv_holder_on_closure hα hc
      (fun x hx y hy => by rw [dist_eq_norm]; exact hg.nondiv_norm_sub_le hx hy) x hx y hy
    rwa [dist_eq_norm] at this

/-- The derivative of a C¹,α function on the open unit half ball extends continuously to the
closed half ball. -/
lemma boundary_nondiv_open_deriv_extension {α : ℝ} (hα : 0 < α)
    {z : EuclideanSpace ℝ (Fin 3) → ℝ} (hz : HasC1HolderOn α z (boundaryHalfBall 1)) :
    EqOn (extendFrom (boundaryHalfBall 1) (fderiv ℝ z)) (fderiv ℝ z) (boundaryHalfBall 1) ∧
      ContinuousOn (extendFrom (boundaryHalfBall 1) (fderiv ℝ z))
        (closure (boundaryHalfBall 1)) := by
  set S := boundaryHalfBall 1
  set H := holderSeminorm α (fderiv ℝ z) S
  have huc : UniformContinuousOn (fderiv ℝ z) S := by
    have ht : Tendsto (fun t : ℝ => H * t ^ α) (𝓝 0) (𝓝 0) := by
      have hc : Continuous (fun t : ℝ => H * t ^ α) :=
        continuous_const.mul (Real.continuous_rpow_const hα.le)
      simpa [Real.zero_rpow hα.ne'] using hc.tendsto 0
    refine Metric.uniformContinuousOn_iff.mpr fun ε hε => ?_
    obtain ⟨δ, hδ, hmod⟩ := Metric.tendsto_nhds_nhds.mp ht ε hε
    refine ⟨δ, hδ, fun x hx y hy hxy => ?_⟩
    rw [dist_eq_norm]
    have h1 := hz.derivative_holder.nondiv_norm_sub_le hx hy
    have h2 := @hmod ‖x - y‖
      (by rw [Real.dist_eq, sub_zero, abs_of_nonneg (norm_nonneg _), ← dist_eq_norm]; exact hxy)
    simp only [Real.dist_eq, sub_zero] at h2
    exact h1.trans_lt ((le_abs_self _).trans_lt h2)
  have hlim : ∀ x ∈ closure S, ∃ L, Tendsto (fderiv ℝ z) (𝓝[S] x) (𝓝 L) := by
    intro x hx
    have : NeBot (𝓝[S] x) := mem_closure_iff_nhdsWithin_neBot.mp hx
    exact cauchy_map_iff_exists_tendsto.mp
      ((cauchy_nhds.mono nhdsWithin_le_nhds).map_of_le huc inf_le_right)
  exact ⟨extendFrom_extends huc.continuousOn, continuousOn_extendFrom Subset.rfl hlim⟩

/-- Every point of the unit ball lies in a reflection slab contained in the unit ball. -/
lemma boundary_nondiv_open_slab {y : EuclideanSpace ℝ (Fin 3)}
    (hy : y ∈ ball (0 : EuclideanSpace ℝ (Fin 3)) 1) :
    ∃ a b : ℝ, y ∈ boundaryReflectSlab a b ∧
      boundaryReflectSlab a b ⊆ ball (0 : EuclideanSpace ℝ (Fin 3)) 1 := by
  rw [mem_ball_zero_iff] at hy
  have hy2 := norm_sq_graphProjectionN y
  set δ := (1 - ‖y‖ ^ 2) / 6 with hδ
  have hn := norm_nonneg y
  have hδ0 : 0 < δ := by rw [hδ]; nlinarith
  have hδ1 : δ ≤ 1 := by rw [hδ]; nlinarith
  set p := ‖graphProjectionN 2 y‖ with hp_def
  set q := |y (Fin.last 2)| with hq_def
  have hp0 : 0 ≤ p := norm_nonneg _
  have hq0 : 0 ≤ q := abs_nonneg _
  have hq2 : q ^ 2 = y (Fin.last 2) ^ 2 := sq_abs _
  have hpq : p ^ 2 + q ^ 2 = ‖y‖ ^ 2 := by rw [hq2, hy2]
  have hp1 : p ≤ 1 := by nlinarith
  have hq1 : q ≤ 1 := by nlinarith
  refine ⟨p + δ, q + δ, ⟨by linarith, by linarith⟩, ?_⟩
  rintro w ⟨hw1, hw2⟩
  rw [mem_ball_zero_iff]
  have hw := norm_sq_graphProjectionN w
  have hw0 := norm_nonneg (graphProjectionN 2 w)
  have hw3 := abs_nonneg (w (Fin.last 2))
  have e1 : ‖graphProjectionN 2 w‖ ^ 2 < (p + δ) ^ 2 := by nlinarith
  have e2 : w (Fin.last 2) ^ 2 < (q + δ) ^ 2 := by
    rw [← sq_abs]
    nlinarith
  have hsq : ‖w‖ ^ 2 < 1 := by
    nlinarith [mul_nonneg hδ0.le (sub_nonneg.mpr hp1), mul_nonneg hδ0.le (sub_nonneg.mpr hq1),
      mul_nonneg hδ0.le (sub_nonneg.mpr hδ1)]
  nlinarith [norm_nonneg w]

/-- The closed unit half ball lies in the closed upper half space. -/
lemma boundary_nondiv_open_closure_last_nonneg {y : EuclideanSpace ℝ (Fin 3)}
    (hy : y ∈ closure (boundaryHalfBall 1)) : 0 ≤ y (Fin.last 2) := by
  have hsub : closure (boundaryHalfBall 1) ⊆
      {y : EuclideanSpace ℝ (Fin 3) | 0 ≤ y (Fin.last 2)} :=
    closure_minimal (fun y hy => le_of_lt (show 0 < y (Fin.last 2) from hy.2))
      (isClosed_le continuous_const (EuclideanSpace.proj (Fin.last 2)).continuous)
  exact hsub hy

/-- A reflection slab inside the unit ball has its upper half inside the unit half ball. -/
lemma boundary_nondiv_open_closedUpper_subset {a b : ℝ}
    (hab : boundaryReflectSlab a b ⊆ ball (0 : EuclideanSpace ℝ (Fin 3)) 1) :
    boundaryReflectUpper a b ⊆ boundaryHalfBall 1 ∧
      boundaryReflectClosedUpper a b ⊆ closure (boundaryHalfBall 1) := by
  have hU : boundaryReflectUpper a b ⊆ boundaryHalfBall 1 := by
    intro y hy
    exact ⟨hab ⟨hy.1, abs_lt.mpr ⟨by linarith [hy.2.1, hy.2.2], hy.2.2⟩⟩, hy.2.1⟩
  exact ⟨hU, boundary_reflect_closedUpper_subset_closure.trans (closure_mono hU)⟩

/-- The C¹ reflection of `z` across the flat face: `z` on the closed upper half space and the
three-term reflection `6 z(y', -y₃) - 32 z(y', -y₃/2) + 27 z(y', -y₃/3)` below. -/
def boundaryNondivOpenReflect (z : EuclideanSpace ℝ (Fin 3) → ℝ) :
    EuclideanSpace ℝ (Fin 3) → ℝ :=
  boundaryReflectGlue boundaryReflectScalarOp z

/-- The derivative field of the reflection: the continuous extension of `fderiv z` to the closed
half ball, reflected. -/
def boundaryNondivOpenReflectDeriv (z : EuclideanSpace ℝ (Fin 3) → ℝ) :
    EuclideanSpace ℝ (Fin 3) → EuclideanSpace ℝ (Fin 3) →L[ℝ] ℝ :=
  boundaryReflectGlue (boundaryReflectDerivOp boundaryReflectScalarOp)
    (extendFrom (boundaryHalfBall 1) (fderiv ℝ z))

/-- The reflection is differentiable on the unit ball, with a continuous derivative field. -/
theorem boundary_nondiv_open_reflect_hasFDerivAt {α : ℝ} (hα : 0 < α)
    {z : EuclideanSpace ℝ (Fin 3) → ℝ} (hz : HasC1HolderOn α z (boundaryHalfBall 1))
    (hzc : ContinuousOn z (closure (boundaryHalfBall 1))) {y : EuclideanSpace ℝ (Fin 3)}
    (hy : y ∈ ball (0 : EuclideanSpace ℝ (Fin 3)) 1) :
    HasFDerivAt (boundaryNondivOpenReflect z) (boundaryNondivOpenReflectDeriv z y) y ∧
      ContinuousAt (boundaryNondivOpenReflectDeriv z) y := by
  obtain ⟨hTe, hTc⟩ := boundary_nondiv_open_deriv_extension hα hz
  obtain ⟨a, b, hya, hab⟩ := boundary_nondiv_open_slab hy
  obtain ⟨hU, hcU⟩ := boundary_nondiv_open_closedUpper_subset hab
  have hg : ∀ w ∈ boundaryReflectUpper a b,
      HasFDerivAt z (extendFrom (boundaryHalfBall 1) (fderiv ℝ z) w) w := by
    intro w hw
    rw [hTe (hU hw)]
    exact ((hz.contDiff.differentiableOn one_ne_zero w (hU hw)).differentiableAt
      ((isOpen_boundaryHalfBall 1).mem_nhds (hU hw))).hasFDerivAt
  have hTA : ∀ w ∈ boundaryReflectSlab a b, w (Fin.last 2) = 0 →
      ∑ k, boundaryReflectDerivOp boundaryReflectScalarOp k
        (extendFrom (boundaryHalfBall 1) (fderiv ℝ z) w) =
        extendFrom (boundaryHalfBall 1) (fderiv ℝ z) w :=
    fun w _ _ => boundary_reflect_derivOp_sum _
  exact ⟨boundary_reflect_glue_hasFDerivAt boundaryReflectScalarOp hg (hzc.mono hcU)
      (hTc.mono hcU) (fun w _ _ => boundary_reflect_scalarOp_sum (z w)) hTA y hya,
    (boundary_reflect_glue_continuousOn (boundaryReflectDerivOp boundaryReflectScalarOp)
      (hTc.mono hcU) hTA).continuousAt ((isOpen_boundaryReflectSlab a b).mem_nhds hya)⟩

/-- **C¹ extension across the flat face.** If `z` is C¹,α on the open unit half ball and
continuous on its closure, its reflection agrees with `z` on the closed half ball, is C¹ on the
unit ball, and is C¹,α on `closure B⁺_1 ∩ B_1` (with the ambient derivative) with norm at most the
C¹,α norm of `z` on the open half ball. -/
theorem boundary_nondiv_open_reflect_c1Holder {α : ℝ} (hα : 0 < α)
    {z : EuclideanSpace ℝ (Fin 3) → ℝ} (hz : HasC1HolderOn α z (boundaryHalfBall 1))
    (hzc : ContinuousOn z (closure (boundaryHalfBall 1))) :
    EqOn (boundaryNondivOpenReflect z) z (closure (boundaryHalfBall 1)) ∧
      (∀ y ∈ ball (0 : EuclideanSpace ℝ (Fin 3)) 1,
        DifferentiableAt ℝ (boundaryNondivOpenReflect z) y) ∧
      ContDiffOn ℝ 1 (boundaryNondivOpenReflect z) (ball 0 1) ∧
      HasC1HolderOn α (boundaryNondivOpenReflect z)
        (closure (boundaryHalfBall 1) ∩ ball 0 1) ∧
      nondivC1HolderNorm α (boundaryNondivOpenReflect z)
          (closure (boundaryHalfBall 1) ∩ ball 0 1) ≤
        nondivC1HolderNorm α z (boundaryHalfBall 1) := by
  obtain ⟨hTe, hTc⟩ := boundary_nondiv_open_deriv_extension hα hz
  set T := extendFrom (boundaryHalfBall 1) (fderiv ℝ z) with hT_def
  set S := closure (boundaryHalfBall 1) ∩ ball (0 : EuclideanSpace ℝ (Fin 3)) 1 with hS_def
  have hd := fun y (hy : y ∈ ball (0 : EuclideanSpace ℝ (Fin 3)) 1) =>
    boundary_nondiv_open_reflect_hasFDerivAt hα hz hzc hy
  have heq : EqOn (boundaryNondivOpenReflect z) z (closure (boundaryHalfBall 1)) := by
    intro y hy
    rw [boundaryNondivOpenReflect, boundaryReflectGlue,
      ite_eq_left (boundary_nondiv_open_closure_last_nonneg hy)]
  have hDeq : EqOn (boundaryNondivOpenReflectDeriv z) T (closure (boundaryHalfBall 1)) := by
    intro y hy
    rw [boundaryNondivOpenReflectDeriv, boundaryReflectGlue,
      ite_eq_left (boundary_nondiv_open_closure_last_nonneg hy)]
  have hfd : EqOn (fderiv ℝ (boundaryNondivOpenReflect z)) (boundaryNondivOpenReflectDeriv z)
      (ball 0 1) := fun y hy => (hd y hy).1.fderiv
  have hC1 : ContDiffOn ℝ 1 (boundaryNondivOpenReflect z) (ball 0 1) := by
    rw [show (1 : WithTop ℕ∞) = 0 + 1 from rfl, contDiffOn_succ_iff_fderiv_of_isOpen isOpen_ball]
    refine ⟨fun y hy => (hd y hy).1.differentiableAt.differentiableWithinAt, by simp, ?_⟩
    rw [contDiffOn_zero]
    exact (show ContinuousOn (boundaryNondivOpenReflectDeriv z) (ball 0 1) from
      fun y hy => (hd y hy).2.continuousWithinAt).congr hfd
  have hzcl := boundary_nondiv_open_holder_closure hα.le hz.function_holder hzc
  obtain ⟨hTB, hTBn⟩ := hz.derivative_holder.congr_eqOn hTe
  have hTcl := boundary_nondiv_open_holder_closure hα.le hTB hTc
  have hSc : S ⊆ closure (boundaryHalfBall 1) := inter_subset_left
  obtain ⟨hzS, hzSn⟩ := schauder_holder_mono hzcl.1 hSc
  obtain ⟨hTS, hTSn⟩ := schauder_holder_mono hTcl.1 hSc
  obtain ⟨h1, h1n⟩ := hzS.congr_eqOn (heq.mono hSc)
  have hfdS : EqOn (fderiv ℝ (boundaryNondivOpenReflect z)) T S :=
    fun y hy => (hfd hy.2).trans (hDeq hy.1)
  obtain ⟨h2, h2n⟩ := hTS.congr_eqOn hfdS
  refine ⟨heq, fun y hy => (hd y hy).1.differentiableAt, hC1,
    ⟨hC1.mono inter_subset_right, h1, h2⟩, ?_⟩
  unfold nondivC1HolderNorm
  rw [h1n, h2n]
  linarith [hzcl.2, hTcl.2]

/-- The distributional equation only sees the solution on the open set. -/
lemma boundary_nondiv_open_equation_congr {n : ℕ}
    {A : EuclideanSpace ℝ (Fin n) → EuclideanSpace ℝ (Fin n) →L[ℝ] EuclideanSpace ℝ (Fin n)}
    {b : EuclideanSpace ℝ (Fin n) → EuclideanSpace ℝ (Fin n)}
    {z w f : EuclideanSpace ℝ (Fin n) → ℝ} {U : Set (EuclideanSpace ℝ (Fin n))}
    (hU : IsOpen U) (hzw : EqOn z w U) (he : IsWeakNondivergenceEquationOn A b z f U) :
    IsWeakNondivergenceEquationOn A b w f U := by
  intro φ hφ hcφ hsφ
  have hg : ∀ x ∈ U, gradient w x = gradient z x := fun x hx => by
    simp only [gradient, (Filter.eventuallyEq_of_mem (hU.mem_nhds hx) hzw).fderiv_eq]
  have h1 : (fun x => inner ℝ (gradient w x)
        (nondivCoefficientDivergence (fun y => φ y • A y) x)) =
      fun x => inner ℝ (gradient z x) (nondivCoefficientDivergence (fun y => φ y • A y) x) := by
    funext x
    by_cases hx : x ∈ U
    · rw [hg x hx]
    · have hx' : x ∉ tsupport (fun y => φ y • A y) :=
        fun h => hx (hsφ (tsupport_smul_subset_left _ _ h))
      rw [nondivCoefficientDivergence_eq_zero_of_notMem_tsupport hx', inner_zero_right,
        inner_zero_right]
  have h2 : (fun x => φ x * inner ℝ (b x) (gradient w x)) =
      fun x => φ x * inner ℝ (b x) (gradient z x) := by
    funext x
    by_cases hx : x ∈ U
    · rw [hg x hx]
    · have : φ x = 0 := image_eq_zero_of_notMem_tsupport (fun h => hx (hsφ h))
      simp [this]
  change -(∫ x, inner ℝ (gradient w x)
        (nondivCoefficientDivergence (fun y => φ y • A y) x)) +
      (∫ x, φ x * inner ℝ (b x) (gradient w x)) = ∫ x, φ x * f x
  rw [h1, h2]
  exact he φ hφ hcφ hsφ

/-- The iterated coordinate derivatives only see the function near the point. -/
lemma boundary_nondiv_open_entry_congr {z w : EuclideanSpace ℝ (Fin 3) → ℝ}
    {U : Set (EuclideanSpace ℝ (Fin 3))} (hU : IsOpen U) (hzw : EqOn z w U)
    {x : EuclideanSpace ℝ (Fin 3)} (hx : x ∈ U) (i j : Fin 3) :
    boundaryNeumannC2Entry z x i j = boundaryNeumannC2Entry w x i j := by
  unfold boundaryNeumannC2Entry
  have hev : (fun y => fderiv ℝ z y (EuclideanSpace.single j 1)) =ᶠ[𝓝 x]
      fun y => fderiv ℝ w y (EuclideanSpace.single j 1) := by
    filter_upwards [hU.mem_nhds hx] with y hy
    rw [(Filter.eventuallyEq_of_mem (hU.mem_nhds hy) hzw).fderiv_eq]
  rw [hev.fderiv_eq]

/-- The boundary pieces of `boundary_nondiv_cover_boundary_piece`, with the solution required to
be C¹,α only on `closure B⁺_1 ∩ B_1`: rescaling by `y ↦ p + 2⁻²¹ • y` at a flat point `p`
with `‖p‖ ≤ 1/2`,
the slab estimate gives C² regularity with bounded, α-Hölder second derivatives on the image of
`boundaryNondivC2Slab`, with a constant fixed before the data. -/
theorem boundary_nondiv_open_boundary_piece {α lam cap M N P : ℝ}
    (hα : 0 < α) (hα1 : α < 1) (hlam : 0 < lam) (hlamcap : lam ≤ cap)
    (hM : 0 ≤ M) (hN : 0 ≤ N) (hP : 0 ≤ P) :
    ∃ K > 0, ∀ (A : EuclideanSpace ℝ (Fin 3) → EuclideanSpace ℝ (Fin 3) →L[ℝ]
        EuclideanSpace ℝ (Fin 3))
      (b : EuclideanSpace ℝ (Fin 3) → EuclideanSpace ℝ (Fin 3))
      (z f φ : EuclideanSpace ℝ (Fin 3) → ℝ) (V : Set (EuclideanSpace ℝ (Fin 3))),
      IsOpen V → closure (boundaryHalfBall 1) ⊆ V →
      HasC1HolderOn α A (closure (boundaryHalfBall 1)) →
      HasFiniteHolderNormOn α b (closure (boundaryHalfBall 1)) →
      HasC1HolderOn α z (closure (boundaryHalfBall 1) ∩ ball 0 1) →
      HasFiniteHolderNormOn α f (closure (boundaryHalfBall 1)) →
      nondivC1HolderNorm α A (closure (boundaryHalfBall 1)) ≤ M →
      holderNorm α b (closure (boundaryHalfBall 1)) ≤ M →
      (∀ x ∈ closure (boundaryHalfBall 1), ‖A x‖ ≤ cap) →
      (∀ x ∈ closure (boundaryHalfBall 1), ∀ v, lam * ‖v‖ ^ 2 ≤ inner ℝ v (A x v)) →
      IsWeakNondivergenceEquationOn A b z f (boundaryHalfBall 1) →
      (∀ x ∈ ball (0 : EuclideanSpace ℝ (Fin 3)) 1, x (Fin.last 2) = 0 →
        DifferentiableAt ℝ z x) →
      ContDiffOn ℝ 2 φ V →
      HasC1HolderOn α φ (closure (boundaryHalfBall 1)) →
      HasFiniteHolderNormOn α (nondivClassicalOperator A b φ) (closure (boundaryHalfBall 1)) →
      (∀ x ∈ closure (boundaryHalfBall 1), x (Fin.last 2) = 0 → z x = φ x) →
      nondivC1HolderNorm α z (closure (boundaryHalfBall 1) ∩ ball 0 1) +
          nondivC1HolderNorm α φ (closure (boundaryHalfBall 1)) +
          holderNorm α f (closure (boundaryHalfBall 1)) +
          holderNorm α (nondivClassicalOperator A b φ) (closure (boundaryHalfBall 1)) ≤ N →
      (∀ i j : Fin 3, (∀ x ∈ boundaryHalfBall 1, |boundaryNeumannC2Entry φ x i j| ≤ P) ∧
        ∀ x ∈ boundaryHalfBall 1, ∀ y ∈ boundaryHalfBall 1,
          |boundaryNeumannC2Entry φ x i j - boundaryNeumannC2Entry φ y i j| ≤
            P * dist x y ^ α) →
      ∀ p : EuclideanSpace ℝ (Fin 3), p (Fin.last 2) = 0 → ‖p‖ ≤ 1 / 2 →
        ContDiffOn ℝ 2 z (frozenBallScaling p boundary_c2a_local_radius_pos ''
          boundaryNondivC2Slab) ∧
        ∀ i j : Fin 3,
          (∀ x ∈ frozenBallScaling p boundary_c2a_local_radius_pos '' boundaryNondivC2Slab,
            |boundaryNeumannC2Entry z x i j| ≤ K) ∧
          ∀ x ∈ frozenBallScaling p boundary_c2a_local_radius_pos '' boundaryNondivC2Slab,
          ∀ y ∈ frozenBallScaling p boundary_c2a_local_radius_pos '' boundaryNondivC2Slab,
            |boundaryNeumannC2Entry z x i j - boundaryNeumannC2Entry z y i j| ≤
              K * dist x y ^ α := by
  obtain ⟨C, hC, hreg⟩ := boundary_nondiv_c2_holder_trace hα hα1 hlam hlamcap hM hN
  set r : ℝ := 1 / 2097152 with hr_def
  have hr0 : 0 < r := boundary_c2a_local_radius_pos
  have hr1 : r ≤ 1 := by norm_num [hr_def]
  have hri : 1 ≤ r⁻¹ := by norm_num [hr_def]
  refine ⟨r⁻¹ ^ 2 * (C + P) * r⁻¹ ^ α, by positivity, ?_⟩
  intro A b z f φ V hV hKV hA hb hz hf hAn hbn hcap hell he hzd hφ2 hφ hL htrace hNb hPφ
    p hp3 hp
  set e := frozenBallScaling p boundary_c2a_local_radius_pos
  set U := closure (boundaryHalfBall 1)
  have hmU : MapsTo e U U := fun y hy => (boundary_c2a_scaling_maps_slab hp3 hp hy).2
  have hmB : MapsTo e (boundaryHalfBall 1) (boundaryHalfBall 1) :=
    boundary_c2a_scaling_maps_halfBall hp3 hp
  have hsub : U ⊆ closedBall (0 : EuclideanSpace ℝ (Fin 3)) 1 ∩
      {y | 0 ≤ y (Fin.last 2)} := by
    apply closure_minimal
    · exact fun y hy => ⟨ball_subset_closedBall hy.1,
        show 0 ≤ y (Fin.last 2) from le_of_lt (show 0 < y (Fin.last 2) from hy.2)⟩
    · exact isClosed_closedBall.inter
        (isClosed_le continuous_const (EuclideanSpace.proj (Fin.last 2)).continuous)
  have hnorm : ∀ x ∈ U, ‖e x‖ < 1 := by
    intro x hx
    have hx1 : ‖x‖ ≤ 1 := mem_closedBall_zero_iff.mp (hsub hx).1
    rw [frozenBallScaling_apply]
    calc ‖p + (1 / 2097152 : ℝ) • x‖ ≤ ‖p‖ + ‖(1 / 2097152 : ℝ) • x‖ := norm_add_le _ _
      _ = ‖p‖ + 1 / 2097152 * ‖x‖ := by rw [norm_smul, Real.norm_of_nonneg (by norm_num)]
      _ < 1 := by nlinarith [norm_nonneg x]
  have hmT : MapsTo e U (U ∩ ball 0 1) :=
    fun y hy => ⟨hmU hy, mem_ball_zero_iff.mpr (hnorm y hy)⟩
  have hBT : boundaryHalfBall 1 ⊆ U ∩ ball 0 1 := fun y hy => ⟨subset_closure hy, hy.1⟩
  have hd : ∀ x ∈ U, ∀ y ∈ U, ‖e x - e y‖ ≤ ‖x - y‖ := by
    intro x _ y _
    have heq : ‖e x - e y‖ = r * ‖x - y‖ := by
      simpa only [dist_eq_norm] using quasilinear_ballScaling_dist p x y hr0
    rw [heq]
    exact (mul_le_mul_of_nonneg_right hr1 (norm_nonneg _)).trans_eq (one_mul _)
  have hec : ContDiff ℝ 2 e := contDiff_const.add (contDiff_id.const_smul r)
  have hr2 : r ^ 2 ≤ 1 := by norm_num [hr_def]
  -- rescaled data
  obtain ⟨hAe, hAeN⟩ := boundary_c2a_c1Holder_comp_scaling hα.le p hr0 hr1 hA hmU
  obtain ⟨hze, hzeN⟩ := boundary_c2a_c1Holder_comp_scaling hα.le p hr0 hr1 hz hmT
  obtain ⟨hφe, hφeN⟩ := boundary_c2a_c1Holder_comp_scaling hα.le p hr0 hr1 hφ hmU
  obtain ⟨hbc, hbcN⟩ := nondiv_holder_comp_contraction hα.le hb hmU hd
  obtain ⟨hbs, hbsN⟩ := nondiv_holder_const_smul hbc r
  obtain ⟨hfc, hfcN⟩ := nondiv_holder_comp_contraction hα.le hf hmU hd
  obtain ⟨hfs, hfsN⟩ := nondiv_holder_const_smul hfc (r ^ 2)
  obtain ⟨hLc, hLcN⟩ := nondiv_holder_comp_contraction hα.le hL hmU hd
  obtain ⟨hLs, hLsN⟩ := nondiv_holder_const_smul hLc (r ^ 2)
  rw [Real.norm_of_nonneg hr0.le] at hbsN
  rw [Real.norm_of_nonneg (sq_nonneg r)] at hfsN hLsN
  have hLeq : nondivClassicalOperator (A ∘ e) (fun x => r • b (e x)) (φ ∘ e) =
      fun x => r ^ 2 • (nondivClassicalOperator A b φ ∘ e) x := by
    funext y
    rw [boundary_nondiv_cover_classical_comp p hr0 A b φ y, smul_eq_mul]
    rfl
  have hfeq : (fun x => r ^ 2 * f (e x)) = fun x => r ^ 2 • (f ∘ e) x := rfl
  have hbeq : (fun x => r • b (e x)) = fun x => r • (b ∘ e) x := rfl
  have hweak := boundary_nondiv_cover_weak_rescale p hr0 (isOpen_boundaryHalfBall 1)
    (isOpen_boundaryHalfBall 1) hmB (hA.contDiff.mono subset_closure)
    ((hb.nondiv_continuousOn hα).mono subset_closure) (hz.contDiff.mono hBT)
    ((hf.nondiv_continuousOn hα).mono subset_closure) he
  have hzd' : ∀ x ∈ U, DifferentiableAt ℝ z (e x) := by
    intro x hx
    have h3 : 0 ≤ (e x) (Fin.last 2) := (hsub (hmU hx)).2
    rcases h3.eq_or_lt with h | h
    · exact hzd _ (mem_ball_zero_iff.mpr (hnorm x hx)) h.symm
    · have hin : e x ∈ boundaryHalfBall 1 := ⟨mem_ball_zero_iff.mpr (hnorm x hx), h⟩
      exact (hz.contDiff.contDiffAt (mem_of_superset
        ((isOpen_boundaryHalfBall 1).mem_nhds hin) hBT)).differentiableAt one_ne_zero
  have hnφ := hφ.norm_nonneg
  have hnz := hz.norm_nonneg
  have hnf := hf.norm_nonneg
  have hnL := hL.norm_nonneg
  have hnb := hb.norm_nonneg
  have hnfc := hfc.norm_nonneg
  have hnLc := hLc.norm_nonneg
  have hnbc := hbc.norm_nonneg
  obtain ⟨hC2, hbd⟩ := hreg (A ∘ e) (fun x => r • b (e x)) (z ∘ e) (fun x => r ^ 2 * f (e x))
    (φ ∘ e) (e ⁻¹' V) P (hV.preimage e.continuous) (fun y hy => hKV (hmU hy)) hAe
    (by rw [hbeq]; exact hbs) hze (by rw [hfeq]; exact hfs) (hAeN.trans hAn)
    (by
      rw [hbeq]
      refine hbsN.trans ?_
      calc r * holderNorm α (b ∘ e) U ≤ 1 * holderNorm α b U := mul_le_mul hr1 hbcN hnbc zero_le_one
        _ = holderNorm α b U := one_mul _
        _ ≤ M := hbn)
    (fun x hx => hcap _ (hmU hx)) (fun x hx v => hell _ (hmU hx) v) hweak
    (fun x hx => (hzd' x hx).comp x ((hec.differentiable (by norm_num)) x))
    (hφ2.comp hec.contDiffOn (mapsTo_preimage _ _)) hφe (by rw [hLeq]; exact hLs)
    (by
      intro x hx hx3
      apply htrace _ (hmU hx)
      change (p + r • x) (Fin.last 2) = 0
      rw [PiLp.add_apply, PiLp.smul_apply, smul_eq_mul, hp3, hx3, mul_zero, add_zero])
    (by
      rw [hfeq, hLeq]
      have h3 : holderNorm α (fun x => r ^ 2 • (f ∘ e) x) U ≤ holderNorm α f U :=
        hfsN.trans ((mul_le_mul hr2 hfcN hnfc zero_le_one).trans_eq (one_mul _))
      have h4 : holderNorm α (fun x => r ^ 2 • (nondivClassicalOperator A b φ ∘ e) x) U ≤
          holderNorm α (nondivClassicalOperator A b φ) U :=
        hLsN.trans ((mul_le_mul hr2 hLcN hnLc zero_le_one).trans_eq (one_mul _))
      linarith)
    (by
      intro i j
      refine ⟨fun x hx => ?_, fun x hx y hy => ?_⟩
      · have hex := hmB (boundaryNondivC2Slab_subset hx)
        rw [boundary_nondiv_cover_entry_comp, abs_mul, abs_of_nonneg (sq_nonneg r)]
        exact (mul_le_mul hr2 ((hPφ i j).1 _ hex) (abs_nonneg _) zero_le_one).trans_eq
          (one_mul _)
      · have hex := hmB (boundaryNondivC2Slab_subset hx)
        have hey := hmB (boundaryNondivC2Slab_subset hy)
        rw [boundary_nondiv_cover_entry_comp, boundary_nondiv_cover_entry_comp, ← mul_sub,
          abs_mul, abs_of_nonneg (sq_nonneg r)]
        have hdist : dist (e x) (e y) ^ α ≤ dist x y ^ α := by
          apply Real.rpow_le_rpow dist_nonneg _ hα.le
          rw [quasilinear_ballScaling_dist p x y hr0]
          exact (mul_le_mul_of_nonneg_right hr1 dist_nonneg).trans_eq (one_mul _)
        calc r ^ 2 * |boundaryNeumannC2Entry φ (e x) i j - boundaryNeumannC2Entry φ (e y) i j|
            ≤ 1 * (P * dist (e x) (e y) ^ α) :=
              mul_le_mul hr2 ((hPφ i j).2 _ hex _ hey) (abs_nonneg _) zero_le_one
          _ ≤ P * dist x y ^ α := by
              rw [one_mul]
              exact mul_le_mul_of_nonneg_left hdist hP)
  -- scale back
  have hzw : z = (z ∘ e) ∘ e.symm := by
    funext x
    simp only [Function.comp_apply, Homeomorph.apply_symm_apply]
  refine ⟨?_, fun i j => ⟨?_, ?_⟩⟩
  · rw [hzw]
    exact boundary_c2a_contDiffOn_comp_scaling_symm p boundary_c2a_local_radius_pos hC2
  · rintro _ ⟨x, hx, rfl⟩
    rw [hzw, boundary_c2a_entry_comp_scaling, abs_mul, abs_of_nonneg (by positivity)]
    have h1 : 1 ≤ r⁻¹ ^ α := Real.one_le_rpow hri hα.le
    calc r⁻¹ ^ 2 * |boundaryNeumannC2Entry (z ∘ e) x i j| ≤ r⁻¹ ^ 2 * (C + P) :=
          mul_le_mul_of_nonneg_left ((hbd i j).1 x hx) (by positivity)
      _ ≤ r⁻¹ ^ 2 * (C + P) * r⁻¹ ^ α := le_mul_of_one_le_right (by positivity) h1
  · rintro _ ⟨x, hx, rfl⟩ _ ⟨y, hy, rfl⟩
    rw [hzw, boundary_c2a_entry_comp_scaling, boundary_c2a_entry_comp_scaling, ← mul_sub,
      abs_mul, abs_of_nonneg (by positivity)]
    have hd' : dist x y = r⁻¹ * dist (e x) (e y) := by
      rw [quasilinear_ballScaling_dist p x y hr0, ← mul_assoc, inv_mul_cancel₀ hr0.ne', one_mul]
    have hdp : dist x y ^ α = r⁻¹ ^ α * dist (e x) (e y) ^ α := by
      rw [hd', Real.mul_rpow (by positivity) dist_nonneg]
    calc r⁻¹ ^ 2 * |boundaryNeumannC2Entry (z ∘ e) x i j - boundaryNeumannC2Entry (z ∘ e) y i j|
        ≤ r⁻¹ ^ 2 * ((C + P) * dist x y ^ α) :=
          mul_le_mul_of_nonneg_left ((hbd i j).2 x hx y hy) (by positivity)
      _ = r⁻¹ ^ 2 * (C + P) * r⁻¹ ^ α * dist (e x) (e y) ^ α := by rw [hdp]; ring

/-- `boundary_nondiv_half_ball_of_face` with the solution required to be C¹,α only on
`closure B⁺_1 ∩ B_1`. `thm:boundary-nondiv` on `B⁺_{1/2}`, with ambient differentiability of
`z` required only on
the open flat face `Γ₁`: under the hypotheses of the slab estimate, with the Hessian bounds of
the boundary datum on the unit half ball, the solution is C² on the open half ball `B⁺_{1/2}`
with uniformly bounded, uniformly α-Hölder second derivatives. -/
theorem boundary_nondiv_open_half_ball_of_face {α lam cap M N P : ℝ}
    (hα : 0 < α) (hα1 : α < 1) (hlam : 0 < lam) (hlamcap : lam ≤ cap)
    (hM : 0 ≤ M) (hN : 0 ≤ N) (hP : 0 ≤ P) :
    ∃ C > 0, ∀ (A : EuclideanSpace ℝ (Fin 3) → EuclideanSpace ℝ (Fin 3) →L[ℝ]
        EuclideanSpace ℝ (Fin 3))
      (b : EuclideanSpace ℝ (Fin 3) → EuclideanSpace ℝ (Fin 3))
      (z f φ : EuclideanSpace ℝ (Fin 3) → ℝ) (V : Set (EuclideanSpace ℝ (Fin 3))),
      IsOpen V → closure (boundaryHalfBall 1) ⊆ V →
      HasC1HolderOn α A (closure (boundaryHalfBall 1)) →
      HasFiniteHolderNormOn α b (closure (boundaryHalfBall 1)) →
      HasC1HolderOn α z (closure (boundaryHalfBall 1) ∩ ball 0 1) →
      HasFiniteHolderNormOn α f (closure (boundaryHalfBall 1)) →
      nondivC1HolderNorm α A (closure (boundaryHalfBall 1)) ≤ M →
      holderNorm α b (closure (boundaryHalfBall 1)) ≤ M →
      (∀ x ∈ closure (boundaryHalfBall 1), ‖A x‖ ≤ cap) →
      (∀ x ∈ closure (boundaryHalfBall 1), ∀ v, lam * ‖v‖ ^ 2 ≤ inner ℝ v (A x v)) →
      IsWeakNondivergenceEquationOn A b z f (boundaryHalfBall 1) →
      (∀ x ∈ ball (0 : EuclideanSpace ℝ (Fin 3)) 1, x (Fin.last 2) = 0 →
        DifferentiableAt ℝ z x) →
      ContDiffOn ℝ 2 φ V →
      HasC1HolderOn α φ (closure (boundaryHalfBall 1)) →
      HasFiniteHolderNormOn α (nondivClassicalOperator A b φ) (closure (boundaryHalfBall 1)) →
      (∀ x ∈ closure (boundaryHalfBall 1), x (Fin.last 2) = 0 → z x = φ x) →
      nondivC1HolderNorm α z (closure (boundaryHalfBall 1) ∩ ball 0 1) +
          nondivC1HolderNorm α φ (closure (boundaryHalfBall 1)) +
          holderNorm α f (closure (boundaryHalfBall 1)) +
          holderNorm α (nondivClassicalOperator A b φ) (closure (boundaryHalfBall 1)) ≤ N →
      (∀ i j : Fin 3, (∀ x ∈ boundaryHalfBall 1, |boundaryNeumannC2Entry φ x i j| ≤ P) ∧
        ∀ x ∈ boundaryHalfBall 1, ∀ y ∈ boundaryHalfBall 1,
          |boundaryNeumannC2Entry φ x i j - boundaryNeumannC2Entry φ y i j| ≤
            P * dist x y ^ α) →
      ContDiffOn ℝ 2 z (boundaryHalfBall (1 / 2)) ∧
      ∀ i j : Fin 3,
        (∀ x ∈ boundaryHalfBall (1 / 2), |boundaryNeumannC2Entry z x i j| ≤ C) ∧
        ∀ x ∈ boundaryHalfBall (1 / 2), ∀ y ∈ boundaryHalfBall (1 / 2),
          |boundaryNeumannC2Entry z x i j - boundaryNeumannC2Entry z y i j| ≤
            C * dist x y ^ α := by
  obtain ⟨Kb, hKb, hbd⟩ :=
    boundary_nondiv_open_boundary_piece hα hα1 hlam hlamcap hM hN hP
  obtain ⟨Ci, hCi, hint⟩ :=
    nondiv_schauder_c1_ball (n := 3) (by norm_num) (by norm_num) hα hα1 hlam hlamcap hM
  set δ : ℝ := 3 / 8796093022208 with hδ_def
  set s : ℝ := δ / 2 with hs_def
  set ρ : ℝ := δ / 4 with hρ_def
  have hδ : 0 < δ := by norm_num [hδ_def]
  have hs0 : 0 < s := by positivity
  have hs1 : s ≤ 1 := by norm_num [hs_def, hδ_def]
  have hρ : 0 < ρ := by positivity
  set K : ℝ := Kb + Ci * s⁻¹ ^ 3 * N with hK_def
  have hK : 0 < K := by positivity
  have hs2 : s < 1 / 2 := by norm_num [hs_def, hδ_def]
  have hρs : ρ = s / 2 := by rw [hρ_def, hs_def]; ring
  have hsδ : s = δ / 2 := hs_def
  have hρδ : ρ = δ / 4 := hρ_def
  have hKN : 0 ≤ Ci * s⁻¹ ^ 3 * N := by positivity
  clear_value K ρ s δ
  refine ⟨max K (2 * K * (ρ ^ α)⁻¹), lt_max_of_lt_left hK, ?_⟩
  intro A b z f φ V hV hKV hA hb hz hf hAn hbn hcap hell he hzd hφ2 hφ hL htrace hNb hPφ
  set U := closure (boundaryHalfBall 1)
  have hzf : nondivC1HolderNorm α z (U ∩ ball 0 1) + holderNorm α f U ≤ N := by
    have := hφ.norm_nonneg
    have := hL.norm_nonneg
    linarith
  have hbdz := hbd A b z f φ V hV hKV hA hb hz hf hAn hbn hcap hell he hzd hφ2 hφ hL htrace
    hNb hPφ
  have hloc : ∀ x ∈ boundaryHalfBall (1 / 2), ∃ O : Set (EuclideanSpace ℝ (Fin 3)),
      IsOpen O ∧ x ∈ O ∧ (∀ y ∈ boundaryHalfBall (1 / 2), dist x y < ρ → y ∈ O) ∧
      ContDiffOn ℝ 2 z O ∧ ∀ i j : Fin 3,
        (∀ w ∈ O, |boundaryNeumannC2Entry z w i j| ≤ K) ∧
        ∀ w ∈ O, ∀ w' ∈ O,
          |boundaryNeumannC2Entry z w i j - boundaryNeumannC2Entry z w' i j| ≤
            K * dist w w' ^ α := by
    intro x hx
    obtain ⟨hx1, hx3⟩ := hx
    rw [mem_ball_zero_iff] at hx1
    change 0 < x (Fin.last 2) at hx3
    by_cases hxs : x (Fin.last 2) < s
    · -- boundary piece at the foot point
      set p : EuclideanSpace ℝ (Fin 3) :=
        x - x (Fin.last 2) • EuclideanSpace.single (Fin.last 2) 1 with hp_def
      have hp3 : p (Fin.last 2) = 0 := by simp [hp_def]
      have hxp : ‖x - p‖ = x (Fin.last 2) := by
        rw [hp_def, sub_sub_cancel, norm_smul, PiLp.norm_single, norm_one, mul_one,
          Real.norm_of_nonneg hx3.le]
      have hpx : ‖p‖ ^ 2 + x (Fin.last 2) ^ 2 = ‖x‖ ^ 2 := by
        rw [EuclideanSpace.real_norm_sq_eq, EuclideanSpace.real_norm_sq_eq,
          Fin.sum_univ_three, Fin.sum_univ_three]
        simp [hp_def]
      have hp : ‖p‖ ≤ 1 / 2 := by
        nlinarith [norm_nonneg x, norm_nonneg p]
      obtain ⟨h2, hent⟩ := hbdz p hp3 hp
      refine ⟨_, (frozenBallScaling p boundary_c2a_local_radius_pos).isOpenMap _
        isOpen_boundaryNondivC2Slab, ?_, ?_, h2, fun i j => ⟨fun w hw => ?_,
          fun w hw w' hw' => ?_⟩⟩
      · exact boundary_nondiv_cover_slab_mem hp3 (by rw [hxp, ← hδ_def]; linarith) hx3
      · intro y hy hxy
        obtain ⟨-, hy3⟩ := hy
        apply boundary_nondiv_cover_slab_mem hp3 _ hy3
        rw [← hδ_def]
        calc ‖y - p‖ ≤ ‖y - x‖ + ‖x - p‖ := norm_sub_le_norm_sub_add_norm_sub y x p
          _ < ρ + s := by
              rw [hxp, ← dist_eq_norm, dist_comm]
              linarith
          _ < δ := by linarith
      · exact ((hent i j).1 w hw).trans (by linarith)
      · exact ((hent i j).2 w hw w' hw').trans (mul_le_mul_of_nonneg_right
          (by linarith) (Real.rpow_nonneg dist_nonneg _))
    · -- interior ball
      have hball : ball x s ⊆ boundaryHalfBall 1 := by
        intro w hw
        rw [mem_ball, dist_eq_norm] at hw
        refine ⟨?_, ?_⟩
        · rw [mem_ball_zero_iff]
          calc ‖w‖ ≤ ‖w - x‖ + ‖x‖ := norm_le_norm_sub_add w x
            _ < 1 := by linarith
        · change 0 < w (Fin.last 2)
          have h3 : |(w - x) (Fin.last 2)| ≤ ‖w - x‖ := by
            simpa only [Real.norm_eq_abs] using PiLp.norm_apply_le (w - x) (Fin.last 2)
          rw [PiLp.sub_apply] at h3
          have := (abs_le.mp h3).1
          linarith
      have hbU : ball x s ⊆ U := hball.trans subset_closure
      have hbT : ball x s ⊆ U ∩ ball 0 1 := fun w hw => ⟨subset_closure (hball hw), (hball hw).1⟩
      obtain ⟨hAs, hAsN⟩ := hA.mono hbU
      obtain ⟨hzs, hzsN⟩ := hz.mono hbT
      obtain ⟨hbs, hbsN⟩ := schauder_holder_mono hb hbU
      obtain ⟨hfs, hfsN⟩ := schauder_holder_mono hf hbU
      obtain ⟨hC2, hC2N⟩ := hint x s hs0 hs1 A b z f hAs hbs hzs hfs (hAsN.trans hAn)
        (hbsN.trans hbn) (fun w hw => hcap w (hbU hw)) (fun w hw v => hell w (hbU hw) v)
        (he.mono hball)
      have hB : schauderC2HolderNorm α z (ball x (s / 2)) ≤ K := by
        refine hC2N.trans ?_
        have : Ci * s⁻¹ ^ 3 * (nondivC1HolderNorm α z (ball x s) + holderNorm α f (ball x s)) ≤
            Ci * s⁻¹ ^ 3 * N :=
          mul_le_mul_of_nonneg_left (by linarith) (by positivity)
        linarith
      refine ⟨ball x (s / 2), isOpen_ball, mem_ball_self (by positivity), ?_, hC2.contDiff,
        fun i j => boundary_nondiv_cover_entry_of_c2Holder isOpen_ball hC2 hB i j⟩
      intro y _ hxy
      rw [mem_ball, dist_comm]
      linarith
  choose! O hOo hxO hOρ hO2 hOb using hloc
  refine ⟨fun x hx => ((hO2 x hx).contDiffAt ((hOo x hx).mem_nhds (hxO x hx))).contDiffWithinAt,
    fun i j => ⟨fun x hx => ((hOb x hx i j).1 x (hxO x hx)).trans (le_max_left _ _), ?_⟩⟩
  apply boundary_nondiv_cover_holder_of_local (g := fun x => boundaryNeumannC2Entry z x i j)
    hα.le hK.le hρ (fun x hx => (hOb x hx i j).1 x (hxO x hx))
  intro x hx y hy hxy
  exact (hOb x hx i j).2 x (hxO x hx) y (hOρ x hx y hy hxy)

/-- **`thm:boundary-nondiv` on `B⁺_{1/2}`, with `z ∈ C^{1,α}(closure B⁺_1)` read literally**:
`z` is C¹,α on the open half ball `B⁺_1` (genuine derivative) and continuous on its closure; no
differentiability of `z` at the flat face is assumed. Under the remaining hypotheses of
`boundary_nondiv_half_ball`, the solution is C² on `B⁺_{1/2}` with uniformly bounded, uniformly
α-Hölder second derivatives. -/
theorem boundary_nondiv_half_ball_open {α lam cap M N P : ℝ}
    (hα : 0 < α) (hα1 : α < 1) (hlam : 0 < lam) (hlamcap : lam ≤ cap)
    (hM : 0 ≤ M) (hN : 0 ≤ N) (hP : 0 ≤ P) :
    ∃ C > 0, ∀ (A : EuclideanSpace ℝ (Fin 3) → EuclideanSpace ℝ (Fin 3) →L[ℝ]
        EuclideanSpace ℝ (Fin 3))
      (b : EuclideanSpace ℝ (Fin 3) → EuclideanSpace ℝ (Fin 3))
      (z f φ : EuclideanSpace ℝ (Fin 3) → ℝ) (V : Set (EuclideanSpace ℝ (Fin 3))),
      IsOpen V → closure (boundaryHalfBall 1) ⊆ V →
      HasC1HolderOn α A (closure (boundaryHalfBall 1)) →
      HasFiniteHolderNormOn α b (closure (boundaryHalfBall 1)) →
      HasC1HolderOn α z (boundaryHalfBall 1) →
      ContinuousOn z (closure (boundaryHalfBall 1)) →
      HasFiniteHolderNormOn α f (closure (boundaryHalfBall 1)) →
      nondivC1HolderNorm α A (closure (boundaryHalfBall 1)) ≤ M →
      holderNorm α b (closure (boundaryHalfBall 1)) ≤ M →
      (∀ x ∈ closure (boundaryHalfBall 1), ‖A x‖ ≤ cap) →
      (∀ x ∈ closure (boundaryHalfBall 1), ∀ v, lam * ‖v‖ ^ 2 ≤ inner ℝ v (A x v)) →
      IsWeakNondivergenceEquationOn A b z f (boundaryHalfBall 1) →
      ContDiffOn ℝ 2 φ V →
      HasC1HolderOn α φ (closure (boundaryHalfBall 1)) →
      HasFiniteHolderNormOn α (nondivClassicalOperator A b φ) (closure (boundaryHalfBall 1)) →
      (∀ x ∈ closure (boundaryHalfBall 1), x (Fin.last 2) = 0 → z x = φ x) →
      nondivC1HolderNorm α z (boundaryHalfBall 1) +
          nondivC1HolderNorm α φ (closure (boundaryHalfBall 1)) +
          holderNorm α f (closure (boundaryHalfBall 1)) +
          holderNorm α (nondivClassicalOperator A b φ) (closure (boundaryHalfBall 1)) ≤ N →
      (∀ i j : Fin 3, (∀ x ∈ boundaryHalfBall 1, |boundaryNeumannC2Entry φ x i j| ≤ P) ∧
        ∀ x ∈ boundaryHalfBall 1, ∀ y ∈ boundaryHalfBall 1,
          |boundaryNeumannC2Entry φ x i j - boundaryNeumannC2Entry φ y i j| ≤
            P * dist x y ^ α) →
      ContDiffOn ℝ 2 z (boundaryHalfBall (1 / 2)) ∧
      ∀ i j : Fin 3,
        (∀ x ∈ boundaryHalfBall (1 / 2), |boundaryNeumannC2Entry z x i j| ≤ C) ∧
        ∀ x ∈ boundaryHalfBall (1 / 2), ∀ y ∈ boundaryHalfBall (1 / 2),
          |boundaryNeumannC2Entry z x i j - boundaryNeumannC2Entry z y i j| ≤
            C * dist x y ^ α := by
  obtain ⟨C, hC, hreg⟩ := boundary_nondiv_open_half_ball_of_face hα hα1 hlam hlamcap hM hN hP
  refine ⟨C, hC, ?_⟩
  intro A b z f φ V hV hKV hA hb hz hzc hf hAn hbn hcap hell he hφ2 hφ hL htrace hNb hPφ
  obtain ⟨heq, hzd, -, hzt, hztN⟩ := boundary_nondiv_open_reflect_c1Holder hα hz hzc
  set zt := boundaryNondivOpenReflect z with hzt_def
  have hB : EqOn z zt (boundaryHalfBall 1) := fun x hx => (heq (subset_closure hx)).symm
  have he' := boundary_nondiv_open_equation_congr (isOpen_boundaryHalfBall 1) hB he
  obtain ⟨h2, hent⟩ := hreg A b zt f φ V hV hKV hA hb hzt hf hAn hbn hcap hell he'
    (fun x hx _ => hzd x hx) hφ2 hφ hL (fun x hx hx3 => (heq hx).trans (htrace x hx hx3))
    (by linarith) hPφ
  have hsub : boundaryHalfBall (1 / 2) ⊆ boundaryHalfBall 1 :=
    boundaryHalfBall_mono (by norm_num)
  have hE : ∀ x ∈ boundaryHalfBall (1 / 2), ∀ i j : Fin 3,
      boundaryNeumannC2Entry z x i j = boundaryNeumannC2Entry zt x i j :=
    fun x hx i j => boundary_nondiv_open_entry_congr (isOpen_boundaryHalfBall 1) hB (hsub hx) i j
  refine ⟨h2.congr fun x hx => hB (hsub hx), fun i j => ⟨fun x hx => ?_, fun x hx y hy => ?_⟩⟩
  · rw [hE x hx]
    exact (hent i j).1 x hx
  · rw [hE x hx, hE y hy]
    exact (hent i j).2 x hx y hy

end LiquidDrop

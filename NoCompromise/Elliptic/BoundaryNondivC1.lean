module

public import NoCompromise.Elliptic.BoundaryNondivHolder
public import NoCompromise.Elliptic.BoundaryC1

@[expose] public section

/-!
# Boundary C¹,α estimates for tangential quotients

The up-to-the-face assumptions and the bound on the original data are recorded
explicitly. The estimate constants are uniform in the tangential direction and
nonzero signed step. The unit coordinates below represent the original half ball
of radius 3/4; the resulting representative meets its closed flat disk of radius
3/8. Reconstruction of second derivatives is not asserted in this file.
-/

noncomputable section
open MeasureTheory Filter Metric Set InnerProductSpace
open scoped ENNReal Topology Gradient RealInnerProductSpace
namespace LiquidDrop

/-- Original nondivergence data up to the flat face, with an explicit upper bound
`N` for `‖z‖_{C¹,α} + ‖f‖_{C⁰,α}`. Derivatives and norms use the existing
`HasC1HolderOn` convention on the closed half ball. -/
structure BoundaryNondivClosedData (α lam cap M N : ℝ)
    (A : EuclideanSpace ℝ (Fin 3) →
      EuclideanSpace ℝ (Fin 3) →L[ℝ] EuclideanSpace ℝ (Fin 3))
    (b : EuclideanSpace ℝ (Fin 3) → EuclideanSpace ℝ (Fin 3))
    (z f : EuclideanSpace ℝ (Fin 3) → ℝ) : Prop where
  coefficient : HasC1HolderOn α A (closure (boundaryHalfBall 1))
  drift : HasFiniteHolderNormOn α b (closure (boundaryHalfBall 1))
  solution : HasC1HolderOn α z (closure (boundaryHalfBall 1))
  source : HasFiniteHolderNormOn α f (closure (boundaryHalfBall 1))
  coefficient_norm : nondivC1HolderNorm α A (closure (boundaryHalfBall 1)) ≤ M
  drift_norm : holderNorm α b (closure (boundaryHalfBall 1)) ≤ M
  coefficient_bound : ∀ x ∈ closure (boundaryHalfBall 1), ‖A x‖ ≤ cap
  elliptic : ∀ x ∈ closure (boundaryHalfBall 1), ∀ v,
    lam * ‖v‖ ^ 2 ≤ inner ℝ v (A x v)
  equation : IsWeakNondivergenceEquationOn A b z f (boundaryHalfBall 1)
  trace_zero : ∀ x ∈ closure (boundaryHalfBall 1), x (Fin.last 2) = 0 → z x = 0
  norm_bound : nondivC1HolderNorm α z (closure (boundaryHalfBall 1)) +
    holderNorm α f (closure (boundaryHalfBall 1)) ≤ N

/-- All hypotheses of the boundary C¹,α theorem are proved for the actual
rescaled tangential quotient; the energy constant precedes the data and step. -/
theorem boundary_nondiv_quotient_unit_data {α lam cap M N : ℝ}
    (hα : 0 < α) (hlam : 0 < lam) (hlamcap : lam ≤ cap)
    (hM : 0 ≤ M) (hN : 0 ≤ N) :
    ∃ E ≥ 0, ∀ (A : EuclideanSpace ℝ (Fin 3) →
        EuclideanSpace ℝ (Fin 3) →L[ℝ] EuclideanSpace ℝ (Fin 3))
      (b : EuclideanSpace ℝ (Fin 3) → EuclideanSpace ℝ (Fin 3))
      (z f : EuclideanSpace ℝ (Fin 3) → ℝ),
      BoundaryNondivClosedData α lam cap M N A b z f →
      ∀ (i : Fin 3) (h : ℝ), i ≠ Fin.last 2 → h ≠ 0 → |h| < 1 / 16 →
      BoundaryHolderUnitData α lam cap M ((1 + 15 * M) * N) E
        (fun x => coordinateDifferenceQuotient i h z ((3 / 4 : ℝ) • x))
        (fun x => (3 / 4 : ℝ) • coordinateDifferenceQuotient i h (gradient z) ((3 / 4 : ℝ) • x))
        (fun x => (3 / 4 : ℝ) • nondivQuotientDatum A b z f i h ((3 / 4 : ℝ) • x))
        (fun x => A ((3 / 4 : ℝ) • x + h • EuclideanSpace.single i 1)) := by
  obtain ⟨C₀, hC₀, hbound⟩ := boundary_nondiv_quotient_h1_bound hα hlam hlamcap hM
  refine ⟨(4 / 3) * (C₀ * N) ^ 2, by positivity, ?_⟩
  intro A b z f d i h hi hh hsmall
  let e := frozenBallScaling (0 : EuclideanSpace ℝ (Fin 3)) (by norm_num : (0 : ℝ) < 3 / 4)
  let q := coordinateDifferenceQuotient i h z
  let D := coordinateDifferenceQuotient i h (gradient z)
  let G := nondivQuotientDatum A b z f i h
  let a := fun x => A (x + h • EuclideanSpace.single i 1)
  have heapply (x) : e x = (3 / 4 : ℝ) • x := by simp only [e, frozenBallScaling_apply, zero_add]
  obtain ⟨hA, hbA⟩ := d.coefficient.mono subset_closure
  obtain ⟨hb, hbb⟩ := schauder_holder_mono d.drift subset_closure
  obtain ⟨hz, hbz⟩ := d.solution.mono subset_closure
  obtain ⟨hf, hbf⟩ := schauder_holder_mono d.source subset_closure
  have hseg : ∀ x ∈ boundaryHalfBall (3 / 4), ∀ t ∈ Icc (0 : ℝ) 1,
      x + t • (h • EuclideanSpace.single i 1) ∈ boundaryHalfBall 1 :=
    fun _ hx _ ht => boundary_nondiv_segment_mem_halfBall hi (by linarith) hx ht
  obtain ⟨hq, heq⟩ := nondiv_quotient_equation hα (isOpen_boundaryHalfBall 1)
    (isOpen_boundaryHalfBall (3 / 4)) (isBounded_ball.subset inter_subset_left)
    (isBounded_ball.subset inter_subset_left) hA hb hz hf d.equation i hh hseg
  have hnorm := (hbound A b z f hA hb hz hf (hbA.trans d.coefficient_norm)
    (hbb.trans d.drift_norm) (fun x hx => d.coefficient_bound x (subset_closure hx))
    (fun x hx => d.elliptic x (subset_closure hx)) d.equation
    d.solution.contDiff.continuousOn d.trace_zero i h hi hh hsmall).2
  have hDN : lpNorm D 2 (volume.restrict (boundaryHalfBall (3 / 4))) ≤ C₀ * N := by
    apply (le_add_of_nonneg_left lpNorm_nonneg).trans (hnorm.trans _)
    exact mul_le_mul_of_nonneg_left ((add_le_add hbz hbf).trans d.norm_bound) hC₀.le
  have hscale : MapsTo e (boundaryHalfBall 1) (boundaryHalfBall (3 / 4)) := by
    intro x hx
    simpa only [mul_one] using
      (boundary_halfBall_scaling_mem (by norm_num : (0 : ℝ) < 3 / 4) x 1).mpr hx
  have hscaleC := hscale.closure e.continuous
  have hmap0 : MapsTo e (closure (boundaryHalfBall 1)) (closure (boundaryHalfBall 1)) :=
    fun _ hx => (closure_mono (boundaryHalfBall_mono (by norm_num : (3 / 4 : ℝ) ≤ 1))) (hscaleC hx)
  have hmap1 : MapsTo (fun x => e x + h • EuclideanSpace.single i 1)
      (closure (boundaryHalfBall 1)) (closure (boundaryHalfBall 1)) := by
    intro x hx
    simpa only [one_smul] using boundary_nondiv_closed_segment hi
      (by linarith : |h| ≤ 1 - 3 / 4) (hscaleC hx) (t := 1) (by simp)
  have hG : ContinuousOn G (closure (boundaryHalfBall (3 / 4))) :=
    boundary_nondiv_quotientDatum_continuous hα d.coefficient d.drift d.solution d.source hi
      (by linarith)
  have hGh := boundary_nondiv_quotientDatum_holder_closed hα hM
    d.coefficient d.drift d.solution d.source d.coefficient_norm d.drift_norm hi hh
    (by linarith : |h| ≤ 1 - 3 / 4)
  have hGbound : ∀ x ∈ closure (boundaryHalfBall (3 / 4)),
      ∀ y ∈ closure (boundaryHalfBall (3 / 4)),
      ‖G x - G y‖ ≤ ((1 + 15 * M) * N) * dist x y ^ α := by
    intro x hx y hy
    exact (hGh x hx y hy).trans (mul_le_mul_of_nonneg_right
      (mul_le_mul_of_nonneg_left d.norm_bound (by positivity)) (Real.rpow_nonneg dist_nonneg _))
  have hdist (x y : EuclideanSpace ℝ (Fin 3)) : dist (e x) (e y) ≤ dist x y := by
    rw [quasilinear_ballScaling_dist]
    nlinarith [dist_nonneg (x := x) (y := y)]
  have hqc : ContinuousOn (q ∘ e) (closure (boundaryHalfBall 1)) :=
    ((d.solution.contDiff.continuousOn.comp
      (e.continuous.add continuous_const).continuousOn hmap1).sub
      (d.solution.contDiff.continuousOn.comp e.continuous.continuousOn hmap0)).const_smul h⁻¹
  have hqflat : ∀ x ∈ closure (boundaryHalfBall 1), x (Fin.last 2) = 0 → (q ∘ e) x = 0 := by
    intro x hx hflat
    have heflat : (e x) (Fin.last 2) = 0 := by
      rw [heapply]
      change (3 / 4 : ℝ) * x (Fin.last 2) = 0
      rw [hflat, mul_zero]
    have hshift : (e x + h • EuclideanSpace.single i (1 : ℝ)) (Fin.last 2) = 0 := by
      have hne : Fin.last 2 ≠ i := Ne.symm hi
      simp only [PiLp.add_apply, PiLp.smul_apply, PiLp.single_apply, hne, ite_false,
        smul_zero, add_zero, heflat]
    simp only [Function.comp_def, q, coordinateDifferenceQuotient,
      d.trace_zero _ (hmap1 hx) hshift, d.trace_zero _ (hmap0 hx) heflat, sub_self, smul_zero]
  have hscaled := (hq.comp_homeomorph_on (isOpen_boundaryHalfBall 1)
    (isOpen_boundaryHalfBall (3 / 4)) e
    (quasilinear_ballScaling_lipschitz 0 (by norm_num : (0 : ℝ) < 3 / 4))
    (quasilinear_ballScaling_symm_lipschitz 0 (by norm_num : (0 : ℝ) < 3 / 4)) hscale).1
  have hd (x) : (fderiv ℝ e x).adjoint = (3 / 4 : ℝ) • ContinuousLinearMap.id ℝ _ := by
    rw [frozenBallScaling_fderiv]
    simp only [map_smul, ContinuousLinearMap.adjoint_id]
  have hH : HasH1GradientOn (q ∘ e) (fun x => (3 / 4 : ℝ) • D (e x)) (boundaryHalfBall 1) := by
    simpa only [hd, smul_apply, ContinuousLinearMap.id_apply] using hscaled
  have heqscaled := heq.boundary_comp_scaling (by norm_num : (0 : ℝ) < 3 / 4)
  have hdata : BoundaryHolderUnitData α lam cap M ((1 + 15 * M) * N)
      ((4 / 3) * (C₀ * N) ^ 2) (q ∘ e) (fun x => (3 / 4 : ℝ) • D (e x))
      (fun x => (3 / 4 : ℝ) • G (e x)) (a ∘ e) := by
    refine ⟨?_, ?_, ?_, ?_, ?_, ?_, hH, hH.boundary_nondiv_zero_trace hqc hqflat,
      heqscaled, ?_⟩
    · exact d.coefficient.contDiff.continuousOn.comp
        (e.continuous.add continuous_const).continuousOn hmap1
    · exact (hG.comp e.continuous.continuousOn hscaleC).const_smul (3 / 4 : ℝ)
    · intro x hx
      exact d.coefficient_bound _ (hmap1 hx)
    · intro x hx ξ
      rw [real_inner_comm]
      exact d.elliptic _ (hmap1 hx) ξ
    · intro x hx y hy
      have ht := d.coefficient.function_holder.nondiv_norm_sub_le (hmap1 hx) (hmap1 hy)
      rw [add_sub_add_right_eq_sub] at ht
      simp only [← dist_eq_norm] at ht ⊢
      apply ht.trans
      exact mul_le_mul ((le_add_of_nonneg_left
        (holderUniformNorm_nonneg d.coefficient.function_holder.uniform_bounded)).trans
          (d.coefficient.function_norm_le.trans d.coefficient_norm))
        (Real.rpow_le_rpow dist_nonneg (hdist x y) hα.le)
        (Real.rpow_nonneg dist_nonneg _) hM
    · intro x hx y hy
      rw [← smul_sub, norm_smul]
      have hn : ‖(3 / 4 : ℝ)‖ ≤ 1 := by norm_num
      have ht := (mul_le_mul_of_nonneg_right hn (norm_nonneg (G (e x) - G (e y))))
      simp only [one_mul] at ht
      exact ht.trans ((hGbound _ (hscaleC hx) _ (hscaleC hy)).trans
        (mul_le_mul_of_nonneg_left (Real.rpow_le_rpow dist_nonneg (hdist x y) hα.le)
          (by positivity)))
    · rw [boundary_integral_energy_scaling D (by norm_num : (0 : ℝ) < 3 / 4) 1]
      norm_num
      rw [← lpNorm_two_sq_eq_integral_norm_sq hq.memLp_gradient]
      exact pow_le_pow_left₀ lpNorm_nonneg hDN 2
  simpa only [Function.comp_def, a, q, D, G, heapply] using hdata

/-- Uniform boundary C¹,α representatives of all small tangential quotients.
`C` and `P` depend on `α`, ellipticity, `M`, and the explicit data-size bound `N`,
and are fixed before the coefficient fields, solution, source, direction and step.
The coordinates are rescaled by 3/4, so the flat disk covered in the original
coordinates has radius 3/8. -/
theorem boundary_nondiv_quotient_boundary_c1 {α lam cap M N : ℝ}
    (hα : 0 < α) (hα1 : α < 1) (hlam : 0 < lam) (hlamcap : lam ≤ cap)
    (hM : 0 ≤ M) (hN : 0 ≤ N) :
    ∃ C P : ℝ, 0 < C ∧ 0 ≤ P ∧
      ∀ (A : EuclideanSpace ℝ (Fin 3) →
          EuclideanSpace ℝ (Fin 3) →L[ℝ] EuclideanSpace ℝ (Fin 3))
        (b : EuclideanSpace ℝ (Fin 3) → EuclideanSpace ℝ (Fin 3))
        (z f : EuclideanSpace ℝ (Fin 3) → ℝ),
        BoundaryNondivClosedData α lam cap M N A b z f →
        ∀ (i : Fin 3) (h : ℝ), i ≠ Fin.last 2 → h ≠ 0 → |h| < 1 / 16 →
        ∃ (W : Set (EuclideanSpace ℝ (Fin 3))) (v : EuclideanSpace ℝ (Fin 3) → ℝ),
          IsOpen W ∧ {x | ‖x‖ ≤ (1 / 2 : ℝ) ∧ x (Fin.last 2) = 0} ⊆ W ∧
          W ⊆ ball 0 (3 / 4 : ℝ) ∧ ContDiffOn ℝ 1 v W ∧
          v =ᵐ[volume.restrict (W ∩ {x | 0 < x (Fin.last 2)})]
            (fun x => coordinateDifferenceQuotient i h z ((3 / 4 : ℝ) • x)) ∧
          gradient v =ᵐ[volume.restrict (W ∩ {x | 0 < x (Fin.last 2)})]
            (fun x => (3 / 4 : ℝ) •
              coordinateDifferenceQuotient i h (gradient z) ((3 / 4 : ℝ) • x)) ∧
          (∀ x ∈ W, ‖gradient v x‖ ≤ P) ∧
          (∀ x ∈ W, ∀ y ∈ W, ‖gradient v x - gradient v y‖ ≤ C * dist x y ^ α) ∧
          ∀ x ∈ W, x (Fin.last 2) = 0 → v x = 0 := by
  obtain ⟨E, hE, hdata⟩ := boundary_nondiv_quotient_unit_data hα hlam hlamcap hM hN
  obtain ⟨C, P, hC, hP, hboundary⟩ := boundary_c1_holder hα hα1 hlam (hlam.le.trans hlamcap)
    hM (show 0 ≤ (1 + 15 * M) * N by positivity) hE
  refine ⟨C, P, hC, hP, ?_⟩
  intro A b z f hd i h hi hh hsmall
  exact hboundary _ _ _ _ (hdata A b z f hd i h hi hh hsmall)

end LiquidDrop

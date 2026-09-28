import NoCompromise.Elliptic.BoundaryNeumannClosedScaling
import NoCompromise.Elliptic.BoundaryNeumannC2

/-!
# The homogeneous conormal C²,α theorem at every scale

`boundary_neumann_c2_holder` is stated on the unit half ball. Composing with the scaling
`x ↦ r x` (`boundary_neumann_closed_data_of_scaling`) gives the same conclusion for closed data
on the closed half ball of radius `r ∈ (0, 1]`, on the half ball of radius `r · 3/8`, with the
second-derivative bounds multiplied by the exact scaling factors.
-/

noncomputable section
open MeasureTheory Filter Metric Set InnerProductSpace
open scoped ENNReal NNReal Topology Gradient RealInnerProductSpace
namespace LiquidDrop

lemma boundary_neumann_c2Entry_comp_scaling {r : ℝ} (hr : 0 < r)
    (w : EuclideanSpace ℝ (Fin 3) → ℝ) (y : EuclideanSpace ℝ (Fin 3)) (i j : Fin 3) :
    boundaryNeumannC2Entry (w ∘ frozenBallScaling 0 hr) y i j =
      r ^ 2 * boundaryNeumannC2Entry w (frozenBallScaling 0 hr y) i j := by
  unfold boundaryNeumannC2Entry
  let g : EuclideanSpace ℝ (Fin 3) → ℝ := fun z => fderiv ℝ w z (EuclideanSpace.single j 1)
  have h1 : (fun y => fderiv ℝ (w ∘ frozenBallScaling 0 hr) y (EuclideanSpace.single j 1)) =
      r • (g ∘ frozenBallScaling 0 hr) := by
    funext y
    rw [boundary_neumann_fderiv_comp_scaling hr w y]
    simp [g]
  rw [h1, fderiv_const_smul_field, Pi.smul_apply, boundary_neumann_fderiv_comp_scaling hr g y,
    smul_smul]
  simp only [g, ← pow_two]
  rfl

lemma boundary_neumann_scaling_symm_mapsTo_halfBall {r : ℝ} (hr : 0 < r) (s : ℝ) :
    MapsTo (frozenBallScaling (0 : EuclideanSpace ℝ (Fin 3)) hr).symm
      (boundaryHalfBall (r * s)) (boundaryHalfBall s) := by
  intro x hx
  have hx' : frozenBallScaling 0 hr ((frozenBallScaling (0 : EuclideanSpace ℝ (Fin 3)) hr).symm x)
      ∈ ball 0 (r * s) := by
    rw [Homeomorph.apply_symm_apply]
    exact hx.1
  refine ⟨(frozenBallScaling_mem_ball_iff 0 _ hr s).mp hx', ?_⟩
  change 0 < ((frozenBallScaling (0 : EuclideanSpace ℝ (Fin 3)) hr).symm x) (Fin.last 2)
  rw [frozenBallScaling_symm_apply]
  simp only [sub_zero, PiLp.smul_apply, smul_eq_mul]
  exact mul_pos (inv_pos.mpr hr) hx.2

/-- The C²,α conclusion of `boundary_neumann_c2_holder` for closed data on the closed half ball
of radius `r ∈ (0, 1]`: C² on the half ball of radius `r · 3/8`, and each second derivative has a
continuous extension to the closure bounded by `C / r²`, with the exact rescaled Hölder bound.
The constant precedes the radius and all data. -/
theorem boundary_neumann_c2_holder_scaled {α lam cap M N : ℝ}
    (hα : 0 < α) (hα1 : α < 1) (hlam : 0 < lam) (hcap : 0 ≤ cap)
    (hM : 0 ≤ M) (hN : 0 ≤ N) :
    ∃ C > 0, ∀ {r : ℝ}, 0 < r → r ≤ 1 →
      ∀ (A : EuclideanSpace ℝ (Fin 3) → EuclideanSpace ℝ (Fin 3) →L[ℝ]
          EuclideanSpace ℝ (Fin 3))
        (H : EuclideanSpace ℝ (Fin 3) → EuclideanSpace ℝ (Fin 3))
        (w : EuclideanSpace ℝ (Fin 3) → ℝ),
      HasC1HolderOn α A (closure (boundaryHalfBall r)) →
      HasC1HolderOn α H (closure (boundaryHalfBall r)) →
      HasC1HolderOn α w (closure (boundaryHalfBall r)) →
      nondivC1HolderNorm α A (closure (boundaryHalfBall r)) ≤ M →
      nondivC1HolderNorm α w (closure (boundaryHalfBall r)) +
        nondivC1HolderNorm α H (closure (boundaryHalfBall r)) ≤ N →
      (∀ x ∈ closure (boundaryHalfBall r), ‖A x‖ ≤ cap) →
      (∀ x ∈ closure (boundaryHalfBall r), ∀ v, lam * ‖v‖ ^ 2 ≤ inner ℝ (A x v) v) →
      (∀ x ∈ closure (boundaryHalfBall r), x (Fin.last 2) = 0 →
        ∀ j : Fin 3, j ≠ Fin.last 2 →
          A x (EuclideanSpace.single j 1) (Fin.last 2) = 0 ∧
          A x (EuclideanSpace.single (Fin.last 2) 1) j = 0) →
      (∀ x ∈ closure (boundaryHalfBall r), x (Fin.last 2) = 0 → H x (Fin.last 2) = 0) →
      (∀ x ∈ closure (boundaryHalfBall r), x (Fin.last 2) = 0 →
        gradient w x (Fin.last 2) = 0) →
      IsBoundaryNeumannEquationOn A (gradient w) H r →
      ContDiffOn ℝ 2 w (boundaryHalfBall (r * (3 / 8))) ∧
      ∀ i j : Fin 3, ∃ D : EuclideanSpace ℝ (Fin 3) → ℝ,
        EqOn D (fun x => boundaryNeumannC2Entry w x i j) (boundaryHalfBall (r * (3 / 8))) ∧
        ContinuousOn D (closure (boundaryHalfBall (r * (3 / 8)))) ∧
        (∀ x ∈ closure (boundaryHalfBall (r * (3 / 8))), |D x| ≤ (r ^ 2)⁻¹ * C) ∧
        ∀ x ∈ closure (boundaryHalfBall (r * (3 / 8))),
          ∀ y ∈ closure (boundaryHalfBall (r * (3 / 8))),
            |D x - D y| ≤ (r ^ 2)⁻¹ * (C * (r⁻¹ * dist x y) ^ α) := by
  obtain ⟨C, hC, hc2⟩ := boundary_neumann_c2_holder hα hα1 hlam hcap hM hN
  refine ⟨C, hC, ?_⟩
  intro r hr hr1 A H w hA hH hw hAM hNb hcapb hell hcross hH0 hw0 heq
  have d := boundary_neumann_closed_data_of_scaling hα.le hr hr1 hA hH hw hAM hNb hcapb hell
    hcross hH0 hw0 heq
  obtain ⟨hW, hent⟩ := hc2 _ _ _ d
  let e := frozenBallScaling (0 : EuclideanSpace ℝ (Fin 3)) hr
  have hm := boundary_neumann_scaling_symm_mapsTo_halfBall hr (3 / 8)
  have hmc : MapsTo e.symm (closure (boundaryHalfBall (r * (3 / 8))))
      (closure (boundaryHalfBall (3 / 8))) := hm.closure e.symm.continuous
  have hes : ContDiff ℝ 2 e.symm := by
    change ContDiff ℝ 2 (frozenBallScaling 0 hr).symm
    rw [frozenBallScaling_symm_coe]
    exact (contDiff_id.sub contDiff_const).const_smul r⁻¹
  have hwe : w = (w ∘ e) ∘ e.symm := by
    funext x
    simp only [Function.comp_apply, Homeomorph.apply_symm_apply]
  have hr2 : 0 < (r ^ 2)⁻¹ := inv_pos.mpr (pow_pos hr 2)
  refine ⟨?_, fun i j => ?_⟩
  · have h := hW.comp hes.contDiffOn hm
    rwa [← hwe] at h
  · obtain ⟨_, _, D, hDeq, hDc, hDb, hDh⟩ := hent i j
    refine ⟨fun x => (r ^ 2)⁻¹ * D (e.symm x), ?_, ?_, ?_, ?_⟩
    · intro x hx
      change (r ^ 2)⁻¹ * D (e.symm x) = boundaryNeumannC2Entry w x i j
      rw [hDeq (hm hx)]
      change (r ^ 2)⁻¹ * boundaryNeumannC2Entry (w ∘ frozenBallScaling 0 hr) (e.symm x) i j = _
      rw [boundary_neumann_c2Entry_comp_scaling hr w, Homeomorph.apply_symm_apply]
      field_simp
    · exact continuousOn_const.mul (hDc.comp e.symm.continuous.continuousOn hmc)
    · intro x hx
      rw [abs_mul, abs_of_pos hr2]
      exact mul_le_mul_of_nonneg_left (hDb _ (hmc hx)) hr2.le
    · intro x hx y hy
      have hd : dist (e.symm x) (e.symm y) = r⁻¹ * dist x y := by
        change dist ((frozenBallScaling 0 hr).symm x) ((frozenBallScaling 0 hr).symm y) = _
        rw [frozenBallScaling_symm_apply, frozenBallScaling_symm_apply, dist_eq_norm,
          dist_eq_norm, ← smul_sub, norm_smul, Real.norm_of_nonneg (inv_pos.mpr hr).le]
        simp only [sub_zero]
      change |(r ^ 2)⁻¹ * D (e.symm x) - (r ^ 2)⁻¹ * D (e.symm y)| ≤ _
      rw [← mul_sub, abs_mul, abs_of_pos hr2, ← hd]
      exact mul_le_mul_of_nonneg_left (hDh _ (hmc hx) _ (hmc hy)) hr2.le

end LiquidDrop

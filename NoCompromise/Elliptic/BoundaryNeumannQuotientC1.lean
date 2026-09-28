import NoCompromise.Elliptic.BoundaryNeumannQuotientScaling

/-!
# Uniform C¹,α representatives of the Neumann tangential quotients

Layer 1 is applied after scaling the original three-quarter half ball to the
unit half ball. Its representative is C¹ on an ambient open ball meeting the
flat face. Constants precede the data, direction and signed nonzero step.
-/

noncomputable section
open MeasureTheory Filter Metric Set InnerProductSpace
open scoped ENNReal Topology Gradient RealInnerProductSpace
namespace LiquidDrop

/-- Uniform C¹,α representatives of the actual rescaled tangential quotients.
The ambient ball in this conclusion corresponds to radius 3/8 in the original
coordinates. No conclusion about the limit as the step tends to zero is asserted. -/
theorem boundary_neumann_quotient_c1_holder {α lam cap M N : ℝ}
    (hα : 0 < α) (hα1 : α < 1) (hlam : 0 < lam) (hcap : 0 ≤ cap)
    (hM : 0 ≤ M) (hN : 0 ≤ N) :
    ∃ C > 0, ∀ (A : EuclideanSpace ℝ (Fin 3) → EuclideanSpace ℝ (Fin 3) →L[ℝ]
        EuclideanSpace ℝ (Fin 3))
      (H : EuclideanSpace ℝ (Fin 3) → EuclideanSpace ℝ (Fin 3))
      (w : EuclideanSpace ℝ (Fin 3) → ℝ),
      BoundaryNeumannClosedData α lam cap M N A H w →
      ∀ (i : Fin 3) (s : ℝ), i ≠ Fin.last 2 → s ≠ 0 → |s| < 1 / 16 →
      ∃ v : EuclideanSpace ℝ (Fin 3) → ℝ,
        ContDiffOn ℝ 1 v (ball 0 (1 / 2 : ℝ)) ∧
        (fun x => coordinateDifferenceQuotient i s w ((3 / 4 : ℝ) • x))
          =ᵐ[volume.restrict (boundaryHalfBall (1 / 2))] v ∧
        (fun x => (3 / 4 : ℝ) •
          coordinateDifferenceQuotient i s (gradient w) ((3 / 4 : ℝ) • x))
          =ᵐ[volume.restrict (boundaryHalfBall (1 / 2))] gradient v ∧
        (∀ x ∈ ball 0 (1 / 2 : ℝ), ‖gradient v x‖ ≤ C) ∧
        ∀ x ∈ ball 0 (1 / 2 : ℝ), ∀ y ∈ ball 0 (1 / 2 : ℝ),
          ‖gradient v x - gradient v y‖ ≤ C * dist x y ^ α := by
  obtain ⟨E, hE, henergy⟩ := boundary_neumann_quotient_h1_bound (cap := cap) hα hlam hM hN
  obtain ⟨K, hK, hdatum⟩ := boundary_neumann_quotient_datum_holder hα hM
  obtain ⟨C, hC, hregularity⟩ := boundary_neumann_homogeneous_c1_holder
    (HA := M) (HH := K * N) (M := (4 / 3) * E)
    hα hα1 hlam hcap hM (by positivity) (by positivity)
  refine ⟨C, hC, ?_⟩
  intro A H w d i s hi hs0 hs
  let e := frozenBallScaling (0 : EuclideanSpace ℝ (Fin 3)) (by norm_num : (0 : ℝ) < 3 / 4)
  let q := coordinateDifferenceQuotient i s w
  let D := coordinateDifferenceQuotient i s (gradient w)
  let G := boundaryNeumannQuotientDatum A (gradient w) H i s
  have heapply (x) : e x = (3 / 4 : ℝ) • x := by
    simp only [e, frozenBallScaling_apply, zero_add]
  have hsR : |s| ≤ 1 - (3 / 4 : ℝ) := by linarith
  have hq := d.quotient_h1 hi hsR
  obtain ⟨heq, hGzero⟩ := d.quotient_equation hα hi hsR
  have hscale : MapsTo e (boundaryHalfBall 1) (boundaryHalfBall (3 / 4)) := by
    intro x hx
    simpa only [mul_one] using
      (boundary_halfBall_scaling_mem (by norm_num : (0 : ℝ) < 3 / 4) x 1).mpr hx
  have hscaleC := hscale.closure e.continuous
  have hmap : MapsTo e (closure (boundaryHalfBall 1)) (closure (boundaryHalfBall 1)) :=
    fun _ hx => (closure_mono (boundaryHalfBall_mono (by norm_num : (3 / 4 : ℝ) ≤ 1)))
      (hscaleC hx)
  have hGc : ContinuousOn G (closure (boundaryHalfBall (3 / 4))) :=
    boundary_neumann_quotient_datum_continuous hα d.coefficient d.source d.solution hi hsR
  have hGh := (hdatum A H w d.coefficient d.source d.solution d.coefficient_norm
    (3 / 4) s i hi hs0 hsR).2
  have hGbound : ∀ x ∈ closure (boundaryHalfBall (3 / 4)),
      ∀ y ∈ closure (boundaryHalfBall (3 / 4)),
      ‖G x - G y‖ ≤ (K * N) * dist x y ^ α := by
    intro x hx y hy
    exact (hGh x hx y hy).trans (mul_le_mul_of_nonneg_right
      (mul_le_mul_of_nonneg_left d.norm_bound hK.le) (Real.rpow_nonneg dist_nonneg _))
  have hdist (x y : EuclideanSpace ℝ (Fin 3)) : dist (e x) (e y) ≤ dist x y := by
    rw [quasilinear_ballScaling_dist]
    nlinarith [dist_nonneg (x := x) (y := y)]
  have hscaled := (hq.comp_homeomorph_on (isOpen_boundaryHalfBall 1)
    (isOpen_boundaryHalfBall (3 / 4)) e
    (quasilinear_ballScaling_lipschitz 0 (by norm_num : (0 : ℝ) < 3 / 4))
    (quasilinear_ballScaling_symm_lipschitz 0 (by norm_num : (0 : ℝ) < 3 / 4)) hscale).1
  have hd (x) : (fderiv ℝ e x).adjoint = (3 / 4 : ℝ) • ContinuousLinearMap.id ℝ _ := by
    rw [frozenBallScaling_fderiv]
    simp only [map_smul, ContinuousLinearMap.adjoint_id]
  have hH1 : HasH1GradientOn (q ∘ e) (fun x => (3 / 4 : ℝ) • D (e x))
      (boundaryHalfBall 1) := by
    simpa only [hd, smul_apply, ContinuousLinearMap.id_apply] using hscaled
  have heqscaled := heq.comp_scaling (by norm_num : (0 : ℝ) < 3 / 4)
  have henergyScaled : (∫ x in boundaryHalfBall 1, ‖(3 / 4 : ℝ) • D (e x)‖ ^ 2) ≤
      (4 / 3) * E := by
    rw [boundary_integral_energy_scaling D (by norm_num : (0 : ℝ) < 3 / 4) 1]
    norm_num only [mul_one, inv_div, invOf_eq_inv, one_div]
    exact mul_le_mul_of_nonneg_left (henergy A H w d i s hi hs0 hs)
      (by norm_num : (0 : ℝ) ≤ 4 / 3)
  have hcross : ∀ x ∈ closure (boundaryHalfBall 1), x (Fin.last 2) = 0 →
      ∀ j : Fin 3, j ≠ Fin.last 2 →
        A (e x) (EuclideanSpace.single j 1) (Fin.last 2) = 0 ∧
        A (e x) (EuclideanSpace.single (Fin.last 2) 1) j = 0 := by
    intro x hx hflat j hj
    apply d.cross_zero _ (hmap hx) _ j hj
    rw [heapply]
    change (3 / 4 : ℝ) * x (Fin.last 2) = 0
    rw [hflat, mul_zero]
  have hzero : ∀ x ∈ closure (boundaryHalfBall 1), x (Fin.last 2) = 0 →
      ((3 / 4 : ℝ) • G (e x)) (Fin.last 2) = 0 := by
    intro x hx hflat
    have heflat : (e x) (Fin.last 2) = 0 := by
      rw [heapply]
      change (3 / 4 : ℝ) * x (Fin.last 2) = 0
      rw [hflat, mul_zero]
    change (3 / 4 : ℝ) * G (e x) (Fin.last 2) = 0
    rw [hGzero _ (hscaleC hx) heflat, mul_zero]
  have hAh : ∀ x ∈ closure (boundaryHalfBall 1), ∀ y ∈ closure (boundaryHalfBall 1),
      ‖A (e x) - A (e y)‖ ≤ M * dist x y ^ α := by
    intro x hx y hy
    have ht := d.coefficient.function_holder.nondiv_norm_sub_le (hmap hx) (hmap hy)
    simp only [← dist_eq_norm] at ht ⊢
    exact ht.trans (mul_le_mul ((le_add_of_nonneg_left
      (holderUniformNorm_nonneg d.coefficient.function_holder.uniform_bounded)).trans
        (d.coefficient.function_norm_le.trans d.coefficient_norm))
      (Real.rpow_le_rpow dist_nonneg (hdist x y) hα.le)
      (Real.rpow_nonneg dist_nonneg _) hM)
  have hGH : ∀ x ∈ closure (boundaryHalfBall 1), ∀ y ∈ closure (boundaryHalfBall 1),
      ‖(3 / 4 : ℝ) • G (e x) - (3 / 4 : ℝ) • G (e y)‖ ≤ (K * N) * dist x y ^ α := by
    intro x hx y hy
    rw [← smul_sub, norm_smul]
    have hn : ‖(3 / 4 : ℝ)‖ ≤ 1 := by norm_num
    have ht := mul_le_mul_of_nonneg_right hn (norm_nonneg (G (e x) - G (e y)))
    simp only [one_mul] at ht
    exact ht.trans ((hGbound _ (hscaleC hx) _ (hscaleC hy)).trans
      (mul_le_mul_of_nonneg_left (Real.rpow_le_rpow dist_nonneg (hdist x y) hα.le)
        (by positivity)))
  have ht := hregularity (A ∘ e) (fun x => (3 / 4 : ℝ) • G (e x))
    (fun x => (3 / 4 : ℝ) • D (e x)) (q ∘ e)
    (d.coefficient.contDiff.continuousOn.comp e.continuous.continuousOn hmap)
    ((hGc.comp e.continuous.continuousOn hscaleC).const_smul (3 / 4 : ℝ))
    (fun _ hx => d.coefficient_bound _ (hmap hx))
    (fun _ hx => d.elliptic _ (hmap hx)) hAh hGH hcross hzero hH1 heqscaled henergyScaled
  simpa only [Function.comp_def, q, D, heapply] using ht

end LiquidDrop

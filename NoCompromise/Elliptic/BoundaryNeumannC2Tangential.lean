module

public import NoCompromise.Elliptic.BoundaryNeumannTangential

@[expose] public section

/-!
# Tangential second derivatives in the original Neumann coordinates

The rescaling in `boundary_neumann_tangential_derivative_c1_holder` is undone here.
The derivatives in the conclusions are ordinary Fréchet derivatives on the open
half ball; the constant is chosen before the coefficient, source, and solution.
-/

noncomputable section
open MeasureTheory Filter Metric Set InnerProductSpace
open scoped ENNReal NNReal Topology Gradient RealInnerProductSpace
namespace LiquidDrop

lemma boundary_neumann_c2_unscale_mem {x : EuclideanSpace ℝ (Fin 3)}
    (hx : x ∈ boundaryHalfBall (3 / 8)) :
    (4 / 3 : ℝ) • x ∈ boundaryHalfBall (1 / 2) := by
  refine ⟨?_, ?_⟩
  · have hb : ‖x‖ < 3 / 8 := by simpa only [mem_ball, dist_zero_right] using hx.1
    simp only [mem_ball, dist_zero_right, norm_smul, Real.norm_eq_abs]
    norm_num
    linarith
  · change 0 < ((4 / 3 : ℝ) • x) (Fin.last 2)
    simpa only [PiLp.smul_apply, smul_eq_mul] using
      mul_pos (by norm_num : (0 : ℝ) < 4 / 3) hx.2

lemma boundary_neumann_c2_gradient_comp_smul
    {f : EuclideanSpace ℝ (Fin 3) → ℝ} {c : ℝ}
    {x : EuclideanSpace ℝ (Fin 3)} (hf : DifferentiableAt ℝ f (c • x)) :
    gradient (fun y => f (c • y)) x = c • gradient f (c • x) := by
  have hd : HasFDerivAt (fun y => f (c • y))
      ((fderiv ℝ f (c • x)).comp (c • ContinuousLinearMap.id ℝ _)) x :=
    hf.hasFDerivAt.comp x ((hasFDerivAt_id x).const_smul c)
  ext i
  simp only [gradient_apply_eq_fderiv_single, hd.fderiv, PiLp.smul_apply,
    ContinuousLinearMap.comp_apply, smul_apply,
    ContinuousLinearMap.id_apply, map_smul, smul_eq_mul]

/-- In original coordinates, every tangential first derivative is differentiable,
with uniformly bounded and Hölder continuous gradient on the radius `3/8` half ball. -/
theorem boundary_neumann_tangential_derivative_c1_holder_original {α lam cap M N : ℝ}
    (hα : 0 < α) (hα1 : α < 1) (hlam : 0 < lam) (hcap : 0 ≤ cap)
    (hM : 0 ≤ M) (hN : 0 ≤ N) :
    ∃ C > 0, ∀ (A : EuclideanSpace ℝ (Fin 3) → EuclideanSpace ℝ (Fin 3) →L[ℝ]
        EuclideanSpace ℝ (Fin 3))
      (H : EuclideanSpace ℝ (Fin 3) → EuclideanSpace ℝ (Fin 3))
      (w : EuclideanSpace ℝ (Fin 3) → ℝ),
      BoundaryNeumannClosedData α lam cap M N A H w →
      ∀ i : Fin 3, i ≠ Fin.last 2 →
        DifferentiableOn ℝ (fun x => fderiv ℝ w x (EuclideanSpace.single i 1))
          (boundaryHalfBall (3 / 8)) ∧
        (∀ x ∈ boundaryHalfBall (3 / 8),
          ‖gradient (fun y => fderiv ℝ w y (EuclideanSpace.single i 1)) x‖ ≤ C) ∧
        ∀ x ∈ boundaryHalfBall (3 / 8), ∀ y ∈ boundaryHalfBall (3 / 8),
          ‖gradient (fun y => fderiv ℝ w y (EuclideanSpace.single i 1)) x -
            gradient (fun y => fderiv ℝ w y (EuclideanSpace.single i 1)) y‖ ≤
              C * dist x y ^ α := by
  obtain ⟨C, hC, ht⟩ := boundary_neumann_tangential_derivative_c1_holder
    hα hα1 hlam hcap hM hN
  refine ⟨(4 / 3) * C * (1 + (4 / 3 : ℝ) ^ α), by positivity, ?_⟩
  intro A H w d i hi
  obtain ⟨hd, hb, hh⟩ := ht A H w d i hi
  let f := fun x => fderiv ℝ w ((3 / 4 : ℝ) • x) (EuclideanSpace.single i 1)
  have he : (fun x => f ((4 / 3 : ℝ) • x)) =
      (fun x => fderiv ℝ w x (EuclideanSpace.single i 1)) := by
    funext x
    dsimp only [f]
    rw [smul_smul]
    norm_num
  have hfd (x) (hx : x ∈ boundaryHalfBall (3 / 8)) :
      DifferentiableAt ℝ f ((4 / 3 : ℝ) • x) :=
    hd.differentiableAt ((isOpen_boundaryHalfBall _).mem_nhds
      (boundary_neumann_c2_unscale_mem hx))
  have hg (x) (hx : x ∈ boundaryHalfBall (3 / 8)) :
      gradient (fun y => fderiv ℝ w y (EuclideanSpace.single i 1)) x =
        (4 / 3 : ℝ) • gradient f ((4 / 3 : ℝ) • x) := by
    rw [← he]
    exact boundary_neumann_c2_gradient_comp_smul (hfd x hx)
  refine ⟨?_, ?_, ?_⟩
  · intro x hx
    rw [← he]
    exact ((hfd x hx).comp x (differentiableAt_id.const_smul (4 / 3 : ℝ))).differentiableWithinAt
  · intro x hx
    rw [hg x hx, norm_smul, Real.norm_of_nonneg (by norm_num : (0 : ℝ) ≤ 4 / 3)]
    apply (mul_le_mul_of_nonneg_left (hb _ (boundary_neumann_c2_unscale_mem hx))
      (by norm_num : (0 : ℝ) ≤ 4 / 3)).trans
    exact le_mul_of_one_le_right (by positivity)
      (by linarith [Real.rpow_nonneg (by norm_num : (0 : ℝ) ≤ 4 / 3) α])
  · intro x hx y hy
    rw [hg x hx, hg y hy, ← smul_sub, norm_smul,
      Real.norm_of_nonneg (by norm_num : (0 : ℝ) ≤ 4 / 3)]
    apply (mul_le_mul_of_nonneg_left
      (hh _ (boundary_neumann_c2_unscale_mem hx) _ (boundary_neumann_c2_unscale_mem hy))
      (by norm_num : (0 : ℝ) ≤ 4 / 3)).trans
    have hdist : dist ((4 / 3 : ℝ) • x) ((4 / 3 : ℝ) • y) =
        (4 / 3 : ℝ) * dist x y := by
      rw [dist_eq_norm, ← smul_sub, norm_smul, Real.norm_of_nonneg (by norm_num), dist_eq_norm]
    rw [hdist, Real.mul_rpow (by norm_num) dist_nonneg]
    have hnonneg := Real.rpow_nonneg (dist_nonneg (x := x) (y := y)) α
    nlinarith [mul_nonneg hC.le hnonneg]

/-- Each `∂ⱼ∂ᵢw`, with `i` tangential and arbitrary `j`, is bounded and Hölder on
the original radius `3/8` half ball. Differentiability is included to ensure that
the Fréchet derivatives here are the actual derivatives. -/
theorem boundary_neumann_tangential_second_derivatives {α lam cap M N : ℝ}
    (hα : 0 < α) (hα1 : α < 1) (hlam : 0 < lam) (hcap : 0 ≤ cap)
    (hM : 0 ≤ M) (hN : 0 ≤ N) :
    ∃ C > 0, ∀ (A : EuclideanSpace ℝ (Fin 3) → EuclideanSpace ℝ (Fin 3) →L[ℝ]
        EuclideanSpace ℝ (Fin 3))
      (H : EuclideanSpace ℝ (Fin 3) → EuclideanSpace ℝ (Fin 3))
      (w : EuclideanSpace ℝ (Fin 3) → ℝ),
      BoundaryNeumannClosedData α lam cap M N A H w →
      ∀ i : Fin 3, i ≠ Fin.last 2 →
        DifferentiableOn ℝ (fun x => fderiv ℝ w x (EuclideanSpace.single i 1))
          (boundaryHalfBall (3 / 8)) ∧
        ∀ j : Fin 3,
          (∀ x ∈ boundaryHalfBall (3 / 8),
            |fderiv ℝ (fun y => fderiv ℝ w y (EuclideanSpace.single i 1)) x
              (EuclideanSpace.single j 1)| ≤ C) ∧
          ∀ x ∈ boundaryHalfBall (3 / 8), ∀ y ∈ boundaryHalfBall (3 / 8),
            |fderiv ℝ (fun y => fderiv ℝ w y (EuclideanSpace.single i 1)) x
                (EuclideanSpace.single j 1) -
              fderiv ℝ (fun y => fderiv ℝ w y (EuclideanSpace.single i 1)) y
                (EuclideanSpace.single j 1)| ≤ C * dist x y ^ α := by
  obtain ⟨C, hC, ht⟩ := boundary_neumann_tangential_derivative_c1_holder_original
    hα hα1 hlam hcap hM hN
  refine ⟨C, hC, ?_⟩
  intro A H w d i hi
  obtain ⟨hd, hb, hh⟩ := ht A H w d i hi
  refine ⟨hd, fun j => ⟨?_, ?_⟩⟩
  · intro x hx
    rw [← gradient_apply_eq_fderiv_single, ← Real.norm_eq_abs]
    exact (PiLp.norm_apply_le _ j).trans (hb x hx)
  · intro x hx y hy
    rw [← gradient_apply_eq_fderiv_single, ← gradient_apply_eq_fderiv_single,
      ← PiLp.sub_apply, ← Real.norm_eq_abs]
    exact (PiLp.norm_apply_le _ j).trans (hh x hx y hy)

end LiquidDrop

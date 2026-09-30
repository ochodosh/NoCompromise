module

public import NoCompromise.Elliptic.BoundaryNeumannInhomC1
public import NoCompromise.Elliptic.BoundaryNeumannEven

@[expose] public section

/-!
# The classical conormal condition in `thm:boundary-neumann` (flat face)

`boundary_neumann_c1_holder_conormal` has exactly the hypotheses and constant of
`boundary_neumann_c1_holder` and additionally asserts that the C¹ representative satisfies
the prescribed inward-coordinate conormal condition `(A∇u)₃ = h` pointwise on the flat face
of `ball 0 (1/2)`. The proof is that of `boundary_neumann_c1_holder`, using the even Layer 1
representative (`boundary_neumann_homogeneous_c1_holder_even`), whose normal derivative
vanishes on the face, and the vanishing cross coefficients.
-/

noncomputable section
open MeasureTheory Filter Metric Set InnerProductSpace
open scoped ENNReal NNReal Topology Gradient RealInnerProductSpace
namespace LiquidDrop

theorem boundary_neumann_c1_holder_conormal {a lam cap HA K M : ℝ}
    (ha : 0 < a) (ha1 : a < 1) (hlam : 0 < lam) (hcap : 0 ≤ cap)
    (hHA : 0 ≤ HA) (hK : 0 ≤ K) (hM : 0 ≤ M) :
    ∃ C : ℝ, 0 < C ∧
      ∀ (A : EuclideanSpace ℝ (Fin 3) → EuclideanSpace ℝ (Fin 3) →L[ℝ]
          EuclideanSpace ℝ (Fin 3))
        (F : EuclideanSpace ℝ (Fin 3) → EuclideanSpace ℝ (Fin 3))
        (z f : EuclideanSpace ℝ (Fin 3) → ℝ)
        (h : EuclideanSpace ℝ (Fin 2) → ℝ),
        ContinuousOn A (closure (boundaryHalfBall 1)) →
        (∀ x ∈ closure (boundaryHalfBall 1), ‖A x‖ ≤ cap) →
        (∀ x ∈ closure (boundaryHalfBall 1), ∀ ξ,
          lam * ‖ξ‖ ^ 2 ≤ inner ℝ (A x ξ) ξ) →
        (∀ x ∈ closure (boundaryHalfBall 1), ∀ y ∈ closure (boundaryHalfBall 1),
          ‖A x - A y‖ ≤ HA * dist x y ^ a) →
        (∀ x ∈ closure (boundaryHalfBall 1), x (Fin.last 2) = 0 →
          ∀ i : Fin 3, i ≠ Fin.last 2 →
            A x (EuclideanSpace.single i 1) (Fin.last 2) = 0 ∧
            A x (EuclideanSpace.single (Fin.last 2) 1) i = 0) →
        (∃ U : Set (EuclideanSpace ℝ (Fin 2)), IsOpen U ∧ closedBall 0 1 ⊆ U ∧
          ContDiffOn ℝ 1 h U ∧ ContDiffOn ℝ 1 (boundaryNeumannNormalCoefficient A) U ∧
          (∀ x ∈ U, lam ≤ boundaryNeumannNormalCoefficient A x)) →
        (∀ x ∈ closedBall 0 1, ‖h x‖ ≤ K) →
        (∀ x ∈ closedBall 0 1, ‖boundaryNeumannNormalCoefficient A x‖ ≤ K) →
        (∀ x ∈ closedBall 0 1, ‖gradient h x‖ ≤ K) →
        (∀ x ∈ closedBall 0 1, ‖gradient (boundaryNeumannNormalCoefficient A) x‖ ≤ K) →
        (∀ x ∈ closedBall 0 1, ∀ y ∈ closedBall 0 1,
          ‖gradient h x - gradient h y‖ ≤ K * dist x y ^ a) →
        (∀ x ∈ closedBall 0 1, ∀ y ∈ closedBall 0 1,
          ‖gradient (boundaryNeumannNormalCoefficient A) x -
            gradient (boundaryNeumannNormalCoefficient A) y‖ ≤ K * dist x y ^ a) →
        ContinuousOn f (closure (boundaryHalfBall 1)) →
        (∀ x ∈ closure (boundaryHalfBall 1), ‖f x‖ ≤ K) →
        (∀ x ∈ closure (boundaryHalfBall 1), ∀ y ∈ closure (boundaryHalfBall 1),
          ‖f x - f y‖ ≤ K * dist x y ^ a) →
        HasH1GradientOn z F (boundaryHalfBall 1) →
        (∫ x in boundaryHalfBall 1, ‖F x‖ ^ 2) ≤ M →
        (∀ φ : EuclideanSpace ℝ (Fin 3) → ℝ, ContDiff ℝ 1 φ → HasCompactSupport φ →
          tsupport φ ⊆ ball 0 1 →
          (∫ x in boundaryHalfBall 1, inner ℝ (A x (F x)) (gradient φ x)) =
            -(∫ x in boundaryHalfBall 1, f x * φ x) -
              ∫ y in ball (0 : EuclideanSpace ℝ (Fin 2)) 1,
                h y * φ (graphBaseEmbedding y)) →
        ∃ u : EuclideanSpace ℝ (Fin 3) → ℝ,
          ContDiffOn ℝ 1 u (ball 0 (1 / 2 : ℝ)) ∧
          z =ᵐ[volume.restrict (boundaryHalfBall (1 / 2))] u ∧
          F =ᵐ[volume.restrict (boundaryHalfBall (1 / 2))] gradient u ∧
          (∀ x ∈ ball 0 (1 / 2 : ℝ), ‖gradient u x‖ ≤ C) ∧
          (∀ x ∈ ball 0 (1 / 2 : ℝ), ∀ y ∈ ball 0 (1 / 2 : ℝ),
            ‖gradient u x - gradient u y‖ ≤ C * dist x y ^ a) ∧
          (∀ y : EuclideanSpace ℝ (Fin 2), graphBaseEmbedding y ∈ ball 0 (1 / 2 : ℝ) →
            A (graphBaseEmbedding y) (gradient u (graphBaseEmbedding y)) (Fin.last 2) =
              h y) := by
  let Bq := boundaryNeumannLiftGradientBound lam K
  let Hq := boundaryNeumannLiftGradientHolder lam K
  have hBq : 0 ≤ Bq := by
    dsimp [Bq, boundaryNeumannLiftGradientBound, boundaryNeumannQuotientGradientBound]
    positivity
  have hHq : 0 ≤ Hq := by
    dsimp [Hq, boundaryNeumannLiftGradientHolder, boundaryNeumannQuotientGradientHolder,
      boundaryNeumannQuotientGradientBound]
    positivity
  let HH := K + 2 * K + 2 * K + cap * Hq + HA * Bq
  have hHH : 0 ≤ HH := by dsimp [HH]; positivity
  let E := 2 * M + 2 * (volume (boundaryHalfBall 1)).toReal * Bq ^ 2
  have hE : 0 ≤ E := by dsimp [E]; positivity
  obtain ⟨C, hC, hregularity⟩ := boundary_neumann_homogeneous_c1_holder_even
    ha ha1 hlam hcap hHA hHH hE
  refine ⟨C + Bq + Hq, by positivity, ?_⟩
  intro A F z f h hA hbA hell hhA hcross hneigh hbh hbb hDh hDb hhDh hhDb hf hbf hhf hz he hweak
  obtain ⟨U, hU, hsub, hh, hb, hpos⟩ := hneigh
  let q := boundaryNeumannLift h (boundaryNeumannNormalCoefficient A)
  let H := boundaryNeumannInhomDatum A f h
  obtain ⟨hcq, hq, hbq, hhq, hhh⟩ := boundaryNeumannLift_c1_estimates ha.le ha1.le hlam hK
    hU hsub hh hb hpos hbh hbb hDh hDb hhDh hhDb
  have hclosed : closure (boundaryHalfBall 1) ⊆ closedBall (0 : EuclideanSpace ℝ (Fin 3)) 1 :=
    fun x hx => by simpa only [mem_closedBall, dist_zero_right] using
      boundary_neumann_closed_norm_le hx
  have hsmall : ball (0 : EuclideanSpace ℝ (Fin 3)) (1 / 2 : ℝ) ⊆ closedBall 0 1 :=
    fun x hx => mem_closedBall.mpr ((mem_ball.mp hx).le.trans (by norm_num))
  have hholderH : ∀ x ∈ closure (boundaryHalfBall 1), ∀ y ∈ closure (boundaryHalfBall 1),
      ‖H x - H y‖ ≤ HH * dist x y ^ a := by
    intro x hx y hy
    exact boundaryNeumannInhomDatum_holder ha.le ha1.le hcap hHA hK hK (by positivity)
      hbA hhA hf hbf hhf hhh (fun x hx => hbq x (hclosed hx))
      (fun x hx y hy => hhq x (hclosed hx) y (hclosed hy)) hx hy
  have hcH : ContinuousOn H (closure (boundaryHalfBall 1)) :=
    campanato_continuousOn_of_holder_bound hHH ha hholderH
  have hzero : ∀ x ∈ closure (boundaryHalfBall 1), x (Fin.last 2) = 0 →
      H x (Fin.last 2) = 0 := by
    intro x hx hx0
    have hp := hsub (boundary_neumann_projection_closedBall (hclosed hx))
    exact boundaryNeumannInhomDatum_flat_of_elliptic hlam f hx0 (hell x hx)
      ((hh.differentiableOn one_ne_zero _ hp).differentiableAt (hU.mem_nhds hp))
      ((hb.differentiableOn one_ne_zero _ hp).differentiableAt (hU.mem_nhds hp))
  have hw := hz.sub hq
  have hred := boundary_neumann_inhomogeneous_weak_reduction ha ha1.le hK hK
    hA hbA hz.memLp_gradient hf hbf hhf (hh.continuousOn.mono hsub) hweak
  have henergy : (∫ x in boundaryHalfBall 1, ‖F x - gradient q x‖ ^ 2) ≤ E :=
    boundary_neumann_c1_energy_sub hBq hz.memLp_gradient hq.memLp_gradient
      (fun x hx => hbq x (hclosed (subset_closure hx))) he
  obtain ⟨v, hv, hwv, hFv, hbv, hhv, -, hv3⟩ := hregularity A H
    (fun x => F x - gradient q x) (fun x => z x - q x)
    hA hcH hbA hell hhA hholderH hcross hzero hw hred henergy
  have hqsmall : ContDiffOn ℝ 1 q (ball 0 (1 / 2 : ℝ)) :=
    hcq.mono (fun x hx => hsub (boundary_neumann_projection_closedBall (hsmall hx)))
  have hgrad : ∀ x ∈ ball 0 (1 / 2 : ℝ),
      gradient (fun y => v y + q y) x = gradient v x + gradient q x :=
    fun x hx => boundary_neumann_c1_gradient_add
      ((hv.differentiableOn one_ne_zero x hx).differentiableAt (isOpen_ball.mem_nhds hx))
      ((hqsmall.differentiableOn one_ne_zero x hx).differentiableAt (isOpen_ball.mem_nhds hx))
  refine ⟨fun x => v x + q x, hv.add hqsmall, ?_, ?_, ?_, ?_, ?_⟩
  · filter_upwards [hwv] with x hx
    linarith
  · filter_upwards [hFv, ae_restrict_mem
      (isOpen_boundaryHalfBall (1 / 2 : ℝ)).measurableSet] with x hx hxb
    rw [hgrad x hxb.1]
    exact sub_eq_iff_eq_add.mp hx
  · intro x hx
    rw [hgrad x hx]
    exact (norm_add_le _ _).trans
      ((add_le_add (hbv x hx) (hbq x (hsmall hx))).trans (by linarith))
  · intro x hx y hy
    rw [hgrad x hx, hgrad y hy]
    have heq : gradient v x + gradient q x - (gradient v y + gradient q y) =
        (gradient v x - gradient v y) + (gradient q x - gradient q y) := by abel
    rw [heq]
    calc
      _ ≤ ‖gradient v x - gradient v y‖ + ‖gradient q x - gradient q y‖ := norm_add_le _ _
      _ ≤ C * dist x y ^ a + Hq * dist x y ^ a :=
        add_le_add (hhv x hx y hy) (hhq x (hsmall hx) y (hsmall hy))
      _ ≤ _ := by nlinarith [Real.rpow_nonneg (dist_nonneg (x := x) (y := y)) a]
  · intro y hy
    have hx0 : graphBaseEmbedding y (Fin.last 2) = 0 := by simp
    have hyc : graphBaseEmbedding y ∈ closure (boundaryHalfBall 1) :=
      boundary_neumann_mem_closure (ball_subset_ball (by norm_num) hy) hx0.ge
    have hyU : y ∈ U := by
      have hp := boundary_neumann_projection_closedBall (hsmall hy)
      rw [boundary_neumann_projection_base] at hp
      exact hsub hp
    rw [hgrad _ hy, map_add, PiLp.add_apply]
    have hq3 := boundaryNeumannLift_conormal (A := A) (h := h) (y := y)
      ((hh.differentiableOn one_ne_zero _ hyU).differentiableAt (hU.mem_nhds hyU))
      ((hb.differentiableOn one_ne_zero _ hyU).differentiableAt (hU.mem_nhds hyU))
      (ne_of_gt (hlam.trans_le (hpos y hyU)))
    have hv0 : A (graphBaseEmbedding y) (gradient v (graphBaseEmbedding y)) (Fin.last 2) = 0 := by
      have h3 : gradient v (graphBaseEmbedding y) 2 = 0 := hv3 _ hy hx0
      have hexp : gradient v (graphBaseEmbedding y) =
          gradient v (graphBaseEmbedding y) 0 • EuclideanSpace.single (0 : Fin 3) (1 : ℝ) +
          gradient v (graphBaseEmbedding y) 1 • EuclideanSpace.single (1 : Fin 3) (1 : ℝ) := by
        ext j
        fin_cases j <;> simp [h3]
      rw [hexp, map_add, map_smul, map_smul, PiLp.add_apply, PiLp.smul_apply, PiLp.smul_apply,
        (hcross _ hyc hx0 0 (by decide)).1, (hcross _ hyc hx0 1 (by decide)).1,
        smul_zero, smul_zero, add_zero]
    rw [hv0, zero_add]
    exact hq3

end LiquidDrop

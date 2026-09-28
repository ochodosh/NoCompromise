import NoCompromise.Elliptic.BoundaryNeumannInhomC1Lift

/-!
# Inhomogeneous conormal C¹,α regularity

This completes the first assertion of blueprint thm:boundary-neumann on the
normalized chart. It strengthens the blueprint assertion by requiring C¹,α
regularity only of the scalar normal coefficient A₃₃(·,0); the full matrix
needs only the stated C⁰,α bounds. The scalar coefficient and boundary datum
are C¹ on a data-dependent open neighbourhood of the closed base disk.
-/

noncomputable section
open MeasureTheory Filter Metric Set InnerProductSpace
open scoped ENNReal NNReal Topology Gradient RealInnerProductSpace
namespace LiquidDrop

lemma boundary_neumann_c1_energy_sub {B M : ℝ} (_hB : 0 ≤ B)
    {F Q : EuclideanSpace ℝ (Fin 3) → EuclideanSpace ℝ (Fin 3)}
    (hF : MemLp F 2 (volume.restrict (boundaryHalfBall 1)))
    (hQ : MemLp Q 2 (volume.restrict (boundaryHalfBall 1)))
    (hb : ∀ x ∈ boundaryHalfBall 1, ‖Q x‖ ≤ B)
    (henergy : (∫ x in boundaryHalfBall 1, ‖F x‖ ^ 2) ≤ M) :
    (∫ x in boundaryHalfBall 1, ‖F x - Q x‖ ^ 2) ≤
      2 * M + 2 * (volume (boundaryHalfBall 1)).toReal * B ^ 2 := by
  let : IsFiniteMeasure (volume.restrict (boundaryHalfBall 1)) :=
    ⟨by simpa using boundaryHalfBall_volume_lt_top 1⟩
  have hiF := hF.integrable_norm_pow (by norm_num : (2 : ℕ) ≠ 0)
  have hiQ := hQ.integrable_norm_pow (by norm_num : (2 : ℕ) ≠ 0)
  have hiD := (hF.sub hQ).integrable_norm_pow (by norm_num : (2 : ℕ) ≠ 0)
  have hqe : (∫ x in boundaryHalfBall 1, ‖Q x‖ ^ 2) ≤
      (volume (boundaryHalfBall 1)).toReal * B ^ 2 := by
    calc
      _ ≤ ∫ _x in boundaryHalfBall 1, B ^ 2 := by
        apply integral_mono_ae hiQ (integrable_const _)
        filter_upwards [ae_restrict_mem (isOpen_boundaryHalfBall 1).measurableSet] with x hx
        exact pow_le_pow_left₀ (norm_nonneg _) (hb x hx) 2
      _ = _ := by simp [measureReal_def]
  calc
    _ ≤ ∫ x in boundaryHalfBall 1, 2 * ‖F x‖ ^ 2 + 2 * ‖Q x‖ ^ 2 := by
      apply integral_mono hiD ((hiF.const_mul 2).add (hiQ.const_mul 2))
      intro x
      have hn := norm_sub_le (F x) (Q x)
      have hs := sq_le_sq₀ (norm_nonneg (F x - Q x))
        (add_nonneg (norm_nonneg (F x)) (norm_nonneg (Q x))) |>.mpr hn
      change ‖F x - Q x‖ ^ 2 ≤ 2 * ‖F x‖ ^ 2 + 2 * ‖Q x‖ ^ 2
      nlinarith [sq_nonneg (‖F x‖ - ‖Q x‖)]
    _ = 2 * (∫ x in boundaryHalfBall 1, ‖F x‖ ^ 2) +
        2 * (∫ x in boundaryHalfBall 1, ‖Q x‖ ^ 2) := by
      rw [integral_add (hiF.const_mul 2) (hiQ.const_mul 2),
        integral_const_mul, integral_const_mul]
    _ ≤ _ := by linarith

lemma boundary_neumann_c1_gradient_add {n : ℕ}
    {v q : EuclideanSpace ℝ (Fin n) → ℝ} {x : EuclideanSpace ℝ (Fin n)}
    (hv : DifferentiableAt ℝ v x) (hq : DifferentiableAt ℝ q x) :
    gradient (fun y => v y + q y) x = gradient v x + gradient q x := by
  simp only [gradient, fderiv_fun_add hv hq, map_add]

/-- Uniform up-to-the-flat-boundary C¹,α regularity with inhomogeneous data.
The constant precedes all coefficients, solutions, data and neighbourhoods.
Only the normal-normal coefficient on the base requires C¹,α regularity. -/
theorem boundary_neumann_c1_holder {a lam cap HA K M : ℝ}
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
            ‖gradient u x - gradient u y‖ ≤ C * dist x y ^ a) := by
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
  obtain ⟨C, hC, hregularity⟩ := boundary_neumann_homogeneous_c1_holder
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
  obtain ⟨v, hv, hwv, hFv, hbv, hhv⟩ := hregularity A H
    (fun x => F x - gradient q x) (fun x => z x - q x)
    hA hcH hbA hell hhA hholderH hcross hzero hw hred henergy
  have hqsmall : ContDiffOn ℝ 1 q (ball 0 (1 / 2 : ℝ)) :=
    hcq.mono (fun x hx => hsub (boundary_neumann_projection_closedBall (hsmall hx)))
  have hgrad : ∀ x ∈ ball 0 (1 / 2 : ℝ),
      gradient (fun y => v y + q y) x = gradient v x + gradient q x :=
    fun x hx => boundary_neumann_c1_gradient_add
      ((hv.differentiableOn one_ne_zero x hx).differentiableAt (isOpen_ball.mem_nhds hx))
      ((hqsmall.differentiableOn one_ne_zero x hx).differentiableAt (isOpen_ball.mem_nhds hx))
  refine ⟨fun x => v x + q x, hv.add hqsmall, ?_, ?_, ?_, ?_⟩
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

end LiquidDrop

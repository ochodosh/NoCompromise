module

public import NoCompromise.Elliptic.BoundaryNeumannQuotientC1
public import NoCompromise.Elliptic.BoundaryNondivTangential

@[expose] public section

/-!
# Tangential derivatives in `thm:boundary-neumann` (second assertion, homogeneous problem)

Passing `boundary_neumann_quotient_c1_holder` to the limit `s → 0`: for every tangential
direction `i`, the rescaled tangential derivative `x ↦ ∂ᵢw((3/4)x)` is differentiable on the
upper half ball `boundaryHalfBall (1/2)`, with gradient bound and `α`-Hölder bound whose
constant depends only on `α, lam, cap, M, N`. Hypotheses are those of
`BoundaryNeumannClosedData`. The normal second derivative and the final `C^{2,α}` estimate
are not asserted here.
-/

noncomputable section
open MeasureTheory Filter Metric Set InnerProductSpace
open scoped ENNReal NNReal Topology Gradient RealInnerProductSpace
namespace LiquidDrop

lemma convex_boundaryHalfBall (r : ℝ) : Convex ℝ (boundaryHalfBall r) := by
  refine (convex_ball 0 r).inter ?_
  have h : {x : EuclideanSpace ℝ (Fin 3) | 0 < x (Fin.last 2)} =
      (EuclideanSpace.proj (Fin.last 2) : EuclideanSpace ℝ (Fin 3) →L[ℝ] ℝ).toLinearMap ⁻¹'
        Ioi 0 := by
    ext x
    simp only [mem_ofPred_eq, mem_preimage, mem_Ioi]
    rfl
  rw [h]
  exact (convex_Ioi _).linear_preimage _

/-- Tangential derivatives of the homogeneous conormal problem are uniformly `C^{1,α}` on
the upper half ball of radius `1/2` (rescaled coordinates `y = (3/4)x`). -/
theorem boundary_neumann_tangential_derivative_c1_holder {α lam cap M N : ℝ}
    (hα : 0 < α) (hα1 : α < 1) (hlam : 0 < lam) (hcap : 0 ≤ cap)
    (hM : 0 ≤ M) (hN : 0 ≤ N) :
    ∃ C > 0, ∀ (A : EuclideanSpace ℝ (Fin 3) → EuclideanSpace ℝ (Fin 3) →L[ℝ]
        EuclideanSpace ℝ (Fin 3))
      (H : EuclideanSpace ℝ (Fin 3) → EuclideanSpace ℝ (Fin 3))
      (w : EuclideanSpace ℝ (Fin 3) → ℝ),
      BoundaryNeumannClosedData α lam cap M N A H w →
      ∀ i : Fin 3, i ≠ Fin.last 2 →
        DifferentiableOn ℝ (fun x => fderiv ℝ w ((3 / 4 : ℝ) • x) (EuclideanSpace.single i 1))
          (boundaryHalfBall (1 / 2)) ∧
        (∀ x ∈ boundaryHalfBall (1 / 2),
          ‖∇ (fun x => fderiv ℝ w ((3 / 4 : ℝ) • x) (EuclideanSpace.single i 1)) x‖ ≤ C) ∧
        ∀ x ∈ boundaryHalfBall (1 / 2), ∀ y ∈ boundaryHalfBall (1 / 2),
          ‖∇ (fun x => fderiv ℝ w ((3 / 4 : ℝ) • x) (EuclideanSpace.single i 1)) x -
            ∇ (fun x => fderiv ℝ w ((3 / 4 : ℝ) • x) (EuclideanSpace.single i 1)) y‖ ≤
              C * dist x y ^ α := by
  obtain ⟨C, hC, hq⟩ := boundary_neumann_quotient_c1_holder hα hα1 hlam hcap hM hN
  refine ⟨C, hC, ?_⟩
  intro A H w d i hi
  let U := boundaryHalfBall (1 / 2 : ℝ)
  have hUo : IsOpen U := isOpen_boundaryHalfBall _
  let s : ℕ → ℝ := fun n => (1 / 32 : ℝ) * (1 / ((n : ℝ) + 1))
  have hs0 : ∀ n, s n ≠ 0 := fun n => by positivity
  have hs1 : ∀ n, |s n| < 1 / 16 := by
    intro n
    have hpos : 0 < 1 / ((n : ℝ) + 1) := by positivity
    have hle : 1 / ((n : ℝ) + 1) ≤ 1 := by
      rw [div_le_one (by positivity)]; linarith [(Nat.cast_nonneg n : (0 : ℝ) ≤ n)]
    rw [abs_of_pos (by positivity)]
    change (1 / 32 : ℝ) * (1 / ((n : ℝ) + 1)) < 1 / 16
    nlinarith
  have hsT : Tendsto s atTop (𝓝[≠] 0) := by
    refine tendsto_nhdsWithin_iff.mpr ⟨?_, Eventually.of_forall hs0⟩
    simpa only [mul_zero] using
      (tendsto_one_div_add_atTop_nhds_zero_nat.const_mul (1 / 32 : ℝ))
  choose v hv hve _ hvb hvh using fun n => hq A H w d i (s n) hi (hs0 n) (hs1 n)
  have hwC : ContDiffOn ℝ 1 w (closure (boundaryHalfBall 1)) := d.solution.contDiff
  have hwc : ContinuousOn w (boundaryHalfBall 1) := hwC.continuousOn.mono subset_closure
  have hUb : U ⊆ ball 0 (1 / 2 : ℝ) := inter_subset_left
  have hU1 : U ⊆ boundaryHalfBall 1 := boundaryHalfBall_mono (by norm_num)
  have hmem0 : ∀ x ∈ U, (3 / 4 : ℝ) • x ∈ boundaryHalfBall 1 := fun x hx =>
    boundaryHalfBall_mono (by norm_num) (boundary_nondiv_scale_mem (hU1 hx))
  have hmem : ∀ n, ∀ x ∈ U,
      (3 / 4 : ℝ) • x + s n • EuclideanSpace.single i 1 ∈ boundaryHalfBall 1 := by
    intro n x hx
    have h1 := boundary_nondiv_scale_mem (hU1 hx)
    have h2 := boundary_nondiv_segment_mem_halfBall (r := 3 / 4) (R := 1) (h := s n) hi
      (by linarith [hs1 n]) h1 (t := 1) (by simp)
    simpa only [one_smul] using h2
  have heq : ∀ n, ∀ x ∈ U,
      v n x = coordinateDifferenceQuotient i (s n) w ((3 / 4 : ℝ) • x) := by
    intro n
    have hc1 : ContinuousOn (v n) U := (hv n).continuousOn.mono hUb
    have hc2 : ContinuousOn
        (fun x => coordinateDifferenceQuotient i (s n) w ((3 / 4 : ℝ) • x)) U := by
      have hsc : Continuous fun x : EuclideanSpace ℝ (Fin 3) => (3 / 4 : ℝ) • x :=
        continuous_const_smul _
      unfold coordinateDifferenceQuotient
      exact ((hwc.comp (hsc.add continuous_const).continuousOn (hmem n)).sub
        (hwc.comp hsc.continuousOn hmem0)).const_smul (s n)⁻¹
    exact fun x hx => (Measure.eqOn_open_of_ae_eq (hve n) hUo hc2 hc1 hx).symm
  have hwd : ∀ x ∈ U, DifferentiableAt ℝ w ((3 / 4 : ℝ) • x) := fun x hx =>
    (hwC.differentiableOn one_ne_zero).differentiableAt
      (mem_of_superset ((isOpen_boundaryHalfBall 1).mem_nhds (hmem0 x hx)) subset_closure)
  have hlim : ∀ x ∈ U, Tendsto (fun n => v n x) atTop
      (𝓝 (fderiv ℝ w ((3 / 4 : ℝ) • x) (EuclideanSpace.single i 1))) := by
    intro x hx
    have ht := (tendsto_coordinateDifferenceQuotient_of_differentiableAt (hwd x hx) i).comp hsT
    exact ht.congr' (Eventually.of_forall fun n => (heq n x hx).symm)
  exact c1_holder_of_tendsto_gradient hUo (convex_boundaryHalfBall _) hα hC.le v _
    (fun n => ((hv n).differentiableOn one_ne_zero).mono hUb)
    (fun n x hx => hvb n x (hUb hx)) (fun n x hx y hy => hvh n x (hUb hx) y (hUb hy)) hlim

end LiquidDrop

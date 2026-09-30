module

public import NoCompromise.Elliptic.BoundaryNondivC1
public import NoCompromise.Elliptic.BoundaryC1Slab
public import NoCompromise.Elliptic.C1HolderLimit

@[expose] public section

/-!
# Tangential derivatives in `thm:boundary-nondiv` (zero trace)

Passing the uniform boundary `C^{1,α}` estimates for tangential difference quotients
(`boundary_nondiv_quotient_boundary_c1`) to the limit: for every tangential direction
`i`, the rescaled tangential derivative `x ↦ ∂ᵢz((3/4)x)` is differentiable on the fixed
upper slab `boundaryC1UpperSlab`, with a gradient bound and an `α`-Hölder bound whose
constant depends only on `α, lam, cap, M, N`. The assumption that `z` is `C^{1,α}` up to
the face is the one recorded in `BoundaryNondivClosedData`. The normal second derivative
and the final `C^{2,α}` estimate on `B_{1/2}^+` are not asserted here.
-/

noncomputable section
open MeasureTheory Filter Metric Set InnerProductSpace
open scoped ENNReal NNReal Topology Gradient RealInnerProductSpace
namespace LiquidDrop

/-- The upper half of the fixed slab `boundaryC1Slab`. -/
def boundaryC1UpperSlab : Set (EuclideanSpace ℝ (Fin 3)) :=
  boundaryC1Slab ∩ {x | 0 < x (Fin.last 2)}

lemma isOpen_boundaryC1UpperSlab : IsOpen boundaryC1UpperSlab :=
  isOpen_boundaryC1Slab.inter (isOpen_lt continuous_const
    (EuclideanSpace.proj (Fin.last 2)).continuous)

lemma convex_boundaryC1UpperSlab : Convex ℝ boundaryC1UpperSlab := by
  refine convex_boundaryC1Slab.inter ?_
  have h : {x : EuclideanSpace ℝ (Fin 3) | 0 < x (Fin.last 2)} =
      (EuclideanSpace.proj (Fin.last 2) : EuclideanSpace ℝ (Fin 3) →L[ℝ] ℝ).toLinearMap ⁻¹'
        Ioi 0 := by
    ext x
    simp only [mem_ofPred_eq, mem_preimage, mem_Ioi]
    rfl
  rw [h]
  exact (convex_Ioi _).linear_preimage _

lemma boundaryC1UpperSlab_subset : boundaryC1UpperSlab ⊆ boundaryHalfBall 1 := by
  rintro x ⟨⟨hx1, hx2⟩, hx3⟩
  refine ⟨?_, hx3⟩
  have hp : ‖graphProjectionN 2 x‖ < 5 / 8 := by
    simpa only [mem_preimage, mem_ball, dist_zero_right] using hx1
  have hl : |x (Fin.last 2)| < 1 / 1048576 := hx2
  have hn := norm_sq_graphProjectionN x
  have hsq : x (Fin.last 2) ^ 2 < 1 / 2 := by
    rw [← sq_abs]; nlinarith [abs_nonneg (x (Fin.last 2))]
  have hp2 : ‖graphProjectionN 2 x‖ ^ 2 < 25 / 64 := by
    nlinarith [norm_nonneg (graphProjectionN 2 x)]
  rw [mem_ball, dist_zero_right]
  nlinarith [norm_nonneg x]

lemma boundary_nondiv_scale_mem {x : EuclideanSpace ℝ (Fin 3)} (hx : x ∈ boundaryHalfBall 1) :
    (3 / 4 : ℝ) • x ∈ boundaryHalfBall (3 / 4) := by
  obtain ⟨h1, h2⟩ := hx
  refine ⟨?_, ?_⟩
  · rw [mem_ball, dist_zero_right] at h1 ⊢
    rw [norm_smul, Real.norm_eq_abs, abs_of_pos (by norm_num : (0 : ℝ) < 3 / 4)]
    linarith
  · change 0 < ((3 / 4 : ℝ) • x) (Fin.last 2)
    rw [PiLp.smul_apply, smul_eq_mul]
    exact mul_pos (by norm_num) h2

/-- `boundary_nondiv_quotient_boundary_c1`, with the representative's set containing the
fixed slab `boundaryC1Slab`. Same hypotheses and constants. -/
theorem boundary_nondiv_quotient_boundary_c1_slab {α lam cap M N : ℝ}
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
          (∀ x ∈ W, x (Fin.last 2) = 0 → v x = 0) ∧ boundaryC1Slab ⊆ W := by
  obtain ⟨E, hE, hdata⟩ := boundary_nondiv_quotient_unit_data hα hlam hlamcap hM hN
  obtain ⟨C, P, hC, hP, hboundary⟩ := boundary_c1_holder_slab hα hα1 hlam
    (hlam.le.trans hlamcap) hM (show 0 ≤ (1 + 15 * M) * N by positivity) hE
  refine ⟨C, P, hC, hP, ?_⟩
  intro A b z f hd i h hi hh hsmall
  exact hboundary _ _ _ _ (hdata A b z f hd i h hi hh hsmall)

/-- Tangential derivatives in the zero-trace boundary nondivergence problem are uniformly
`C^{1,α}` on the fixed upper slab (rescaled coordinates `y = (3/4)x`). -/
theorem boundary_nondiv_tangential_derivative_c1_holder {α lam cap M N : ℝ}
    (hα : 0 < α) (hα1 : α < 1) (hlam : 0 < lam) (hlamcap : lam ≤ cap)
    (hM : 0 ≤ M) (hN : 0 ≤ N) :
    ∃ K : ℝ, 0 < K ∧
      ∀ (A : EuclideanSpace ℝ (Fin 3) →
          EuclideanSpace ℝ (Fin 3) →L[ℝ] EuclideanSpace ℝ (Fin 3))
        (b : EuclideanSpace ℝ (Fin 3) → EuclideanSpace ℝ (Fin 3))
        (z f : EuclideanSpace ℝ (Fin 3) → ℝ),
        BoundaryNondivClosedData α lam cap M N A b z f →
        ∀ i : Fin 3, i ≠ Fin.last 2 →
          DifferentiableOn ℝ (fun x => fderiv ℝ z ((3 / 4 : ℝ) • x) (EuclideanSpace.single i 1))
            boundaryC1UpperSlab ∧
          (∀ x ∈ boundaryC1UpperSlab,
            ‖∇ (fun x => fderiv ℝ z ((3 / 4 : ℝ) • x) (EuclideanSpace.single i 1)) x‖ ≤ K) ∧
          ∀ x ∈ boundaryC1UpperSlab, ∀ y ∈ boundaryC1UpperSlab,
            ‖∇ (fun x => fderiv ℝ z ((3 / 4 : ℝ) • x) (EuclideanSpace.single i 1)) x -
              ∇ (fun x => fderiv ℝ z ((3 / 4 : ℝ) • x) (EuclideanSpace.single i 1)) y‖ ≤
                K * dist x y ^ α := by
  obtain ⟨C, P, hC, hP, hq⟩ := boundary_nondiv_quotient_boundary_c1_slab hα hα1 hlam hlamcap hM hN
  refine ⟨max C P, lt_max_of_lt_left hC, ?_⟩
  intro A b z f hd i hi
  set U := boundaryC1UpperSlab
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
  choose W v hWo _ _ hv hve _ hvb hvh _ hslab using
    fun n => hq A b z f hd i (s n) hi (hs0 n) (hs1 n)
  have hzC : ContDiffOn ℝ 1 z (closure (boundaryHalfBall 1)) := hd.solution.contDiff
  have hzc : ContinuousOn z (boundaryHalfBall 1) := hzC.continuousOn.mono subset_closure
  have hUW : ∀ n, U ⊆ W n ∩ {x | 0 < x (Fin.last 2)} := by
    rintro n x ⟨hx1, hx2⟩
    exact ⟨hslab n hx1, hx2⟩
  have hmem0 : ∀ x ∈ U, (3 / 4 : ℝ) • x ∈ boundaryHalfBall 1 := fun x hx =>
    boundaryHalfBall_mono (by norm_num)
      (boundary_nondiv_scale_mem (boundaryC1UpperSlab_subset hx))
  have hmem : ∀ n, ∀ x ∈ U,
      (3 / 4 : ℝ) • x + s n • EuclideanSpace.single i 1 ∈ boundaryHalfBall 1 := by
    intro n x hx
    have h1 := boundary_nondiv_scale_mem (boundaryC1UpperSlab_subset hx)
    have h2 := boundary_nondiv_segment_mem_halfBall (r := 3 / 4) (R := 1) (h := s n) hi
      (by linarith [hs1 n]) h1 (t := 1) (by simp)
    simpa only [one_smul] using h2
  have heq : ∀ n, ∀ x ∈ U,
      v n x = coordinateDifferenceQuotient i (s n) z ((3 / 4 : ℝ) • x) := by
    intro n
    have hae : v n =ᵐ[volume.restrict U]
        (fun x => coordinateDifferenceQuotient i (s n) z ((3 / 4 : ℝ) • x)) :=
      ae_restrict_of_ae_restrict_of_subset (hUW n) (hve n)
    have hc1 : ContinuousOn (v n) U :=
      (hv n).continuousOn.mono (fun x hx => (hUW n hx).1)
    have hc2 : ContinuousOn
        (fun x => coordinateDifferenceQuotient i (s n) z ((3 / 4 : ℝ) • x)) U := by
      have hsc : Continuous fun x : EuclideanSpace ℝ (Fin 3) => (3 / 4 : ℝ) • x :=
        continuous_const_smul _
      unfold coordinateDifferenceQuotient
      exact ((hzc.comp (hsc.add continuous_const).continuousOn (hmem n)).sub
        (hzc.comp hsc.continuousOn hmem0)).const_smul (s n)⁻¹
    exact fun x hx => Measure.eqOn_open_of_ae_eq hae isOpen_boundaryC1UpperSlab hc1 hc2 hx
  have hzd : ∀ x ∈ U, DifferentiableAt ℝ z ((3 / 4 : ℝ) • x) := fun x hx =>
    (hzC.differentiableOn one_ne_zero).differentiableAt
      (mem_of_superset ((isOpen_boundaryHalfBall 1).mem_nhds (hmem0 x hx)) subset_closure)
  have hlim : ∀ x ∈ U, Tendsto (fun n => v n x) atTop
      (𝓝 (fderiv ℝ z ((3 / 4 : ℝ) • x) (EuclideanSpace.single i 1))) := by
    intro x hx
    have ht := (tendsto_coordinateDifferenceQuotient_of_differentiableAt (hzd x hx) i).comp hsT
    exact ht.congr' (Eventually.of_forall fun n => (heq n x hx).symm)
  have hK : ∀ n, ∀ x ∈ U, ‖∇ (v n) x‖ ≤ max C P := fun n x hx =>
    (hvb n x (hUW n hx).1).trans (le_max_right _ _)
  have hH : ∀ n, ∀ x ∈ U, ∀ y ∈ U, ‖∇ (v n) x - ∇ (v n) y‖ ≤ max C P * dist x y ^ α :=
    fun n x hx y hy => (hvh n x (hUW n hx).1 y (hUW n hy).1).trans
      (mul_le_mul_of_nonneg_right (le_max_left _ _) (Real.rpow_nonneg dist_nonneg _))
  exact c1_holder_of_tendsto_gradient isOpen_boundaryC1UpperSlab convex_boundaryC1UpperSlab hα
    (le_max_of_le_left hC.le) v _
    (fun n => ((hv n).differentiableOn one_ne_zero).mono (fun x hx => (hUW n hx).1)) hK hH hlim

end LiquidDrop

module

public import NoCompromise.Elliptic.BoundaryNondivC2

@[expose] public section

/-!
# Boundary C²,α for the divergence-form Dirichlet problem (zero trace, C¹,α solution)

`div(A∇w) = div G` weakly is the nondivergence equation with drift `div A` and
right side `div G`. For a solution already known to be C¹,α up to the flat face
(the conclusion of `thm:boundary-C1a`) with zero trace, the slab estimate
`boundary_nondiv_c2_holder` for the nondivergence problem applies.
-/

noncomputable section
open MeasureTheory Filter Metric Set InnerProductSpace
open scoped ENNReal NNReal Topology Gradient RealInnerProductSpace
namespace LiquidDrop

/-- Blueprint `thm:boundary-C2a`, zero-trace case for a C¹,α solution: C²,α
estimates on the fixed slab `boundaryNondivC2Slab`, with a constant chosen from
`α, lam, cap, M, N` before the data. -/
theorem boundary_c2a_holder_zero_trace {α lam cap M N : ℝ}
    (hα : 0 < α) (hα1 : α < 1) (hlam : 0 < lam) (hlamcap : lam ≤ cap)
    (hM : 0 ≤ M) (hN : 0 ≤ N) :
    ∃ C > 0, ∀ (A : EuclideanSpace ℝ (Fin 3) → EuclideanSpace ℝ (Fin 3) →L[ℝ]
        EuclideanSpace ℝ (Fin 3))
      (G : EuclideanSpace ℝ (Fin 3) → EuclideanSpace ℝ (Fin 3))
      (w : EuclideanSpace ℝ (Fin 3) → ℝ),
      HasC1HolderOn α A (closure (boundaryHalfBall 1)) →
      HasC1HolderOn α G (closure (boundaryHalfBall 1)) →
      HasC1HolderOn α w (closure (boundaryHalfBall 1)) →
      nondivC1HolderNorm α A (closure (boundaryHalfBall 1)) ≤ M →
      nondivC1HolderNorm α w (closure (boundaryHalfBall 1)) +
        3 * nondivC1HolderNorm α G (closure (boundaryHalfBall 1)) ≤ N →
      (∀ x ∈ closure (boundaryHalfBall 1), ‖A x‖ ≤ cap) →
      (∀ x ∈ closure (boundaryHalfBall 1), ∀ v, lam * ‖v‖ ^ 2 ≤ inner ℝ v (A x v)) →
      (∀ φ : EuclideanSpace ℝ (Fin 3) → ℝ, ContDiff ℝ (⊤ : ℕ∞) φ → HasCompactSupport φ →
        tsupport φ ⊆ boundaryHalfBall 1 →
        (∫ x, inner ℝ (A x (gradient w x)) (gradient φ x)) =
          ∫ x, inner ℝ (G x) (gradient φ x)) →
      (∀ x ∈ closure (boundaryHalfBall 1), x (Fin.last 2) = 0 → w x = 0) →
      ContDiffOn ℝ 2 w boundaryNondivC2Slab ∧
      ∀ i j : Fin 3,
        (∀ x ∈ boundaryNondivC2Slab, |boundaryNeumannC2Entry w x i j| ≤ C) ∧
        ∀ x ∈ boundaryNondivC2Slab, ∀ y ∈ boundaryNondivC2Slab,
          |boundaryNeumannC2Entry w x i j - boundaryNeumannC2Entry w y i j| ≤
            C * dist x y ^ α := by
  obtain ⟨C, hC, hreg⟩ := boundary_nondiv_c2_holder hα hα1 hlam hlamcap
    (by positivity : (0 : ℝ) ≤ 3 * M) hN
  refine ⟨C, hC, ?_⟩
  intro A G w hA hG hw hAn hN' hcap hell he htrace
  have hU := isOpen_boundaryHalfBall (1 : ℝ)
  obtain ⟨hdA, hdAb⟩ := nondivCoefficientDivergence_holder hA
  obtain ⟨hdiv, hdivb⟩ := nondiv_holder_comp_clm hG.derivative_holder boundaryNeumannC2Trace
  have heqd : (fun x => boundaryNeumannC2Trace (fderiv ℝ G x)) = divergenceN G := by
    funext x
    exact boundaryNeumannC2Trace_apply _
  rw [heqd] at hdiv hdivb
  have hdivN : holderNorm α (divergenceN G) (closure (boundaryHalfBall 1)) ≤
      3 * nondivC1HolderNorm α G (closure (boundaryHalfBall 1)) :=
    hdivb.trans (mul_le_mul boundaryNeumannC2Trace_norm hG.derivative_norm_le
      hG.derivative_holder.norm_nonneg (by norm_num))
  have hAU : ContDiffOn ℝ 1 A (boundaryHalfBall 1) := hA.contDiff.mono subset_closure
  have hGU : ContDiffOn ℝ 1 G (boundaryHalfBall 1) := hG.contDiff.mono subset_closure
  have hwU : ContDiffOn ℝ 1 w (boundaryHalfBall 1) := hw.contDiff.mono subset_closure
  have hbU : ContinuousOn (nondivCoefficientDivergence A) (boundaryHalfBall 1) :=
    (hdA.nondiv_continuousOn hα).mono subset_closure
  have hfU : ContinuousOn (divergenceN G) (boundaryHalfBall 1) :=
    (hdiv.nondiv_continuousOn hα).mono subset_closure
  have hweak : IsWeakNondivergenceEquationOn A (nondivCoefficientDivergence A) w
      (divergenceN G) (boundaryHalfBall 1) := by
    apply (isWeakNondivergenceEquationOn_iff_divergence hU hAU hbU hwU hfU).mpr
    intro φ hφ hcφ hsφ
    have hsrc : nondivDivergenceSource A (nondivCoefficientDivergence A) w (divergenceN G) =
        divergenceN G := by
      funext x
      simp only [nondivDivergenceSource, sub_self, inner_zero_left, add_zero]
    rw [hsrc, he φ hφ hcφ hsφ]
    exact boundary_neumann_c2_integral_divergence hU hGU (hφ.of_le (by simp)) hcφ hsφ
  have d : BoundaryNondivClosedData α lam cap (3 * M) N A (nondivCoefficientDivergence A) w
      (divergenceN G) :=
    { coefficient := hA
      drift := hdA
      solution := hw
      source := hdiv
      coefficient_norm := hAn.trans (by linarith)
      drift_norm := hdAb.trans (by
        have : ((3 : ℕ) : ℝ) = 3 := by norm_num
        rw [this]
        exact mul_le_mul_of_nonneg_left hAn (by norm_num))
      coefficient_bound := hcap
      elliptic := hell
      equation := hweak
      trace_zero := htrace
      norm_bound := by linarith }
  obtain ⟨h2, hent⟩ := hreg A _ w _ d
  exact ⟨h2, fun i j => ⟨(hent i j).1, (hent i j).2.1⟩⟩

end LiquidDrop

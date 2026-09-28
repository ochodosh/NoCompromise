import NoCompromise.Elliptic.BoundaryNeumannC2HolderLift
import NoCompromise.Elliptic.BoundaryNeumannC2HolderDatum

/-!
# Boundary Neumann C²,α regularity with the literal data classes

The second assertion of `thm:boundary-neumann` with `A ∈ C^{2,α}`, `f ∈ C^{1,α}`,
`h ∈ C^{2,α}` on the closed unit disk/ball, and a constant depending only on
`α`, `λ`, the data bound `K` and the energy bound `M`. All lift-step and C¹-level
hypotheses of `boundary_neumann_c2_holder_inhom_of_lift` are derived from these
data classes.
-/

noncomputable section
open Set Metric InnerProductSpace MeasureTheory
open scoped Gradient
namespace LiquidDrop
set_option maxSynthPendingDepth 8

/-- Pointwise and Hölder bounds from a bound on the C⁰,α norm. -/
lemma boundaryNeumannData_holder_bounds {E F : Type*} [NormedAddCommGroup E]
    [NormedAddCommGroup F] {α K : ℝ} {f : E → F} {D : Set E}
    (hf : HasFiniteHolderNormOn α f D) (hK : holderNorm α f D ≤ K) :
    (∀ x ∈ D, ‖f x‖ ≤ K) ∧ ∀ x ∈ D, ∀ y ∈ D, ‖f x - f y‖ ≤ K * dist x y ^ α := by
  refine ⟨fun x hx => (hf.nondiv_norm_le hx).trans hK, fun x hx y hy => ?_⟩
  rw [dist_eq_norm]
  have hs : holderSeminorm α f D ≤ K :=
    (le_add_of_nonneg_left (holderUniformNorm_nonneg hf.uniform_bounded)).trans hK
  exact (hf.nondiv_norm_sub_le hx hy).trans
    (mul_le_mul_of_nonneg_right hs (Real.rpow_nonneg (norm_nonneg _) α))

/-- Pointwise and Hölder bounds of a C¹,α function and of its gradient. -/
lemma boundaryNeumannData_c1_bounds {n : ℕ} {α K : ℝ}
    {u : EuclideanSpace ℝ (Fin n) → ℝ} {D : Set (EuclideanSpace ℝ (Fin n))}
    (hu : HasC1HolderOn α u D) (hK : nondivC1HolderNorm α u D ≤ K) :
    (∀ x ∈ D, ‖u x‖ ≤ K) ∧ (∀ x ∈ D, ∀ y ∈ D, ‖u x - u y‖ ≤ K * dist x y ^ α) ∧
      (∀ x ∈ D, ‖gradient u x‖ ≤ K) ∧
      ∀ x ∈ D, ∀ y ∈ D, ‖gradient u x - gradient u y‖ ≤ K * dist x y ^ α := by
  obtain ⟨h1, h2⟩ := boundaryNeumannData_holder_bounds hu.function_holder
    (hu.function_norm_le.trans hK)
  obtain ⟨hg, hgn⟩ := hu.gradient_holder
  obtain ⟨h3, h4⟩ := boundaryNeumannData_holder_bounds hg
    (hgn.trans (hu.derivative_norm_le.trans hK))
  exact ⟨h1, h2, h3, h4⟩

/-- **Boundary Neumann C²,α estimate with literal data classes.** `A ∈ C^{2,α}`,
`f ∈ C^{1,α}`, `h ∈ C^{2,α}` with norms at most `K`; the constant depends only on
`α`, `λ`, `K`, `M`. -/
theorem boundary_neumann_c2_holder_inhom_holder_data {α lam K M : ℝ}
    (hα : 0 < α) (hα1 : α < 1) (hlam : 0 < lam) (hK : 0 ≤ K) (hM : 0 ≤ M) :
    ∃ Cb : ℝ, 0 < Cb ∧
      ∀ (A : EuclideanSpace ℝ (Fin 3) → EuclideanSpace ℝ (Fin 3) →L[ℝ]
          EuclideanSpace ℝ (Fin 3))
        (F : EuclideanSpace ℝ (Fin 3) → EuclideanSpace ℝ (Fin 3))
        (z f : EuclideanSpace ℝ (Fin 3) → ℝ)
        (h : EuclideanSpace ℝ (Fin 2) → ℝ)
        (O : Set (EuclideanSpace ℝ (Fin 3))) (U : Set (EuclideanSpace ℝ (Fin 2))),
        IsOpen O → closedBall 0 1 ⊆ O → ContDiffOn ℝ 2 A O →
        HasC1HolderOn α A (closedBall 0 1) → HasC1HolderOn α (fderiv ℝ A) (closedBall 0 1) →
        nondivC1HolderNorm α A (closedBall 0 1) ≤ K →
        nondivC1HolderNorm α (fderiv ℝ A) (closedBall 0 1) ≤ K →
        (∀ x ∈ closure (boundaryHalfBall 1), ∀ ξ,
          lam * ‖ξ‖ ^ 2 ≤ inner ℝ (A x ξ) ξ) →
        (∀ x ∈ closure (boundaryHalfBall 1), x (Fin.last 2) = 0 →
          ∀ i : Fin 3, i ≠ Fin.last 2 →
            A x (EuclideanSpace.single i 1) (Fin.last 2) = 0 ∧
            A x (EuclideanSpace.single (Fin.last 2) 1) i = 0) →
        IsOpen U → closedBall 0 1 ⊆ U →
        (∀ y ∈ U, lam ≤ boundaryNeumannNormalCoefficient A y) →
        ContDiffOn ℝ 2 h U →
        HasC1HolderOn α h (closedBall 0 1) → HasC1HolderOn α (fderiv ℝ h) (closedBall 0 1) →
        nondivC1HolderNorm α h (closedBall 0 1) ≤ K →
        nondivC1HolderNorm α (fderiv ℝ h) (closedBall 0 1) ≤ K →
        ContDiffOn ℝ 1 f O → HasC1HolderOn α f (closedBall 0 1) →
        nondivC1HolderNorm α f (closedBall 0 1) ≤ K →
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
          ContDiffOn ℝ 2 u (boundaryHalfBall (1 / 4 * (3 / 8))) ∧
          z =ᵐ[volume.restrict (boundaryHalfBall (1 / 4 * (3 / 8)))] u ∧
          F =ᵐ[volume.restrict (boundaryHalfBall (1 / 4 * (3 / 8)))] gradient u ∧
          (∀ i j : Fin 3, ∃ D : EuclideanSpace ℝ (Fin 3) → ℝ,
            EqOn D (fun x => boundaryNeumannC2Entry u x i j)
              (boundaryHalfBall (1 / 4 * (3 / 8))) ∧
            ContinuousOn D (closure (boundaryHalfBall (1 / 4 * (3 / 8)))) ∧
            (∀ x ∈ closure (boundaryHalfBall (1 / 4 * (3 / 8))), |D x| ≤ Cb) ∧
            ∀ x ∈ closure (boundaryHalfBall (1 / 4 * (3 / 8))),
              ∀ y ∈ closure (boundaryHalfBall (1 / 4 * (3 / 8))),
                |D x - D y| ≤ Cb * dist x y ^ α) ∧
          (∀ y : EuclideanSpace ℝ (Fin 2), graphBaseEmbedding y ∈ ball 0 (1 / 2 : ℝ) →
            A (graphBaseEmbedding y) (gradient u (graphBaseEmbedding y)) (Fin.last 2) =
              h y) := by
  obtain ⟨Ql, hQl, hlift⟩ := boundaryNeumannLift_c2_holder (K := K) hα hα1.le hlam
  obtain ⟨c, hc, hdat⟩ := boundaryNeumannInhomDatum_hasC1HolderOn hα hα1.le
  set Q : ℝ := K + Ql + (c * K + K + 3 * K * Ql) with hQdef
  have hQ : 0 ≤ Q := by positivity
  have hQlQ : Ql ≤ Q := by
    have : 0 ≤ c * K + K + 3 * K * Ql := by positivity
    linarith
  have hKQ : K ≤ Q := by
    have : 0 ≤ c * K + K + 3 * K * Ql := by positivity
    linarith
  have hHQ' : c * K + K + 3 * K * Ql ≤ Q := by linarith
  obtain ⟨Cb, hCb, hmain⟩ :=
    boundary_neumann_c2_holder_inhom_of_lift (cap := K) (HA := K) (K := K) hα hα1 hlam hK hK
      hK hM hQ
  refine ⟨Cb, hCb, ?_⟩
  intro A F z f h O U hO hOsub hA2 hA hA' hAK hAK' hell hcross hU hUsub hlow hh2 hh hh' hhK
    hhK' hf1 hf hfK hz hE hweak
  obtain ⟨hb2, hb, hbK, hb', hbK'⟩ :=
    boundaryNeumannNormalCoefficient_c2_holder hα.le hO hOsub hA2 hA hA' hAK hAK'
  set V : Set (EuclideanSpace ℝ (Fin 2)) := U ∩ graphBaseEmbedding ⁻¹' O with hVdef
  have hV : IsOpen V := hU.inter (hO.preimage graphBaseEmbedding.continuous)
  have hVsub : closedBall (0 : EuclideanSpace ℝ (Fin 2)) 1 ⊆ V :=
    fun y hy => ⟨hUsub hy, hOsub (graphBaseEmbedding_mapsTo_closedBall hy)⟩
  have hh2V : ContDiffOn ℝ 2 h V := hh2.mono inter_subset_left
  have hb2V : ContDiffOn ℝ 2 (boundaryNeumannNormalCoefficient A) V :=
    hb2.mono inter_subset_right
  obtain ⟨hq2, hqH, hqQ, hDqH, hDqQ, hEh, hEb⟩ := hlift h (boundaryNeumannNormalCoefficient A)
    V hV hVsub hh2V hb2V (fun y hy => hlow y hy.1) hh hh' hb hb' hhK hhK' hbK hbK'
  obtain ⟨hHH, hHQ⟩ := hdat K Ql A f h O U hO hOsub (hA2.of_le (by norm_num)) hA hAK hf1 hf
    hfK hU hUsub (hh2.of_le (by norm_num)) hh hhK hq2 hDqH hDqQ
  have hclosed : closure (boundaryHalfBall 1) ⊆ closedBall (0 : EuclideanSpace ℝ (Fin 3)) 1 :=
    closure_minimal (inter_subset_left.trans ball_subset_closedBall) isClosed_closedBall
  have hS : closure (boundaryHalfBall (1 / 4 : ℝ)) ⊆
      closedBall (0 : EuclideanSpace ℝ (Fin 3)) 1 :=
    (closure_mono (boundaryHalfBall_mono (by norm_num))).trans hclosed
  obtain ⟨hAS, hASn⟩ := hA.mono hS
  obtain ⟨hAb, hAh⟩ := boundaryNeumannData_holder_bounds hA.function_holder
    (hA.function_norm_le.trans hAK)
  obtain ⟨hfb, hfh, -, -⟩ := boundaryNeumannData_c1_bounds hf hfK
  obtain ⟨hhb, -, hhg, hhgh⟩ := boundaryNeumannData_c1_bounds hh hhK
  obtain ⟨hbb, -, hbg, hbgh⟩ := boundaryNeumannData_c1_bounds hb hbK
  have hpow : ∀ x y : EuclideanSpace ℝ (Fin 3), 0 ≤ dist x y ^ α :=
    fun x y => Real.rpow_nonneg dist_nonneg α
  exact hmain A F z f h (hA2.continuousOn.mono (hclosed.trans hOsub))
    (fun x hx => hAb x (hclosed hx)) hell
    (fun x hx y hy => hAh x (hclosed hx) y (hclosed hy)) hcross
    ⟨V, hV, hVsub, hh2V.of_le (by norm_num), hb2V.of_le (by norm_num),
      fun y hy => hlow y hy.1⟩
    hhb hbb hhg hbg hhgh hbgh (hf1.continuousOn.mono (hclosed.trans hOsub))
    (fun x hx => hfb x (hclosed hx)) (fun x hx y hy => hfh x (hclosed hx) y (hclosed hy))
    hz hE hweak hAS (hASn.trans (hAK.trans hKQ)) hq2 hqH (hqQ.trans hQlQ)
    (fun i j x hx y hy => (hEh i j x hx y hy).trans
      (mul_le_mul_of_nonneg_right hQlQ (hpow x y)))
    (fun i j x hx => (hEb i j x hx).trans hQlQ) hHH (hHQ.trans hHQ')

end LiquidDrop

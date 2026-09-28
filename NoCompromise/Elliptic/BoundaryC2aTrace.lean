import NoCompromise.Elliptic.BoundaryC2aZeroTrace
import NoCompromise.Elliptic.BoundaryNondivC2TraceData

/-!
# Boundary C²,α for the divergence-form Dirichlet problem (nonzero C²,α trace)

`div(A∇w) = div G` weakly is the nondivergence equation with drift `div A` and
right side `div G`. For a nonzero trace given by a C²,α extension `φ`, the nonzero
trace slab estimate `boundary_nondiv_c2_holder_trace` applies: `w - φ` solves the
nondivergence equation with right side `div G - Lφ`, `Lφ` the classical
nondivergence operator of `φ`, which is C⁰,α with an explicit bound, and the
second derivatives of `φ` on the slab are controlled by the C¹,α norm of `∇φ`.

The reduction goes through the nondivergence form rather than through the field
`G - A∇φ`: the C¹,α hypothesis on `G` concerns its ambient derivative on the closed
half ball, and `G` is not assumed ambient-differentiable at the boundary points,
so the ambient derivative of `G - A∇φ` need not be the difference of derivatives there.
-/

noncomputable section
open MeasureTheory Filter Metric Set InnerProductSpace
open scoped ENNReal NNReal Topology Gradient RealInnerProductSpace
namespace LiquidDrop
set_option maxSynthPendingDepth 8

/-- The fixed bilinear pairing `(T, S) ↦ Σᵢ Σⱼ (T eⱼ)ᵢ (S eᵢ)ⱼ` of two operators. -/
def boundaryC2aHessianPairing :
    (EuclideanSpace ℝ (Fin 3) →L[ℝ] EuclideanSpace ℝ (Fin 3)) →L[ℝ]
      (EuclideanSpace ℝ (Fin 3) →L[ℝ] EuclideanSpace ℝ (Fin 3)) →L[ℝ] ℝ :=
  ∑ i : Fin 3, ∑ j : Fin 3,
    (ContinuousLinearMap.mul ℝ ℝ).bilinearComp
      ((EuclideanSpace.proj i) ∘L
        ContinuousLinearMap.apply ℝ (EuclideanSpace ℝ (Fin 3)) (EuclideanSpace.single j 1))
      ((EuclideanSpace.proj j) ∘L
        ContinuousLinearMap.apply ℝ (EuclideanSpace ℝ (Fin 3)) (EuclideanSpace.single i 1))

lemma boundaryC2aHessianPairing_apply
    (T S : EuclideanSpace ℝ (Fin 3) →L[ℝ] EuclideanSpace ℝ (Fin 3)) :
    boundaryC2aHessianPairing T S =
      ∑ i : Fin 3, ∑ j : Fin 3,
        T (EuclideanSpace.single j 1) i * S (EuclideanSpace.single i 1) j := by
  simp [boundaryC2aHessianPairing]

lemma boundaryC2aHessianPairing_norm : ‖boundaryC2aHessianPairing‖ ≤ 9 := by
  apply ContinuousLinearMap.opNorm_le_bound₂ _ (by norm_num)
  intro T S
  rw [boundaryC2aHessianPairing_apply, Real.norm_eq_abs]
  calc
    _ ≤ ∑ _i : Fin 3, ∑ _j : Fin 3, ‖T‖ * ‖S‖ := by
      refine (Finset.abs_sum_le_sum_abs _ _).trans (Finset.sum_le_sum fun i _ => ?_)
      refine (Finset.abs_sum_le_sum_abs _ _).trans (Finset.sum_le_sum fun j _ => ?_)
      rw [abs_mul]
      exact mul_le_mul (boundary_neumann_c2_matrix_entry_bound T i j)
        (boundary_neumann_c2_matrix_entry_bound S j i) (abs_nonneg _) (norm_nonneg _)
    _ = 9 * ‖T‖ * ‖S‖ := by
      simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
      push_cast
      ring

/-- The second coordinate derivative `∂ᵢ(∂ⱼφ)` is the `j`-th component of the derivative
of `∇φ` in direction `eᵢ`, wherever `∇φ` is differentiable. -/
lemma boundary_c2a_entry_eq_gradient {φ : EuclideanSpace ℝ (Fin 3) → ℝ}
    {x : EuclideanSpace ℝ (Fin 3)} (hd : DifferentiableAt ℝ (gradient φ) x) (i j : Fin 3) :
    boundaryNeumannC2Entry φ x i j =
      fderiv ℝ (gradient φ) x (EuclideanSpace.single i 1) j := by
  unfold boundaryNeumannC2Entry
  have he' : (fun y => fderiv ℝ φ y (EuclideanSpace.single j 1)) =
      fun y => gradient φ y j :=
    funext fun y => (gradient_apply_eq_fderiv_single φ y j).symm
  rw [he']
  change fderiv ℝ ((EuclideanSpace.proj j) ∘ gradient φ) x _ = _
  rw [((EuclideanSpace.proj j).hasFDerivAt.comp x hd.hasFDerivAt).fderiv]
  rfl

/-- The classical nondivergence operator of `φ` is C⁰,α, with a bound by the C⁰,α norms
of `A`, `b`, `∇φ` and of the derivative of `∇φ`. -/
theorem boundary_c2a_classical_operator_holder {α : ℝ}
    {A : EuclideanSpace ℝ (Fin 3) → EuclideanSpace ℝ (Fin 3) →L[ℝ]
      EuclideanSpace ℝ (Fin 3)}
    {b : EuclideanSpace ℝ (Fin 3) → EuclideanSpace ℝ (Fin 3)}
    {φ : EuclideanSpace ℝ (Fin 3) → ℝ} {K : Set (EuclideanSpace ℝ (Fin 3))}
    (hA : HasFiniteHolderNormOn α A K) (hb : HasFiniteHolderNormOn α b K)
    (hg : HasC1HolderOn α (gradient φ) K)
    (hd : ∀ x ∈ K, DifferentiableAt ℝ (gradient φ) x) :
    HasFiniteHolderNormOn α (nondivClassicalOperator A b φ) K ∧
      holderNorm α (nondivClassicalOperator A b φ) K ≤
        27 * holderNorm α A K * holderNorm α (fderiv ℝ (gradient φ)) K +
          3 * holderNorm α b K * holderNorm α (gradient φ) K := by
  obtain ⟨hH, hHb⟩ := nondiv_holder_bilinear hA hg.derivative_holder boundaryC2aHessianPairing
  obtain ⟨hI, hIb⟩ := nondiv_holder_inner hb hg.function_holder
  obtain ⟨hS, hSb⟩ := schauder_holder_add hH hI
  have heq : EqOn (nondivClassicalOperator A b φ)
      (fun x => boundaryC2aHessianPairing (A x) (fderiv ℝ (gradient φ) x) +
        inner ℝ (b x) (gradient φ x)) K := by
    intro x hx
    simp only [nondivClassicalOperator, boundaryC2aHessianPairing_apply]
    congr 1
    refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
    rw [← boundary_c2a_entry_eq_gradient (hd x hx) i j]
    rfl
  obtain ⟨hc, hce⟩ := hS.congr_eqOn heq
  refine ⟨hc, hce.trans_le (hSb.trans (add_le_add (hHb.trans ?_) hIb))⟩
  have h := mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right
    (mul_le_mul_of_nonneg_left boundaryC2aHessianPairing_norm (by norm_num : (0 : ℝ) ≤ 3))
    hA.norm_nonneg) hg.derivative_holder.norm_nonneg
  linarith

/-- Blueprint `thm:boundary-C2a` with a nonzero C²,α trace: C²,α estimates on the fixed
slab `boundaryNondivC2Slab` for a C¹,α weak solution of `div(A∇w) = div G` whose trace on
the flat face is that of a C²,α extension `φ`, with a constant chosen from
`α, lam, cap, M, N` before the data. -/
theorem boundary_c2a_holder_trace {α lam cap M N : ℝ}
    (hα : 0 < α) (hα1 : α < 1) (hlam : 0 < lam) (hlamcap : lam ≤ cap)
    (hM : 0 ≤ M) (hN : 0 ≤ N) :
    ∃ C > 0, ∀ (A : EuclideanSpace ℝ (Fin 3) → EuclideanSpace ℝ (Fin 3) →L[ℝ]
        EuclideanSpace ℝ (Fin 3))
      (G : EuclideanSpace ℝ (Fin 3) → EuclideanSpace ℝ (Fin 3))
      (w φ : EuclideanSpace ℝ (Fin 3) → ℝ) (V : Set (EuclideanSpace ℝ (Fin 3))),
      IsOpen V → closure (boundaryHalfBall 1) ⊆ V →
      ContDiffOn ℝ 2 φ V →
      HasC1HolderOn α A (closure (boundaryHalfBall 1)) →
      HasC1HolderOn α G (closure (boundaryHalfBall 1)) →
      HasC1HolderOn α w (closure (boundaryHalfBall 1)) →
      (∀ x ∈ closure (boundaryHalfBall 1), DifferentiableAt ℝ w x) →
      HasC1HolderOn α φ (closure (boundaryHalfBall 1)) →
      HasC1HolderOn α (gradient φ) (closure (boundaryHalfBall 1)) →
      nondivC1HolderNorm α A (closure (boundaryHalfBall 1)) ≤ M →
      nondivC1HolderNorm α w (closure (boundaryHalfBall 1)) +
        nondivC1HolderNorm α φ (closure (boundaryHalfBall 1)) +
        nondivC1HolderNorm α (gradient φ) (closure (boundaryHalfBall 1)) +
        nondivC1HolderNorm α G (closure (boundaryHalfBall 1)) ≤ N →
      (∀ x ∈ closure (boundaryHalfBall 1), ‖A x‖ ≤ cap) →
      (∀ x ∈ closure (boundaryHalfBall 1), ∀ v, lam * ‖v‖ ^ 2 ≤ inner ℝ v (A x v)) →
      (∀ ψ : EuclideanSpace ℝ (Fin 3) → ℝ, ContDiff ℝ (⊤ : ℕ∞) ψ → HasCompactSupport ψ →
        tsupport ψ ⊆ boundaryHalfBall 1 →
        (∫ x, inner ℝ (A x (gradient w x)) (gradient ψ x)) =
          ∫ x, inner ℝ (G x) (gradient ψ x)) →
      (∀ x ∈ closure (boundaryHalfBall 1), x (Fin.last 2) = 0 → w x = φ x) →
      ContDiffOn ℝ 2 w boundaryNondivC2Slab ∧
      ∀ i j : Fin 3,
        (∀ x ∈ boundaryNondivC2Slab, |boundaryNeumannC2Entry w x i j| ≤ C) ∧
        ∀ x ∈ boundaryNondivC2Slab, ∀ y ∈ boundaryNondivC2Slab,
          |boundaryNeumannC2Entry w x i j - boundaryNeumannC2Entry w y i j| ≤
            C * dist x y ^ α := by
  obtain ⟨C, hC, hreg⟩ := boundary_nondiv_c2_holder_trace hα hα1 hlam hlamcap
    (by positivity : (0 : ℝ) ≤ 3 * M) (by positivity : (0 : ℝ) ≤ 3 * N + 36 * M * N)
  refine ⟨C + N, by linarith, ?_⟩
  intro A G w φ V hV hKV hφ2 hA hG hw hwd hφ hgφ hAn hNb hcap hell he htrace
  have hU := isOpen_boundaryHalfBall (1 : ℝ)
  -- the drift `div A` and the right side `div G`
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
  have hdAM : holderNorm α (nondivCoefficientDivergence A) (closure (boundaryHalfBall 1)) ≤
      3 * M := hdAb.trans (by
        have : ((3 : ℕ) : ℝ) = 3 := by norm_num
        rw [this]
        exact mul_le_mul_of_nonneg_left hAn (by norm_num))
  -- the weak nondivergence equation for `w`
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
    intro ψ hψ hcψ hsψ
    have hsrc : nondivDivergenceSource A (nondivCoefficientDivergence A) w (divergenceN G) =
        divergenceN G := by
      funext x
      simp only [nondivDivergenceSource, sub_self, inner_zero_left, add_zero]
    rw [hsrc, he ψ hψ hcψ hsψ]
    exact boundary_neumann_c2_integral_divergence hU hGU (hψ.of_le (by simp)) hcψ hsψ
  -- the classical operator of `φ`
  have hgd : ∀ x ∈ closure (boundaryHalfBall 1), DifferentiableAt ℝ (gradient φ) x := by
    intro x hx
    have hDφ : ContDiffOn ℝ 1 (fderiv ℝ φ) V := hφ2.fderiv_of_isOpen hV (by norm_num)
    have hGφ : ContDiffOn ℝ 1 (gradient φ) V :=
      (toDual ℝ (EuclideanSpace ℝ (Fin 3))).symm.toContinuousLinearEquiv.contDiff
        |>.comp_contDiffOn hDφ
    exact (hGφ.contDiffAt (hV.mem_nhds (hKV hx))).differentiableAt one_ne_zero
  obtain ⟨hL, hLb⟩ := boundary_c2a_classical_operator_holder hA.function_holder hdA hgφ hgd
  have hwn := hw.norm_nonneg
  have hφn := hφ.norm_nonneg
  have hgn := hgφ.norm_nonneg
  have hGn := hG.norm_nonneg
  have hAM : holderNorm α A (closure (boundaryHalfBall 1)) ≤ M :=
    hA.function_norm_le.trans hAn
  have hDN : holderNorm α (fderiv ℝ (gradient φ)) (closure (boundaryHalfBall 1)) ≤ N :=
    hgφ.derivative_norm_le.trans (by linarith)
  have hgN : holderNorm α (gradient φ) (closure (boundaryHalfBall 1)) ≤ N :=
    hgφ.function_norm_le.trans (by linarith)
  have hLN : holderNorm α (nondivClassicalOperator A (nondivCoefficientDivergence A) φ)
      (closure (boundaryHalfBall 1)) ≤ 36 * M * N := by
    have h1 := mul_le_mul hAM hDN hgφ.derivative_holder.norm_nonneg hM
    have h2 := mul_le_mul hdAM hgN hgφ.function_holder.norm_nonneg (by positivity)
    nlinarith
  -- the second derivatives of `φ` on the slab
  have hSK : boundaryNondivC2Slab ⊆ closure (boundaryHalfBall 1) :=
    boundaryNondivC2Slab_subset.trans subset_closure
  have hP : ∀ i j : Fin 3,
      (∀ x ∈ boundaryNondivC2Slab, |boundaryNeumannC2Entry φ x i j| ≤ N) ∧
        ∀ x ∈ boundaryNondivC2Slab, ∀ y ∈ boundaryNondivC2Slab,
          |boundaryNeumannC2Entry φ x i j - boundaryNeumannC2Entry φ y i j| ≤
            N * dist x y ^ α := by
    intro i j
    constructor
    · intro x hx
      rw [boundary_c2a_entry_eq_gradient (hgd x (hSK hx))]
      exact (boundary_neumann_c2_matrix_entry_bound _ j i).trans
        ((hgφ.derivative_holder.nondiv_norm_le (hSK hx)).trans hDN)
    · intro x hx y hy
      rw [boundary_c2a_entry_eq_gradient (hgd x (hSK hx)),
        boundary_c2a_entry_eq_gradient (hgd y (hSK hy))]
      have hsub : fderiv ℝ (gradient φ) x (EuclideanSpace.single i 1) j -
          fderiv ℝ (gradient φ) y (EuclideanSpace.single i 1) j =
            (fderiv ℝ (gradient φ) x - fderiv ℝ (gradient φ) y)
              (EuclideanSpace.single i 1) j := by
        simp
      rw [hsub]
      refine (boundary_neumann_c2_matrix_entry_bound _ j i).trans ?_
      refine (hgφ.derivative_holder.nondiv_norm_sub_le (hSK hx) (hSK hy)).trans ?_
      rw [← dist_eq_norm]
      have hsem : holderSeminorm α (fderiv ℝ (gradient φ)) (closure (boundaryHalfBall 1)) ≤
          holderNorm α (fderiv ℝ (gradient φ)) (closure (boundaryHalfBall 1)) :=
        le_add_of_nonneg_left (holderUniformNorm_nonneg hgφ.derivative_holder.uniform_bounded)
      exact mul_le_mul_of_nonneg_right (hsem.trans hDN) (Real.rpow_nonneg dist_nonneg _)
  exact hreg A (nondivCoefficientDivergence A) w (divergenceN G) φ V N hV hKV hA hdA hw hdiv
    (hAn.trans (by linarith)) hdAM hcap hell hweak hwd hφ2 hφ hL htrace (by linarith) hP

end LiquidDrop

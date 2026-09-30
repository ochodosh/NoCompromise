module

public import NoCompromise.Elliptic.BoundaryNeumannSmoothTangential
public import NoCompromise.Elliptic.BoundaryNeumannC2Scaled
public import NoCompromise.Elliptic.BoundaryNeumannC2InhomFinite
public import NoCompromise.Elliptic.BoundaryNeumannC2HolderAlgebra
public import NoCompromise.Elliptic.BoundaryNeumannTangential
public import NoCompromise.Elliptic.BoundaryNeumannInhom
public import NoCompromise.Elliptic.BoundaryNeumannC2HolderLift

@[expose] public section

/-!
# First step of the smooth boundary Neumann iteration

Let `w` be C² on an open neighbourhood of the closed unit half ball, with Hessian
entries α-Hölder on the closed half ball, solving the homogeneous conormal problem
with C³ coefficient `A` and C³ vector datum `H`, vanishing cross coefficients,
`H₃ = 0` and `∂₃w = 0` on the flat face. For a tangential direction `i`, the
tangential derivative `∂ᵢw` solves the differentiated problem
(`boundary_neumann_smooth_tangential_equation`) with the datum
`∂ᵢH - (∂ᵢA)∇w`, which is C¹,α on the closed half ball of radius `1/2`. The
C²,α theorem at scale `1/2` then shows that `∂ᵢw` is C² on the half ball of
radius `1/2 · 3/8`, with bounded and α-Hölder second derivatives there: every
third derivative of `w` with at least one tangential index is bounded and
α-Hölder near the face.
-/

noncomputable section
open MeasureTheory Filter Metric Set InnerProductSpace
open scoped ENNReal Topology Gradient RealInnerProductSpace
namespace LiquidDrop
set_option maxSynthPendingDepth 8

/-- A real bilinear form on `ℝ³` is the sum of its coordinate entries times the
coordinate products. -/
lemma boundaryNeumannIterate_bilin_eq_sum
    (T : EuclideanSpace ℝ (Fin 3) →L[ℝ] EuclideanSpace ℝ (Fin 3) →L[ℝ] ℝ) :
    T = ∑ i, ∑ j, T (EuclideanSpace.single i 1) (EuclideanSpace.single j 1) •
      (EuclideanSpace.proj i : EuclideanSpace ℝ (Fin 3) →L[ℝ] ℝ).smulRight
        (EuclideanSpace.proj j : EuclideanSpace ℝ (Fin 3) →L[ℝ] ℝ) := by
  apply ContinuousLinearMap.coe_injective
  refine (EuclideanSpace.basisFun (Fin 3) ℝ).toBasis.ext fun i => ?_
  apply ContinuousLinearMap.coe_injective
  refine (EuclideanSpace.basisFun (Fin 3) ℝ).toBasis.ext fun j => ?_
  simp only [OrthonormalBasis.coe_toBasis, EuclideanSpace.basisFun_apply,
    ContinuousLinearMap.coe_coe]
  simp

/-- The operator norm of a real bilinear form on `ℝ³` is at most the sum of the
absolute values of its coordinate entries. -/
lemma boundaryNeumannIterate_bilin_norm_le
    (T : EuclideanSpace ℝ (Fin 3) →L[ℝ] EuclideanSpace ℝ (Fin 3) →L[ℝ] ℝ) :
    ‖T‖ ≤ ∑ i, ∑ j, |T (EuclideanSpace.single i 1) (EuclideanSpace.single j 1)| := by
  have hp : ∀ i : Fin 3, ‖(EuclideanSpace.proj i : EuclideanSpace ℝ (Fin 3) →L[ℝ] ℝ)‖ ≤ 1 :=
    fun i => ContinuousLinearMap.opNorm_le_bound _ zero_le_one fun x => by
      rw [one_mul]
      exact PiLp.norm_apply_le x i
  have hS : ∀ i j : Fin 3, ‖(EuclideanSpace.proj i : EuclideanSpace ℝ (Fin 3) →L[ℝ] ℝ).smulRight
      (EuclideanSpace.proj j : EuclideanSpace ℝ (Fin 3) →L[ℝ] ℝ)‖ ≤ 1 := by
    intro i j
    rw [ContinuousLinearMap.norm_smulRight_apply]
    exact mul_le_one₀ (hp i) (norm_nonneg _) (hp j)
  calc
    ‖T‖ = ‖∑ i, ∑ j, T (EuclideanSpace.single i 1) (EuclideanSpace.single j 1) •
        (EuclideanSpace.proj i : EuclideanSpace ℝ (Fin 3) →L[ℝ] ℝ).smulRight
          (EuclideanSpace.proj j : EuclideanSpace ℝ (Fin 3) →L[ℝ] ℝ)‖ :=
      congrArg _ (boundaryNeumannIterate_bilin_eq_sum T)
    _ ≤ ∑ i, ‖∑ j, T (EuclideanSpace.single i 1) (EuclideanSpace.single j 1) •
        (EuclideanSpace.proj i : EuclideanSpace ℝ (Fin 3) →L[ℝ] ℝ).smulRight
          (EuclideanSpace.proj j : EuclideanSpace ℝ (Fin 3) →L[ℝ] ℝ)‖ := norm_sum_le _ _
    _ ≤ ∑ i, ∑ j, ‖T (EuclideanSpace.single i 1) (EuclideanSpace.single j 1) •
        (EuclideanSpace.proj i : EuclideanSpace ℝ (Fin 3) →L[ℝ] ℝ).smulRight
          (EuclideanSpace.proj j : EuclideanSpace ℝ (Fin 3) →L[ℝ] ℝ)‖ :=
      Finset.sum_le_sum fun i _ => norm_sum_le _ _
    _ ≤ _ := Finset.sum_le_sum fun i _ => Finset.sum_le_sum fun j _ => by
      rw [norm_smul, Real.norm_eq_abs]
      exact mul_le_of_le_one_right (abs_nonneg _) (hS i j)

/-- C¹,α is preserved by composition with a fixed continuous linear map. -/
lemma boundaryNeumannIterate_hasC1HolderOn_clm {E F G : Type*}
    [NormedAddCommGroup E] [NormedSpace ℝ E]
    [NormedAddCommGroup F] [NormedSpace ℝ F] [NormedAddCommGroup G] [NormedSpace ℝ G]
    {α : ℝ} {u : E → F} {S O : Set E} (hO : IsOpen O) (hSO : S ⊆ O)
    (huO : ContDiffOn ℝ 1 u O) (hu : HasC1HolderOn α u S) (L : F →L[ℝ] G) :
    HasC1HolderOn α (fun x => L (u x)) S := by
  have hd : ∀ x ∈ S, DifferentiableAt ℝ u x := fun x hx =>
    (huO.differentiableOn one_ne_zero).differentiableAt (hO.mem_nhds (hSO hx))
  obtain ⟨h1, -⟩ := nondiv_holder_comp_clm hu.derivative_holder
    (ContinuousLinearMap.compL ℝ E F G L)
  obtain ⟨h2, -⟩ := boundaryNeumann_holder_congr h1
    (g := fderiv ℝ (fun x => L (u x))) (fun x hx => by
      have h := (L.hasFDerivAt.comp x (hd x hx).hasFDerivAt).fderiv
      exact h.symm)
  exact ⟨L.contDiff.comp_contDiffOn hu.contDiff,
    (nondiv_holder_comp_clm hu.function_holder L).1, h2⟩

/-- A C² function whose Hessian entries are α-Hölder on a compact convex set
inside its open domain has C¹,α derivative there. -/
lemma boundaryNeumannIterate_fderiv_hasC1HolderOn {α : ℝ} (hα : 0 ≤ α) (hα1 : α ≤ 1)
    {K U : Set (EuclideanSpace ℝ (Fin 3))} (hK : IsCompact K) (hcK : Convex ℝ K)
    (hU : IsOpen U) (hKU : K ⊆ U) {w : EuclideanSpace ℝ (Fin 3) → ℝ}
    (hw : ContDiffOn ℝ 2 w U)
    (hhol : ∃ C, ∀ i j : Fin 3, ∀ x ∈ K, ∀ y ∈ K,
      |boundaryNeumannC2Entry w x i j - boundaryNeumannC2Entry w y i j| ≤ C * dist x y ^ α) :
    HasC1HolderOn α (fderiv ℝ w) K := by
  have hD1 : ContDiffOn ℝ 1 (fderiv ℝ w) U := hw.fderiv_of_isOpen hU (by norm_num)
  have hd : ∀ x ∈ U, DifferentiableAt ℝ (fderiv ℝ w) x := fun x hx =>
    (hD1.differentiableOn one_ne_zero).differentiableAt (hU.mem_nhds hx)
  obtain ⟨C, hC⟩ := hhol
  obtain ⟨B, hB⟩ := hK.exists_bound_of_continuousOn
    ((hD1.continuousOn_fderiv_of_isOpen hU le_rfl).mono hKU)
  have hC0 : 0 ≤ max C 0 := le_max_right _ _
  refine ⟨hD1.mono hKU,
    boundary_neumann_c2_inhom_finiteHolder_of_contDiffOn hα hα1 hK hcK hU hKU hD1,
    HasFiniteHolderNormOn.of_bounds (le_max_right B 0)
      (mul_nonneg (by norm_num : (0 : ℝ) ≤ 9) hC0)
      (fun x hx => (hB x hx).trans (le_max_left _ _)) ?_⟩
  intro x hx y hy
  by_cases he : x = y
  · subst y
    simpa only [sub_self, norm_zero, zero_div] using mul_nonneg (by norm_num : (0 : ℝ) ≤ 9) hC0
  apply (div_le_iff₀ (Real.rpow_pos_of_pos (norm_pos_iff.mpr (sub_ne_zero.mpr he)) α)).mpr
  have hent : ∀ i j : Fin 3, |(fderiv ℝ (fderiv ℝ w) x - fderiv ℝ (fderiv ℝ w) y)
      (EuclideanSpace.single i 1) (EuclideanSpace.single j 1)| ≤ max C 0 * ‖x - y‖ ^ α := by
    intro i j
    rw [sub_apply, sub_apply,
      ← boundaryNeumannC2Entry_eq_fderiv_fderiv (hd x (hKU hx)),
      ← boundaryNeumannC2Entry_eq_fderiv_fderiv (hd y (hKU hy)), ← dist_eq_norm]
    exact (hC i j x hx y hy).trans (mul_le_mul_of_nonneg_right (le_max_left _ _)
      (Real.rpow_nonneg dist_nonneg α))
  calc
    _ ≤ ∑ i : Fin 3, ∑ j : Fin 3, |(fderiv ℝ (fderiv ℝ w) x - fderiv ℝ (fderiv ℝ w) y)
        (EuclideanSpace.single i 1) (EuclideanSpace.single j 1)| :=
      boundaryNeumannIterate_bilin_norm_le _
    _ ≤ ∑ i : Fin 3, ∑ j : Fin 3, max C 0 * ‖x - y‖ ^ α :=
      Finset.sum_le_sum fun i _ => Finset.sum_le_sum fun j _ => hent i j
    _ = 9 * max C 0 * ‖x - y‖ ^ α := by
      simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
      ring

/-- The datum `∂ᵢH - (∂ᵢA)∇w` of the differentiated problem is C¹,α on a compact
convex set, when `A` and `H` are C³ on the open domain and `∇w` is C¹,α there. -/
lemma boundaryNeumannIterate_datum_hasC1HolderOn {α : ℝ} (hα : 0 ≤ α) (hα1 : α ≤ 1)
    {K U : Set (EuclideanSpace ℝ (Fin 3))} (hK : IsCompact K) (hcK : Convex ℝ K)
    (hU : IsOpen U) (hKU : K ⊆ U)
    {A : EuclideanSpace ℝ (Fin 3) → EuclideanSpace ℝ (Fin 3) →L[ℝ]
      EuclideanSpace ℝ (Fin 3)}
    {H : EuclideanSpace ℝ (Fin 3) → EuclideanSpace ℝ (Fin 3)}
    {w : EuclideanSpace ℝ (Fin 3) → ℝ}
    (hA : ContDiffOn ℝ 3 A U) (hH : ContDiffOn ℝ 3 H U) (hw : ContDiffOn ℝ 2 w U)
    (hG : HasC1HolderOn α (gradient w) K) (i : Fin 3) :
    HasC1HolderOn α (boundaryNeumannSmoothDatum A (gradient w) H i) K := by
  have hGU : ContDiffOn ℝ 1 (gradient w) U :=
    (toDual ℝ (EuclideanSpace ℝ (Fin 3))).symm.toContinuousLinearEquiv.contDiff
      |>.comp_contDiffOn (hw.fderiv_of_isOpen hU (by norm_num))
  have hf1U : ContDiffOn ℝ 2 (fun x => fderiv ℝ H x (EuclideanSpace.single i 1)) U :=
    (hH.fderiv_of_isOpen hU (by norm_num)).clm_apply contDiffOn_const
  have hf2U : ContDiffOn ℝ 2 (fun x => fderiv ℝ A x (EuclideanSpace.single i 1)) U :=
    (hA.fderiv_of_isOpen hU (by norm_num)).clm_apply contDiffOn_const
  have hf1 := hasC1HolderOn_of_contDiffOn_two hα hα1 hK hcK hU hKU hf1U
  have hf2 := hasC1HolderOn_of_contDiffOn_two hα hα1 hK hcK hU hKU hf2U
  obtain ⟨hp, -⟩ := boundaryNeumann_hasC1HolderOn_bilinear hU hKU (hf2U.of_le (by norm_num))
    hGU hf2 hG (ContinuousLinearMap.id ℝ
      (EuclideanSpace ℝ (Fin 3) →L[ℝ] EuclideanSpace ℝ (Fin 3)))
  have hpU : ContDiffOn ℝ 1 (fun x => ContinuousLinearMap.id ℝ
      (EuclideanSpace ℝ (Fin 3) →L[ℝ] EuclideanSpace ℝ (Fin 3))
      (fderiv ℝ A x (EuclideanSpace.single i 1)) (gradient w x)) U :=
    (hf2U.of_le (by norm_num)).clm_apply hGU
  obtain ⟨hs, -⟩ := boundaryNeumann_hasC1HolderOn_sub hU hKU (hf1U.of_le (by norm_num)) hpU
    hf1 hp
  exact hs

/-- First step of the smooth iteration for the homogeneous conormal problem
(blueprint `thm:boundary-neumann`). Let `w` be C² on an open neighbourhood `U` of the
closed unit half ball, with α-Hölder Hessian entries on the closed half ball, solving
the conormal equation with C³ coefficient `A` (bounded by `cap`, `lam`-elliptic) and C³
datum `H` on `U`, vanishing cross coefficients, `H₃ = 0` and `∂₃w = 0` on the face.
Then for a tangential direction `i`, `∂ᵢw` is C² on the half ball of radius
`1/2 · 3/8`, and its second derivatives (the third derivatives of `w` with a
tangential index `i`) are bounded and α-Hölder there. -/
theorem boundary_neumann_tangential_c2_holder {α : ℝ} (hα : 0 < α) (hα1 : α < 1)
    {lam cap : ℝ} (hlam : 0 < lam) (hcap : 0 ≤ cap)
    {U : Set (EuclideanSpace ℝ (Fin 3))} (hU : IsOpen U)
    (hUc : closure (boundaryHalfBall 1) ⊆ U)
    {A : EuclideanSpace ℝ (Fin 3) → EuclideanSpace ℝ (Fin 3) →L[ℝ]
      EuclideanSpace ℝ (Fin 3)}
    {H : EuclideanSpace ℝ (Fin 3) → EuclideanSpace ℝ (Fin 3)}
    {w : EuclideanSpace ℝ (Fin 3) → ℝ}
    (hA : ContDiffOn ℝ 3 A U) (hH : ContDiffOn ℝ 3 H U) (hw : ContDiffOn ℝ 2 w U)
    (hhol : ∃ C, ∀ i j : Fin 3, ∀ x ∈ closure (boundaryHalfBall 1),
      ∀ y ∈ closure (boundaryHalfBall 1),
        |boundaryNeumannC2Entry w x i j - boundaryNeumannC2Entry w y i j| ≤ C * dist x y ^ α)
    (hcap' : ∀ x ∈ closure (boundaryHalfBall 1), ‖A x‖ ≤ cap)
    (hell : ∀ x ∈ closure (boundaryHalfBall 1), ∀ v, lam * ‖v‖ ^ 2 ≤ inner ℝ (A x v) v)
    (hcross : ∀ x ∈ closure (boundaryHalfBall 1), x (Fin.last 2) = 0 →
      ∀ j : Fin 3, j ≠ Fin.last 2 →
        A x (EuclideanSpace.single j 1) (Fin.last 2) = 0 ∧
        A x (EuclideanSpace.single (Fin.last 2) 1) j = 0)
    (hH0 : ∀ x ∈ closure (boundaryHalfBall 1), x (Fin.last 2) = 0 → H x (Fin.last 2) = 0)
    (hw0 : ∀ x ∈ closure (boundaryHalfBall 1), x (Fin.last 2) = 0 →
      gradient w x (Fin.last 2) = 0)
    (he : IsBoundaryNeumannEquationOn A (gradient w) H 1)
    {i : Fin 3} (hi : i ≠ Fin.last 2) :
    ContDiffOn ℝ 2 (fun x => fderiv ℝ w x (EuclideanSpace.single i 1))
      (boundaryHalfBall (1 / 2 * (3 / 8))) ∧
    ∃ C, ∀ k l : Fin 3,
      (∀ x ∈ boundaryHalfBall (1 / 2 * (3 / 8)),
        |boundaryNeumannC2Entry (fun x => fderiv ℝ w x (EuclideanSpace.single i 1)) x k l| ≤
          C) ∧
      ∀ x ∈ boundaryHalfBall (1 / 2 * (3 / 8)), ∀ y ∈ boundaryHalfBall (1 / 2 * (3 / 8)),
        |boundaryNeumannC2Entry (fun x => fderiv ℝ w x (EuclideanSpace.single i 1)) x k l -
          boundaryNeumannC2Entry (fun x => fderiv ℝ w x (EuclideanSpace.single i 1)) y k l| ≤
          C * dist x y ^ α := by
  have hK1 : closure (boundaryHalfBall (1 / 2 : ℝ)) ⊆ closure (boundaryHalfBall 1) :=
    closure_mono (boundaryHalfBall_mono (by norm_num))
  have hKc : IsCompact (closure (boundaryHalfBall (1 / 2 : ℝ))) :=
    boundary_neumann_isCompact_closure.of_isClosed_subset isClosed_closure hK1
  have hKv : Convex ℝ (closure (boundaryHalfBall (1 / 2 : ℝ))) :=
    (convex_boundaryHalfBall _).closure
  have hKU := hK1.trans hUc
  have hDw : HasC1HolderOn α (fderiv ℝ w) (closure (boundaryHalfBall (1 / 2 : ℝ))) := by
    obtain ⟨C, hC⟩ := hhol
    exact boundaryNeumannIterate_fderiv_hasC1HolderOn hα.le hα1.le hKc hKv hU hKU hw
      ⟨C, fun i j x hx y hy => hC i j x (hK1 hx) y (hK1 hy)⟩
  have hD1 : ContDiffOn ℝ 1 (fderiv ℝ w) U := hw.fderiv_of_isOpen hU (by norm_num)
  have hG : HasC1HolderOn α (gradient w) (closure (boundaryHalfBall (1 / 2 : ℝ))) :=
    boundaryNeumannIterate_hasC1HolderOn_clm hU hKU hD1 hDw
      (toDual ℝ (EuclideanSpace ℝ (Fin 3))).symm.toContinuousLinearEquiv.toContinuousLinearMap
  have hv : HasC1HolderOn α (fun x => fderiv ℝ w x (EuclideanSpace.single i 1))
      (closure (boundaryHalfBall (1 / 2 : ℝ))) :=
    boundaryNeumannIterate_hasC1HolderOn_clm hU hKU hD1 hDw
      (ContinuousLinearMap.apply ℝ ℝ (EuclideanSpace.single i (1 : ℝ)))
  have hHi := boundaryNeumannIterate_datum_hasC1HolderOn hα.le hα1.le hKc hKv hU hKU
    hA hH hw hG i
  have hAK : HasC1HolderOn α A (closure (boundaryHalfBall (1 / 2 : ℝ))) :=
    hasC1HolderOn_of_contDiffOn_two hα.le hα1.le hKc hKv hU hKU (hA.of_le (by norm_num))
  obtain ⟨heq, hdat0, hgrad0⟩ := boundary_neumann_smooth_tangential_equation
    (R := 1) (r := 1 / 2) (by norm_num) hU hUc (hA.of_le (by norm_num))
    (hH.of_le (by norm_num)) hw he hcross hH0 hw0 hi
  obtain ⟨C, hC, hsc⟩ := boundary_neumann_c2_holder_scaled hα hα1 hlam hcap
    hAK.norm_nonneg (add_nonneg hv.norm_nonneg hHi.norm_nonneg)
  obtain ⟨hc2, hent⟩ := hsc (r := 1 / 2) (by norm_num) (by norm_num) A _ _ hAK hHi hv
    le_rfl le_rfl (fun x hx => hcap' x (hK1 hx)) (fun x hx => hell x (hK1 hx))
    (fun x hx => hcross x (hK1 hx)) hdat0 hgrad0 heq
  refine ⟨hc2, 8 * C, fun k l => ?_⟩
  obtain ⟨D, hDeq, -, hDb, hDh⟩ := hent k l
  have h2 : (2 : ℝ) ^ α ≤ 2 :=
    calc (2 : ℝ) ^ α ≤ 2 ^ (1 : ℝ) :=
          Real.rpow_le_rpow_of_exponent_le (by norm_num) hα1.le
      _ = 2 := Real.rpow_one 2
  have h4 : ((1 / 2 : ℝ) ^ 2)⁻¹ = 4 := by norm_num
  refine ⟨fun x hx => ?_, fun x hx y hy => ?_⟩
  · have e1 : boundaryNeumannC2Entry (fun x => fderiv ℝ w x (EuclideanSpace.single i 1))
        x k l = D x := (hDeq hx).symm
    rw [e1]
    have := hDb x (subset_closure hx)
    rw [h4] at this
    linarith
  · have e1 : boundaryNeumannC2Entry (fun x => fderiv ℝ w x (EuclideanSpace.single i 1))
        x k l = D x := (hDeq hx).symm
    have e2 : boundaryNeumannC2Entry (fun x => fderiv ℝ w x (EuclideanSpace.single i 1))
        y k l = D y := (hDeq hy).symm
    rw [e1, e2]
    have := hDh x (subset_closure hx) y (subset_closure hy)
    have hd : ((1 / 2 : ℝ)⁻¹ * dist x y) ^ α = 2 ^ α * dist x y ^ α := by
      rw [show (1 / 2 : ℝ)⁻¹ = 2 by norm_num]
      exact Real.mul_rpow (by norm_num) dist_nonneg
    rw [hd, h4] at this
    have hpow : 0 ≤ dist x y ^ α := Real.rpow_nonneg dist_nonneg α
    have hCd : 0 ≤ C * dist x y ^ α := mul_nonneg hC.le hpow
    calc
      _ ≤ 4 * (C * (2 ^ α * dist x y ^ α)) := this
      _ = 4 * 2 ^ α * (C * dist x y ^ α) := by ring
      _ ≤ 4 * 2 * (C * dist x y ^ α) := by gcongr
      _ = 8 * C * dist x y ^ α := by ring

/-! ## The normal third derivative from the classical equation -/

/-- The operator norm of a real linear functional on `ℝ³` is at most the sum of the
absolute values of its coordinate entries. -/
lemma boundaryNeumannIterate_functional_norm_le
    (ℓ : EuclideanSpace ℝ (Fin 3) →L[ℝ] ℝ) :
    ‖ℓ‖ ≤ ∑ k, |ℓ (EuclideanSpace.single k 1)| := by
  have hp : ∀ i : Fin 3, ‖(EuclideanSpace.proj i : EuclideanSpace ℝ (Fin 3) →L[ℝ] ℝ)‖ ≤ 1 :=
    fun i => ContinuousLinearMap.opNorm_le_bound _ zero_le_one fun x => by
      rw [one_mul]
      exact PiLp.norm_apply_le x i
  have he : ℓ = ∑ k, ℓ (EuclideanSpace.single k 1) •
      (EuclideanSpace.proj k : EuclideanSpace ℝ (Fin 3) →L[ℝ] ℝ) := by
    apply ContinuousLinearMap.coe_injective
    refine (EuclideanSpace.basisFun (Fin 3) ℝ).toBasis.ext fun i => ?_
    simp only [OrthonormalBasis.coe_toBasis, EuclideanSpace.basisFun_apply,
      ContinuousLinearMap.coe_coe]
    simp
  calc
    ‖ℓ‖ = ‖∑ k, ℓ (EuclideanSpace.single k 1) •
        (EuclideanSpace.proj k : EuclideanSpace ℝ (Fin 3) →L[ℝ] ℝ)‖ := congrArg _ he
    _ ≤ ∑ k, ‖ℓ (EuclideanSpace.single k 1) •
        (EuclideanSpace.proj k : EuclideanSpace ℝ (Fin 3) →L[ℝ] ℝ)‖ := norm_sum_le _ _
    _ ≤ _ := Finset.sum_le_sum fun k _ => by
      rw [norm_smul, Real.norm_eq_abs]
      exact mul_le_of_le_one_right (abs_nonneg _) (hp k)

/-- Pointwise Hölder bounds give the Hölder quotient bound. -/
lemma boundaryNeumannIterate_quotient_le {E F : Type*} [NormedAddCommGroup E]
    [NormedAddCommGroup F] {α B : ℝ} (hB : 0 ≤ B) {f : E → F} {x y : E}
    (h : ‖f x - f y‖ ≤ B * ‖x - y‖ ^ α) : ‖f x - f y‖ / ‖x - y‖ ^ α ≤ B := by
  by_cases he : x = y
  · subst y
    simpa only [sub_self, norm_zero, zero_div] using hB
  exact (div_le_iff₀ (Real.rpow_pos_of_pos (norm_pos_iff.mpr (sub_ne_zero.mpr he)) α)).mpr h

/-- A real C¹ function whose values and first coordinate derivatives are bounded and
α-Hölder with constant `C` is C¹,α. -/
lemma boundaryNeumannIterate_hasC1HolderOn_of_entries {α C : ℝ} (hC : 0 ≤ C)
    {S : Set (EuclideanSpace ℝ (Fin 3))} {g : EuclideanSpace ℝ (Fin 3) → ℝ}
    (hg : ContDiffOn ℝ 1 g S) (hb : ∀ x ∈ S, |g x| ≤ C)
    (hh : ∀ x ∈ S, ∀ y ∈ S, |g x - g y| ≤ C * dist x y ^ α)
    (hdb : ∀ k : Fin 3, ∀ x ∈ S, |fderiv ℝ g x (EuclideanSpace.single k 1)| ≤ C)
    (hdh : ∀ k : Fin 3, ∀ x ∈ S, ∀ y ∈ S,
      |fderiv ℝ g x (EuclideanSpace.single k 1) - fderiv ℝ g y (EuclideanSpace.single k 1)| ≤
        C * dist x y ^ α) :
    HasC1HolderOn α g S := by
  have h3 : 0 ≤ 3 * C := by positivity
  refine ⟨hg, HasFiniteHolderNormOn.of_bounds hC hC (fun x hx => hb x hx)
    (fun x hx y hy => boundaryNeumannIterate_quotient_le hC (by
      rw [Real.norm_eq_abs, ← dist_eq_norm]; exact hh x hx y hy)),
    HasFiniteHolderNormOn.of_bounds h3 h3 (fun x hx => ?_) (fun x hx y hy => ?_)⟩
  · refine (boundaryNeumannIterate_functional_norm_le _).trans ?_
    calc
      _ ≤ ∑ k : Fin 3, C := Finset.sum_le_sum fun k _ => hdb k x hx
      _ = 3 * C := by simp
  · refine boundaryNeumannIterate_quotient_le h3 ?_
    refine (boundaryNeumannIterate_functional_norm_le _).trans ?_
    calc
      _ ≤ ∑ k : Fin 3, C * ‖x - y‖ ^ α := Finset.sum_le_sum fun k _ => by
        rw [sub_apply, ← dist_eq_norm]; exact hdh k x hx y hy
      _ = 3 * C * ‖x - y‖ ^ α := by simp; ring

/-- The expanded classical equation in the open unit half ball, for a solution that is
C² on an open neighbourhood of the closed half ball, with the convention
`Aᵢⱼ = (A eⱼ)ᵢ`. -/
theorem boundaryNeumannIterate_pointwise_equation
    {U : Set (EuclideanSpace ℝ (Fin 3))}
    (hUc : closure (boundaryHalfBall 1) ⊆ U)
    {A : EuclideanSpace ℝ (Fin 3) → EuclideanSpace ℝ (Fin 3) →L[ℝ]
      EuclideanSpace ℝ (Fin 3)}
    {H : EuclideanSpace ℝ (Fin 3) → EuclideanSpace ℝ (Fin 3)}
    {w : EuclideanSpace ℝ (Fin 3) → ℝ}
    (hA : ContDiffOn ℝ 1 A U) (hH : ContDiffOn ℝ 1 H U) (hw : ContDiffOn ℝ 2 w U)
    (he : IsBoundaryNeumannEquationOn A (gradient w) H 1) :
    ∀ x ∈ boundaryHalfBall 1,
      (∑ i, ∑ j, A x (EuclideanSpace.single j 1) i * boundaryNeumannC2Entry w x i j) +
      (∑ i, ∑ j, fderiv ℝ A x (EuclideanSpace.single i 1)
        (EuclideanSpace.single j 1) i * fderiv ℝ w x (EuclideanSpace.single j 1)) =
      divergenceN H x := by
  intro x hx
  have hU := isOpen_boundaryHalfBall (1 : ℝ)
  have hsub : boundaryHalfBall 1 ⊆ U := subset_closure.trans hUc
  have hw1 : ContDiffOn ℝ 2 w (boundaryHalfBall 1) := hw.mono hsub
  have hDw : ContDiffOn ℝ 1 (fderiv ℝ w) (boundaryHalfBall 1) :=
    hw1.fderiv_of_isOpen hU (by norm_num)
  have hGw : ContDiffOn ℝ 1 (gradient w) (boundaryHalfBall 1) :=
    (toDual ℝ (EuclideanSpace ℝ (Fin 3))).symm.toContinuousLinearEquiv.contDiff
      |>.comp_contDiffOn hDw
  have hF : ContDiffOn ℝ 1 (fun y => A y (gradient w y) - H y) (boundaryHalfBall 1) :=
    ((hA.mono hsub).clm_apply hGw).sub (hH.mono hsub)
  have hflux : divergenceN (fun y => A y (gradient w y) - H y) x = 0 := by
    refine boundary_neumann_c2_divergence_eq_zero hU hF ?_ hx
    intro φ hφ hcφ hsφ
    rw [← setIntegral_eq_integral_of_forall_compl_eq_zero (s := boundaryHalfBall 1)
      (fun x hx => by
        rw [gradient_eq_zero_of_notMem_tsupport (fun ht => hx (hsφ ht)), inner_zero_right])]
    exact he φ hφ hcφ (hsφ.trans inter_subset_left)
  have hdG := (hGw.contDiffAt (hU.mem_nhds hx)).differentiableAt one_ne_zero
  have hpartial (i j : Fin 3) :
      fderiv ℝ (gradient w) x (EuclideanSpace.single i 1) j =
        boundaryNeumannC2Entry w x i j := by
    have he : (fun y => fderiv ℝ w y (EuclideanSpace.single j 1)) =
        fun y => gradient w y j := funext fun y => (gradient_apply_eq_fderiv_single w y j).symm
    unfold boundaryNeumannC2Entry
    rw [he]
    change _ = fderiv ℝ ((EuclideanSpace.proj j) ∘ gradient w) x _
    rw [((EuclideanSpace.proj j).hasFDerivAt.comp x hdG.hasFDerivAt).fderiv]
    rfl
  have hdA := ((hA.mono hsub).contDiffAt (hU.mem_nhds hx)).differentiableAt one_ne_zero
  have hdH := ((hH.mono hsub).contDiffAt (hU.mem_nhds hx)).differentiableAt one_ne_zero
  have hp := boundary_neumann_c2_divergence_product hdA hdG hdH
  rw [hflux] at hp
  simp only [hpartial, gradient_apply_eq_fderiv_single] at hp
  linarith

/-- All third derivatives of `w` are bounded and α-Hölder on the half ball of radius
`1/2 · 3/8 = 3/16`, under the hypotheses of `boundary_neumann_tangential_c2_holder`.
The derivatives with a tangential index come from that theorem (with the symmetry of
the Hessian of `w`); the remaining `∂₃∂₃∂₃w` comes from differentiating the classical
equation solved for `∂₃∂₃w`, using `A₃₃ ≥ lam`. The entry
`boundaryNeumannC2Entry (∂ₘw) x k l` is `∂ₖ∂ₗ∂ₘw`. -/
theorem boundary_neumann_third_derivatives_holder {α : ℝ} (hα : 0 < α) (hα1 : α < 1)
    {lam cap : ℝ} (hlam : 0 < lam) (hcap : 0 ≤ cap)
    {U : Set (EuclideanSpace ℝ (Fin 3))} (hU : IsOpen U)
    (hUc : closure (boundaryHalfBall 1) ⊆ U)
    {A : EuclideanSpace ℝ (Fin 3) → EuclideanSpace ℝ (Fin 3) →L[ℝ]
      EuclideanSpace ℝ (Fin 3)}
    {H : EuclideanSpace ℝ (Fin 3) → EuclideanSpace ℝ (Fin 3)}
    {w : EuclideanSpace ℝ (Fin 3) → ℝ}
    (hA : ContDiffOn ℝ 3 A U) (hH : ContDiffOn ℝ 3 H U) (hw : ContDiffOn ℝ 2 w U)
    (hhol : ∃ C, ∀ i j : Fin 3, ∀ x ∈ closure (boundaryHalfBall 1),
      ∀ y ∈ closure (boundaryHalfBall 1),
        |boundaryNeumannC2Entry w x i j - boundaryNeumannC2Entry w y i j| ≤ C * dist x y ^ α)
    (hcap' : ∀ x ∈ closure (boundaryHalfBall 1), ‖A x‖ ≤ cap)
    (hell : ∀ x ∈ closure (boundaryHalfBall 1), ∀ v, lam * ‖v‖ ^ 2 ≤ inner ℝ (A x v) v)
    (hcross : ∀ x ∈ closure (boundaryHalfBall 1), x (Fin.last 2) = 0 →
      ∀ j : Fin 3, j ≠ Fin.last 2 →
        A x (EuclideanSpace.single j 1) (Fin.last 2) = 0 ∧
        A x (EuclideanSpace.single (Fin.last 2) 1) j = 0)
    (hH0 : ∀ x ∈ closure (boundaryHalfBall 1), x (Fin.last 2) = 0 → H x (Fin.last 2) = 0)
    (hw0 : ∀ x ∈ closure (boundaryHalfBall 1), x (Fin.last 2) = 0 →
      gradient w x (Fin.last 2) = 0)
    (he : IsBoundaryNeumannEquationOn A (gradient w) H 1) :
    ∃ C, ∀ m k l : Fin 3,
      (∀ x ∈ boundaryHalfBall (1 / 2 * (3 / 8)),
        |boundaryNeumannC2Entry (fun x => fderiv ℝ w x (EuclideanSpace.single m 1)) x k l| ≤
          C) ∧
      ∀ x ∈ boundaryHalfBall (1 / 2 * (3 / 8)), ∀ y ∈ boundaryHalfBall (1 / 2 * (3 / 8)),
        |boundaryNeumannC2Entry (fun x => fderiv ℝ w x (EuclideanSpace.single m 1)) x k l -
          boundaryNeumannC2Entry (fun x => fderiv ℝ w x (EuclideanSpace.single m 1)) y k l| ≤
          C * dist x y ^ α := by
  have hS : IsOpen (boundaryHalfBall (1 / 2 * (3 / 8) : ℝ)) := isOpen_boundaryHalfBall _
  have hS1 : boundaryHalfBall (1 / 2 * (3 / 8) : ℝ) ⊆ boundaryHalfBall 1 :=
    boundaryHalfBall_mono (by norm_num)
  have hK1 : closure (boundaryHalfBall (1 / 2 * (3 / 8) : ℝ)) ⊆
      closure (boundaryHalfBall 1) := closure_mono hS1
  have hKc : IsCompact (closure (boundaryHalfBall (1 / 2 * (3 / 8) : ℝ))) :=
    boundary_neumann_isCompact_closure.of_isClosed_subset isClosed_closure hK1
  have hKv : Convex ℝ (closure (boundaryHalfBall (1 / 2 * (3 / 8) : ℝ))) :=
    (convex_boundaryHalfBall _).closure
  have hKU := hK1.trans hUc
  have hSK1 : boundaryHalfBall (1 / 2 * (3 / 8) : ℝ) ⊆ closure (boundaryHalfBall 1) :=
    subset_closure.trans hK1
  have h0 : (0 : Fin 3) ≠ 2 := by decide
  have h1 : (1 : Fin 3) ≠ 2 := by decide
  -- the tangential theorem, with a nonnegative constant
  have hT : ∀ t : Fin 3, t ≠ 2 →
      ContDiffOn ℝ 2 (fun x => fderiv ℝ w x (EuclideanSpace.single t 1))
        (boundaryHalfBall (1 / 2 * (3 / 8))) ∧
      ∃ C, 0 ≤ C ∧ ∀ k l : Fin 3,
        (∀ x ∈ boundaryHalfBall (1 / 2 * (3 / 8)),
          |boundaryNeumannC2Entry (fun x => fderiv ℝ w x (EuclideanSpace.single t 1)) x k l| ≤
            C) ∧
        ∀ x ∈ boundaryHalfBall (1 / 2 * (3 / 8)), ∀ y ∈ boundaryHalfBall (1 / 2 * (3 / 8)),
          |boundaryNeumannC2Entry (fun x => fderiv ℝ w x (EuclideanSpace.single t 1)) x k l -
            boundaryNeumannC2Entry (fun x => fderiv ℝ w x (EuclideanSpace.single t 1)) y k l| ≤
            C * dist x y ^ α := by
    intro t ht
    obtain ⟨hc, C, hC⟩ := boundary_neumann_tangential_c2_holder hα hα1 hlam hcap hU hUc
      hA hH hw hhol hcap' hell hcross hH0 hw0 he (i := t) ht
    exact ⟨hc, max C 0, le_max_right _ _, fun k l =>
      ⟨fun x hx => ((hC k l).1 x hx).trans (le_max_left _ _), fun x hx y hy =>
        ((hC k l).2 x hx y hy).trans (mul_le_mul_of_nonneg_right (le_max_left _ _)
          (Real.rpow_nonneg dist_nonneg _))⟩⟩
  -- Hessian bounds of `w` on the closed unit half ball, and symmetry
  have hDw1 : HasC1HolderOn α (fderiv ℝ w) (closure (boundaryHalfBall 1)) :=
    boundaryNeumannIterate_fderiv_hasC1HolderOn hα.le hα1.le boundary_neumann_isCompact_closure
      (convex_boundaryHalfBall 1).closure hU hUc hw hhol
  obtain ⟨hwh, hwb⟩ := boundaryNeumannC2Entry_holder_of_hasC1HolderOn hU hUc hw hDw1
  have hNw := hDw1.norm_nonneg
  have hsymm : ∀ x ∈ boundaryHalfBall 1, ∀ i j : Fin 3,
      boundaryNeumannC2Entry w x i j = boundaryNeumannC2Entry w x j i :=
    fun x hx i j => boundary_neumann_c2_entry_comm (hw.mono (subset_closure.trans hUc)) hx i j
  -- Hölder algebra on the open half ball
  have hC2 : ∀ g : EuclideanSpace ℝ (Fin 3) → ℝ, ContDiffOn ℝ 2 g U →
      HasC1HolderOn α g (boundaryHalfBall (1 / 2 * (3 / 8))) := fun g hg =>
    ((hasC1HolderOn_of_contDiffOn_two hα.le hα1.le hKc hKv hU hKU hg).mono subset_closure).1
  have hadd : ∀ {f g : EuclideanSpace ℝ (Fin 3) → ℝ},
      HasC1HolderOn α f (boundaryHalfBall (1 / 2 * (3 / 8))) →
      HasC1HolderOn α g (boundaryHalfBall (1 / 2 * (3 / 8))) →
      HasC1HolderOn α (fun x => f x + g x) (boundaryHalfBall (1 / 2 * (3 / 8))) :=
    fun hf hg => (boundaryNeumann_hasC1HolderOn_add hS subset_rfl hf.contDiff hg.contDiff
      hf hg).1
  have hsub : ∀ {f g : EuclideanSpace ℝ (Fin 3) → ℝ},
      HasC1HolderOn α f (boundaryHalfBall (1 / 2 * (3 / 8))) →
      HasC1HolderOn α g (boundaryHalfBall (1 / 2 * (3 / 8))) →
      HasC1HolderOn α (fun x => f x - g x) (boundaryHalfBall (1 / 2 * (3 / 8))) :=
    fun hf hg => (boundaryNeumann_hasC1HolderOn_sub hS subset_rfl hf.contDiff hg.contDiff
      hf hg).1
  have hmul : ∀ {f g : EuclideanSpace ℝ (Fin 3) → ℝ},
      HasC1HolderOn α f (boundaryHalfBall (1 / 2 * (3 / 8))) →
      HasC1HolderOn α g (boundaryHalfBall (1 / 2 * (3 / 8))) →
      HasC1HolderOn α (fun x => f x * g x) (boundaryHalfBall (1 / 2 * (3 / 8))) :=
    fun hf hg => (boundaryNeumann_hasC1HolderOn_mul hS subset_rfl hf.contDiff hg.contDiff
      hf hg).1
  have hsum3 : ∀ f : Fin 3 → EuclideanSpace ℝ (Fin 3) → ℝ,
      (∀ i, HasC1HolderOn α (f i) (boundaryHalfBall (1 / 2 * (3 / 8)))) →
      HasC1HolderOn α (fun x => ∑ i, f i x) (boundaryHalfBall (1 / 2 * (3 / 8))) := by
    intro f hf
    simp only [Fin.sum_univ_three]
    exact hadd (hadd (hf 0) (hf 1)) (hf 2)
  -- the pieces of the equation
  have ha : ∀ i j : Fin 3, HasC1HolderOn α (fun x => A x (EuclideanSpace.single j 1) i)
      (boundaryHalfBall (1 / 2 * (3 / 8))) := fun i j =>
    hC2 _ ((EuclideanSpace.proj i).contDiff.comp_contDiffOn
      ((hA.of_le (by norm_num)).clm_apply contDiffOn_const))
  have hdA : ∀ i j : Fin 3, HasC1HolderOn α
      (fun x => fderiv ℝ A x (EuclideanSpace.single i 1) (EuclideanSpace.single j 1) i)
      (boundaryHalfBall (1 / 2 * (3 / 8))) := fun i j =>
    hC2 _ ((EuclideanSpace.proj i).contDiff.comp_contDiffOn
      (((hA.fderiv_of_isOpen hU (by norm_num)).clm_apply contDiffOn_const).clm_apply
        contDiffOn_const))
  have hDwS : HasC1HolderOn α (fderiv ℝ w) (boundaryHalfBall (1 / 2 * (3 / 8))) :=
    (hDw1.mono hSK1).1
  have hdw : ∀ j : Fin 3, HasC1HolderOn α (fun x => fderiv ℝ w x (EuclideanSpace.single j 1))
      (boundaryHalfBall (1 / 2 * (3 / 8))) := fun j =>
    boundaryNeumannIterate_hasC1HolderOn_clm hS subset_rfl hDwS.contDiff hDwS
      (ContinuousLinearMap.apply ℝ ℝ (EuclideanSpace.single j (1 : ℝ)))
  have hdivH : HasC1HolderOn α (divergenceN H) (boundaryHalfBall (1 / 2 * (3 / 8))) := by
    apply hC2
    unfold divergenceN
    exact ContDiffOn.sum fun i _ => (EuclideanSpace.proj i).contDiff.comp_contDiffOn
      ((hH.fderiv_of_isOpen hU (by norm_num)).clm_apply contDiffOn_const)
  have hE : ∀ i j : Fin 3, j ≠ 2 → HasC1HolderOn α (fun x => boundaryNeumannC2Entry w x i j)
      (boundaryHalfBall (1 / 2 * (3 / 8))) := by
    intro i j hj
    obtain ⟨hc, C, hC, hCb⟩ := hT j hj
    refine boundaryNeumannIterate_hasC1HolderOn_of_entries
      (C := max (nondivC1HolderNorm α (fderiv ℝ w) (closure (boundaryHalfBall 1))) C)
      (le_max_of_le_left hNw) ?_ ?_ ?_ ?_ ?_
    · exact (hc.fderiv_of_isOpen hS (by norm_num)).clm_apply contDiffOn_const
    · exact fun x hx => (hwb i j x (hSK1 hx)).trans (le_max_left _ _)
    · exact fun x hx y hy => (hwh i j x (hSK1 hx) y (hSK1 hy)).trans
        (mul_le_mul_of_nonneg_right (le_max_left _ _) (Real.rpow_nonneg dist_nonneg _))
    · exact fun k x hx => ((hCb k i).1 x hx).trans (le_max_right _ _)
    · exact fun k x hx y hy => ((hCb k i).2 x hx y hy).trans
        (mul_le_mul_of_nonneg_right (le_max_right _ _) (Real.rpow_nonneg dist_nonneg _))
  have hlow : ∀ x ∈ boundaryHalfBall (1 / 2 * (3 / 8) : ℝ),
      lam ≤ A x (EuclideanSpace.single 2 1) 2 := by
    intro x hx
    have h := hell x (hSK1 hx) (EuclideanSpace.single 2 1)
    simpa [EuclideanSpace.inner_single_right, PiLp.norm_single] using h
  -- the normal second derivative solved from the classical equation
  let T : EuclideanSpace ℝ (Fin 3) → ℝ := fun x => ∑ i, ∑ j,
    fderiv ℝ A x (EuclideanSpace.single i 1) (EuclideanSpace.single j 1) i *
      fderiv ℝ w x (EuclideanSpace.single j 1)
  let R : EuclideanSpace ℝ (Fin 3) → ℝ := fun x =>
    A x (EuclideanSpace.single 0 1) 0 * boundaryNeumannC2Entry w x 0 0 +
    A x (EuclideanSpace.single 1 1) 0 * boundaryNeumannC2Entry w x 0 1 +
    A x (EuclideanSpace.single 2 1) 0 * boundaryNeumannC2Entry w x 2 0 +
    A x (EuclideanSpace.single 0 1) 1 * boundaryNeumannC2Entry w x 1 0 +
    A x (EuclideanSpace.single 1 1) 1 * boundaryNeumannC2Entry w x 1 1 +
    A x (EuclideanSpace.single 2 1) 1 * boundaryNeumannC2Entry w x 2 1 +
    A x (EuclideanSpace.single 0 1) 2 * boundaryNeumannC2Entry w x 2 0 +
    A x (EuclideanSpace.single 1 1) 2 * boundaryNeumannC2Entry w x 2 1
  let Q : EuclideanSpace ℝ (Fin 3) → ℝ := fun x =>
    (divergenceN H x - T x - R x) / A x (EuclideanSpace.single 2 1) 2
  have hTh : HasC1HolderOn α T (boundaryHalfBall (1 / 2 * (3 / 8))) :=
    hsum3 _ fun i => hsum3 _ fun j => hmul (hdA i j) (hdw j)
  have hRh : HasC1HolderOn α R (boundaryHalfBall (1 / 2 * (3 / 8))) :=
    hadd (hadd (hadd (hadd (hadd (hadd (hadd (hmul (ha 0 0) (hE 0 0 h0))
      (hmul (ha 0 1) (hE 0 1 h1))) (hmul (ha 0 2) (hE 2 0 h0)))
      (hmul (ha 1 0) (hE 1 0 h0))) (hmul (ha 1 1) (hE 1 1 h1)))
      (hmul (ha 1 2) (hE 2 1 h1))) (hmul (ha 2 0) (hE 2 0 h0)))
      (hmul (ha 2 1) (hE 2 1 h1))
  have hnum := hsub (hsub hdivH hTh) hRh
  have hQh : HasC1HolderOn α Q (boundaryHalfBall (1 / 2 * (3 / 8))) :=
    (boundaryNeumann_hasC1HolderOn_div hS subset_rfl hnum.contDiff (ha 2 2).contDiff
      hnum (ha 2 2) hlam hlow).1
  have hQeq : ∀ x ∈ boundaryHalfBall (1 / 2 * (3 / 8) : ℝ),
      boundaryNeumannC2Entry w x 2 2 = Q x := by
    intro x hx
    have hx1 := hS1 hx
    have heqn := boundaryNeumannIterate_pointwise_equation hUc (hA.of_le (by norm_num))
      (hH.of_le (by norm_num)) hw he x hx1
    have hpos : 0 < A x (EuclideanSpace.single 2 1) 2 := hlam.trans_le (hlow x hx)
    simp only [Fin.sum_univ_three] at heqn
    rw [hsymm x hx1 0 2, hsymm x hx1 1 2] at heqn
    simp only [Q, T, R]
    rw [eq_div_iff hpos.ne']
    simp only [Fin.sum_univ_three]
    linear_combination heqn
  -- the third derivatives through the normal entry and through symmetry
  have hnormal : ∀ k : Fin 3, ∀ x ∈ boundaryHalfBall (1 / 2 * (3 / 8) : ℝ),
      boundaryNeumannC2Entry (fun x => fderiv ℝ w x (EuclideanSpace.single 2 1)) x k 2 =
        fderiv ℝ Q x (EuclideanSpace.single k 1) := by
    intro k x hx
    have hev : (fun y => boundaryNeumannC2Entry w y 2 2) =ᶠ[𝓝 x] Q :=
      Filter.eventuallyEq_of_mem (hS.mem_nhds hx) hQeq
    change fderiv ℝ (fun y => boundaryNeumannC2Entry w y 2 2) x (EuclideanSpace.single k 1) = _
    rw [hev.fderiv_eq]
  have hswap : ∀ k l : Fin 3, ∀ x ∈ boundaryHalfBall (1 / 2 * (3 / 8) : ℝ),
      boundaryNeumannC2Entry (fun x => fderiv ℝ w x (EuclideanSpace.single 2 1)) x k l =
        boundaryNeumannC2Entry (fun x => fderiv ℝ w x (EuclideanSpace.single l 1)) x k 2 := by
    intro k l x hx
    have hev : (fun y => boundaryNeumannC2Entry w y l 2) =ᶠ[𝓝 x]
        (fun y => boundaryNeumannC2Entry w y 2 l) :=
      Filter.eventuallyEq_of_mem (hS.mem_nhds hx) fun y hy => hsymm y (hS1 hy) l 2
    change fderiv ℝ (fun y => boundaryNeumannC2Entry w y l 2) x (EuclideanSpace.single k 1) =
      fderiv ℝ (fun y => boundaryNeumannC2Entry w y 2 l) x (EuclideanSpace.single k 1)
    rw [hev.fderiv_eq]
  -- constants
  obtain ⟨-, C0, -, hC0⟩ := hT 0 h0
  obtain ⟨-, C1, -, hC1⟩ := hT 1 h1
  have hQd := hQh.derivative_holder
  have hentry : ∀ (L : EuclideanSpace ℝ (Fin 3) →L[ℝ] ℝ) (k : Fin 3),
      |L (EuclideanSpace.single k 1)| ≤ ‖L‖ := by
    intro L k
    have := L.le_opNorm (EuclideanSpace.single k 1)
    simpa [PiLp.norm_single] using this
  have hsemi : holderSeminorm α (fderiv ℝ Q) (boundaryHalfBall (1 / 2 * (3 / 8) : ℝ)) ≤
      holderNorm α (fderiv ℝ Q) (boundaryHalfBall (1 / 2 * (3 / 8) : ℝ)) :=
    le_add_of_nonneg_left (holderUniformNorm_nonneg hQd.uniform_bounded)
  have hpw : ∀ x y : EuclideanSpace ℝ (Fin 3), 0 ≤ dist x y ^ α :=
    fun x y => Real.rpow_nonneg dist_nonneg α
  have hfin : ∀ t : Fin 3, t = 0 ∨ t = 1 ∨ t = 2 := by decide
  have htan : ∀ t : Fin 3, t ≠ 2 → ∀ k l : Fin 3,
      (∀ x ∈ boundaryHalfBall (1 / 2 * (3 / 8)),
        |boundaryNeumannC2Entry (fun x => fderiv ℝ w x (EuclideanSpace.single t 1)) x k l| ≤
          max (max C0 C1) (holderNorm α (fderiv ℝ Q) (boundaryHalfBall (1 / 2 * (3 / 8))))) ∧
      ∀ x ∈ boundaryHalfBall (1 / 2 * (3 / 8)), ∀ y ∈ boundaryHalfBall (1 / 2 * (3 / 8)),
        |boundaryNeumannC2Entry (fun x => fderiv ℝ w x (EuclideanSpace.single t 1)) x k l -
          boundaryNeumannC2Entry (fun x => fderiv ℝ w x (EuclideanSpace.single t 1)) y k l| ≤
          max (max C0 C1) (holderNorm α (fderiv ℝ Q) (boundaryHalfBall (1 / 2 * (3 / 8)))) *
            dist x y ^ α := by
    intro t ht k l
    obtain rfl | rfl | rfl := hfin t
    · exact ⟨fun x hx => ((hC0 k l).1 x hx).trans (le_max_of_le_left (le_max_left _ _)),
        fun x hx y hy => ((hC0 k l).2 x hx y hy).trans (mul_le_mul_of_nonneg_right
          (le_max_of_le_left (le_max_left _ _)) (hpw x y))⟩
    · exact ⟨fun x hx => ((hC1 k l).1 x hx).trans (le_max_of_le_left (le_max_right _ _)),
        fun x hx y hy => ((hC1 k l).2 x hx y hy).trans (mul_le_mul_of_nonneg_right
          (le_max_of_le_left (le_max_right _ _)) (hpw x y))⟩
    · exact absurd rfl ht
  refine ⟨max (max C0 C1) (holderNorm α (fderiv ℝ Q) (boundaryHalfBall (1 / 2 * (3 / 8)))),
    fun m k l => ?_⟩
  by_cases hm : m = 2
  · subst hm
    by_cases hl : l = 2
    · subst hl
      refine ⟨fun x hx => ?_, fun x hx y hy => ?_⟩
      · rw [hnormal k x hx]
        exact ((hentry _ k).trans (hQd.nondiv_norm_le hx)).trans (le_max_right _ _)
      · rw [hnormal k x hx, hnormal k y hy, ← sub_apply]
        refine (hentry _ k).trans ((hQd.nondiv_norm_sub_le hx hy).trans ?_)
        rw [← dist_eq_norm]
        exact mul_le_mul_of_nonneg_right (hsemi.trans (le_max_right _ _)) (hpw x y)
    · obtain ⟨hb, hh⟩ := htan l hl k 2
      exact ⟨fun x hx => by rw [hswap k l x hx]; exact hb x hx, fun x hx y hy => by
        rw [hswap k l x hx, hswap k l y hy]; exact hh x hx y hy⟩
  · exact htan m hm k l

end LiquidDrop

module

public import NoCompromise.Elliptic.BoundaryC2aCover
public import NoCompromise.Elliptic.BoundaryNeumannTangential

@[expose] public section

/-!
# Full C²,α norm on the half ball `B⁺_{1/2}` (`thm:boundary-C2a`)

`boundary_c2a_half_ball_of_h1` bounds the coordinate second derivatives of the C²
representative on `B⁺_{1/2}` and their α-Hölder quotients. Since `B⁺_{1/2}` is convex and has
diameter at most `1`, the bounded Hessian makes the gradient Lipschitz, hence α-Hölder there;
the gradient and the function itself are controlled at one point of the fixed slab near the
flat face by the C¹ slab estimate `boundary_c1_holder_slab_trace` and the flat trace `φ`.
-/

noncomputable section
open MeasureTheory Filter Metric Set InnerProductSpace
open scoped ENNReal NNReal Topology Gradient RealInnerProductSpace
namespace LiquidDrop

/-- A linear functional on `ℝ³` whose values on the coordinate vectors are bounded by `B` has
operator norm at most `3 B`. -/
lemma boundary_c2a_norm_clm_le_of_single {L : EuclideanSpace ℝ (Fin 3) →L[ℝ] ℝ} {B : ℝ}
    (hB : 0 ≤ B) (h : ∀ i : Fin 3, |L (EuclideanSpace.single i 1)| ≤ B) : ‖L‖ ≤ 3 * B := by
  refine ContinuousLinearMap.opNorm_le_bound _ (by positivity) fun x => ?_
  have hx : x = ∑ i, x i • EuclideanSpace.single i (1 : ℝ) := by
    conv_lhs => rw [← (EuclideanSpace.basisFun (Fin 3) ℝ).sum_repr x]
    simp only [EuclideanSpace.basisFun_repr, EuclideanSpace.basisFun_apply]
  have hLx : L x = ∑ i, x i * L (EuclideanSpace.single i 1) := by
    conv_lhs => rw [hx]
    simp only [map_sum, map_smul, smul_eq_mul]
  have hi : ∀ i : Fin 3, |x i * L (EuclideanSpace.single i 1)| ≤ ‖x‖ * B := by
    intro i
    rw [abs_mul]
    have h1 : |x i| ≤ ‖x‖ := by
      simpa only [Real.norm_eq_abs] using PiLp.norm_apply_le x i
    exact mul_le_mul h1 (h i) (abs_nonneg _) (norm_nonneg _)
  rw [Real.norm_eq_abs, hLx]
  calc |∑ i, x i * L (EuclideanSpace.single i 1)|
      ≤ ∑ i, |x i * L (EuclideanSpace.single i 1)| := Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ _i : Fin 3, ‖x‖ * B := Finset.sum_le_sum fun i _ => hi i
    _ = 3 * B * ‖x‖ := by
        simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
        push_cast
        ring

/-- On an open convex set, coordinate second derivatives bounded by `B` make the derivative
`9 B`-Lipschitz. -/
lemma boundary_c2a_fderiv_lipschitz_of_entry {v : EuclideanSpace ℝ (Fin 3) → ℝ}
    {U : Set (EuclideanSpace ℝ (Fin 3))} (hU : IsOpen U) (hUc : Convex ℝ U)
    (hv : ContDiffOn ℝ 2 v U) {B : ℝ} (hB : 0 ≤ B)
    (hb : ∀ x ∈ U, ∀ i j : Fin 3, |boundaryNeumannC2Entry v x i j| ≤ B) :
    ∀ x ∈ U, ∀ y ∈ U, ‖fderiv ℝ v x - fderiv ℝ v y‖ ≤ 9 * B * ‖x - y‖ := by
  intro x hx y hy
  have hj : ∀ j : Fin 3, |(fderiv ℝ v x - fderiv ℝ v y) (EuclideanSpace.single j 1)| ≤
      3 * B * ‖x - y‖ := by
    intro j
    set g : EuclideanSpace ℝ (Fin 3) → ℝ := fun z => fderiv ℝ v z (EuclideanSpace.single j 1)
    have hd : ∀ z ∈ U, DifferentiableAt ℝ g z := by
      intro z hz
      have h1 : DifferentiableAt ℝ (fderiv ℝ v) z :=
        (((hv.contDiffAt (hU.mem_nhds hz)).fderiv_right (m := 1) (by norm_num)).differentiableAt
          one_ne_zero)
      exact h1.clm_apply (differentiableAt_const _)
    have hbd : ∀ z ∈ U, ‖fderiv ℝ g z‖ ≤ 3 * B := fun z hz =>
      boundary_c2a_norm_clm_le_of_single hB fun i => hb z hz i j
    have h := hUc.norm_image_sub_le_of_norm_fderiv_le hd hbd hy hx
    rw [sub_apply, ← Real.norm_eq_abs]
    exact h
  have h := boundary_c2a_norm_clm_le_of_single (by positivity) hj
  linarith

/-- Blueprint `thm:boundary-C2a` on `B⁺_{1/2}` with the full C²,α norm: under the hypotheses of
`boundary_c2a_local_of_h1`, `u` has a representative `v` that is C² on the open half ball
`B⁺_{1/2}`, with `|v|`, `‖∇v‖` and all coordinate second derivatives bounded by `C` there, and
`∇v` and the coordinate second derivatives α-Hölder with constant `C` on `B⁺_{1/2}`. `C` depends
only on `α, lam, cap, M, N, P₁, P₂, E`. -/
theorem boundary_c2a_half_ball_full_of_h1 {α lam cap M N P₁ P₂ E : ℝ}
    (hα : 0 < α) (hα1 : α < 1) (hlam : 0 < lam) (hlamcap : lam ≤ cap)
    (hM : 0 ≤ M) (hN : 0 ≤ N) (hP₁ : 0 ≤ P₁) (hP₂ : 0 ≤ P₂) (hE : 0 ≤ E) :
    ∃ C > 0, ∀ (u φ : EuclideanSpace ℝ (Fin 3) → ℝ)
      (F G : EuclideanSpace ℝ (Fin 3) → EuclideanSpace ℝ (Fin 3))
      (A : EuclideanSpace ℝ (Fin 3) → EuclideanSpace ℝ (Fin 3) →L[ℝ] EuclideanSpace ℝ (Fin 3)),
      ContDiff ℝ 2 φ →
      HasC1HolderOn α A (closure (boundaryHalfBall 1)) →
      HasC1HolderOn α G (closure (boundaryHalfBall 1)) →
      HasC1HolderOn α φ (closure (boundaryHalfBall 1)) →
      HasC1HolderOn α (gradient φ) (closure (boundaryHalfBall 1)) →
      nondivC1HolderNorm α A (closure (boundaryHalfBall 1)) ≤ M →
      nondivC1HolderNorm α φ (closure (boundaryHalfBall 1)) +
        nondivC1HolderNorm α (gradient φ) (closure (boundaryHalfBall 1)) +
        nondivC1HolderNorm α G (closure (boundaryHalfBall 1)) ≤ N →
      (∀ x ∈ closure (boundaryHalfBall 1), ‖A x‖ ≤ cap) →
      (∀ x ∈ closure (boundaryHalfBall 1), ∀ ξ, lam * ‖ξ‖ ^ 2 ≤ inner ℝ (A x ξ) ξ) →
      (∀ x ∈ closedBall (0 : EuclideanSpace ℝ (Fin 3)) 1, ‖gradient φ x‖ ≤ P₁) →
      (∀ x ∈ closedBall (0 : EuclideanSpace ℝ (Fin 3)) 1,
        ∀ y ∈ closedBall (0 : EuclideanSpace ℝ (Fin 3)) 1,
        ‖gradient φ x - gradient φ y‖ ≤ P₂ * dist x y ^ α) →
      HasH1GradientOn u F (boundaryHalfBall 1) →
      IsWeakDivergenceEquationOn A F G (boundaryHalfBall 1) →
      HasZeroFlatTraceOn (fun x => u x - φ x) (fun x => F x - gradient φ x) (ball 0 1) →
      (∫ x in boundaryHalfBall 1, ‖F x - gradient φ x‖ ^ 2) ≤ E →
      ∃ v : EuclideanSpace ℝ (Fin 3) → ℝ,
        ContDiffOn ℝ 2 v (boundaryHalfBall (1 / 2)) ∧
        v =ᵐ[volume.restrict (boundaryHalfBall (1 / 2))] u ∧
        (∀ i j : Fin 3,
          (∀ x ∈ boundaryHalfBall (1 / 2), |boundaryNeumannC2Entry v x i j| ≤ C) ∧
          ∀ x ∈ boundaryHalfBall (1 / 2), ∀ y ∈ boundaryHalfBall (1 / 2),
            |boundaryNeumannC2Entry v x i j - boundaryNeumannC2Entry v y i j| ≤
              C * dist x y ^ α) ∧
        (∀ x ∈ boundaryHalfBall (1 / 2), |v x| ≤ C) ∧
        (∀ x ∈ boundaryHalfBall (1 / 2), ‖gradient v x‖ ≤ C) ∧
        (∀ x ∈ boundaryHalfBall (1 / 2), ∀ y ∈ boundaryHalfBall (1 / 2),
          ‖gradient v x - gradient v y‖ ≤ C * dist x y ^ α) := by
  have hcap : 0 ≤ cap := hlam.le.trans hlamcap
  obtain ⟨C₀, hC₀, hhalf⟩ := boundary_c2a_half_ball_of_h1 hα hα1 hlam hlamcap hM hN hP₁ hP₂ hE
  obtain ⟨C₁, P, hC₁, hP, hreg1⟩ :=
    boundary_c1_holder_slab_trace hα hα1 hlam hcap hM hN hE hP₁ hP₂
  refine ⟨10 * C₀ + 2 * P + N, by positivity, ?_⟩
  intro u φ F G A hφ2 hA hG hφ hgφ hAM hNb hcapb hell hφb hφh hu hw htr hen
  obtain ⟨v, hvC, hvu, hent⟩ :=
    hhalf u φ F G A hφ2 hA hG hφ hgφ hAM hNb hcapb hell hφb hφh hu hw htr hen
  have hnA := hA.norm_nonneg
  have hnG := hG.norm_nonneg
  have hnφ := hφ.norm_nonneg
  have hngφ := hgφ.norm_nonneg
  have hAh := boundary_c2a_local_holder_pointwise hA.function_holder
    (hA.function_norm_le.trans hAM)
  have hGh := boundary_c2a_local_holder_pointwise (B := N) hG.function_holder
    (hG.function_norm_le.trans (by linarith))
  obtain ⟨W, v₁, hWo, -, -, hv₁, hv₁u, -, hgv₁, -, hv₁tr, hslab⟩ :=
    hreg1 u φ F G A (hA.contDiff.continuousOn) (hG.contDiff.continuousOn) hcapb hell hAh hGh
      hu hw (hφ2.of_le (by norm_num)) hφb hφh htr hen
  set U := boundaryHalfBall (1 / 2 : ℝ) with hU_def
  have hUo : IsOpen U := isOpen_boundaryHalfBall _
  have hUc : Convex ℝ U := convex_boundaryHalfBall _
  -- the base point `x₀ = s e₃` in the slab
  obtain ⟨s, hs_def⟩ : ∃ s : ℝ, s = 1 / 2097152 := ⟨_, rfl⟩
  have hs0 : 0 < s := by norm_num [hs_def]
  have hs1 : s ≤ 1 := by norm_num [hs_def]
  set x₀ : EuclideanSpace ℝ (Fin 3) := s • EuclideanSpace.single (Fin.last 2) (1 : ℝ)
    with hx₀_def
  have hx₀n : ‖x₀‖ = s := by
    rw [hx₀_def, norm_smul, PiLp.norm_single, norm_one, mul_one, Real.norm_eq_abs,
      abs_of_pos hs0]
  have hx₀3 : x₀ (Fin.last 2) = s := by simp [x₀]
  have hx₀U : x₀ ∈ U := ⟨by rw [mem_ball_zero_iff, hx₀n, hs_def]; norm_num, by
    change 0 < x₀ (Fin.last 2); rw [hx₀3]; exact hs0⟩
  have hx₀S : x₀ ∈ boundaryC1Slab := by
    refine ⟨?_, ?_⟩
    · rw [mem_preimage, mem_ball_zero_iff]
      have h := norm_sq_graphProjectionN x₀
      rw [hx₀3, hx₀n] at h
      nlinarith [norm_nonneg (graphProjectionN 2 x₀)]
    · change |x₀ (Fin.last 2)| < 1 / 1048576
      rw [hx₀3, abs_of_pos hs0, hs_def]
      norm_num
  have h0S : (0 : EuclideanSpace ℝ (Fin 3)) ∈ boundaryC1Slab := by
    refine ⟨?_, ?_⟩
    · rw [mem_preimage, map_zero]
      exact mem_ball_self (by norm_num)
    · change |(0 : EuclideanSpace ℝ (Fin 3)) (Fin.last 2)| < 1 / 1048576
      simp
  -- the two representatives agree on `W ∩ U`
  have hO : IsOpen (W ∩ U) := hWo.inter hUo
  have heq : EqOn v v₁ (W ∩ U) := by
    have h₁ : v =ᵐ[volume.restrict (W ∩ U)] u :=
      ae_restrict_of_ae_restrict_of_subset inter_subset_right hvu
    have h₂ : v₁ =ᵐ[volume.restrict (W ∩ U)] u :=
      ae_restrict_of_ae_restrict_of_subset
        (show W ∩ U ⊆ W ∩ {x | 0 < x (Fin.last 2)} from fun y hy => ⟨hy.1, hy.2.2⟩) hv₁u
    exact Measure.eqOn_open_of_ae_eq (h₁.trans h₂.symm) hO
      (hvC.continuousOn.mono inter_subset_right) (hv₁.continuousOn.mono inter_subset_left)
  have hx₀O : x₀ ∈ W ∩ U := ⟨hslab hx₀S, hx₀U⟩
  have hnear : v =ᶠ[𝓝 x₀] v₁ :=
    Filter.eventually_of_mem (hO.mem_nhds hx₀O) fun z hz => heq hz
  have hgx₀ : ‖gradient v x₀‖ ≤ P := by
    rw [hnear.gradient_eq]
    exact hgv₁ x₀ (hslab hx₀S)
  -- the value at `x₀`
  have hφ0 : |φ 0| ≤ N := by
    have h0U : (0 : EuclideanSpace ℝ (Fin 3)) ∈ closure (boundaryHalfBall 1) :=
      zero_mem_closure_boundaryHalfBall one_pos
    have h := (hφ.function_holder.nondiv_norm_le h0U).trans hφ.function_norm_le
    rw [Real.norm_eq_abs] at h
    linarith
  have hv₁0 : v₁ 0 = φ 0 := hv₁tr 0 (hslab h0S) (by simp)
  have hvx₀ : |v x₀| ≤ N + P := by
    have hd : ∀ z ∈ boundaryC1Slab, DifferentiableAt ℝ v₁ z := fun z hz =>
      (hv₁.contDiffAt (hWo.mem_nhds (hslab hz))).differentiableAt one_ne_zero
    have hbd : ∀ z ∈ boundaryC1Slab, ‖fderiv ℝ v₁ z‖ ≤ P := by
      intro z hz
      have h := hgv₁ z (hslab hz)
      rwa [gradient, LinearIsometryEquiv.norm_map] at h
    have h := convex_boundaryC1Slab.norm_image_sub_le_of_norm_fderiv_le hd hbd h0S hx₀S
    rw [sub_zero, hx₀n, hv₁0, Real.norm_eq_abs] at h
    rw [heq hx₀O]
    have h2 := abs_sub_abs_le_abs_sub (v₁ x₀) (φ 0)
    have h3 : P * s ≤ P := mul_le_of_le_one_right hP hs1
    linarith
  -- the gradient is Lipschitz on `U`
  have hbent : ∀ x ∈ U, ∀ i j : Fin 3, |boundaryNeumannC2Entry v x i j| ≤ C₀ :=
    fun x hx i j => (hent i j).1 x hx
  have hlip := boundary_c2a_fderiv_lipschitz_of_entry hUo hUc hvC hC₀.le hbent
  have hgrad_sub : ∀ x y, ‖gradient v x - gradient v y‖ = ‖fderiv ℝ v x - fderiv ℝ v y‖ := by
    intro x y
    rw [gradient, gradient, ← map_sub, LinearIsometryEquiv.norm_map]
  have hdist1 : ∀ x ∈ U, ∀ y ∈ U, ‖x - y‖ ≤ 1 := by
    intro x hx y hy
    have h1 := mem_ball_zero_iff.mp hx.1
    have h2 := mem_ball_zero_iff.mp hy.1
    have := norm_sub_le x y
    linarith
  have hgradb : ∀ x ∈ U, ‖gradient v x‖ ≤ P + 9 * C₀ := by
    intro x hx
    have h1 := hlip x hx x₀ hx₀U
    rw [← hgrad_sub] at h1
    have h2 := norm_sub_norm_le (gradient v x) (gradient v x₀)
    have h3 := hdist1 x hx x₀ hx₀U
    have h4 : 9 * C₀ * ‖x - x₀‖ ≤ 9 * C₀ := mul_le_of_le_one_right (by positivity) h3
    linarith
  have hvb : ∀ x ∈ U, |v x| ≤ N + 2 * P + 9 * C₀ := by
    intro x hx
    have hd : ∀ z ∈ U, DifferentiableAt ℝ v z := fun z hz =>
      (hvC.contDiffAt (hUo.mem_nhds hz)).differentiableAt (by norm_num)
    have hbd : ∀ z ∈ U, ‖fderiv ℝ v z‖ ≤ P + 9 * C₀ := by
      intro z hz
      have h := hgradb z hz
      rwa [gradient, LinearIsometryEquiv.norm_map] at h
    have h := hUc.norm_image_sub_le_of_norm_fderiv_le hd hbd hx₀U hx
    rw [Real.norm_eq_abs] at h
    have h3 := hdist1 x hx x₀ hx₀U
    have h4 : (P + 9 * C₀) * ‖x - x₀‖ ≤ P + 9 * C₀ :=
      mul_le_of_le_one_right (by positivity) h3
    have h2 := abs_sub_abs_le_abs_sub (v x) (v x₀)
    linarith
  refine ⟨v, hvC, hvu, fun i j => ⟨fun x hx => ((hent i j).1 x hx).trans (by linarith),
    fun x hx y hy => ((hent i j).2 x hx y hy).trans (mul_le_mul_of_nonneg_right (by linarith)
      (Real.rpow_nonneg dist_nonneg _))⟩, fun x hx => (hvb x hx).trans (by linarith),
    fun x hx => (hgradb x hx).trans (by linarith), fun x hx y hy => ?_⟩
  have h1 := hlip x hx y hy
  rw [← hgrad_sub, ← dist_eq_norm] at h1
  have hd1 : dist x y ≤ 1 := by rw [dist_eq_norm]; exact hdist1 x hx y hy
  have hdα : dist x y ≤ dist x y ^ α := by
    have h := Real.rpow_le_rpow_of_exponent_ge' dist_nonneg hd1 hα.le hα1.le
    rwa [Real.rpow_one] at h
  calc ‖gradient v x - gradient v y‖ ≤ 9 * C₀ * dist x y := h1
    _ ≤ 9 * C₀ * dist x y ^ α := mul_le_mul_of_nonneg_left hdα (by positivity)
    _ ≤ (10 * C₀ + 2 * P + N) * dist x y ^ α :=
        mul_le_mul_of_nonneg_right (by linarith) (Real.rpow_nonneg dist_nonneg _)

end LiquidDrop

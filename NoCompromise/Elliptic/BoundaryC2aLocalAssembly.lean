import NoCompromise.Elliptic.BoundaryC2aLocal

/-!
# Local boundary C²,α near flat points from H¹ (`thm:boundary-C2a`, assembly)

The C¹,α representative of `boundary_c1_holder_slab_trace`, rescaled by `y ↦ p + 2⁻²¹ • y`
at each flat point `p` with `‖p‖ ≤ 1/2`, satisfies the hypotheses of
`boundary_c2a_holder_trace`; scaling back gives C² regularity with bounded α-Hölder second
derivatives on the image of `boundaryNondivC2Slab`, with constants fixed before the data.
-/

noncomputable section
open MeasureTheory Filter Metric Set InnerProductSpace
open scoped ENNReal NNReal Topology Gradient RealInnerProductSpace
namespace LiquidDrop

/-- A C⁰,α bound gives the pointwise Hölder estimate with the full norm as constant. -/
lemma boundary_c2a_local_holder_pointwise {E F : Type*} [NormedAddCommGroup E]
    [NormedAddCommGroup F] {α B : ℝ} {f : E → F} {U : Set E}
    (hf : HasFiniteHolderNormOn α f U) (hB : holderNorm α f U ≤ B) :
    ∀ x ∈ U, ∀ y ∈ U, ‖f x - f y‖ ≤ B * dist x y ^ α := by
  intro x hx y hy
  have hs : holderSeminorm α f U ≤ B := by
    have := holderUniformNorm_nonneg hf.uniform_bounded
    unfold holderNorm at hB
    linarith
  rw [dist_eq_norm]
  exact (hf.nondiv_norm_sub_le hx hy).trans
    (mul_le_mul_of_nonneg_right hs (Real.rpow_nonneg (norm_nonneg _) _))

theorem boundary_c2a_local_of_h1 {α lam cap M N P₁ P₂ E : ℝ}
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
      ∃ (W : Set (EuclideanSpace ℝ (Fin 3))) (v : EuclideanSpace ℝ (Fin 3) → ℝ),
        IsOpen W ∧ boundaryC1Slab ⊆ W ∧ ContDiffOn ℝ 1 v W ∧
        v =ᵐ[volume.restrict (W ∩ {x | 0 < x (Fin.last 2)})] u ∧
        (∀ x ∈ W, x (Fin.last 2) = 0 → v x = φ x) ∧
        ∀ p : EuclideanSpace ℝ (Fin 3), p (Fin.last 2) = 0 → ‖p‖ ≤ 1 / 2 →
          ContDiffOn ℝ 2 v ((fun y => p + (1 / 2097152 : ℝ) • y) '' boundaryNondivC2Slab) ∧
          ∀ i j : Fin 3,
            (∀ x ∈ (fun y => p + (1 / 2097152 : ℝ) • y) '' boundaryNondivC2Slab,
              |boundaryNeumannC2Entry v x i j| ≤ C) ∧
            ∀ x ∈ (fun y => p + (1 / 2097152 : ℝ) • y) '' boundaryNondivC2Slab,
            ∀ y ∈ (fun y => p + (1 / 2097152 : ℝ) • y) '' boundaryNondivC2Slab,
              |boundaryNeumannC2Entry v x i j - boundaryNeumannC2Entry v y i j| ≤
                C * dist x y ^ α := by
  have hcap : 0 ≤ cap := hlam.le.trans hlamcap
  obtain ⟨C₁, P, hC₁, hP, hreg1⟩ :=
    boundary_c1_holder_slab_trace hα hα1 hlam hcap hM hN hE hP₁ hP₂
  set N₀ : ℝ := N + P₁
  set N' : ℝ := (N₀ + P + 2 * P) + (P + C₁) + N
  have hN₀ : 0 ≤ N₀ := by positivity
  have hN' : 0 ≤ N' := by positivity
  obtain ⟨C₂, hC₂, hreg2⟩ := boundary_c2a_holder_trace hα hα1 hlam hlamcap hM hN'
  set r : ℝ := 1 / 2097152 with hr_def
  have hr0 : 0 < r := boundary_c2a_local_radius_pos
  have hr1 : r ≤ 1 := by norm_num [hr_def]
  have hri : 1 ≤ r⁻¹ := by norm_num [hr_def]
  refine ⟨r⁻¹ ^ 2 * C₂ * r⁻¹ ^ α, by positivity, ?_⟩
  intro u φ F G A hφ2 hA hG hφ hgφ hAM hNb hcapb hell hφb hφh hu hw htr hen
  set U := closure (boundaryHalfBall 1)
  have hφ1 : ContDiff ℝ 1 φ := hφ2.of_le (by norm_num)
  have hnA := hA.norm_nonneg
  have hnG := hG.norm_nonneg
  have hnφ := hφ.norm_nonneg
  have hngφ := hgφ.norm_nonneg
  have hAh := boundary_c2a_local_holder_pointwise hA.function_holder
    (hA.function_norm_le.trans hAM)
  have hGh := boundary_c2a_local_holder_pointwise (B := N) hG.function_holder
    (hG.function_norm_le.trans (by linarith))
  obtain ⟨W, v, hWo, -, -, hv1, hvu, hgv, hvP, hvC, hvtr, hslab⟩ :=
    hreg1 u φ F G A (hA.contDiff.continuousOn) (hG.contDiff.continuousOn) hcapb hell hAh hGh
      hu hw hφ1 hφb hφh htr hen
  refine ⟨W, v, hWo, hslab, hv1, hvu, hvtr, ?_⟩
  intro p hp3 hp
  set e := frozenBallScaling p boundary_c2a_local_radius_pos
  -- sup bound for `φ` on the closed unit ball
  have hφN₀ : ∀ x ∈ closedBall (0 : EuclideanSpace ℝ (Fin 3)) 1, |φ x| ≤ N₀ := by
    intro x hx
    have h0U : (0 : EuclideanSpace ℝ (Fin 3)) ∈ U := zero_mem_closure_boundaryHalfBall one_pos
    have hφ0 : ‖φ 0‖ ≤ N := (hφ.function_holder.nondiv_norm_le h0U).trans
      (hφ.function_norm_le.trans (by linarith))
    have hdφ : ∀ z ∈ closedBall (0 : EuclideanSpace ℝ (Fin 3)) 1, DifferentiableAt ℝ φ z :=
      fun z _ => hφ1.differentiable one_ne_zero z
    have hbφ : ∀ z ∈ closedBall (0 : EuclideanSpace ℝ (Fin 3)) 1, ‖fderiv ℝ φ z‖ ≤ P₁ := by
      intro z hz
      have : ‖fderiv ℝ φ z‖ = ‖gradient φ z‖ := by
        change ‖fderiv ℝ φ z‖ = ‖(InnerProductSpace.toDual ℝ _).symm (fderiv ℝ φ z)‖
        rw [LinearIsometryEquiv.norm_map]
      rw [this]
      exact hφb z hz
    have hmv :=
      (convex_closedBall (0 : EuclideanSpace ℝ (Fin 3)) 1).norm_image_sub_le_of_norm_fderiv_le
      hdφ hbφ (mem_closedBall_self zero_le_one) hx
    rw [sub_zero] at hmv
    have hx1 : ‖x‖ ≤ 1 := mem_closedBall_zero_iff.mp hx
    rw [Real.norm_eq_abs] at hmv hφ0
    have := abs_sub_abs_le_abs_sub (φ x) (φ 0)
    have : P₁ * ‖x‖ ≤ P₁ := by nlinarith
    change |φ x| ≤ N + P₁
    linarith
  -- rescaled data
  have hmU : MapsTo e U U := fun y hy => (boundary_c2a_scaling_maps_slab hp3 hp hy).2
  have hmS : MapsTo e U W := fun y hy => hslab (boundary_c2a_scaling_maps_slab hp3 hp hy).1
  obtain ⟨hwC, hwN⟩ := boundary_c2a_rescaled_c1Holder hα hα1 hC₁.le hP hN₀ hp3 hp hWo hslab hv1
    hvP hvC hvtr hφN₀
  obtain ⟨hAe, hAeN⟩ := boundary_c2a_c1Holder_comp_scaling hα.le p
    boundary_c2a_local_radius_pos hr1 hA hmU
  obtain ⟨hGe0, hGe0N⟩ := boundary_c2a_c1Holder_comp_scaling hα.le p
    boundary_c2a_local_radius_pos hr1 hG hmU
  obtain ⟨hGe, hGeN⟩ := boundary_c2a_c1Holder_const_smul hGe0 hr0.le hr1
  obtain ⟨hφe, hφeN⟩ := boundary_c2a_c1Holder_comp_scaling hα.le p
    boundary_c2a_local_radius_pos hr1 hφ hmU
  obtain ⟨hgφe0, hgφe0N⟩ := boundary_c2a_c1Holder_comp_scaling hα.le p
    boundary_c2a_local_radius_pos hr1 hgφ hmU
  obtain ⟨hgφe, hgφeN⟩ := boundary_c2a_c1Holder_const_smul hgφe0 hr0.le hr1
  have hgrad : gradient (φ ∘ e) = fun y => r • (gradient φ ∘ e) y := by
    funext y
    exact boundary_c2a_gradient_comp_scaling p y boundary_c2a_local_radius_pos φ
  rw [← hgrad] at hgφe hgφeN
  have hec : ContDiff ℝ 2 e := contDiff_const.add (contDiff_id.const_smul r)
  have hsub : e '' boundaryHalfBall 1 ⊆ W ∩ boundaryHalfBall 1 := by
    rintro _ ⟨y, hy, rfl⟩
    exact ⟨hmS (subset_closure hy), boundary_c2a_scaling_maps_halfBall hp3 hp hy⟩
  have hweak := hw.boundary_c2a_rescale p hr0 hWo hv1 hgv hsub hA.contDiff.continuousOn
    hG.contDiff.continuousOn
  have hdw : ∀ x ∈ U, DifferentiableAt ℝ (v ∘ e) x := fun x hx =>
    ((hv1.contDiffAt (hWo.mem_nhds (hmS hx))).differentiableAt one_ne_zero).comp x
      ((hec.differentiable (by norm_num)) x)
  have htr2 : ∀ x ∈ U, x (Fin.last 2) = 0 → (v ∘ e) x = (φ ∘ e) x := by
    intro x hx hx3
    apply hvtr _ (hmS hx)
    change (p + r • x) (Fin.last 2) = 0
    rw [PiLp.add_apply, PiLp.smul_apply, smul_eq_mul, hp3, hx3, mul_zero, add_zero]
  obtain ⟨hC2, hbd⟩ := hreg2 (A ∘ e) (fun y => r • G (e y)) (v ∘ e) (φ ∘ e) univ isOpen_univ
    (subset_univ _) (hφ2.comp hec).contDiffOn hAe hGe hwC hdw hφe hgφe (hAeN.trans hAM)
    (by
      have h1 : nondivC1HolderNorm α (φ ∘ e) U ≤ nondivC1HolderNorm α φ U := hφeN
      have h2 : nondivC1HolderNorm α (gradient (φ ∘ e)) U ≤
          nondivC1HolderNorm α (gradient φ) U := hgφeN.trans hgφe0N
      have h3 : nondivC1HolderNorm α (fun y => r • G (e y)) U ≤ nondivC1HolderNorm α G U :=
        hGeN.trans hGe0N
      have h4 : nondivC1HolderNorm α (v ∘ e) U ≤ (N₀ + P + 2 * P) + (P + C₁) := hwN
      have h5 : N' = (N₀ + P + 2 * P) + (P + C₁) + N := rfl
      rw [h5]
      linarith)
    (fun x hx => hcapb _ (hmU hx))
    (fun x hx ξ => by rw [real_inner_comm]; exact hell _ (hmU hx) ξ)
    hweak htr2
  -- scale back
  have hvw : v = (v ∘ e) ∘ e.symm := by
    funext x
    simp only [Function.comp_apply, Homeomorph.apply_symm_apply]
  have himg : (fun y => p + (1 / 2097152 : ℝ) • y) '' boundaryNondivC2Slab =
      e '' boundaryNondivC2Slab := rfl
  rw [himg]
  refine ⟨?_, fun i j => ⟨?_, ?_⟩⟩
  · rw [hvw]
    exact boundary_c2a_contDiffOn_comp_scaling_symm p boundary_c2a_local_radius_pos hC2
  · rintro _ ⟨x, hx, rfl⟩
    rw [hvw, boundary_c2a_entry_comp_scaling, abs_mul, abs_of_nonneg (by positivity)]
    have h1 : 1 ≤ r⁻¹ ^ α := Real.one_le_rpow hri hα.le
    calc r⁻¹ ^ 2 * |boundaryNeumannC2Entry (v ∘ e) x i j| ≤ r⁻¹ ^ 2 * C₂ :=
          mul_le_mul_of_nonneg_left ((hbd i j).1 x hx) (by positivity)
      _ ≤ r⁻¹ ^ 2 * C₂ * r⁻¹ ^ α := le_mul_of_one_le_right (by positivity) h1
  · rintro _ ⟨x, hx, rfl⟩ _ ⟨y, hy, rfl⟩
    rw [hvw, boundary_c2a_entry_comp_scaling, boundary_c2a_entry_comp_scaling, ← mul_sub,
      abs_mul, abs_of_nonneg (by positivity)]
    have hd : dist x y = r⁻¹ * dist (e x) (e y) := by
      rw [quasilinear_ballScaling_dist p x y hr0, ← mul_assoc, inv_mul_cancel₀ hr0.ne', one_mul]
    have hdp : dist x y ^ α = r⁻¹ ^ α * dist (e x) (e y) ^ α := by
      rw [hd, Real.mul_rpow (by positivity) dist_nonneg]
    calc r⁻¹ ^ 2 * |boundaryNeumannC2Entry (v ∘ e) x i j - boundaryNeumannC2Entry (v ∘ e) y i j|
        ≤ r⁻¹ ^ 2 * (C₂ * dist x y ^ α) :=
          mul_le_mul_of_nonneg_left ((hbd i j).2 x hx y hy) (by positivity)
      _ = r⁻¹ ^ 2 * C₂ * r⁻¹ ^ α * dist (e x) (e y) ^ α := by rw [hdp]; ring

end LiquidDrop

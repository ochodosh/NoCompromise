import NoCompromise.Elliptic.BoundaryNeumannC2InhomSmooth

/-!
# Flat boundary C²,α bounds for inhomogeneous conormal data

Second assertion of blueprint `thm:boundary-neumann` with the Hölder bounds on the
continuous extensions of the second-derivative entries retained. The radius is
`1/4 * (3/8)`.
-/

noncomputable section
open Set Filter Metric InnerProductSpace MeasureTheory
open scoped Topology Gradient RealInnerProductSpace
namespace LiquidDrop

/-- Second assertion of `thm:boundary-neumann` at finite regularity, with the lift step
of the TeX proof (`q ∈ C^{2,α}`, `H ∈ C^{1,α}` on the closed quarter half-ball) taken as
named hypotheses controlled by `Q`. The constant `Cb` is uniform: it depends only on
`α, lam, cap, HA, K, M, Q`. -/
theorem boundary_neumann_c2_holder_inhom_of_lift {α lam cap HA K M Q : ℝ}
    (hα : 0 < α) (hα1 : α < 1) (hlam : 0 < lam) (hcap : 0 ≤ cap)
    (hHA : 0 ≤ HA) (hK : 0 ≤ K) (hM : 0 ≤ M) (hQ : 0 ≤ Q) :
    ∃ Cb : ℝ, 0 < Cb ∧
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
          ‖A x - A y‖ ≤ HA * dist x y ^ α) →
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
          ‖gradient h x - gradient h y‖ ≤ K * dist x y ^ α) →
        (∀ x ∈ closedBall 0 1, ∀ y ∈ closedBall 0 1,
          ‖gradient (boundaryNeumannNormalCoefficient A) x -
            gradient (boundaryNeumannNormalCoefficient A) y‖ ≤ K * dist x y ^ α) →
        ContinuousOn f (closure (boundaryHalfBall 1)) →
        (∀ x ∈ closure (boundaryHalfBall 1), ‖f x‖ ≤ K) →
        (∀ x ∈ closure (boundaryHalfBall 1), ∀ y ∈ closure (boundaryHalfBall 1),
          ‖f x - f y‖ ≤ K * dist x y ^ α) →
        HasH1GradientOn z F (boundaryHalfBall 1) →
        (∫ x in boundaryHalfBall 1, ‖F x‖ ^ 2) ≤ M →
        (∀ φ : EuclideanSpace ℝ (Fin 3) → ℝ, ContDiff ℝ 1 φ → HasCompactSupport φ →
          tsupport φ ⊆ ball 0 1 →
          (∫ x in boundaryHalfBall 1, inner ℝ (A x (F x)) (gradient φ x)) =
            -(∫ x in boundaryHalfBall 1, f x * φ x) -
              ∫ y in ball (0 : EuclideanSpace ℝ (Fin 2)) 1,
                h y * φ (graphBaseEmbedding y)) →
        HasC1HolderOn α A (closure (boundaryHalfBall (1 / 4))) →
        nondivC1HolderNorm α A (closure (boundaryHalfBall (1 / 4))) ≤ Q →
        ContDiffOn ℝ 2 (boundaryNeumannLift h (boundaryNeumannNormalCoefficient A)) (ball 0 1) →
        HasC1HolderOn α (boundaryNeumannLift h (boundaryNeumannNormalCoefficient A))
          (closure (boundaryHalfBall (1 / 4))) →
        nondivC1HolderNorm α (boundaryNeumannLift h (boundaryNeumannNormalCoefficient A))
          (closure (boundaryHalfBall (1 / 4))) ≤ Q →
        (∀ i j : Fin 3, ∀ x ∈ closure (boundaryHalfBall (1 / 4)),
          ∀ y ∈ closure (boundaryHalfBall (1 / 4)),
            |boundaryNeumannC2Entry (boundaryNeumannLift h (boundaryNeumannNormalCoefficient A))
                x i j -
              boundaryNeumannC2Entry (boundaryNeumannLift h (boundaryNeumannNormalCoefficient A))
                y i j| ≤ Q * dist x y ^ α) →
        (∀ i j : Fin 3, ∀ x ∈ closure (boundaryHalfBall (1 / 4)),
          |boundaryNeumannC2Entry (boundaryNeumannLift h (boundaryNeumannNormalCoefficient A))
            x i j| ≤ Q) →
        HasC1HolderOn α (boundaryNeumannInhomDatum A f h) (closure (boundaryHalfBall (1 / 4))) →
        nondivC1HolderNorm α (boundaryNeumannInhomDatum A f h)
          (closure (boundaryHalfBall (1 / 4))) ≤ Q →
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
  obtain ⟨C, hC, hreg⟩ := boundary_neumann_c1_holder_conormal hα hα1 hlam hcap hHA hK hM
  let G : ℝ := C + Q
  have hG : 0 ≤ G := add_nonneg hC.le hQ
  let N0 : ℝ := G + G + (G + G) + Q
  have hN0 : 0 ≤ N0 :=
    add_nonneg (add_nonneg (add_nonneg hG hG) (add_nonneg hG hG)) hQ
  obtain ⟨C0, hC0, hsc⟩ := boundary_neumann_c2_holder_scaled hα hα1 hlam hcap hQ hN0
  let C1 : ℝ := ((1 / 4 : ℝ) ^ 2)⁻¹ * C0 * ((1 / 4 : ℝ)⁻¹) ^ α +
    ((1 / 4 : ℝ) ^ 2)⁻¹ * C0 + Q
  have hC1 : 0 < C1 :=
    add_pos_of_pos_of_nonneg (add_pos_of_nonneg_of_pos (by positivity) (by positivity)) hQ
  refine ⟨C1, hC1, ?_⟩
  intro A F z f h hAc hbA hell hhA hcross hneigh hbh hbb hDh hDb hhDh hhDb hfc hbf hhf hz hE
    hweak hAH hAQ hq2 hqH hqQ hEh hEb hHH hHQ
  obtain ⟨u, hu, hzu, hFu, hbu, hhu, hface⟩ := hreg A F z f h hAc hbA hell hhA hcross hneigh
    hbh hbb hDh hDb hhDh hhDb hfc hbf hhf hz hE hweak
  let q := boundaryNeumannLift h (boundaryNeumannNormalCoefficient A)
  let H := boundaryNeumannInhomDatum A f h
  let S := closure (boundaryHalfBall (1 / 4 : ℝ))
  have hSc : IsCompact S :=
    (isBounded_ball.subset (inter_subset_left : boundaryHalfBall (1 / 4 : ℝ) ⊆
      ball 0 (1 / 4 : ℝ))).isCompact_closure
  have hSconv : Convex ℝ S := (convex_boundaryHalfBall (1 / 4 : ℝ)).closure
  have hSclosed : S ⊆ closedBall (0 : EuclideanSpace ℝ (Fin 3)) (1 / 4 : ℝ) :=
    closure_minimal (inter_subset_left.trans ball_subset_closedBall) isClosed_closedBall
  have hSsmall : S ⊆ ball (0 : EuclideanSpace ℝ (Fin 3)) (1 / 2 : ℝ) :=
    hSclosed.trans (closedBall_subset_ball (by norm_num))
  have hSone : S ⊆ ball (0 : EuclideanSpace ℝ (Fin 3)) 1 :=
    hSclosed.trans (closedBall_subset_ball (by norm_num))
  have hSunit : S ⊆ closure (boundaryHalfBall 1) :=
    closure_mono (boundaryHalfBall_mono (by norm_num))
  have h0S : (0 : EuclideanSpace ℝ (Fin 3)) ∈ S :=
    zero_mem_closure_boundaryHalfBall (by norm_num)
  -- normalize the additive constant so that the C¹,α norm of `u - q` is controlled
  let c : ℝ := u 0 - q 0
  let u' : EuclideanSpace ℝ (Fin 3) → ℝ := fun x => u x - c
  let w := fun x => u' x - q x
  have hu' : ContDiffOn ℝ 1 u' (ball 0 (1 / 2 : ℝ)) := hu.sub contDiffOn_const
  have hfu' : ∀ x, fderiv ℝ u' x = fderiv ℝ u x := fun x => fderiv_sub_const c
  have hgu' : ∀ x, gradient u' x = gradient u x := fun x => by
    simp only [gradient, hfu']
  have huH : HasC1HolderOn α u' S := boundary_neumann_c2_inhom_holder_of_gradient
    hα.le hα1.le hC.le hSc hSconv isOpen_ball hSsmall hu'
    (fun x hx => by rw [hgu']; exact hbu x (hSsmall hx))
    (fun x hx y hy => by rw [hgu', hgu']; exact hhu x (hSsmall hx) y (hSsmall hy))
  have hud (x) (hx : x ∈ S) : DifferentiableAt ℝ u' x :=
    (hu'.contDiffAt (isOpen_ball.mem_nhds (hSsmall hx))).differentiableAt one_ne_zero
  have hqd (x) (hx : x ∈ S) : DifferentiableAt ℝ q x :=
    (hq2.contDiffAt (isOpen_ball.mem_nhds (hSone hx))).differentiableAt (by norm_num)
  have hwH : HasC1HolderOn α w S :=
    boundary_neumann_c2_inhom_holder_sub huH hqH hud hqd
  have hgrad (x) (hx : x ∈ S) : gradient w x = gradient u x - gradient q x := by
    rw [boundary_neumann_c2_inhom_gradient_sub (hud x hx) (hqd x hx), hgu']
  have hfw (x) (hx : x ∈ S) : fderiv ℝ w x = fderiv ℝ u x - fderiv ℝ q x := by
    rw [← hfu' x]
    exact fderiv_fun_sub (hud x hx) (hqd x hx)
  -- the C¹,α bound for `w` on `S`
  have hfu_b (x) (hx : x ∈ S) : ‖fderiv ℝ u x‖ ≤ C := by
    have := hbu x (hSsmall hx)
    simpa only [gradient, LinearIsometryEquiv.norm_map] using this
  have hfu_h (x) (hx : x ∈ S) (y) (hy : y ∈ S) :
      ‖fderiv ℝ u x - fderiv ℝ u y‖ ≤ C * ‖x - y‖ ^ α := by
    have := hhu x (hSsmall hx) y (hSsmall hy)
    rw [dist_eq_norm] at this
    simpa only [gradient, ← map_sub, LinearIsometryEquiv.norm_map] using this
  have hfq_b (x) (hx : x ∈ S) : ‖fderiv ℝ q x‖ ≤ Q :=
    (hqH.derivative_holder.nondiv_norm_le hx).trans (hqH.derivative_norm_le.trans hqQ)
  have hfq_h (x) (hx : x ∈ S) (y) (hy : y ∈ S) :
      ‖fderiv ℝ q x - fderiv ℝ q y‖ ≤ Q * ‖x - y‖ ^ α := by
    refine (hqH.derivative_holder.nondiv_norm_sub_le hx hy).trans
      (mul_le_mul_of_nonneg_right ?_ (Real.rpow_nonneg (norm_nonneg _) α))
    have hs : holderSeminorm α (fderiv ℝ q) S ≤ holderNorm α (fderiv ℝ q) S :=
      le_add_of_nonneg_left (holderUniformNorm_nonneg hqH.derivative_holder.uniform_bounded)
    exact hs.trans (hqH.derivative_norm_le.trans hqQ)
  have hSd (x) (hx : x ∈ S) (y) (hy : y ∈ S) : ‖x - y‖ ≤ 1 := by
    have h1 := hSclosed hx
    have h2 := hSclosed hy
    rw [mem_closedBall, dist_zero_right] at h1 h2
    linarith [norm_sub_le x y]
  have hpow (x) (hx : x ∈ S) (y) (hy : y ∈ S) : ‖x - y‖ ≤ ‖x - y‖ ^ α := by
    by_cases hxy : x = y
    · subst hxy
      simp [Real.zero_rpow hα.ne']
    · have := Real.rpow_le_rpow_of_exponent_ge
        (norm_pos_iff.mpr (sub_ne_zero.mpr hxy)) (hSd x hx y hy) hα1.le
      simpa using this
  have hfw_b (x) (hx : x ∈ S) : ‖fderiv ℝ w x‖ ≤ G := by
    rw [hfw x hx]
    exact (norm_sub_le _ _).trans (add_le_add (hfu_b x hx) (hfq_b x hx))
  have hfw_h (x) (hx : x ∈ S) (y) (hy : y ∈ S) :
      ‖fderiv ℝ w x - fderiv ℝ w y‖ ≤ G * ‖x - y‖ ^ α := by
    rw [hfw x hx, hfw y hy]
    have e : fderiv ℝ u x - fderiv ℝ q x - (fderiv ℝ u y - fderiv ℝ q y) =
        (fderiv ℝ u x - fderiv ℝ u y) - (fderiv ℝ q x - fderiv ℝ q y) := by abel
    rw [e]
    calc _ ≤ ‖fderiv ℝ u x - fderiv ℝ u y‖ + ‖fderiv ℝ q x - fderiv ℝ q y‖ :=
          norm_sub_le _ _
      _ ≤ C * ‖x - y‖ ^ α + Q * ‖x - y‖ ^ α :=
          add_le_add (hfu_h x hx y hy) (hfq_h x hx y hy)
      _ = G * ‖x - y‖ ^ α := by dsimp only [G]; ring
  have hw_lip (x) (hx : x ∈ S) (y) (hy : y ∈ S) : ‖w x - w y‖ ≤ G * ‖x - y‖ :=
    Convex.norm_image_sub_le_of_norm_fderiv_le (f := w)
      (fun z hz => (hud z hz).sub (hqd z hz)) hfw_b hSconv hy hx
  have hw00 : w 0 = 0 := by
    change u 0 - (u 0 - q 0) - q 0 = 0
    ring
  have hwf : holderNorm α w S ≤ G + G := by
    change holderUniformNorm w S + holderSeminorm α w S ≤ G + G
    apply add_le_add
    · apply holderUniformNorm_le hG
      intro x hx
      have h1 := hw_lip x hx 0 h0S
      rw [hw00, sub_zero, sub_zero] at h1
      have h2 := hSd x hx 0 h0S
      rw [sub_zero] at h2
      exact h1.trans (mul_le_of_le_one_right hG h2)
    · apply holderSeminorm_le hG
      intro x hx y hy
      exact div_le_of_le_mul₀ (Real.rpow_nonneg (norm_nonneg _) α) hG
        ((hw_lip x hx y hy).trans (mul_le_mul_of_nonneg_left (hpow x hx y hy) hG))
  have hwd : holderNorm α (fderiv ℝ w) S ≤ G + G := by
    change holderUniformNorm (fderiv ℝ w) S + holderSeminorm α (fderiv ℝ w) S ≤ G + G
    apply add_le_add
    · exact holderUniformNorm_le hG hfw_b
    · apply holderSeminorm_le hG
      intro x hx y hy
      exact div_le_of_le_mul₀ (Real.rpow_nonneg (norm_nonneg _) α) hG (hfw_h x hx y hy)
  have hNb : nondivC1HolderNorm α w S + nondivC1HolderNorm α H S ≤ N0 :=
    add_le_add (add_le_add hwf hwd) hHQ
  -- the homogeneous flat problem for `w`
  obtain ⟨V, hV, hVs, hhV, hbV, hposV⟩ := hneigh
  have hproj (x) (hx : x ∈ S) : graphProjectionN 2 x ∈ V :=
    hVs (boundary_neumann_projection_closedBall (ball_subset_closedBall (hSone hx)))
  have hhd (x) (hx : x ∈ S) : DifferentiableAt ℝ h (graphProjectionN 2 x) :=
    (hhV.contDiffAt (hV.mem_nhds (hproj x hx))).differentiableAt one_ne_zero
  have hbd (x) (hx : x ∈ S) :
      DifferentiableAt ℝ (boundaryNeumannNormalCoefficient A) (graphProjectionN 2 x) :=
    (hbV.contDiffAt (hV.mem_nhds (hproj x hx))).differentiableAt one_ne_zero
  have hH0 : ∀ x ∈ S, x (Fin.last 2) = 0 → H x (Fin.last 2) = 0 :=
    fun x hx hx0 => boundaryNeumannInhomDatum_flat_of_elliptic hlam f hx0
      (hell x (hSunit hx)) (hhd x hx) (hbd x hx)
  have hw0 : ∀ x ∈ S, x (Fin.last 2) = 0 → gradient w x (Fin.last 2) = 0 := by
    intro x hx hx0
    have he : graphBaseEmbedding (graphProjectionN 2 x) = x := by
      rw [boundary_neumann_graphBase_eq_append, ← hx0, graphAppendN_projection]
    have hnon : boundaryNeumannNormalCoefficient A (graphProjectionN 2 x) ≠ 0 :=
      (hlam.trans_le (hposV _ (hproj x hx))).ne'
    have hqc := boundaryNeumannLift_conormal (hhd x hx) (hbd x hx) hnon
    rw [he] at hqc
    have huc := hface (graphProjectionN 2 x) (by rw [he]; exact hSsmall hx)
    rw [he] at huc
    apply boundary_neumann_c2_inhom_normal_zero
      (fun i hi => (hcross x (hSunit hx) hx0 i hi).1)
    · have hn := hnon
      rwa [boundaryNeumannNormalCoefficient_eq, he] at hn
    · rw [hgrad x hx, map_sub, PiLp.sub_apply]
      exact sub_eq_zero.mpr (huc.trans hqc.symm)
  have hred : IsBoundaryNeumannEquationOn A (fun x => F x - gradient q x) H 1 :=
    boundary_neumann_inhomogeneous_weak_reduction hα hα1.le hK hK
      hAc hbA hz.memLp_gradient hfc hbf hhf (hhV.continuousOn.mono hVs) hweak
  have hFsmall : F =ᵐ[volume.restrict (boundaryHalfBall (1 / 4))] gradient u :=
    ae_restrict_of_ae_restrict_of_subset (boundaryHalfBall_mono (by norm_num)) hFu
  have heq : IsBoundaryNeumannEquationOn A (gradient w) H (1 / 4) :=
    boundary_neumann_c2_inhom_equation_congr
      (boundary_neumann_c2_inhom_equation_mono (by norm_num : (1 / 4 : ℝ) ≤ 1) hred) (by
        filter_upwards [hFsmall,
          ae_restrict_mem (isOpen_boundaryHalfBall (1 / 4 : ℝ)).measurableSet]
          with x hx hxs
        rw [hgrad x (subset_closure hxs), hx])
  obtain ⟨hw2, hentries⟩ := hsc (by norm_num : (0 : ℝ) < 1 / 4) (by norm_num)
    A H w hAH hHH hwH hAQ hNb
    (fun x hx => hbA x (hSunit hx))
    (fun x hx => hell x (hSunit hx))
    (fun x hx => hcross x (hSunit hx)) hH0 hw0 heq
  let r : ℝ := 1 / 4 * (3 / 8)
  have hrsmall : boundaryHalfBall r ⊆ boundaryHalfBall (1 / 2) :=
    boundaryHalfBall_mono (by dsimp [r]; norm_num)
  have hrS : closure (boundaryHalfBall r) ⊆ S :=
    closure_mono (boundaryHalfBall_mono (by dsimp [r]; norm_num))
  have hrball : closure (boundaryHalfBall r) ⊆ ball (0 : EuclideanSpace ℝ (Fin 3)) 1 :=
    hrS.trans hSone
  have hq2r : ContDiffOn ℝ 2 q (boundaryHalfBall r) := hq2.mono (subset_closure.trans hrball)
  have he : (fun x => w x + q x) = u' := by funext x; exact sub_add_cancel _ _
  have hu2' : ContDiffOn ℝ 2 u' (boundaryHalfBall r) := by
    rw [← he]
    exact hw2.add hq2r
  have hu2 : ContDiffOn ℝ 2 u (boundaryHalfBall r) := by
    have e2 : u = fun x => u' x + c := by
      funext x
      change u x = u x - c + c
      ring
    rw [e2]
    exact hu2'.add contDiffOn_const
  have hEu (x) (i j : Fin 3) :
      boundaryNeumannC2Entry u' x i j = boundaryNeumannC2Entry u x i j := by
    simp only [boundaryNeumannC2Entry, hfu']
  refine ⟨u, hu, hu2,
    ae_restrict_of_ae_restrict_of_subset hrsmall hzu,
    ae_restrict_of_ae_restrict_of_subset hrsmall hFu, ?_, hface⟩
  intro i j
  obtain ⟨D, hDeq, hDc, hDb, hDh⟩ := hentries i j
  refine ⟨fun x => D x + boundaryNeumannC2Entry q x i j, ?_,
    hDc.add ((boundary_neumann_c2_inhom_entry_continuous isOpen_ball hq2 i j).mono hrball),
    ?_, ?_⟩
  · intro x hx
    change D x + boundaryNeumannC2Entry q x i j = boundaryNeumannC2Entry u x i j
    rw [hDeq hx, ← boundary_neumann_c2_inhom_entry_add (isOpen_boundaryHalfBall r) hw2 hq2r hx,
      he, hEu]
  · intro x hx
    have h1 := hDb x hx
    have h2 := hEb i j x (hrS hx)
    have hp1 : 0 ≤ ((1 / 4 : ℝ) ^ 2)⁻¹ * C0 * ((1 / 4 : ℝ)⁻¹) ^ α := by positivity
    calc |D x + boundaryNeumannC2Entry q x i j|
        ≤ |D x| + |boundaryNeumannC2Entry q x i j| := abs_add_le _ _
      _ ≤ C1 := by dsimp only [C1]; linarith
  · intro x hx y hy
    have h1 := hDh x hx y hy
    rw [Real.mul_rpow (by norm_num) dist_nonneg] at h1
    have h2 := hEh i j x (hrS hx) y (hrS hy)
    have h5 : 0 ≤ ((1 / 4 : ℝ) ^ 2)⁻¹ * C0 * dist x y ^ α := by positivity
    have hexp : C1 * dist x y ^ α =
        ((1 / 4 : ℝ) ^ 2)⁻¹ * (C0 * (((1 / 4 : ℝ)⁻¹) ^ α * dist x y ^ α)) +
          ((1 / 4 : ℝ) ^ 2)⁻¹ * C0 * dist x y ^ α + Q * dist x y ^ α := by
      dsimp only [C1]; ring
    have h6 : |D x + boundaryNeumannC2Entry q x i j -
        (D y + boundaryNeumannC2Entry q y i j)| ≤
        |D x - D y| + |boundaryNeumannC2Entry q x i j - boundaryNeumannC2Entry q y i j| := by
      have := abs_add_le (D x - D y)
        (boundaryNeumannC2Entry q x i j - boundaryNeumannC2Entry q y i j)
      have he' : D x - D y + (boundaryNeumannC2Entry q x i j - boundaryNeumannC2Entry q y i j) =
          D x + boundaryNeumannC2Entry q x i j - (D y + boundaryNeumannC2Entry q y i j) := by
        ring
      rwa [he'] at this
    change |D x + boundaryNeumannC2Entry q x i j -
        (D y + boundaryNeumannC2Entry q y i j)| ≤ C1 * dist x y ^ α
    linarith

/-- Smooth-data second assertion of `thm:boundary-neumann` with Hölder bounds on the
extended Hessian entries; the constant `Cb` depends on the data. -/
theorem boundary_neumann_c2_holder_inhom_smooth
    {α lam : ℝ} (hα : 0 < α) (hα1 : α < 1) (hlam : 0 < lam)
    {A : EuclideanSpace ℝ (Fin 3) → EuclideanSpace ℝ (Fin 3) →L[ℝ]
      EuclideanSpace ℝ (Fin 3)} {f z : EuclideanSpace ℝ (Fin 3) → ℝ}
    {F : EuclideanSpace ℝ (Fin 3) → EuclideanSpace ℝ (Fin 3)}
    {h : EuclideanSpace ℝ (Fin 2) → ℝ} {O : Set (EuclideanSpace ℝ (Fin 3))}
    (hO : IsOpen O) (hsub : closedBall 0 1 ⊆ O)
    (hA : ContDiffOn ℝ (⊤ : ℕ∞) A O) (hf : ContDiffOn ℝ (⊤ : ℕ∞) f O)
    (hh : ContDiff ℝ (⊤ : ℕ∞) h)
    (hell : ∀ x ∈ closure (boundaryHalfBall 1), ∀ ξ,
      lam * ‖ξ‖ ^ 2 ≤ inner ℝ (A x ξ) ξ)
    (hcross : ∀ x ∈ closure (boundaryHalfBall 1), x (Fin.last 2) = 0 →
      ∀ i : Fin 3, i ≠ Fin.last 2 →
        A x (EuclideanSpace.single i 1) (Fin.last 2) = 0 ∧
        A x (EuclideanSpace.single (Fin.last 2) 1) i = 0)
    (hpos : ∃ U : Set (EuclideanSpace ℝ (Fin 2)), IsOpen U ∧ closedBall 0 1 ⊆ U ∧
      ∀ x ∈ U, lam ≤ boundaryNeumannNormalCoefficient A x)
    (hz : HasH1GradientOn z F (boundaryHalfBall 1))
    (hweak : ∀ φ : EuclideanSpace ℝ (Fin 3) → ℝ, ContDiff ℝ 1 φ → HasCompactSupport φ →
      tsupport φ ⊆ ball 0 1 →
      (∫ x in boundaryHalfBall 1, inner ℝ (A x (F x)) (gradient φ x)) =
        -(∫ x in boundaryHalfBall 1, f x * φ x) -
          ∫ y in ball (0 : EuclideanSpace ℝ (Fin 2)) 1, h y * φ (graphBaseEmbedding y)) :
    ∃ u : EuclideanSpace ℝ (Fin 3) → ℝ,
      ContDiffOn ℝ 1 u (ball 0 (1 / 2 : ℝ)) ∧
      ContDiffOn ℝ 2 u (boundaryHalfBall (1 / 4 * (3 / 8))) ∧
      z =ᵐ[volume.restrict (boundaryHalfBall (1 / 4 * (3 / 8)))] u ∧
      F =ᵐ[volume.restrict (boundaryHalfBall (1 / 4 * (3 / 8)))] gradient u ∧
      (∃ Cb > 0, ∀ i j : Fin 3, ∃ D : EuclideanSpace ℝ (Fin 3) → ℝ,
        ContinuousOn D (closure (boundaryHalfBall (1 / 4 * (3 / 8)))) ∧
        EqOn D (fun x => boundaryNeumannC2Entry u x i j) (boundaryHalfBall (1 / 4 * (3 / 8))) ∧
        (∀ x ∈ closure (boundaryHalfBall (1 / 4 * (3 / 8))), |D x| ≤ Cb) ∧
        ∀ x ∈ closure (boundaryHalfBall (1 / 4 * (3 / 8))),
          ∀ y ∈ closure (boundaryHalfBall (1 / 4 * (3 / 8))),
            |D x - D y| ≤ Cb * dist x y ^ α) ∧
      (∀ y : EuclideanSpace ℝ (Fin 2), graphBaseEmbedding y ∈ ball 0 (1 / 2 : ℝ) →
        A (graphBaseEmbedding y) (gradient u (graphBaseEmbedding y)) (Fin.last 2) = h y) := by
  obtain ⟨cap, HA, B, hcap, hHA, hB, d⟩ :=
    boundary_neumann_c2_inhom_smooth_exists_data hα hα1 hO hsub hA hf hh hell hcross hpos
  let E := max (∫ x in boundaryHalfBall 1, ‖F x‖ ^ 2) 0
  obtain ⟨C, hC, hreg⟩ := boundary_neumann_c1_holder_conormal
    hα hα1 hlam hcap hHA hB (le_max_right _ _ : 0 ≤ E)
  obtain ⟨u, hu, hzu, hFu, hbu, hhu, hface⟩ := hreg A F z f h
    d.continuous_coefficient d.bound_coefficient d.elliptic d.holder_coefficient d.cross_face
    d.normal_neighborhood d.bound_datum d.bound_normal d.bound_gradient_datum
    d.bound_gradient_normal d.holder_gradient_datum d.holder_gradient_normal
    d.continuous_forcing d.bound_forcing d.holder_forcing hz (le_max_left _ _) hweak
  let q := boundaryNeumannLift h (boundaryNeumannNormalCoefficient A)
  let H := boundaryNeumannInhomDatum A f h
  let w := fun x => u x - q x
  obtain ⟨hqs, hHs⟩ := boundary_neumann_c2_inhom_smooth_lift_datum
    hlam hO hsub hA hf hh hpos
  let S := closure (boundaryHalfBall (1 / 4 : ℝ))
  have hSc : IsCompact S :=
    (isBounded_ball.subset (inter_subset_left : boundaryHalfBall (1 / 4 : ℝ) ⊆
      ball 0 (1 / 4 : ℝ))).isCompact_closure
  have hSconv : Convex ℝ S := (convex_boundaryHalfBall (1 / 4 : ℝ)).closure
  have hSclosed : S ⊆ closedBall (0 : EuclideanSpace ℝ (Fin 3)) (1 / 4 : ℝ) :=
    closure_minimal (inter_subset_left.trans ball_subset_closedBall) isClosed_closedBall
  have hSsmall : S ⊆ ball (0 : EuclideanSpace ℝ (Fin 3)) (1 / 2 : ℝ) :=
    hSclosed.trans (closedBall_subset_ball (by norm_num))
  have hSone : S ⊆ ball (0 : EuclideanSpace ℝ (Fin 3)) 1 :=
    hSclosed.trans (closedBall_subset_ball (by norm_num))
  have hSunit : S ⊆ closure (boundaryHalfBall 1) :=
    closure_mono (boundaryHalfBall_mono (by norm_num))
  have hAH : HasC1HolderOn α A S := hasC1HolderOn_of_contDiffOn hα.le hα1.le
    hSc hSconv hO (hSone.trans (ball_subset_closedBall.trans hsub)) hA
  have hHH : HasC1HolderOn α H S := hasC1HolderOn_of_contDiffOn hα.le hα1.le
    hSc hSconv isOpen_ball hSone hHs
  have hqH : HasC1HolderOn α q S := hasC1HolderOn_of_contDiffOn hα.le hα1.le
    hSc hSconv isOpen_ball hSone hqs
  have huH : HasC1HolderOn α u S := boundary_neumann_c2_inhom_holder_of_gradient
    hα.le hα1.le hC.le hSc hSconv isOpen_ball hSsmall hu
    (fun x hx => hbu x (hSsmall hx))
    (fun x hx y hy => hhu x (hSsmall hx) y (hSsmall hy))
  have hud (x) (hx : x ∈ S) : DifferentiableAt ℝ u x :=
    (hu.contDiffAt (isOpen_ball.mem_nhds (hSsmall hx))).differentiableAt one_ne_zero
  have hqd (x) (hx : x ∈ S) : DifferentiableAt ℝ q x :=
    (hqs.contDiffAt (isOpen_ball.mem_nhds (hSone hx))).differentiableAt (by simp)
  have hwH : HasC1HolderOn α w S :=
    boundary_neumann_c2_inhom_holder_sub huH hqH hud hqd
  have hgrad (x) (hx : x ∈ S) : gradient w x = gradient u x - gradient q x :=
    boundary_neumann_c2_inhom_gradient_sub (hud x hx) (hqd x hx)
  obtain ⟨V, hV, hVs, hhV, hbV, hposV⟩ := d.normal_neighborhood
  have hproj (x) (hx : x ∈ S) : graphProjectionN 2 x ∈ V :=
    hVs (boundary_neumann_projection_closedBall (ball_subset_closedBall (hSone hx)))
  have hhd (x) (hx : x ∈ S) : DifferentiableAt ℝ h (graphProjectionN 2 x) :=
    (hhV.contDiffAt (hV.mem_nhds (hproj x hx))).differentiableAt one_ne_zero
  have hbd (x) (hx : x ∈ S) :
      DifferentiableAt ℝ (boundaryNeumannNormalCoefficient A) (graphProjectionN 2 x) :=
    (hbV.contDiffAt (hV.mem_nhds (hproj x hx))).differentiableAt one_ne_zero
  have hH0 : ∀ x ∈ S, x (Fin.last 2) = 0 → H x (Fin.last 2) = 0 :=
    fun x hx hx0 => boundaryNeumannInhomDatum_flat_of_elliptic hlam f hx0
      (hell x (hSunit hx)) (hhd x hx) (hbd x hx)
  have hw0 : ∀ x ∈ S, x (Fin.last 2) = 0 → gradient w x (Fin.last 2) = 0 := by
    intro x hx hx0
    have he : graphBaseEmbedding (graphProjectionN 2 x) = x := by
      rw [boundary_neumann_graphBase_eq_append, ← hx0, graphAppendN_projection]
    have hnon : boundaryNeumannNormalCoefficient A (graphProjectionN 2 x) ≠ 0 :=
      (hlam.trans_le (hposV _ (hproj x hx))).ne'
    have hqc := boundaryNeumannLift_conormal (hhd x hx) (hbd x hx) hnon
    rw [he] at hqc
    have huc := hface (graphProjectionN 2 x) (by rw [he]; exact hSsmall hx)
    rw [he] at huc
    apply boundary_neumann_c2_inhom_normal_zero
      (fun i hi => (hcross x (hSunit hx) hx0 i hi).1)
    · have hn := hnon
      rwa [boundaryNeumannNormalCoefficient_eq, he] at hn
    · rw [hgrad x hx, map_sub, PiLp.sub_apply]
      exact sub_eq_zero.mpr (huc.trans hqc.symm)
  have hred : IsBoundaryNeumannEquationOn A (fun x => F x - gradient q x) H 1 :=
    boundary_neumann_inhomogeneous_weak_reduction hα hα1.le hB hB
      d.continuous_coefficient d.bound_coefficient hz.memLp_gradient d.continuous_forcing
      d.bound_forcing d.holder_forcing hh.continuous.continuousOn hweak
  have hFsmall : F =ᵐ[volume.restrict (boundaryHalfBall (1 / 4))] gradient u :=
    ae_restrict_of_ae_restrict_of_subset (boundaryHalfBall_mono (by norm_num)) hFu
  have heq : IsBoundaryNeumannEquationOn A (gradient w) H (1 / 4) :=
    boundary_neumann_c2_inhom_equation_congr
      (boundary_neumann_c2_inhom_equation_mono (by norm_num : (1 / 4 : ℝ) ≤ 1) hred) (by
        filter_upwards [hFsmall,
          ae_restrict_mem (isOpen_boundaryHalfBall (1 / 4 : ℝ)).measurableSet]
          with x hx hxs
        rw [hgrad x (subset_closure hxs), hx])
  obtain ⟨C0, hC0, hreg2⟩ := boundary_neumann_c2_holder_scaled hα hα1 hlam hcap
    hAH.norm_nonneg (add_nonneg hwH.norm_nonneg hHH.norm_nonneg)
  obtain ⟨hw2, hentries⟩ := hreg2 (by norm_num : (0 : ℝ) < 1 / 4) (by norm_num)
    A H w hAH hHH hwH le_rfl le_rfl
    (fun x hx => d.bound_coefficient x (hSunit hx))
    (fun x hx => hell x (hSunit hx))
    (fun x hx => hcross x (hSunit hx)) hH0 hw0 heq
  let r : ℝ := 1 / 4 * (3 / 8)
  have hrsmall : boundaryHalfBall r ⊆ boundaryHalfBall (1 / 2) :=
    boundaryHalfBall_mono (by dsimp [r]; norm_num)
  have hrball : closure (boundaryHalfBall r) ⊆ ball (0 : EuclideanSpace ℝ (Fin 3)) 1 :=
    (closure_mono (boundaryHalfBall_mono (by dsimp [r]; norm_num : r ≤ 1 / 4))).trans hSone
  have hq2 : ContDiffOn ℝ 2 q (boundaryHalfBall r) :=
    (hqs.of_le (by simp)).mono (subset_closure.trans hrball)
  have he : (fun x => w x + q x) = u := by funext x; exact sub_add_cancel _ _
  have hu2 : ContDiffOn ℝ 2 u (boundaryHalfBall r) := by
    rw [← he]
    exact hw2.add hq2
  let K := closure (boundaryHalfBall r)
  have hKc : IsCompact K :=
    (isBounded_ball.subset (inter_subset_left : boundaryHalfBall r ⊆
      ball 0 r)).isCompact_closure
  have hKconv : Convex ℝ K := (convex_boundaryHalfBall r).closure
  have hq3 : ContDiffOn ℝ 2 q (ball 0 1) := hqs.of_le (by simp)
  have hEc : ∀ i j : Fin 3,
      ContDiffOn ℝ 1 (fun x => boundaryNeumannC2Entry q x i j) (ball 0 1) := by
    intro i j
    have hd : ContDiffOn ℝ 1 (fderiv ℝ (fderiv ℝ q)) (ball 0 1) :=
      (hqs.fderiv_of_isOpen isOpen_ball (m := 2) (by simp)).fderiv_of_isOpen
        isOpen_ball (by norm_num)
    have hc : ContDiffOn ℝ 1 (fun x =>
        fderiv ℝ (fderiv ℝ q) x (EuclideanSpace.single i 1) (EuclideanSpace.single j 1))
        (ball 0 1) :=
      (hd.clm_apply contDiffOn_const).clm_apply contDiffOn_const
    apply hc.congr
    intro x hx
    dsimp only [boundaryNeumannC2Entry]
    rw [nondiv_fderiv_coordinate_eq isOpen_ball hq3 j hx]
    rfl
  have hEH : ∀ i j : Fin 3,
      HasFiniteHolderNormOn α (fun x => boundaryNeumannC2Entry q x i j) K :=
    fun i j => boundary_neumann_c2_inhom_finiteHolder_of_contDiffOn hα.le hα1.le hKc hKconv
      isOpen_ball hrball (hEc i j)
  let N : Fin 3 → Fin 3 → ℝ := fun i j =>
    holderNorm α (fun x => boundaryNeumannC2Entry q x i j) K
  let Qs : ℝ := ∑ i, ∑ j, N i j
  have hNQ : ∀ i j, N i j ≤ Qs := by
    intro i j
    have h1 : N i j ≤ ∑ j', N i j' :=
      Finset.single_le_sum (f := N i) (fun j' _ => (hEH i j').norm_nonneg)
        (Finset.mem_univ j)
    have h2 : ∑ j', N i j' ≤ Qs :=
      Finset.single_le_sum (f := fun i' => ∑ j', N i' j')
        (fun i' _ => Finset.sum_nonneg (fun j' _ => (hEH i' j').norm_nonneg))
        (Finset.mem_univ i)
    exact h1.trans h2
  have hQs : 0 ≤ Qs := (hEH 0 0).norm_nonneg.trans (hNQ 0 0)
  let C1 : ℝ := ((1 / 4 : ℝ) ^ 2)⁻¹ * C0 * ((1 / 4 : ℝ)⁻¹) ^ α +
    ((1 / 4 : ℝ) ^ 2)⁻¹ * C0 + Qs
  have hC1 : 0 < C1 :=
    add_pos_of_pos_of_nonneg (add_pos_of_nonneg_of_pos (by positivity) (by positivity)) hQs
  refine ⟨u, hu, hu2,
    ae_restrict_of_ae_restrict_of_subset hrsmall hzu,
    ae_restrict_of_ae_restrict_of_subset hrsmall hFu, ⟨C1, hC1, ?_⟩, hface⟩
  intro i j
  obtain ⟨D, hDeq, hDc, hDb, hDh⟩ := hentries i j
  have hEi := hEH i j
  refine ⟨fun x => D x + boundaryNeumannC2Entry q x i j,
    hDc.add ((boundary_neumann_c2_inhom_entry_continuous isOpen_ball
      (hqs.of_le (by simp)) i j).mono hrball), ?_, ?_, ?_⟩
  · intro x hx
    change D x + boundaryNeumannC2Entry q x i j = boundaryNeumannC2Entry u x i j
    rw [hDeq hx, ← boundary_neumann_c2_inhom_entry_add (isOpen_boundaryHalfBall r) hw2 hq2 hx,
      he]
  · intro x hx
    have h1 := hDb x hx
    have h2 : |boundaryNeumannC2Entry q x i j| ≤ N i j := by
      have := hEi.nondiv_norm_le hx
      rwa [Real.norm_eq_abs] at this
    have h3 := hNQ i j
    have hp1 : 0 ≤ ((1 / 4 : ℝ) ^ 2)⁻¹ * C0 * ((1 / 4 : ℝ)⁻¹) ^ α := by positivity
    calc |D x + boundaryNeumannC2Entry q x i j|
        ≤ |D x| + |boundaryNeumannC2Entry q x i j| := abs_add_le _ _
      _ ≤ C1 := by dsimp only [C1]; linarith
  · intro x hx y hy
    have h1 := hDh x hx y hy
    rw [Real.mul_rpow (by norm_num) dist_nonneg] at h1
    have h2 := hEi.nondiv_norm_sub_le hx hy
    rw [Real.norm_eq_abs, ← dist_eq_norm] at h2
    have hsN : holderSeminorm α (fun x => boundaryNeumannC2Entry q x i j) K ≤ N i j :=
      le_add_of_nonneg_left (holderUniformNorm_nonneg hEi.uniform_bounded)
    have hdα : 0 ≤ dist x y ^ α := Real.rpow_nonneg dist_nonneg α
    have h4 : holderSeminorm α (fun x => boundaryNeumannC2Entry q x i j) K * dist x y ^ α ≤
        Qs * dist x y ^ α :=
      mul_le_mul_of_nonneg_right (hsN.trans (hNQ i j)) hdα
    have h5 : 0 ≤ ((1 / 4 : ℝ) ^ 2)⁻¹ * C0 * dist x y ^ α := by positivity
    have hexp : C1 * dist x y ^ α =
        ((1 / 4 : ℝ) ^ 2)⁻¹ * (C0 * (((1 / 4 : ℝ)⁻¹) ^ α * dist x y ^ α)) +
          ((1 / 4 : ℝ) ^ 2)⁻¹ * C0 * dist x y ^ α + Qs * dist x y ^ α := by
      dsimp only [C1]; ring
    have h6 : |D x + boundaryNeumannC2Entry q x i j -
        (D y + boundaryNeumannC2Entry q y i j)| ≤
        |D x - D y| + |boundaryNeumannC2Entry q x i j - boundaryNeumannC2Entry q y i j| := by
      have := abs_add_le (D x - D y)
        (boundaryNeumannC2Entry q x i j - boundaryNeumannC2Entry q y i j)
      have he' : D x - D y + (boundaryNeumannC2Entry q x i j - boundaryNeumannC2Entry q y i j) =
          D x + boundaryNeumannC2Entry q x i j - (D y + boundaryNeumannC2Entry q y i j) := by
        ring
      rwa [he'] at this
    change |D x + boundaryNeumannC2Entry q x i j -
        (D y + boundaryNeumannC2Entry q y i j)| ≤ C1 * dist x y ^ α
    linarith

end LiquidDrop

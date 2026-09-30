module

public import NoCompromise.Elliptic.BoundaryNeumannC2InhomHolder

@[expose] public section

/-!
# Flat boundary C²,α bounds for inhomogeneous conormal data of finite regularity

Second assertion of blueprint `thm:boundary-neumann` with the Hölder bounds on the
continuous extensions of the second-derivative entries, for coefficients `A` of class
`C³`, forcing `f` of class `C²` and boundary datum `h` of class `C³` on neighborhoods of
the closed unit ball. The radius is `1/4 * (3/8)`. The proof follows
`boundary_neumann_c2_holder_inhom_smooth`, using only finite-order consequences of the
hypotheses: the lift `q = x₃ h / b` is `C³` and the reduced datum `H` is `C²` on the unit
ball, which give `C¹,α` bounds for `A`, `H` and the Hessian entries of `q` on compact
convex subsets.
-/

noncomputable section
open Set Filter Metric InnerProductSpace MeasureTheory
open scoped Topology Gradient RealInnerProductSpace
namespace LiquidDrop

/-- `C²` data have genuine `C¹,α` regularity on each compact convex subset of
their open domain. -/
theorem hasC1HolderOn_of_contDiffOn_two
    {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [NormedAddCommGroup F] [NormedSpace ℝ F]
    {α : ℝ} (hα : 0 ≤ α) (hα1 : α ≤ 1)
    {g : E → F} {K O : Set E} (hK : IsCompact K) (hcK : Convex ℝ K)
    (hO : IsOpen O) (hKO : K ⊆ O) (hg : ContDiffOn ℝ 2 g O) :
    HasC1HolderOn α g K := by
  have hg1 : ContDiffOn ℝ 1 g O := hg.of_le (by norm_num)
  have hD : ContDiffOn ℝ 1 (fderiv ℝ g) O :=
    hg.fderiv_of_isOpen hO (by norm_num)
  exact ⟨hg1.mono hKO,
    boundary_neumann_c2_inhom_finiteHolder_of_contDiffOn hα hα1 hK hcK hO hKO hg1,
    boundary_neumann_c2_inhom_finiteHolder_of_contDiffOn hα hα1 hK hcK hO hKO hD⟩

lemma boundaryNeumannNormalCoefficient_contDiffOn_n {n : WithTop ℕ∞}
    {A : EuclideanSpace ℝ (Fin 3) → EuclideanSpace ℝ (Fin 3) →L[ℝ]
      EuclideanSpace ℝ (Fin 3)} {O : Set (EuclideanSpace ℝ (Fin 3))}
    (hA : ContDiffOn ℝ n A O) :
    ContDiffOn ℝ n (boundaryNeumannNormalCoefficient A)
      (graphBaseEmbedding ⁻¹' O) := by
  have he := hA.comp graphBaseEmbedding.contDiff.contDiffOn (fun _ ht => ht)
  exact (he.clm_apply contDiffOn_const).inner ℝ contDiffOn_const

lemma boundaryNeumannLift_contDiffOn_n {n : WithTop ℕ∞} {h b : EuclideanSpace ℝ (Fin 2) → ℝ}
    {U : Set (EuclideanSpace ℝ (Fin 2))}
    (hh : ContDiffOn ℝ n h U) (hb : ContDiffOn ℝ n b U)
    (hb0 : ∀ y ∈ U, b y ≠ 0) :
    ContDiffOn ℝ n (boundaryNeumannLift h b) ((graphProjectionN 2) ⁻¹' U) := by
  exact (EuclideanSpace.proj (Fin.last 2)).contDiff.contDiffOn.mul
    ((hh.div hb hb0).comp (graphProjectionN 2).contDiff.contDiffOn (fun _ hx => hx))

/-- No coefficient, forcing, or boundary-data norm is assumed: the constants
in the C¹ conormal theorem follow from `A ∈ C²`, `f ∈ C¹`, `h ∈ C²` on the stated
neighborhoods. -/
theorem boundary_neumann_c2_inhom_exists_data_contDiff
    {α lam : ℝ} (hα : 0 < α) (hα1 : α < 1)
    {A : EuclideanSpace ℝ (Fin 3) → EuclideanSpace ℝ (Fin 3) →L[ℝ]
      EuclideanSpace ℝ (Fin 3)} {f : EuclideanSpace ℝ (Fin 3) → ℝ}
    {h : EuclideanSpace ℝ (Fin 2) → ℝ} {O : Set (EuclideanSpace ℝ (Fin 3))}
    (hO : IsOpen O) (hsub : closedBall 0 1 ⊆ O)
    (hA : ContDiffOn ℝ 2 A O) (hf : ContDiffOn ℝ 1 f O)
    (hh : ContDiff ℝ 2 h)
    (hell : ∀ x ∈ closure (boundaryHalfBall 1), ∀ ξ,
      lam * ‖ξ‖ ^ 2 ≤ inner ℝ (A x ξ) ξ)
    (hcross : ∀ x ∈ closure (boundaryHalfBall 1), x (Fin.last 2) = 0 →
      ∀ i : Fin 3, i ≠ Fin.last 2 →
        A x (EuclideanSpace.single i 1) (Fin.last 2) = 0 ∧
        A x (EuclideanSpace.single (Fin.last 2) 1) i = 0)
    (hpos : ∃ U : Set (EuclideanSpace ℝ (Fin 2)), IsOpen U ∧ closedBall 0 1 ⊆ U ∧
      ∀ x ∈ U, lam ≤ boundaryNeumannNormalCoefficient A x) :
    ∃ cap HA K : ℝ, 0 ≤ cap ∧ 0 ≤ HA ∧ 0 ≤ K ∧
      NeumannChartC1Data A f h α lam cap HA K := by
  obtain ⟨U, hU, hUs, hUp⟩ := hpos
  let V := U ∩ graphBaseEmbedding ⁻¹' O
  have hV : IsOpen V := hU.inter (hO.preimage graphBaseEmbedding.continuous)
  have hVs : closedBall (0 : EuclideanSpace ℝ (Fin 2)) 1 ⊆ V := by
    intro x hx
    refine ⟨hUs hx, hsub ?_⟩
    simpa only [mem_closedBall, dist_zero_right, norm_graphBaseEmbedding] using hx
  have hb : ContDiffOn ℝ 2 (boundaryNeumannNormalCoefficient A) V :=
    (boundaryNeumannNormalCoefficient_contDiffOn_n hA).mono inter_subset_right
  have hgrad (g : EuclideanSpace ℝ (Fin 2) → ℝ)
      (hg : ContDiffOn ℝ 2 g V) :
      ContDiffOn ℝ 1 (gradient g) V :=
    (toDual ℝ (EuclideanSpace ℝ (Fin 2))).symm.contDiff.comp_contDiffOn
      (hg.fderiv_of_isOpen hV (by norm_num))
  have bounds {n : ℕ} {E : Type} [NormedAddCommGroup E] [NormedSpace ℝ E]
      {g : EuclideanSpace ℝ (Fin n) → E} {W : Set (EuclideanSpace ℝ (Fin n))}
      (hW : IsOpen W) (hs : closedBall 0 1 ⊆ W)
      (hg : ContDiffOn ℝ 1 g W) :=
    boundary_neumann_c2_inhom_compact_bounds hα.le hα1.le
      (isCompact_closedBall (0 : EuclideanSpace ℝ (Fin n)) 1)
      (convex_closedBall (0 : EuclideanSpace ℝ (Fin n)) 1) hW hs hg
  obtain ⟨BA, hBA, hbA, hhA⟩ := bounds hO hsub (hA.of_le (by norm_num))
  obtain ⟨Kf, hKf, hbf, hhf⟩ := bounds hO hsub hf
  obtain ⟨Kh, hKh, hbh, -⟩ := bounds hV hVs (hh.contDiffOn.of_le (by norm_num))
  obtain ⟨Kb, hKb, hbb, -⟩ := bounds hV hVs (hb.of_le (by norm_num))
  obtain ⟨KDh, hKDh, hbDh, hhDh⟩ := bounds hV hVs (hgrad h hh.contDiffOn)
  obtain ⟨KDb, hKDb, hbDb, hhDb⟩ := bounds hV hVs (hgrad _ hb)
  let K := Kf + Kh + Kb + KDh + KDb
  have hK : 0 ≤ K := by dsimp [K]; positivity
  have hKf' : Kf ≤ K := by dsimp [K]; linarith
  have hKh' : Kh ≤ K := by dsimp [K]; linarith
  have hKb' : Kb ≤ K := by dsimp [K]; linarith
  have hKDh' : KDh ≤ K := by dsimp [K]; linarith
  have hKDb' : KDb ≤ K := by dsimp [K]; linarith
  have hclosed : closure (boundaryHalfBall 1) ⊆
      closedBall (0 : EuclideanSpace ℝ (Fin 3)) 1 :=
    fun x hx => by simpa only [mem_closedBall, dist_zero_right] using
      boundary_neumann_closed_norm_le hx
  refine ⟨BA, BA, K, hBA, hBA, hK, ?_⟩
  refine ⟨hA.continuousOn.mono (hclosed.trans hsub),
    fun x hx => hbA x (hclosed hx), hell,
    fun x hx y hy => hhA x (hclosed hx) y (hclosed hy), hcross,
    ⟨V, hV, hVs, (hh.of_le (by norm_num)).contDiffOn,
      hb.of_le (by norm_num), fun x hx => hUp x hx.1⟩,
    fun x hx => (hbh x hx).trans hKh', fun x hx => (hbb x hx).trans hKb',
    fun x hx => (hbDh x hx).trans hKDh', fun x hx => (hbDb x hx).trans hKDb',
    ?_, ?_, hf.continuousOn.mono (hclosed.trans hsub),
    fun x hx => (hbf x (hclosed hx)).trans hKf', ?_⟩
  · intro x hx y hy
    exact (hhDh x hx y hy).trans
      (mul_le_mul_of_nonneg_right hKDh' (Real.rpow_nonneg dist_nonneg _))
  · intro x hx y hy
    exact (hhDb x hx y hy).trans
      (mul_le_mul_of_nonneg_right hKDb' (Real.rpow_nonneg dist_nonneg _))
  · intro x hx y hy
    exact (hhf x (hclosed hx) y (hclosed hy)).trans
      (mul_le_mul_of_nonneg_right hKf' (Real.rpow_nonneg dist_nonneg _))

/-- The vertical primitive of a forcing of class `Cⁿ` on a neighborhood of the closed
unit ball is of class `Cⁿ` on the open unit ball. -/
theorem boundaryNeumannPrimitive_contDiffOn_n (n : ℕ)
    {f : EuclideanSpace ℝ (Fin 3) → ℝ} {O : Set (EuclideanSpace ℝ (Fin 3))}
    (hO : IsOpen O) (hsub : closedBall 0 1 ⊆ O)
    (hf : ContDiffOn ℝ n f O) :
    ContDiffOn ℝ n (boundaryNeumannPrimitive f) (ball 0 1) := by
  let V (p : EuclideanSpace ℝ (Fin 3) × ℝ) := boundaryNeumannVerticalContraction p.2 p.1
  have hV : ContDiff ℝ n V := by
    unfold V boundaryNeumannVerticalContraction graphAppendN
    exact ((graphBaseN 2).contDiff.comp ((graphProjectionN 2).contDiff.comp contDiff_fst)).add
      ((contDiff_snd.mul ((EuclideanSpace.proj (Fin.last 2) :
        EuclideanSpace ℝ (Fin 3) →L[ℝ] ℝ).contDiff.comp contDiff_fst)).smul
        contDiff_const)
  have hmaps : closedBall 0 1 ×ˢ Icc (0 : ℝ) 1 ⊆ V ⁻¹' O := by
    intro p hp
    apply hsub
    simp only [mem_prod, mem_closedBall, dist_zero_right] at hp ⊢
    exact (boundaryNeumannVerticalContraction_norm hp.2 p.1).trans hp.1
  have hI : ContDiffOn ℝ n
      (fun x => ∫ t in (0 : ℝ)..1, f (boundaryNeumannVerticalContraction t x)) (ball 0 1) :=
    boundary_neumann_c2_inhom_integral_contDiffOn n
      (hO.preimage hV.continuous) hmaps (hf.comp hV.contDiffOn (fun _ hx => hx))
  have he : boundaryNeumannPrimitive f = fun x =>
      (x (Fin.last 2) * ∫ t in (0 : ℝ)..1, f (boundaryNeumannVerticalContraction t x)) •
        EuclideanSpace.single (Fin.last 2) 1 :=
    funext (boundaryNeumannPrimitive_normalized f)
  rw [he]
  exact ((EuclideanSpace.proj (Fin.last 2) :
    EuclideanSpace ℝ (Fin 3) →L[ℝ] ℝ).contDiff.contDiffOn.mul hI).smul contDiffOn_const

/-- With `A ∈ C³`, `f ∈ C²` and `h ∈ C³`, the lift `q = x₃ h / b` is `C³` and the
reduced datum `H` is `C²` on the open unit ball. -/
theorem boundary_neumann_c2_inhom_lift_datum_contDiff
    {lam : ℝ} (hlam : 0 < lam)
    {A : EuclideanSpace ℝ (Fin 3) → EuclideanSpace ℝ (Fin 3) →L[ℝ]
      EuclideanSpace ℝ (Fin 3)} {f : EuclideanSpace ℝ (Fin 3) → ℝ}
    {h : EuclideanSpace ℝ (Fin 2) → ℝ} {O : Set (EuclideanSpace ℝ (Fin 3))}
    (hO : IsOpen O) (hsub : closedBall 0 1 ⊆ O)
    (hA : ContDiffOn ℝ 3 A O) (hf : ContDiffOn ℝ 2 f O)
    (hh : ContDiff ℝ 3 h)
    (hpos : ∃ U : Set (EuclideanSpace ℝ (Fin 2)), IsOpen U ∧ closedBall 0 1 ⊆ U ∧
      ∀ x ∈ U, lam ≤ boundaryNeumannNormalCoefficient A x) :
    ContDiffOn ℝ 3 (boundaryNeumannLift h (boundaryNeumannNormalCoefficient A))
      (ball 0 1) ∧
    ContDiffOn ℝ 2 (boundaryNeumannInhomDatum A f h) (ball 0 1) := by
  obtain ⟨U, -, hUs, hUp⟩ := hpos
  let V := U ∩ graphBaseEmbedding ⁻¹' O
  have hb : ContDiffOn ℝ 3 (boundaryNeumannNormalCoefficient A) V :=
    (boundaryNeumannNormalCoefficient_contDiffOn_n hA).mono inter_subset_right
  have hVs : closedBall (0 : EuclideanSpace ℝ (Fin 2)) 1 ⊆ V := by
    intro x hx
    refine ⟨hUs hx, hsub ?_⟩
    simpa only [mem_closedBall, dist_zero_right, norm_graphBaseEmbedding] using hx
  have hq : ContDiffOn ℝ 3
      (boundaryNeumannLift h (boundaryNeumannNormalCoefficient A)) (ball 0 1) :=
    (boundaryNeumannLift_contDiffOn_n hh.contDiffOn hb
      (fun x hx => (hlam.trans_le (hUp x hx.1)).ne')).mono
        (fun x hx => hVs (boundary_neumann_projection_closedBall (ball_subset_closedBall hx)))
  refine ⟨hq, ?_⟩
  have hg : ContDiffOn ℝ 2
      (gradient (boundaryNeumannLift h (boundaryNeumannNormalCoefficient A))) (ball 0 1) :=
    (toDual ℝ (EuclideanSpace ℝ (Fin 3))).symm.contDiff.comp_contDiffOn
      (hq.fderiv_of_isOpen isOpen_ball (by norm_num))
  exact ((boundaryNeumannPrimitive_contDiffOn_n 2 hO hsub hf).add
    ((hh.comp (graphProjectionN 2).contDiff).contDiffOn.of_le (by norm_num)
      |>.smul contDiffOn_const)).sub
      (((hA.mono (ball_subset_closedBall.trans hsub)).of_le (by norm_num)).clm_apply hg)

theorem boundary_neumann_c2_holder_inhom_contDiff
    {α lam : ℝ} (hα : 0 < α) (hα1 : α < 1) (hlam : 0 < lam)
    {A : EuclideanSpace ℝ (Fin 3) → EuclideanSpace ℝ (Fin 3) →L[ℝ]
      EuclideanSpace ℝ (Fin 3)} {f z : EuclideanSpace ℝ (Fin 3) → ℝ}
    {F : EuclideanSpace ℝ (Fin 3) → EuclideanSpace ℝ (Fin 3)}
    {h : EuclideanSpace ℝ (Fin 2) → ℝ} {O : Set (EuclideanSpace ℝ (Fin 3))}
    (hO : IsOpen O) (hsub : closedBall 0 1 ⊆ O)
    (hA : ContDiffOn ℝ 3 A O) (hf : ContDiffOn ℝ 2 f O)
    (hh : ContDiff ℝ 3 h)
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
    boundary_neumann_c2_inhom_exists_data_contDiff hα hα1 hO hsub
      (hA.of_le (by norm_num)) (hf.of_le (by norm_num)) (hh.of_le (by norm_num))
      hell hcross hpos
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
  obtain ⟨hqs, hHs⟩ := boundary_neumann_c2_inhom_lift_datum_contDiff
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
  have hAH : HasC1HolderOn α A S := hasC1HolderOn_of_contDiffOn_two hα.le hα1.le
    hSc hSconv hO (hSone.trans (ball_subset_closedBall.trans hsub)) (hA.of_le (by norm_num))
  have hHH : HasC1HolderOn α H S := hasC1HolderOn_of_contDiffOn_two hα.le hα1.le
    hSc hSconv isOpen_ball hSone hHs
  have hqH : HasC1HolderOn α q S := hasC1HolderOn_of_contDiffOn_two hα.le hα1.le
    hSc hSconv isOpen_ball hSone (hqs.of_le (by norm_num))
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
    (hqs.of_le (by norm_num)).mono (subset_closure.trans hrball)
  have he : (fun x => w x + q x) = u := by funext x; exact sub_add_cancel _ _
  have hu2 : ContDiffOn ℝ 2 u (boundaryHalfBall r) := by
    rw [← he]
    exact hw2.add hq2
  let K := closure (boundaryHalfBall r)
  have hKc : IsCompact K :=
    (isBounded_ball.subset (inter_subset_left : boundaryHalfBall r ⊆
      ball 0 r)).isCompact_closure
  have hKconv : Convex ℝ K := (convex_boundaryHalfBall r).closure
  have hq3 : ContDiffOn ℝ 2 q (ball 0 1) := hqs.of_le (by norm_num)
  have hEc : ∀ i j : Fin 3,
      ContDiffOn ℝ 1 (fun x => boundaryNeumannC2Entry q x i j) (ball 0 1) := by
    intro i j
    have hd : ContDiffOn ℝ 1 (fderiv ℝ (fderiv ℝ q)) (ball 0 1) :=
      (hqs.fderiv_of_isOpen isOpen_ball (m := 2) (by norm_num)).fderiv_of_isOpen
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
      (hqs.of_le (by norm_num)) i j).mono hrball), ?_, ?_, ?_⟩
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

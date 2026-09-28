import NoCompromise.Elliptic.BoundaryNeumannC2InhomFinite
import NoCompromise.Elliptic.BoundaryNeumannC2HolderAlgebra

/-!
# C¹,α bounds for the vertical primitive of the Neumann source

The normalized primitive is `x₃ · I(x)` with `I(x) = ∫₀¹ f(x', t x₃) dt`. The
contraction `x ↦ (x', t x₃)` is linear of norm at most one, so differentiation
under the integral gives `DI(x) = ∫₀¹ Df(x', t x₃) ∘ V_t dt`, and every C⁰,α
bound for `f` and `Df` on the closed unit ball passes to `I` and `DI`.
-/

noncomputable section
open Set Filter Metric MeasureTheory
open scoped Topology Interval
namespace LiquidDrop
set_option maxSynthPendingDepth 8

/-- The vertical contraction `x ↦ (x', t x₃)` as a continuous linear map. -/
def boundaryNeumannVerticalCLM (t : ℝ) :
    EuclideanSpace ℝ (Fin 3) →L[ℝ] EuclideanSpace ℝ (Fin 3) :=
  (graphBaseN 2).comp (graphProjectionN 2) +
    t • (EuclideanSpace.proj (Fin.last 2) :
      EuclideanSpace ℝ (Fin 3) →L[ℝ] ℝ).smulRight (EuclideanSpace.single (Fin.last 2) 1)

lemma boundaryNeumannVerticalCLM_apply (t : ℝ) (x : EuclideanSpace ℝ (Fin 3)) :
    boundaryNeumannVerticalCLM t x = boundaryNeumannVerticalContraction t x := by
  simp [boundaryNeumannVerticalCLM, boundaryNeumannVerticalContraction, graphAppendN, smul_smul]

lemma boundaryNeumannVerticalCLM_continuous : Continuous boundaryNeumannVerticalCLM := by
  unfold boundaryNeumannVerticalCLM
  fun_prop

lemma boundaryNeumannVerticalCLM_norm_le {t : ℝ} (ht : t ∈ Icc (0 : ℝ) 1) :
    ‖boundaryNeumannVerticalCLM t‖ ≤ 1 :=
  ContinuousLinearMap.opNorm_le_bound _ zero_le_one (fun x => by
    rw [boundaryNeumannVerticalCLM_apply, one_mul]
    exact boundaryNeumannVerticalContraction_norm ht x)

lemma boundaryNeumannVerticalCLM_mem {t : ℝ} (ht : t ∈ Icc (0 : ℝ) 1)
    {x : EuclideanSpace ℝ (Fin 3)} (hx : x ∈ closedBall 0 1) :
    boundaryNeumannVerticalCLM t x ∈ closedBall (0 : EuclideanSpace ℝ (Fin 3)) 1 := by
  simp only [mem_closedBall, dist_zero_right] at hx ⊢
  rw [boundaryNeumannVerticalCLM_apply]
  exact (boundaryNeumannVerticalContraction_norm ht x).trans hx

lemma boundaryNeumannVerticalCLM_sub_le {t : ℝ} (ht : t ∈ Icc (0 : ℝ) 1)
    (x y : EuclideanSpace ℝ (Fin 3)) :
    ‖boundaryNeumannVerticalCLM t x - boundaryNeumannVerticalCLM t y‖ ≤ ‖x - y‖ := by
  rw [← map_sub]
  exact ((boundaryNeumannVerticalCLM t).le_opNorm _).trans
    (mul_le_of_le_one_left (norm_nonneg _) (boundaryNeumannVerticalCLM_norm_le ht))

lemma boundaryNeumann_mem_Icc_of_uIoc {t : ℝ} (ht : t ∈ Ι (0 : ℝ) 1) : t ∈ Icc (0 : ℝ) 1 := by
  simpa only [min_eq_left zero_le_one, max_eq_right zero_le_one] using Ioc_subset_Icc_self ht

/-- Uniform and Hölder bounds, uniform in the parameter, pass to the integral over `[0,1]`. -/
lemma boundaryNeumann_integral_holder {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]
    {α A B : ℝ} (hA : 0 ≤ A) (hB : 0 ≤ B) {G : ℝ → EuclideanSpace ℝ (Fin 3) → F}
    {U : Set (EuclideanSpace ℝ (Fin 3))}
    (hc : ∀ x ∈ U, ContinuousOn (fun t => G t x) (Icc 0 1))
    (hb : ∀ t ∈ Icc (0 : ℝ) 1, ∀ x ∈ U, ‖G t x‖ ≤ A)
    (hh : ∀ t ∈ Icc (0 : ℝ) 1, ∀ x ∈ U, ∀ y ∈ U, ‖G t x - G t y‖ ≤ B * ‖x - y‖ ^ α) :
    HasFiniteHolderNormOn α (fun x => ∫ t in (0 : ℝ)..1, G t x) U ∧
      holderNorm α (fun x => ∫ t in (0 : ℝ)..1, G t x) U ≤ A + B := by
  have hv : ∀ x ∈ U, ‖∫ t in (0 : ℝ)..1, G t x‖ ≤ A := by
    intro x hx
    have he := intervalIntegral.norm_integral_le_of_norm_le_const
      (f := fun t => G t x) (a := (0 : ℝ)) (b := 1) (C := A)
      (fun t ht => hb t (boundaryNeumann_mem_Icc_of_uIoc ht) x hx)
    simpa using he
  have hq : ∀ x ∈ U, ∀ y ∈ U, ‖(∫ t in (0 : ℝ)..1, G t x) - ∫ t in (0 : ℝ)..1, G t y‖ /
      ‖x - y‖ ^ α ≤ B := by
    intro x hx y hy
    apply div_le_of_le_mul₀ (Real.rpow_nonneg (norm_nonneg _) _) hB
    rw [← intervalIntegral.integral_sub ((hc x hx).intervalIntegrable_of_Icc zero_le_one)
      ((hc y hy).intervalIntegrable_of_Icc zero_le_one)]
    have he := intervalIntegral.norm_integral_le_of_norm_le_const
      (f := fun t => G t x - G t y) (a := (0 : ℝ)) (b := 1) (C := B * ‖x - y‖ ^ α)
      (fun t ht => hh t (boundaryNeumann_mem_Icc_of_uIoc ht) x hx y hy)
    simpa using he
  exact ⟨HasFiniteHolderNormOn.of_bounds hA hB hv hq, holderNorm_le hA hB hv hq⟩

/-- Differentiation under the normalized vertical integral:
`D(∫₀¹ f(V_t x) dt) = ∫₀¹ Df(V_t x) ∘ V_t dt` on the open unit ball. -/
theorem boundaryNeumannVerticalIntegral_hasFDerivAt
    {f : EuclideanSpace ℝ (Fin 3) → ℝ} {O : Set (EuclideanSpace ℝ (Fin 3))}
    (hO : IsOpen O) (hsub : closedBall 0 1 ⊆ O) (hf : ContDiffOn ℝ 1 f O)
    {x : EuclideanSpace ℝ (Fin 3)} (hx : x ∈ ball 0 1) :
    HasFDerivAt (fun y => ∫ t in (0 : ℝ)..1, f (boundaryNeumannVerticalContraction t y))
      (∫ t in (0 : ℝ)..1, (fderiv ℝ f (boundaryNeumannVerticalCLM t x)).comp
        (boundaryNeumannVerticalCLM t)) x := by
  simp_rw [← boundaryNeumannVerticalCLM_apply]
  have hfd : ContinuousOn (fderiv ℝ f) O := hf.continuousOn_fderiv_of_isOpen hO le_rfl
  obtain ⟨C, hC⟩ := (isCompact_closedBall (0 : EuclideanSpace ℝ (Fin 3))
    1).exists_bound_of_continuousOn (hfd.mono hsub)
  have hLx (y : EuclideanSpace ℝ (Fin 3)) :
      Continuous (fun t => boundaryNeumannVerticalCLM t y) :=
    boundaryNeumannVerticalCLM_continuous.clm_apply continuous_const
  have hmaps (y : EuclideanSpace ℝ (Fin 3)) (hy : y ∈ ball 0 1) :
      MapsTo (fun t => boundaryNeumannVerticalCLM t y) (Icc 0 1) O :=
    fun t ht => hsub (boundaryNeumannVerticalCLM_mem ht (ball_subset_closedBall hy))
  have hslice (y : EuclideanSpace ℝ (Fin 3)) (hy : y ∈ ball 0 1) :
      ContinuousOn (fun t => f (boundaryNeumannVerticalCLM t y)) (Icc (0 : ℝ) 1) :=
    hf.continuousOn.comp (hLx y).continuousOn (hmaps y hy)
  have hdslice (y : EuclideanSpace ℝ (Fin 3)) (hy : y ∈ ball 0 1) :
      ContinuousOn (fun t => (fderiv ℝ f (boundaryNeumannVerticalCLM t y)).comp
        (boundaryNeumannVerticalCLM t)) (Icc (0 : ℝ) 1) :=
    (hfd.comp (hLx y).continuousOn (hmaps y hy)).clm_comp
      boundaryNeumannVerticalCLM_continuous.continuousOn
  have hsubI : Ι (0 : ℝ) 1 ⊆ Icc 0 1 := fun t ht => boundaryNeumann_mem_Icc_of_uIoc ht
  apply intervalIntegral.hasFDerivAt_integral_of_dominated_of_fderiv_le
    (s := ball 0 1) (bound := fun _ => C)
    (F' := fun y t => (fderiv ℝ f (boundaryNeumannVerticalCLM t y)).comp
      (boundaryNeumannVerticalCLM t))
    (isOpen_ball.mem_nhds hx)
  · filter_upwards [isOpen_ball.mem_nhds hx] with y hy
    exact ((hslice y hy).mono hsubI).aestronglyMeasurable measurableSet_uIoc
  · exact (hslice x hx).intervalIntegrable_of_Icc zero_le_one
  · exact ((hdslice x hx).mono hsubI).aestronglyMeasurable measurableSet_uIoc
  · refine ae_of_all _ (fun t ht y hy => ?_)
    have ht' := boundaryNeumann_mem_Icc_of_uIoc ht
    exact (ContinuousLinearMap.opNorm_comp_le _ _).trans
      ((mul_le_of_le_one_right (norm_nonneg _) (boundaryNeumannVerticalCLM_norm_le ht')).trans
        (hC _ (boundaryNeumannVerticalCLM_mem ht' (ball_subset_closedBall hy))))
  · exact intervalIntegrable_const
  · refine ae_of_all _ (fun t ht y hy => ?_)
    have ht' := boundaryNeumann_mem_Icc_of_uIoc ht
    have hg : DifferentiableAt ℝ f (boundaryNeumannVerticalCLM t y) :=
      (hf.differentiableOn one_ne_zero).differentiableAt (hO.mem_nhds (hmaps y hy ht'))
    exact hg.hasFDerivAt.comp y (boundaryNeumannVerticalCLM t).hasFDerivAt

/-- The normalized vertical integral `I(x) = ∫₀¹ f(x', t x₃) dt` is C¹ on the unit ball and
C¹,α on every subset of it, with C¹,α norm at most that of `f` on the closed unit ball. -/
theorem boundaryNeumannVerticalIntegral_hasC1HolderOn {α : ℝ} (hα : 0 ≤ α)
    {f : EuclideanSpace ℝ (Fin 3) → ℝ} {O : Set (EuclideanSpace ℝ (Fin 3))}
    (hO : IsOpen O) (hsub : closedBall 0 1 ⊆ O) (hf : ContDiffOn ℝ 1 f O)
    (hfh : HasC1HolderOn α f (closedBall 0 1))
    {U : Set (EuclideanSpace ℝ (Fin 3))} (hU : U ⊆ ball 0 1) :
    ContDiffOn ℝ 1
        (fun x => ∫ t in (0 : ℝ)..1, f (boundaryNeumannVerticalContraction t x)) (ball 0 1) ∧
      HasC1HolderOn α
        (fun x => ∫ t in (0 : ℝ)..1, f (boundaryNeumannVerticalContraction t x)) U ∧
      nondivC1HolderNorm α
        (fun x => ∫ t in (0 : ℝ)..1, f (boundaryNeumannVerticalContraction t x)) U ≤
          nondivC1HolderNorm α f (closedBall 0 1) := by
  let V (p : EuclideanSpace ℝ (Fin 3) × ℝ) := boundaryNeumannVerticalContraction p.2 p.1
  have hV : ContDiff ℝ 1 V := by
    unfold V boundaryNeumannVerticalContraction graphAppendN
    exact ((graphBaseN 2).contDiff.comp ((graphProjectionN 2).contDiff.comp contDiff_fst)).add
      ((contDiff_snd.mul ((EuclideanSpace.proj (Fin.last 2) :
        EuclideanSpace ℝ (Fin 3) →L[ℝ] ℝ).contDiff.comp contDiff_fst)).smul
        contDiff_const)
  have hmapsV : closedBall 0 1 ×ˢ Icc (0 : ℝ) 1 ⊆ V ⁻¹' O := by
    intro p hp
    apply hsub
    simp only [mem_prod, mem_closedBall, dist_zero_right] at hp ⊢
    exact (boundaryNeumannVerticalContraction_norm hp.2 p.1).trans hp.1
  have hI : ContDiffOn ℝ 1
      (fun x => ∫ t in (0 : ℝ)..1, f (boundaryNeumannVerticalContraction t x)) (ball 0 1) :=
    boundary_neumann_c2_inhom_integral_contDiffOn 1
      (hO.preimage hV.continuous) hmapsV (hf.comp hV.contDiffOn (fun _ hx => hx))
  have hIe : (fun x => ∫ t in (0 : ℝ)..1, f (boundaryNeumannVerticalContraction t x)) =
      fun x => ∫ t in (0 : ℝ)..1, f (boundaryNeumannVerticalCLM t x) := by
    simp_rw [boundaryNeumannVerticalCLM_apply]
  have hfd : ContinuousOn (fderiv ℝ f) O := hf.continuousOn_fderiv_of_isOpen hO le_rfl
  have hLx (y : EuclideanSpace ℝ (Fin 3)) :
      Continuous (fun t => boundaryNeumannVerticalCLM t y) :=
    boundaryNeumannVerticalCLM_continuous.clm_apply continuous_const
  have hmem (t : ℝ) (ht : t ∈ Icc (0 : ℝ) 1) (y : EuclideanSpace ℝ (Fin 3)) (hy : y ∈ U) :
      boundaryNeumannVerticalCLM t y ∈ closedBall (0 : EuclideanSpace ℝ (Fin 3)) 1 :=
    boundaryNeumannVerticalCLM_mem ht (ball_subset_closedBall (hU hy))
  have hmaps (y : EuclideanSpace ℝ (Fin 3)) (hy : y ∈ U) :
      MapsTo (fun t => boundaryNeumannVerticalCLM t y) (Icc 0 1) O :=
    fun t ht => hsub (hmem t ht y hy)
  have f0 := hfh.function_holder
  have f1 := hfh.derivative_holder
  obtain ⟨h0, n0⟩ := boundaryNeumann_integral_holder (α := α)
    (G := fun t x => f (boundaryNeumannVerticalCLM t x)) (U := U)
    (holderUniformNorm_nonneg f0.uniform_bounded) f0.seminorm_nonneg
    (fun y hy => hf.continuousOn.comp (hLx y).continuousOn (hmaps y hy))
    (fun t ht x hx => norm_le_holderUniformNorm f0.uniform_bounded (hmem t ht x hx))
    (fun t ht x hx y hy => (f0.nondiv_norm_sub_le (hmem t ht x hx) (hmem t ht y hy)).trans
      (mul_le_mul_of_nonneg_left (Real.rpow_le_rpow (norm_nonneg _)
        (boundaryNeumannVerticalCLM_sub_le ht x y) hα) f0.seminorm_nonneg))
  obtain ⟨h1, n1⟩ := boundaryNeumann_integral_holder (α := α)
    (G := fun t x => (fderiv ℝ f (boundaryNeumannVerticalCLM t x)).comp
      (boundaryNeumannVerticalCLM t)) (U := U)
    (holderUniformNorm_nonneg f1.uniform_bounded) f1.seminorm_nonneg
    (fun y hy => (hfd.comp (hLx y).continuousOn (hmaps y hy)).clm_comp
      boundaryNeumannVerticalCLM_continuous.continuousOn)
    (fun t ht x hx => (ContinuousLinearMap.opNorm_comp_le _ _).trans
      ((mul_le_of_le_one_right (norm_nonneg _) (boundaryNeumannVerticalCLM_norm_le ht)).trans
        (norm_le_holderUniformNorm f1.uniform_bounded (hmem t ht x hx))))
    (fun t ht x hx y hy => by
      rw [← ContinuousLinearMap.sub_comp]
      exact (ContinuousLinearMap.opNorm_comp_le _ _).trans
        ((mul_le_of_le_one_right (norm_nonneg _) (boundaryNeumannVerticalCLM_norm_le ht)).trans
          ((f1.nondiv_norm_sub_le (hmem t ht x hx) (hmem t ht y hy)).trans
            (mul_le_mul_of_nonneg_left (Real.rpow_le_rpow (norm_nonneg _)
              (boundaryNeumannVerticalCLM_sub_le ht x y) hα) f1.seminorm_nonneg))))
  obtain ⟨h2, n2⟩ := boundaryNeumann_holder_congr h1
    (g := fderiv ℝ (fun x => ∫ t in (0 : ℝ)..1, f (boundaryNeumannVerticalContraction t x)))
    (fun x hx => (boundaryNeumannVerticalIntegral_hasFDerivAt hO hsub hf (hU hx)).fderiv.symm)
  rw [hIe] at hI h2 n2 ⊢
  refine ⟨hI, ⟨hI.mono hU, h0, h2⟩, ?_⟩
  unfold nondivC1HolderNorm
  unfold holderNorm at n0 n1 n2 ⊢
  linarith

/-- The normal coordinate is C¹,α on every subset of the unit ball, with norm at most `4`. -/
lemma boundaryNeumann_coord_hasC1HolderOn {α : ℝ} (hα : 0 ≤ α) (hα1 : α ≤ 1)
    {U : Set (EuclideanSpace ℝ (Fin 3))} (hU : U ⊆ ball 0 1) :
    HasC1HolderOn α (fun x : EuclideanSpace ℝ (Fin 3) => x (Fin.last 2)) U ∧
      nondivC1HolderNorm α (fun x : EuclideanSpace ℝ (Fin 3) => x (Fin.last 2)) U ≤ 4 := by
  let p : EuclideanSpace ℝ (Fin 3) →L[ℝ] ℝ := EuclideanSpace.proj (Fin.last 2)
  have hpe : (fun x : EuclideanSpace ℝ (Fin 3) => x (Fin.last 2)) = ⇑p := rfl
  have hp : ‖p‖ ≤ 1 := ContinuousLinearMap.opNorm_le_bound _ zero_le_one (fun x => by
    rw [one_mul]
    exact PiLp.norm_apply_le x (Fin.last 2))
  rw [hpe]
  have hv : ∀ x ∈ U, ‖p x‖ ≤ 1 := fun x hx => by
    have hx' := hU hx
    rw [mem_ball, dist_zero_right] at hx'
    exact (p.le_opNorm x).trans (by nlinarith [norm_nonneg p, norm_nonneg x])
  have hq : ∀ x ∈ U, ∀ y ∈ U, ‖p x - p y‖ / ‖x - y‖ ^ α ≤ 2 := by
    intro x hx y hy
    apply div_le_of_le_mul₀ (Real.rpow_nonneg (norm_nonneg _) _) (by norm_num)
    have hx' := hU hx
    have hy' := hU hy
    rw [mem_ball, dist_zero_right] at hx' hy'
    have hd : ‖x - y‖ ≤ 2 := by linarith [norm_sub_le x y]
    have hpd : ‖x - y‖ ≤ 2 * ‖x - y‖ ^ α := by
      by_cases hd1 : ‖x - y‖ ≤ 1
      · have he := Real.self_le_rpow_of_le_one (norm_nonneg (x - y)) hd1 hα1
        linarith [Real.rpow_nonneg (norm_nonneg (x - y)) α]
      · have he := Real.one_le_rpow (le_of_not_ge hd1) hα
        linarith
    rw [← map_sub]
    exact ((p.le_opNorm _).trans (mul_le_of_le_one_left (norm_nonneg _) hp)).trans hpd
  have hdv : ∀ x ∈ U, ‖fderiv ℝ p x‖ ≤ 1 := fun x _ => by
    rw [ContinuousLinearMap.fderiv]
    exact hp
  have hdq : ∀ x ∈ U, ∀ y ∈ U, ‖fderiv ℝ p x - fderiv ℝ p y‖ / ‖x - y‖ ^ α ≤ 0 :=
    fun x _ y _ => by simp [ContinuousLinearMap.fderiv]
  refine ⟨⟨p.contDiff.contDiffOn,
    HasFiniteHolderNormOn.of_bounds zero_le_one (by norm_num) hv hq,
    HasFiniteHolderNormOn.of_bounds zero_le_one le_rfl hdv hdq⟩, ?_⟩
  unfold nondivC1HolderNorm
  linarith [holderNorm_le zero_le_one (by norm_num : (0 : ℝ) ≤ 2) hv hq,
    holderNorm_le zero_le_one le_rfl hdv hdq]

/-- Constant fields are C¹,α with norm at most the norm of the constant. -/
lemma boundaryNeumann_const_hasC1HolderOn {α : ℝ} {F : Type*} [NormedAddCommGroup F]
    [NormedSpace ℝ F] (e : F) (U : Set (EuclideanSpace ℝ (Fin 3))) :
    HasC1HolderOn α (fun _ : EuclideanSpace ℝ (Fin 3) => e) U ∧
      nondivC1HolderNorm α (fun _ : EuclideanSpace ℝ (Fin 3) => e) U ≤ ‖e‖ := by
  have hv : ∀ x ∈ U, ‖(fun _ : EuclideanSpace ℝ (Fin 3) => e) x‖ ≤ ‖e‖ := fun _ _ => le_rfl
  have hq : ∀ x ∈ U, ∀ y ∈ U, ‖(fun _ : EuclideanSpace ℝ (Fin 3) => e) x -
      (fun _ : EuclideanSpace ℝ (Fin 3) => e) y‖ / ‖x - y‖ ^ α ≤ 0 :=
    fun _ _ _ _ => by simp
  have hdv : ∀ x ∈ U, ‖fderiv ℝ (fun _ : EuclideanSpace ℝ (Fin 3) => e) x‖ ≤ 0 :=
    fun _ _ => by simp
  have hdq : ∀ x ∈ U, ∀ y ∈ U, ‖fderiv ℝ (fun _ : EuclideanSpace ℝ (Fin 3) => e) x -
      fderiv ℝ (fun _ : EuclideanSpace ℝ (Fin 3) => e) y‖ / ‖x - y‖ ^ α ≤ 0 :=
    fun _ _ _ _ => by simp
  refine ⟨⟨contDiffOn_const,
    HasFiniteHolderNormOn.of_bounds (norm_nonneg e) le_rfl hv hq,
    HasFiniteHolderNormOn.of_bounds le_rfl le_rfl hdv hdq⟩, ?_⟩
  unfold nondivC1HolderNorm
  linarith [holderNorm_le (norm_nonneg e) le_rfl hv hq, holderNorm_le le_rfl le_rfl hdv hdq]

/-- The vertical primitive `P = (∫₀^{x₃} f(x', t) dt) e₃` of a C¹,α source is C¹ on the unit
ball and C¹,α on every subset of it, with C¹,α norm at most `36` times that of `f` on the
closed unit ball. -/
theorem boundaryNeumannPrimitive_hasC1HolderOn_of_subset {α K : ℝ} (hα : 0 ≤ α) (hα1 : α ≤ 1)
    {f : EuclideanSpace ℝ (Fin 3) → ℝ} {O : Set (EuclideanSpace ℝ (Fin 3))}
    (hO : IsOpen O) (hsub : closedBall 0 1 ⊆ O) (hf : ContDiffOn ℝ 1 f O)
    (hfh : HasC1HolderOn α f (closedBall 0 1))
    (hK : nondivC1HolderNorm α f (closedBall 0 1) ≤ K)
    {U : Set (EuclideanSpace ℝ (Fin 3))} (hU : U ⊆ ball 0 1) :
    ContDiffOn ℝ 1 (boundaryNeumannPrimitive f) (ball 0 1) ∧
      HasC1HolderOn α (boundaryNeumannPrimitive f) U ∧
      nondivC1HolderNorm α (boundaryNeumannPrimitive f) U ≤ 36 * K := by
  obtain ⟨hIc, hIh, hIn⟩ := boundaryNeumannVerticalIntegral_hasC1HolderOn hα hO hsub hf hfh hU
  obtain ⟨hph, hpn⟩ := boundaryNeumann_coord_hasC1HolderOn hα hα1 hU
  have hpc : ContDiffOn ℝ 1 (fun x : EuclideanSpace ℝ (Fin 3) => x (Fin.last 2)) (ball 0 1) :=
    (EuclideanSpace.proj (Fin.last 2) :
      EuclideanSpace ℝ (Fin 3) →L[ℝ] ℝ).contDiff.contDiffOn
  obtain ⟨hmh, hmn⟩ := boundaryNeumann_hasC1HolderOn_mul isOpen_ball hU hpc hIc hph hIh
  obtain ⟨heh, hen⟩ := boundaryNeumann_const_hasC1HolderOn (α := α)
    (EuclideanSpace.single (Fin.last 2) (1 : ℝ)) U
  obtain ⟨hsh, hsn⟩ := boundaryNeumann_hasC1HolderOn_smul isOpen_ball hU (hpc.mul hIc)
    contDiffOn_const hmh heh
  have he : boundaryNeumannPrimitive f = fun x =>
      (x (Fin.last 2) * ∫ t in (0 : ℝ)..1, f (boundaryNeumannVerticalContraction t x)) •
        EuclideanSpace.single (Fin.last 2) (1 : ℝ) :=
    funext (boundaryNeumannPrimitive_normalized f)
  rw [he]
  refine ⟨(hpc.mul hIc).smul contDiffOn_const, hsh, ?_⟩
  have hn1 : ‖EuclideanSpace.single (Fin.last 2) (1 : ℝ)‖ = 1 := by simp
  have h1 := mul_le_mul hpn (hIn.trans hK) hIh.norm_nonneg (by norm_num)
  have h2 := mul_le_mul_of_nonneg_left (hen.trans hn1.le) hmh.norm_nonneg
  have h3 := hph.norm_nonneg
  nlinarith

lemma boundaryNeumann_closure_halfBall_quarter_subset :
    closure (boundaryHalfBall (1 / 4)) ⊆ ball (0 : EuclideanSpace ℝ (Fin 3)) 1 :=
  (closure_minimal (fun _ hx => ball_subset_closedBall hx.1) isClosed_closedBall).trans
    (closedBall_subset_ball (by norm_num))

/-- Blueprint `thm:boundary-neumann` (Hölder classes): the vertical primitive of a C¹,α source
is C¹,α on the closed quarter half ball, with a numerical constant. -/
theorem boundaryNeumannPrimitive_hasC1HolderOn {α : ℝ} (hα : 0 < α) (hα1 : α ≤ 1) :
    ∃ c : ℝ, 0 ≤ c ∧ ∀ (f : EuclideanSpace ℝ (Fin 3) → ℝ) (K : ℝ)
      (O : Set (EuclideanSpace ℝ (Fin 3))), IsOpen O → closedBall 0 1 ⊆ O →
      ContDiffOn ℝ 1 f O → HasC1HolderOn α f (closedBall 0 1) →
      nondivC1HolderNorm α f (closedBall 0 1) ≤ K →
      ContDiffOn ℝ 1 (boundaryNeumannPrimitive f) (ball 0 1) ∧
        HasC1HolderOn α (boundaryNeumannPrimitive f) (closure (boundaryHalfBall (1 / 4))) ∧
        nondivC1HolderNorm α (boundaryNeumannPrimitive f)
          (closure (boundaryHalfBall (1 / 4))) ≤ c * K :=
  ⟨36, by norm_num, fun _ _ _ hO hsub hf hfh hK =>
    boundaryNeumannPrimitive_hasC1HolderOn_of_subset hα.le hα1 hO hsub hf hfh hK
      boundaryNeumann_closure_halfBall_quarter_subset⟩

end LiquidDrop

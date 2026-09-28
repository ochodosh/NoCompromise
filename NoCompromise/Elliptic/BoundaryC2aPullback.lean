import NoCompromise.Elliptic.BoundaryC2aLocalAssembly
import Mathlib.Analysis.Calculus.Deriv.Abs

/-!
# Pullback of the Dirichlet form under a C¹ diffeomorphism

For a global C¹ diffeomorphism `Θ` of `ℝ³` (with C¹ inverse `Θi`), the weak Laplace equation
for `u` on `V` pulls back to the weak divergence equation for `u ∘ Θ` on any open `U` with
`Θ '' U ⊆ V`, with coefficient `|det DΘ| · DΘ⁻¹ DΘ⁻*`. The coefficient is C² when `Θ` is C³,
uniformly bounded and elliptic on compact sets, and C² fields are C¹,α on the closed half ball.
-/

noncomputable section
open MeasureTheory Filter Metric Set InnerProductSpace
open scoped ENNReal NNReal Topology Gradient RealInnerProductSpace
namespace LiquidDrop

/-- The Dirichlet-form pullback coefficient `|det DΘ| · DΘ⁻¹ DΘ⁻*`. -/
def dirichletPullbackCoefficient (Θ : EuclideanSpace ℝ (Fin 3) → EuclideanSpace ℝ (Fin 3))
    (y : EuclideanSpace ℝ (Fin 3)) :
    EuclideanSpace ℝ (Fin 3) →L[ℝ] EuclideanSpace ℝ (Fin 3) :=
  |(fderiv ℝ Θ y).det| • ((fderiv ℝ Θ y).inverse.comp (fderiv ℝ Θ y).inverse.adjoint)

/-- A C¹ map with a C¹ two-sided inverse has an invertible derivative everywhere. -/
lemma dirichletPullback_isInvertible
    {Θ Θi : EuclideanSpace ℝ (Fin 3) → EuclideanSpace ℝ (Fin 3)}
    (hΘ : ContDiff ℝ 1 Θ) (hΘi : ContDiff ℝ 1 Θi)
    (hl : Function.LeftInverse Θi Θ) (hr : Function.RightInverse Θi Θ)
    (y : EuclideanSpace ℝ (Fin 3)) : (fderiv ℝ Θ y).IsInvertible := by
  have hdΘ : DifferentiableAt ℝ Θ y := hΘ.differentiable one_ne_zero y
  have hdΘi : DifferentiableAt ℝ Θi (Θ y) := hΘi.differentiable one_ne_zero (Θ y)
  have hdΘ' : DifferentiableAt ℝ Θ (Θi (Θ y)) := by rw [hl y]; exact hdΘ
  refine ContinuousLinearMap.IsInvertible.of_inverse (g := fderiv ℝ Θi (Θ y)) ?_ ?_
  · have h1 : fderiv ℝ (Θ ∘ Θi) (Θ y) = (fderiv ℝ Θ (Θi (Θ y))).comp (fderiv ℝ Θi (Θ y)) :=
      fderiv_comp _ hdΘ' hdΘi
    have h2 : Θ ∘ Θi = id := funext hr
    rw [h2, fderiv_id, hl y] at h1
    exact h1.symm
  · have h1 : fderiv ℝ (Θi ∘ Θ) y = (fderiv ℝ Θi (Θ y)).comp (fderiv ℝ Θ y) :=
      fderiv_comp _ hdΘi hdΘ
    have h2 : Θi ∘ Θ = id := funext hl
    rw [h2, fderiv_id] at h1
    exact h1.symm

/-- The gradient chain rule through a differentiable map. -/
lemma dirichletPullback_gradient_comp
    {Θ : EuclideanSpace ℝ (Fin 3) → EuclideanSpace ℝ (Fin 3)}
    {u : EuclideanSpace ℝ (Fin 3) → ℝ} {y : EuclideanSpace ℝ (Fin 3)}
    (hΘ : DifferentiableAt ℝ Θ y) (hu : DifferentiableAt ℝ u (Θ y)) :
    gradient (u ∘ Θ) y = (fderiv ℝ Θ y).adjoint (gradient u (Θ y)) := by
  apply ext_inner_right ℝ
  intro v
  rw [inner_gradient_left, ContinuousLinearMap.adjoint_inner_left, inner_gradient_left,
    fderiv_comp y hu hΘ, ContinuousLinearMap.comp_apply]

/-- The pointwise Dirichlet pairing transforms by the pullback coefficient. -/
lemma dirichletPullback_pairing
    {Θ : EuclideanSpace ℝ (Fin 3) → EuclideanSpace ℝ (Fin 3)}
    {u φ : EuclideanSpace ℝ (Fin 3) → ℝ} {y : EuclideanSpace ℝ (Fin 3)}
    (hΘ : DifferentiableAt ℝ Θ y) (hu : DifferentiableAt ℝ u (Θ y))
    (hφ : DifferentiableAt ℝ φ (Θ y)) (hy : (fderiv ℝ Θ y).IsInvertible) :
    inner ℝ (dirichletPullbackCoefficient Θ y (gradient (u ∘ Θ) y)) (gradient (φ ∘ Θ) y) =
      |(fderiv ℝ Θ y).det| * inner ℝ (gradient u (Θ y)) (gradient φ (Θ y)) := by
  let L := fderiv ℝ Θ y
  have hstar : L.inverse.adjoint.comp L.adjoint = ContinuousLinearMap.id ℝ _ := by
    rw [← ContinuousLinearMap.adjoint_comp, hy.self_comp_inverse,
      ContinuousLinearMap.adjoint_id]
  have hs (v : EuclideanSpace ℝ (Fin 3)) : L.inverse.adjoint (L.adjoint v) = v :=
    congrArg (fun A : EuclideanSpace ℝ (Fin 3) →L[ℝ] EuclideanSpace ℝ (Fin 3) => A v) hstar
  rw [dirichletPullback_gradient_comp hΘ hu, dirichletPullback_gradient_comp hΘ hφ]
  change inner ℝ (|L.det| • L.inverse
    (L.inverse.adjoint (L.adjoint (gradient u (Θ y)))))
      (L.adjoint (gradient φ (Θ y))) = _
  rw [hs, real_inner_smul_left, ContinuousLinearMap.adjoint_inner_right, hy.self_apply_inverse]

/-- **B1.** The weak Laplace equation for `u` on `V` pulls back under a C¹ diffeomorphism `Θ`
to the weak divergence equation for `u ∘ Θ` on `U`, with the Dirichlet pullback coefficient. -/
theorem isWeakDivergenceEquationOn_dirichletPullback
    {Θ Θi : EuclideanSpace ℝ (Fin 3) → EuclideanSpace ℝ (Fin 3)}
    (hΘ : ContDiff ℝ 1 Θ) (hΘi : ContDiff ℝ 1 Θi)
    (hl : Function.LeftInverse Θi Θ) (hr : Function.RightInverse Θi Θ)
    {V U : Set (EuclideanSpace ℝ (Fin 3))} (hV : IsOpen V)
    (hUV : MapsTo Θ U V) {u : EuclideanSpace ℝ (Fin 3) → ℝ} (hu : ContDiffOn ℝ 1 u V)
    (hweak : IsWeakDivergenceEquationOn
      (fun _ => ContinuousLinearMap.id ℝ (EuclideanSpace ℝ (Fin 3))) (gradient u)
      (fun _ => 0) V) :
    IsWeakDivergenceEquationOn (dirichletPullbackCoefficient Θ) (gradient (u ∘ Θ))
      (fun _ => 0) U := by
  intro φ hφ hφc hφU
  let e : EuclideanSpace ℝ (Fin 3) ≃ₜ EuclideanSpace ℝ (Fin 3) :=
    { toFun := Θ
      invFun := Θi
      left_inv := hl
      right_inv := hr
      continuous_toFun := hΘ.continuous
      continuous_invFun := hΘi.continuous }
  obtain ⟨ψ, hψdef⟩ : ∃ ψ : EuclideanSpace ℝ (Fin 3) → ℝ, ψ = φ ∘ Θi := ⟨_, rfl⟩
  have hψ : ContDiff ℝ 1 ψ := hψdef ▸ hφ.comp hΘi
  have hψc : HasCompactSupport ψ := hψdef ▸ hφc.comp_homeomorph e.symm
  have hψs : tsupport ψ = Θ '' tsupport φ := by
    have h := tsupport_comp_eq_preimage φ e.symm
    rw [hψdef]
    change tsupport (φ ∘ e.symm) = _
    rw [h, e.preimage_symm]
    rfl
  have hψV : tsupport ψ ⊆ V := hψs ▸ (image_mono hφU).trans hUV.image_subset
  have h0 := hweak ψ hψ hψc hψV
  have hφψ : φ = ψ ∘ Θ := funext fun y => by simp [hψdef, hl y]
  have hderiv : ∀ y ∈ (univ : Set (EuclideanSpace ℝ (Fin 3))),
      HasFDerivWithinAt Θ (fderiv ℝ Θ y) univ y :=
    fun y _ => (hΘ.differentiable one_ne_zero y).hasFDerivAt.hasFDerivWithinAt
  have hcv := integral_image_eq_integral_abs_det_fderiv_smul volume MeasurableSet.univ hderiv
    hl.injective.injOn (fun x => inner ℝ (gradient u x) (gradient ψ x))
  rw [image_univ, hr.surjective.range_eq, Measure.restrict_univ] at hcv
  simp only [ContinuousLinearMap.id_apply, sub_zero] at h0
  rw [hcv] at h0
  rw [← h0]
  congr 1
  funext y
  simp only [sub_zero, smul_eq_mul]
  by_cases hy : y ∈ tsupport φ
  · have hΘyV := hUV (hφU hy)
    have hud : DifferentiableAt ℝ u (Θ y) :=
      (hu.differentiableOn one_ne_zero _ hΘyV).differentiableAt (hV.mem_nhds hΘyV)
    rw [show gradient φ y = gradient (ψ ∘ Θ) y by rw [← hφψ]]
    exact dirichletPullback_pairing (hΘ.differentiable one_ne_zero y) hud
      (hψ.differentiable one_ne_zero _) (dirichletPullback_isInvertible hΘ hΘi hl hr y)
  · have h1 : gradient φ y = 0 := by simp [gradient, fderiv_of_notMem_tsupport (𝕜 := ℝ) hy]
    have hny : Θ y ∉ tsupport ψ := by
      rw [hψs]
      rintro ⟨z, hz, hzy⟩
      exact hy (hl.injective hzy ▸ hz)
    have h2 : gradient ψ (Θ y) = 0 := by simp [gradient, fderiv_of_notMem_tsupport (𝕜 := ℝ) hny]
    rw [h1, h2, inner_zero_right, inner_zero_right, mul_zero]

/-- On a set of diameter at most `2`, a distance is at most twice its `α`-th power. -/
lemma dirichletPullback_le_two_mul_rpow {α t : ℝ} (hα0 : 0 < α) (hα1 : α ≤ 1)
    (ht0 : 0 ≤ t) (ht2 : t ≤ 2) : t ≤ 2 * t ^ α := by
  rcases eq_or_lt_of_le ht0 with rfl | ht
  · rw [Real.zero_rpow hα0.ne', mul_zero]
  have hsplit : t = t ^ α * t ^ (1 - α) := by
    rw [← Real.rpow_add ht, add_sub_cancel, Real.rpow_one]
  have h1 : t ^ (1 - α) ≤ 2 ^ (1 - α) := Real.rpow_le_rpow ht0 ht2 (by linarith)
  have h2 : (2 : ℝ) ^ (1 - α) ≤ 2 := by
    calc (2 : ℝ) ^ (1 - α) ≤ 2 ^ (1 : ℝ) :=
          Real.rpow_le_rpow_of_exponent_le (by norm_num) (by linarith)
      _ = 2 := Real.rpow_one 2
  have hpos : 0 ≤ t ^ α := Real.rpow_nonneg ht0 α
  calc t = t ^ α * t ^ (1 - α) := hsplit
    _ ≤ t ^ α * 2 := mul_le_mul_of_nonneg_left (h1.trans h2) hpos
    _ = 2 * t ^ α := mul_comm _ _

/-- A C¹ map has finite `α`-Hölder norm on any subset of the closed unit ball. -/
lemma dirichletPullback_hasFiniteHolderNormOn_of_contDiff {F : Type*} [NormedAddCommGroup F]
    [NormedSpace ℝ F] {α : ℝ} (hα0 : 0 < α) (hα1 : α ≤ 1)
    {g : EuclideanSpace ℝ (Fin 3) → F} (hg : ContDiff ℝ 1 g)
    {s : Set (EuclideanSpace ℝ (Fin 3))} (hs : s ⊆ closedBall 0 1) :
    HasFiniteHolderNormOn α g s := by
  have hK := isCompact_closedBall (0 : EuclideanSpace ℝ (Fin 3)) 1
  obtain ⟨C, hC⟩ := hK.exists_bound_of_continuousOn hg.continuous.continuousOn
  obtain ⟨D, hD⟩ := hK.exists_bound_of_continuousOn (hg.continuous_fderiv one_ne_zero).continuousOn
  have h0 : (0 : EuclideanSpace ℝ (Fin 3)) ∈ closedBall (0 : EuclideanSpace ℝ (Fin 3)) 1 :=
    mem_closedBall_self zero_le_one
  have hC0 : 0 ≤ C := (norm_nonneg _).trans (hC 0 h0)
  have hD0 : 0 ≤ D := (norm_nonneg _).trans (hD 0 h0)
  refine HasFiniteHolderNormOn.of_bounds (A := C) (B := 2 * D) hC0 (by positivity)
    (fun x hx => hC x (hs hx)) ?_
  intro x hx y hy
  have hlip : ‖g x - g y‖ ≤ D * ‖x - y‖ :=
    (convex_closedBall (0 : EuclideanSpace ℝ (Fin 3)) 1).norm_image_sub_le_of_norm_fderiv_le
      (fun z _ => hg.differentiable one_ne_zero z) (fun z hz => hD z hz) (hs hy) (hs hx)
  have hxy : ‖x - y‖ ≤ 2 := by
    have hx1 := mem_closedBall_zero_iff.mp (hs hx)
    have hy1 := mem_closedBall_zero_iff.mp (hs hy)
    have := norm_sub_le x y
    linarith
  rcases eq_or_lt_of_le (norm_nonneg (x - y)) with h | h
  · rw [← h, Real.zero_rpow hα0.ne', div_zero]
    positivity
  · rw [div_le_iff₀ (Real.rpow_pos_of_pos h α)]
    calc ‖g x - g y‖ ≤ D * ‖x - y‖ := hlip
      _ ≤ D * (2 * ‖x - y‖ ^ α) :=
          mul_le_mul_of_nonneg_left
            (dirichletPullback_le_two_mul_rpow hα0 hα1 (norm_nonneg _) hxy) hD0
      _ = 2 * D * ‖x - y‖ ^ α := by ring

/-- **B4.** A C² map is C¹,α on the closed unit half ball. -/
theorem hasC1HolderOn_closure_boundaryHalfBall_of_contDiff {F : Type*} [NormedAddCommGroup F]
    [NormedSpace ℝ F] {α : ℝ} (hα0 : 0 < α) (hα1 : α ≤ 1)
    {f : EuclideanSpace ℝ (Fin 3) → F} (hf : ContDiff ℝ 2 f) :
    HasC1HolderOn α f (closure (boundaryHalfBall 1)) := by
  have hs : closure (boundaryHalfBall 1) ⊆ closedBall 0 1 :=
    closure_minimal (inter_subset_left.trans ball_subset_closedBall) isClosed_closedBall
  have hf1 : ContDiff ℝ 1 f := hf.of_le (by norm_num)
  exact ⟨hf1.contDiffOn, dirichletPullback_hasFiniteHolderNormOn_of_contDiff hα0 hα1 hf1 hs,
    dirichletPullback_hasFiniteHolderNormOn_of_contDiff hα0 hα1
      (hf.fderiv_right (m := 1) (by norm_num)) hs⟩

/-- The determinant is a smooth polynomial in the entries of a Euclidean operator. -/
lemma dirichletPullback_contDiff_det {r : WithTop ℕ∞} :
    ContDiff ℝ r (fun L : EuclideanSpace ℝ (Fin 3) →L[ℝ]
      EuclideanSpace ℝ (Fin 3) => L.det) := by
  let b := (EuclideanSpace.basisFun (Fin 3) ℝ).toBasis
  have he (L : EuclideanSpace ℝ (Fin 3) →L[ℝ] EuclideanSpace ℝ (Fin 3)) :
      L.det = Matrix.det (Matrix.of (fun i j : Fin 3 => L (EuclideanSpace.single j 1) i)) := by
    rw [ContinuousLinearMap.det, ← LinearMap.det_toMatrix b]
    congr 1
  simp_rw [he, Matrix.det_apply']
  apply ContDiff.sum
  intro σ _
  apply contDiff_const.mul
  apply contDiff_prod
  intro i _
  exact (EuclideanSpace.proj (𝕜 := ℝ) (σ i)).contDiff.comp
    (contDiff_id.clm_apply contDiff_const)

/-- The real adjoint is a bounded real-linear map, hence smooth. -/
lemma dirichletPullback_contDiff_adjoint {r : WithTop ℕ∞} :
    ContDiff ℝ r (fun L : EuclideanSpace ℝ (Fin 3) →L[ℝ]
      EuclideanSpace ℝ (Fin 3) => ContinuousLinearMap.adjoint L) := by
  let T : (EuclideanSpace ℝ (Fin 3) →L[ℝ] EuclideanSpace ℝ (Fin 3)) →L[ℝ]
      (EuclideanSpace ℝ (Fin 3) →L[ℝ] EuclideanSpace ℝ (Fin 3)) :=
    LinearMap.mkContinuous
      { toFun := fun L => ContinuousLinearMap.adjoint L
        map_add' := fun L M => map_add _ L M
        map_smul' := fun c L => by simp } 1 (fun L => by simp)
  exact T.contDiff

lemma dirichletPullback_det_ne_zero
    {L : EuclideanSpace ℝ (Fin 3) →L[ℝ] EuclideanSpace ℝ (Fin 3)}
    (hL : L.IsInvertible) : L.det ≠ 0 := by
  obtain ⟨e, rfl⟩ := hL
  exact e.toLinearEquiv.isUnit_det'.ne_zero

/-- The pullback coefficient has one derivative less than `Θ`. -/
lemma contDiff_dirichletPullbackCoefficient_of_le {m : ℕ∞} {n : WithTop ℕ∞}
    {Θ Θi : EuclideanSpace ℝ (Fin 3) → EuclideanSpace ℝ (Fin 3)}
    (hΘ : ContDiff ℝ n Θ) (hmn : (m : WithTop ℕ∞) + 1 ≤ n) (hΘi : ContDiff ℝ 1 Θi)
    (hl : Function.LeftInverse Θi Θ) (hr : Function.RightInverse Θi Θ) :
    ContDiff ℝ m (dirichletPullbackCoefficient Θ) := by
  have hD : ContDiff ℝ m (fderiv ℝ Θ) := hΘ.fderiv_right hmn
  have hΘ1 : ContDiff ℝ 1 Θ := hΘ.of_le (le_add_self.trans hmn)
  rw [contDiff_iff_contDiffAt]
  intro y
  have hy := dirichletPullback_isInvertible hΘ1 hΘi hl hr y
  obtain ⟨e, he⟩ := hy
  have hinv : ContDiffAt ℝ m (fun z => (fderiv ℝ Θ z).inverse) y :=
    ContDiffAt.comp (g := ContinuousLinearMap.inverse) y
      (he ▸ contDiffAt_map_inverse e) hD.contDiffAt
  have hadj : ContDiffAt ℝ m (fun z => (fderiv ℝ Θ z).inverse.adjoint) y :=
    dirichletPullback_contDiff_adjoint.contDiffAt.comp y hinv
  have hdet : ContDiffAt ℝ m (fun z => |(fderiv ℝ Θ z).det|) y :=
    (dirichletPullback_contDiff_det.contDiffAt.comp y hD.contDiffAt).abs
      (dirichletPullback_det_ne_zero ⟨e, he⟩)
  exact hdet.smul (hinv.clm_comp hadj)

/-- **B2.** For a C³ diffeomorphism the pullback coefficient is C². -/
theorem contDiff_dirichletPullbackCoefficient
    {Θ Θi : EuclideanSpace ℝ (Fin 3) → EuclideanSpace ℝ (Fin 3)}
    (hΘ : ContDiff ℝ 3 Θ) (hΘi : ContDiff ℝ 1 Θi)
    (hl : Function.LeftInverse Θi Θ) (hr : Function.RightInverse Θi Θ) :
    ContDiff ℝ 2 (dirichletPullbackCoefficient Θ) :=
  contDiff_dirichletPullbackCoefficient_of_le (m := 2) hΘ (by norm_num) hΘi hl hr

/-- On a compact set the derivative of a C¹ diffeomorphism is bounded and its Jacobian
determinant is bounded away from zero. -/
lemma dirichletPullback_fderiv_det_bounds
    {Θ Θi : EuclideanSpace ℝ (Fin 3) → EuclideanSpace ℝ (Fin 3)}
    (hΘ : ContDiff ℝ 1 Θ) (hΘi : ContDiff ℝ 1 Θi)
    (hl : Function.LeftInverse Θi Θ) (hr : Function.RightInverse Θi Θ)
    {S : Set (EuclideanSpace ℝ (Fin 3))} (hS : IsCompact S) :
    ∃ M δ : ℝ, 0 < M ∧ 0 < δ ∧ ∀ y ∈ S, ‖fderiv ℝ Θ y‖ ≤ M ∧ δ ≤ |(fderiv ℝ Θ y).det| := by
  have hDc : Continuous (fderiv ℝ Θ) := hΘ.continuous_fderiv one_ne_zero
  have hdet : Continuous (fun y => |(fderiv ℝ Θ y).det|) :=
    ((dirichletPullback_contDiff_det (r := 0)).continuous.comp hDc).abs
  obtain ⟨M₀, hM₀⟩ := hS.exists_bound_of_continuousOn hDc.continuousOn
  rcases S.eq_empty_or_nonempty with rfl | hne
  · exact ⟨1, 1, one_pos, one_pos, by simp⟩
  obtain ⟨y₀, hy₀, hmin⟩ := hS.exists_isMinOn hne hdet.continuousOn
  refine ⟨max M₀ 1, |(fderiv ℝ Θ y₀).det|, lt_max_of_lt_right one_pos,
    abs_pos.mpr (dirichletPullback_det_ne_zero
      (dirichletPullback_isInvertible hΘ hΘi hl hr y₀)), fun y hy => ⟨?_, hmin hy⟩⟩
  exact (hM₀ y hy).trans (le_max_left _ _)

/-- **B3.** On a compact set the pullback coefficient is uniformly bounded and elliptic. -/
theorem dirichletPullbackCoefficient_bounds
    {Θ Θi : EuclideanSpace ℝ (Fin 3) → EuclideanSpace ℝ (Fin 3)}
    (hΘ : ContDiff ℝ 1 Θ) (hΘi : ContDiff ℝ 1 Θi)
    (hl : Function.LeftInverse Θi Θ) (hr : Function.RightInverse Θi Θ)
    {S : Set (EuclideanSpace ℝ (Fin 3))} (hS : IsCompact S) :
    ∃ lam cap : ℝ, 0 < lam ∧ lam ≤ cap ∧ ∀ y ∈ S, ‖dirichletPullbackCoefficient Θ y‖ ≤ cap ∧
      ∀ ξ, lam * ‖ξ‖ ^ 2 ≤ inner ℝ (dirichletPullbackCoefficient Θ y ξ) ξ := by
  have hA : Continuous (dirichletPullbackCoefficient Θ) :=
    (contDiff_dirichletPullbackCoefficient_of_le (m := 0) hΘ (by simp) hΘi hl hr).continuous
  obtain ⟨cap₀, hcap₀⟩ := hS.exists_bound_of_continuousOn hA.continuousOn
  obtain ⟨M, δ, hM, hδ, hMδ⟩ := dirichletPullback_fderiv_det_bounds hΘ hΘi hl hr hS
  refine ⟨δ / M ^ 2, max cap₀ (δ / M ^ 2), by positivity, le_max_right _ _,
    fun y hy => ⟨(hcap₀ y hy).trans (le_max_left _ _), fun ξ => ?_⟩⟩
  obtain ⟨hLM, hδL⟩ := hMδ y hy
  set L := fderiv ℝ Θ y with hLdef
  have hL : L.IsInvertible := dirichletPullback_isInvertible hΘ hΘi hl hr y
  set w := L.inverse.adjoint ξ with hw
  have hinner : inner ℝ (dirichletPullbackCoefficient Θ y ξ) ξ = |L.det| * ‖w‖ ^ 2 := by
    change inner ℝ (|L.det| • L.inverse (L.inverse.adjoint ξ)) ξ = _
    rw [real_inner_smul_left, ← ContinuousLinearMap.adjoint_inner_right,
      real_inner_self_eq_norm_sq]
  have hξ : ξ = L.adjoint w := by
    have hstar : L.adjoint.comp L.inverse.adjoint = ContinuousLinearMap.id ℝ _ := by
      rw [← ContinuousLinearMap.adjoint_comp, hL.inverse_comp_self,
        ContinuousLinearMap.adjoint_id]
    exact (congrArg (fun A : EuclideanSpace ℝ (Fin 3) →L[ℝ] EuclideanSpace ℝ (Fin 3) => A ξ)
      hstar).symm
  have hξw : ‖ξ‖ ≤ M * ‖w‖ := by
    calc ‖ξ‖ = ‖L.adjoint w‖ := congrArg norm hξ
      _ ≤ ‖L.adjoint‖ * ‖w‖ := L.adjoint.le_opNorm w
      _ = ‖L‖ * ‖w‖ := by rw [LinearIsometryEquiv.norm_map]
      _ ≤ M * ‖w‖ := mul_le_mul_of_nonneg_right hLM (norm_nonneg _)
  have hsq : ‖ξ‖ ^ 2 ≤ M ^ 2 * ‖w‖ ^ 2 := by
    rw [← mul_pow]
    exact pow_le_pow_left₀ (norm_nonneg _) hξw 2
  rw [hinner]
  calc δ / M ^ 2 * ‖ξ‖ ^ 2 ≤ δ / M ^ 2 * (M ^ 2 * ‖w‖ ^ 2) :=
        mul_le_mul_of_nonneg_left hsq (by positivity)
    _ = δ * ‖w‖ ^ 2 := by field_simp
    _ ≤ |L.det| * ‖w‖ ^ 2 := mul_le_mul_of_nonneg_right hδL (by positivity)

/-- **B5.** The pulled-back gradient is square integrable on a bounded `U` whenever the
original gradient is square integrable on `Θ '' U`. -/
theorem memLp_gradient_comp_dirichletPullback
    {Θ Θi : EuclideanSpace ℝ (Fin 3) → EuclideanSpace ℝ (Fin 3)}
    (hΘ : ContDiff ℝ 1 Θ) (hΘi : ContDiff ℝ 1 Θi)
    (hl : Function.LeftInverse Θi Θ) (hr : Function.RightInverse Θi Θ)
    {V U : Set (EuclideanSpace ℝ (Fin 3))} (hV : IsOpen V) (hU : IsOpen U)
    (hUV : MapsTo Θ U V) (hUb : Bornology.IsBounded U)
    {u : EuclideanSpace ℝ (Fin 3) → ℝ} (hu : ContDiffOn ℝ 1 u V)
    (hL2 : IntegrableOn (fun x => ‖gradient u x‖ ^ 2) (Θ '' U)) :
    MemLp (gradient (u ∘ Θ)) 2 (volume.restrict U) := by
  obtain ⟨M, δ, hM, hδ, hMδ⟩ :=
    dirichletPullback_fderiv_det_bounds hΘ hΘi hl hr hUb.isCompact_closure
  have huΘ : ContDiffOn ℝ 1 (u ∘ Θ) U := hu.comp hΘ.contDiffOn hUV
  have hcont : ContinuousOn (gradient (u ∘ Θ)) U :=
    (InnerProductSpace.toDual ℝ (EuclideanSpace ℝ (Fin 3))).symm.continuous.comp_continuousOn
      (huΘ.continuousOn_fderiv_of_isOpen hU le_rfl)
  have hmeas : AEStronglyMeasurable (gradient (u ∘ Θ)) (volume.restrict U) :=
    hcont.aestronglyMeasurable hU.measurableSet
  have hderiv : ∀ y ∈ U, HasFDerivWithinAt Θ (fderiv ℝ Θ y) U y :=
    fun y _ => (hΘ.differentiable one_ne_zero y).hasFDerivAt.hasFDerivWithinAt
  have hint := (integrableOn_image_iff_integrableOn_abs_det_fderiv_smul volume hU.measurableSet
    hderiv hl.injective.injOn (fun x => ‖gradient u x‖ ^ 2)).mp hL2
  rw [memLp_two_iff_integrable_sq_norm hmeas]
  refine (hint.const_mul (M ^ 2 / δ)).mono' (hmeas.norm.pow 2) ?_
  refine (ae_restrict_iff' hU.measurableSet).mpr (Eventually.of_forall fun y hy => ?_)
  obtain ⟨hLM, hδL⟩ := hMδ y (subset_closure hy)
  have hΘyV := hUV hy
  have hud : DifferentiableAt ℝ u (Θ y) :=
    (hu.differentiableOn one_ne_zero _ hΘyV).differentiableAt (hV.mem_nhds hΘyV)
  have hgrad : ‖gradient (u ∘ Θ) y‖ ≤ M * ‖gradient u (Θ y)‖ := by
    rw [dirichletPullback_gradient_comp (hΘ.differentiable one_ne_zero y) hud]
    calc ‖(fderiv ℝ Θ y).adjoint (gradient u (Θ y))‖
        ≤ ‖(fderiv ℝ Θ y).adjoint‖ * ‖gradient u (Θ y)‖ := ContinuousLinearMap.le_opNorm _ _
      _ = ‖fderiv ℝ Θ y‖ * ‖gradient u (Θ y)‖ := by rw [LinearIsometryEquiv.norm_map]
      _ ≤ M * ‖gradient u (Θ y)‖ := mul_le_mul_of_nonneg_right hLM (norm_nonneg _)
  have hsq : ‖gradient (u ∘ Θ) y‖ ^ 2 ≤ M ^ 2 * ‖gradient u (Θ y)‖ ^ 2 := by
    rw [← mul_pow]
    exact pow_le_pow_left₀ (norm_nonneg _) hgrad 2
  have hone : 1 ≤ |(fderiv ℝ Θ y).det| / δ := (one_le_div hδ).mpr hδL
  rw [Real.norm_eq_abs, abs_of_nonneg (by positivity), smul_eq_mul]
  calc ‖gradient (u ∘ Θ) y‖ ^ 2 ≤ M ^ 2 * ‖gradient u (Θ y)‖ ^ 2 := hsq
    _ = M ^ 2 * ‖gradient u (Θ y)‖ ^ 2 * 1 := (mul_one _).symm
    _ ≤ M ^ 2 * ‖gradient u (Θ y)‖ ^ 2 * (|(fderiv ℝ Θ y).det| / δ) :=
        mul_le_mul_of_nonneg_left hone (by positivity)
    _ = M ^ 2 / δ * (|(fderiv ℝ Θ y).det| * ‖gradient u (Θ y)‖ ^ 2) := by ring

end LiquidDrop

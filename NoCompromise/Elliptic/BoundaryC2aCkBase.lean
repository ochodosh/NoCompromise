module

public import NoCompromise.Elliptic.BoundaryC2aCkIterate
public import NoCompromise.Elliptic.BoundaryC2aCoverNorm
public import NoCompromise.Elliptic.BoundaryC2aFlatTraceZero
public import NoCompromise.Elliptic.BoundaryC2aLocal

@[expose] public section

/-!
# The base level of the Dirichlet boundary higher-regularity iteration (`thm:boundary-C2a`)

* `boundaryC2aCkBase_unit`: the unit-radius classical-data form of the flat Dirichlet C²,α
  theorem `boundary_c2a_half_ball_full_of_h1`. A smooth coefficient `A` and boundary datum
  `φ`, a C¹,α datum `G` and a C¹ solution `u` near the closed unit half ball give `u ∈ C²` on
  the half ball of radius `1/2` with bounded, α-Hölder second coordinate derivatives. The H¹
  hypotheses, the zero flat trace of `u - φ` and the energy bound are verified from the
  classical data, and the returned representative is identified with `u` (both continuous
  and equal a.e. on the open half ball).
* `boundaryDirichletCkLevel_zero`: level `0` at radius `R ≤ 1`, by rescaling
  `u_R = u ∘ (R • ·)`, `A_R = A ∘ (R • ·)`, `G_R = R • G ∘ (R • ·)`, `φ_R = φ ∘ (R • ·)` to the
  unit half ball; second coordinate derivatives scale by `R⁻²`.
* `boundaryDirichletCkLevel_holds`: every level, from `boundaryDirichletCkLevel_of_zero`.
-/

noncomputable section
open MeasureTheory Filter Metric Set InnerProductSpace
open scoped ENNReal Topology Gradient RealInnerProductSpace
namespace LiquidDrop

/-- A C¹ function near the closed unit half ball is H¹ on the unit half ball with its
classical gradient. -/
lemma boundaryC2aCkBase_hasH1GradientOn {U : Set (EuclideanSpace ℝ (Fin 3))} (hU : IsOpen U)
    (hUc : closure (boundaryHalfBall 1) ⊆ U) {u : EuclideanSpace ℝ (Fin 3) → ℝ}
    (hu : ContDiffOn ℝ 1 u U) : HasH1GradientOn u (gradient u) (boundaryHalfBall 1) := by
  have hB := isOpen_boundaryHalfBall (1 : ℝ)
  have hKc := boundaryNeumannCkIterate_isCompact_closure 1
  let : IsFiniteMeasure (volume.restrict (boundaryHalfBall 1)) :=
    isFiniteMeasure_restrict.mpr (boundaryHalfBall_volume_lt_top 1).ne
  have hBU : boundaryHalfBall 1 ⊆ U := subset_closure.trans hUc
  have hgc : ContinuousOn (gradient u) U :=
    (toDual ℝ (EuclideanSpace ℝ (Fin 3))).symm.continuous.comp_continuousOn
      (hu.continuousOn_fderiv_of_isOpen hU le_rfl)
  obtain ⟨C, hC⟩ := hKc.exists_bound_of_continuousOn (hu.continuousOn.mono hUc)
  obtain ⟨B, hBd⟩ := hKc.exists_bound_of_continuousOn (hgc.mono hUc)
  refine ⟨hasWeakGradientOn_of_contDiffOn hB (hu.mono hBU),
    MemLp.of_bound ((hu.continuousOn.mono hBU).aestronglyMeasurable hB.measurableSet) C ?_,
    MemLp.of_bound ((hgc.mono hBU).aestronglyMeasurable hB.measurableSet) B ?_⟩
  · filter_upwards [ae_restrict_mem hB.measurableSet] with x hx
    exact hC x (subset_closure hx)
  · filter_upwards [ae_restrict_mem hB.measurableSet] with x hx
    exact hBd x (subset_closure hx)

/-- Unit-radius classical-data form of the flat Dirichlet C²,α theorem. -/
theorem boundaryC2aCkBase_unit {α lam cap : ℝ} (hα : 0 < α) (hα1 : α < 1) (hlam : 0 < lam)
    {U : Set (EuclideanSpace ℝ (Fin 3))} (hU : IsOpen U)
    (hUc : closure (boundaryHalfBall 1) ⊆ U)
    {A : EuclideanSpace ℝ (Fin 3) → EuclideanSpace ℝ (Fin 3) →L[ℝ] EuclideanSpace ℝ (Fin 3)}
    {G : EuclideanSpace ℝ (Fin 3) → EuclideanSpace ℝ (Fin 3)}
    {u φ : EuclideanSpace ℝ (Fin 3) → ℝ}
    (hA : ContDiffOn ℝ (⊤ : ℕ∞) A U) (hφ : ContDiff ℝ (⊤ : ℕ∞) φ)
    (hG : HasC1HolderOn α G (closure (boundaryHalfBall 1))) (hu : ContDiffOn ℝ 1 u U)
    (hcap : ∀ x ∈ closure (boundaryHalfBall 1), ‖A x‖ ≤ cap)
    (hell : ∀ x ∈ closure (boundaryHalfBall 1), ∀ v, lam * ‖v‖ ^ 2 ≤ inner ℝ (A x v) v)
    (hface : ∀ x ∈ closure (boundaryHalfBall 1), x (Fin.last 2) = 0 → u x = φ x)
    (he : IsWeakDivergenceEquationOn A (gradient u) G (boundaryHalfBall 1)) :
    ContDiffOn ℝ 2 u (boundaryHalfBall (1 / 2)) ∧ ∃ C, ∀ i j : Fin 3,
      (∀ x ∈ boundaryHalfBall (1 / 2), |boundaryNeumannC2Entry u x i j| ≤ C) ∧
      ∀ x ∈ boundaryHalfBall (1 / 2), ∀ y ∈ boundaryHalfBall (1 / 2),
        |boundaryNeumannC2Entry u x i j - boundaryNeumannC2Entry u y i j| ≤
          C * dist x y ^ α := by
  set K := closure (boundaryHalfBall (1 : ℝ)) with hK_def
  have hKc : IsCompact K := boundaryNeumannCkIterate_isCompact_closure 1
  have hKv : Convex ℝ K := (convex_boundaryHalfBall 1).closure
  have hB := isOpen_boundaryHalfBall (1 : ℝ)
  have hBU : boundaryHalfBall 1 ⊆ U := subset_closure.trans hUc
  have hAK : HasC1HolderOn α A K :=
    hasC1HolderOn_of_contDiffOn_two hα.le hα1.le hKc hKv hU hUc
      (hA.of_le (by simp : (2 : WithTop ℕ∞) ≤ ↑(⊤ : ℕ∞)))
  have hφ2 : ContDiff ℝ 2 φ := hφ.of_le (by simp : (2 : WithTop ℕ∞) ≤ ↑(⊤ : ℕ∞))
  have hgφ : ContDiff ℝ 2 (gradient φ) :=
    contDiff_gradient_of_contDiff_succ (hφ.of_le (by simp : ((2 : WithTop ℕ∞) + 1) ≤ ↑(⊤ : ℕ∞)))
  have hφK : HasC1HolderOn α φ K :=
    hasC1HolderOn_of_contDiffOn_two hα.le hα1.le hKc hKv isOpen_univ (subset_univ _)
      hφ2.contDiffOn
  have hgφK : HasC1HolderOn α (gradient φ) K :=
    hasC1HolderOn_of_contDiffOn_two hα.le hα1.le hKc hKv isOpen_univ (subset_univ _)
      hgφ.contDiffOn
  have hgφD : HasC1HolderOn α (gradient φ) (closedBall (0 : EuclideanSpace ℝ (Fin 3)) 1) :=
    hasC1HolderOn_of_contDiffOn_two hα.le hα1.le (isCompact_closedBall _ _)
      (convex_closedBall _ _) isOpen_univ (subset_univ _) hgφ.contDiffOn
  obtain ⟨P₁, hP₁⟩ := (isCompact_closedBall (0 : EuclideanSpace ℝ (Fin 3)) 1
    ).exists_bound_of_continuousOn hgφ.continuous.continuousOn
  have hP₂ := boundary_c2a_local_holder_pointwise hgφD.function_holder le_rfl
  have hP₁0 : 0 ≤ P₁ := (norm_nonneg _).trans (hP₁ 0 (mem_closedBall_self zero_le_one))
  have hP₂0 : 0 ≤ holderNorm α (gradient φ) (closedBall (0 : EuclideanSpace ℝ (Fin 3)) 1) :=
    hgφD.function_holder.norm_nonneg
  have hφ1 : ContDiff ℝ 1 φ := hφ.of_le (by simp : (1 : WithTop ℕ∞) ≤ ↑(⊤ : ℕ∞))
  have hH1 := boundaryC2aCkBase_hasH1GradientOn hU hUc hu
  have hgu : ContinuousOn (gradient u) U :=
    (toDual ℝ (EuclideanSpace ℝ (Fin 3))).symm.continuous.comp_continuousOn
      (hu.continuousOn_fderiv_of_isOpen hU le_rfl)
  -- the zero flat trace of `u - φ`
  have htr : HasZeroFlatTraceOn (fun x => u x - φ x) (fun x => gradient u x - gradient φ x)
      (ball 0 1) := by
    refine hasZeroFlatTraceOn_of_continuousOn ?_ ((hu.mono hBU).sub hφ1.contDiffOn) ?_ ?_ ?_
    · exact (hu.continuousOn.sub hφ.continuous.continuousOn).mono fun y hy =>
        hUc (boundaryC2aCkIterate_mem_closure (mem_ball_zero_iff.1 hy.1) hy.2)
    · intro x hx
      have hdu : DifferentiableAt ℝ u x :=
        (hu.differentiableOn one_ne_zero x (hBU hx)).differentiableAt (hU.mem_nhds (hBU hx))
      have hdφ : DifferentiableAt ℝ φ x := hφ1.differentiable one_ne_zero x
      simp only [gradient]
      rw [fderiv_fun_sub hdu hdφ, map_sub]
    · have hc : ContinuousOn (fun x => ‖gradient u x - gradient φ x‖) K :=
        ((hgu.mono hUc).sub hgφ.continuous.continuousOn).norm
      exact (hc.integrableOn_compact hKc).mono_set subset_closure
    · intro x hx hx3
      exact sub_eq_zero.2 (hface x (boundaryC2aCkIterate_mem_closure (mem_ball_zero_iff.1 hx)
        hx3.symm.le) hx3)
  have hE0 : 0 ≤ ∫ x in boundaryHalfBall 1, ‖gradient u x - gradient φ x‖ ^ 2 :=
    integral_nonneg fun _ => by positivity
  obtain ⟨C, -, hmain⟩ := boundary_c2a_half_ball_full_of_h1 hα hα1 hlam
    (le_max_right cap lam) hAK.norm_nonneg
    (add_nonneg (add_nonneg hφK.norm_nonneg hgφK.norm_nonneg) hG.norm_nonneg) hP₁0 hP₂0 hE0
  obtain ⟨v, hvC, hvu, hent, -⟩ := hmain u φ (gradient u) G A hφ2 hAK hG hφK hgφK le_rfl le_rfl
    (fun x hx => (hcap x hx).trans (le_max_left _ _)) hell hP₁ hP₂ hH1 he htr le_rfl
  have hS := isOpen_boundaryHalfBall (1 / 2 : ℝ)
  have hSU : boundaryHalfBall (1 / 2) ⊆ U :=
    (boundaryHalfBall_mono (by norm_num)).trans hBU
  have hvu' : EqOn v u (boundaryHalfBall (1 / 2)) :=
    Measure.eqOn_open_of_ae_eq hvu hS hvC.continuousOn (hu.continuousOn.mono hSU)
  have hentry : ∀ x ∈ boundaryHalfBall (1 / 2), ∀ i j : Fin 3,
      boundaryNeumannC2Entry u x i j = boundaryNeumannC2Entry v x i j := by
    intro x hx i j
    have hd : ∀ y ∈ boundaryHalfBall (1 / 2), fderiv ℝ u y = fderiv ℝ v y := fun y hy =>
      ((hvu'.eventuallyEq_of_mem (hS.mem_nhds hy)).fderiv_eq).symm
    have hev : (fun z => fderiv ℝ u z (EuclideanSpace.single j 1)) =ᶠ[𝓝 x]
        (fun z => fderiv ℝ v z (EuclideanSpace.single j 1)) :=
      Filter.eventually_of_mem (hS.mem_nhds hx) fun y hy => by simp only [hd y hy]
    unfold boundaryNeumannC2Entry
    rw [hev.fderiv_eq]
  refine ⟨hvC.congr fun x hx => (hvu' hx).symm, C, fun i j => ⟨fun x hx => ?_,
    fun x hx y hy => ?_⟩⟩
  · rw [hentry x hx]
    exact (hent i j).1 x hx
  · rw [hentry x hx, hentry y hy]
    exact (hent i j).2 x hx y hy

/-- A constant multiple of a C¹,α function is C¹,α. -/
lemma boundaryC2aCkBase_c1Holder_const_smul {α : ℝ}
    {f : EuclideanSpace ℝ (Fin 3) → EuclideanSpace ℝ (Fin 3)}
    {S : Set (EuclideanSpace ℝ (Fin 3))} (hf : HasC1HolderOn α f S) (c : ℝ) :
    HasC1HolderOn α (fun x => c • f x) S := by
  refine ⟨hf.contDiff.const_smul c, (nondiv_holder_const_smul hf.function_holder c).1, ?_⟩
  have h : fderiv ℝ (fun x => c • f x) = fun x => c • fderiv ℝ f x :=
    fderiv_const_smul_field (𝕜 := ℝ) (f := f) c
  rw [h]
  exact (nondiv_holder_const_smul hf.derivative_holder c).1

/-- The dilation `y ↦ R • y` maps the closed unit half ball into the closed half ball of
radius `R`. -/
lemma boundaryC2aCkBase_mapsTo_closure {R : ℝ} (hR : 0 < R) :
    MapsTo (frozenBallScaling (0 : EuclideanSpace ℝ (Fin 3)) hR) (closure (boundaryHalfBall 1))
      (closure (boundaryHalfBall R)) := by
  intro y hy
  refine closure_mono ?_ (image_closure_subset_closure_image
    (frozenBallScaling (0 : EuclideanSpace ℝ (Fin 3)) hR).continuous ⟨y, hy, rfl⟩)
  rintro _ ⟨z, hz, rfl⟩
  simpa using (boundary_halfBall_scaling_mem hR z 1).2 hz

/-- Level `0` of the Dirichlet boundary iteration: the flat C²,α theorem at scale `R`. -/
theorem boundaryDirichletCkLevel_zero : BoundaryDirichletCkLevel 0 := by
  intro α lam cap R hα hα1 hlam hR hR1 U hU hUc A G u φ hA hφ hG hu hcap hell hface he
  set e := frozenBallScaling (0 : EuclideanSpace ℝ (Fin 3)) hR with he_def
  have hKc := boundaryNeumannCkIterate_isCompact_closure R
  have hKv : Convex ℝ (closure (boundaryHalfBall R)) := (convex_boundaryHalfBall R).closure
  have hKb := hKc.isBounded
  have hec : ContDiff ℝ (⊤ : ℕ∞) e := contDiff_const.add (contDiff_id.const_smul R)
  have hmK : MapsTo e (closure (boundaryHalfBall 1)) (closure (boundaryHalfBall R)) :=
    boundaryC2aCkBase_mapsTo_closure hR
  have heapp : ∀ y, e y = R • y := fun y => by rw [he_def, frozenBallScaling_apply, zero_add]
  -- the rescaled data on the unit half ball
  have hU₁ : IsOpen (e ⁻¹' U) := hU.preimage e.continuous
  have hU₁c : closure (boundaryHalfBall 1) ⊆ e ⁻¹' U := fun y hy => hUc (hmK hy)
  have hA₁ : ContDiffOn ℝ (⊤ : ℕ∞) (A ∘ e) (e ⁻¹' U) :=
    hA.comp hec.contDiffOn (mapsTo_preimage _ _)
  have hφ₁ : ContDiff ℝ (⊤ : ℕ∞) (φ ∘ e) := hφ.comp hec
  have hGK : HasC1HolderOn α G (closure (boundaryHalfBall R)) :=
    hG.hasC1HolderOn hα1.le hU hUc hKv hKb
  have hG₁ : HasC1HolderOn α (fun y => R • G (e y)) (closure (boundaryHalfBall 1)) :=
    boundaryC2aCkBase_c1Holder_const_smul
      (boundary_c2a_c1Holder_comp_scaling hα.le 0 hR hR1 hGK hmK).1 R
  have hu₁ : ContDiffOn ℝ 1 (u ∘ e) (e ⁻¹' U) :=
    (hu.contDiffOn.of_le (by norm_num)).comp (hec.of_le (by simp)).contDiffOn
      (mapsTo_preimage _ _)
  have hcap₁ : ∀ y ∈ closure (boundaryHalfBall 1), ‖(A ∘ e) y‖ ≤ cap :=
    fun y hy => hcap _ (hmK hy)
  have hell₁ : ∀ y ∈ closure (boundaryHalfBall 1), ∀ v,
      lam * ‖v‖ ^ 2 ≤ inner ℝ ((A ∘ e) y v) v := fun y hy => hell _ (hmK hy)
  have hface₁ : ∀ y ∈ closure (boundaryHalfBall 1), y (Fin.last 2) = 0 →
      (u ∘ e) y = (φ ∘ e) y := by
    intro y hy hy3
    refine hface _ (hmK hy) ?_
    rw [heapp, PiLp.smul_apply, hy3, smul_zero]
  have hgrad : gradient (u ∘ e) = fun y => R • gradient u (e y) := by
    funext y
    exact boundary_c2a_gradient_comp_scaling 0 y hR u
  have he₁ : IsWeakDivergenceEquationOn (A ∘ e) (gradient (u ∘ e)) (fun y => R • G (e y))
      (boundaryHalfBall 1) := by
    rw [hgrad]
    exact he.boundary_comp_scaling hR
  obtain ⟨hC2, C, hCb⟩ :=
    boundaryC2aCkBase_unit hα hα1 hlam hU₁ hU₁c hA₁ hφ₁ hG₁ hu₁ hcap₁ hell₁ hface₁ he₁
  -- transfer back along `e⁻¹`
  have hρ : (3 / 8 * (1 / 2 : ℝ) ^ 0 * R) = R * (3 / 8) := by ring
  rw [hρ]
  set S := boundaryHalfBall (R * (3 / 8)) with hS_def
  have hS : IsOpen S := isOpen_boundaryHalfBall _
  have hSR : S ⊆ closure (boundaryHalfBall R) :=
    (boundaryHalfBall_mono (by linarith)).trans subset_closure
  have hmS : MapsTo e.symm S (boundaryHalfBall (1 / 2)) := by
    intro x hx
    have h1 : e (e.symm x) ∈ boundaryHalfBall (R * (3 / 8)) := by
      rw [e.apply_symm_apply]; exact hx
    exact boundaryHalfBall_mono (by norm_num) ((boundary_halfBall_scaling_mem hR _ _).1 h1)
  have hesc : ContDiff ℝ 2 e.symm := by
    rw [he_def, frozenBallScaling_symm_coe]
    exact (contDiff_id.sub contDiff_const).const_smul R⁻¹
  have hu_eq : (u ∘ e) ∘ e.symm = u := by
    funext x
    simp
  have hc2 : ContDiffOn ℝ 2 u S := by
    have h := hC2.comp hesc.contDiffOn hmS
    rwa [hu_eq] at h
  have hent : ∀ x ∈ S, ∀ i j : Fin 3, boundaryNeumannC2Entry u x i j =
      R⁻¹ ^ 2 * boundaryNeumannC2Entry (u ∘ e) (e.symm x) i j := by
    intro x _ i j
    have h := boundary_c2a_entry_comp_scaling 0 (e.symm x) hR (u ∘ e) i j
    rw [← he_def, hu_eq, e.apply_symm_apply] at h
    exact h
  have hdist : ∀ x y, dist (e.symm x) (e.symm y) = R⁻¹ * dist x y := fun x y =>
    quasilinear_ballScaling_symm_dist 0 x y hR
  have hwb : ∃ B, ∀ x ∈ S, ‖u x‖ ≤ B := by
    obtain ⟨B, hB⟩ := hu.bounded 0 (Nat.zero_le _)
    refine ⟨B, fun x hx => ?_⟩
    have h := hB x (hSR hx)
    rwa [norm_iteratedFDeriv_zero] at h
  have hdwb : ∀ i : Fin 3, ∃ B, ∀ x ∈ S,
      ‖fderiv ℝ u x (EuclideanSpace.single i 1)‖ ≤ B := by
    intro i
    obtain ⟨-, ⟨B, hB⟩, -⟩ :=
      hasCkHolderOn_zero_iff.1 (hu.partial hU hUc (EuclideanSpace.single i 1))
    exact ⟨B, fun x hx => hB x (hSR hx)⟩
  refine hasCkHolderOn_succ_of_partials (k := 1) hS subset_rfl
    (hc2.differentiableOn (by norm_num)) hwb fun i => ?_
  have hd1 : ContDiffOn ℝ 1 (fun x => fderiv ℝ u x (EuclideanSpace.single i 1)) S :=
    (hc2.fderiv_of_isOpen hS (by norm_num)).clm_apply contDiffOn_const
  refine hasCkHolderOn_succ_of_partials (k := 0) hS subset_rfl
    (hd1.differentiableOn one_ne_zero) (hdwb i) fun j => ?_
  have hDc : ContinuousOn (fun x => fderiv ℝ (fun y => fderiv ℝ u y
      (EuclideanSpace.single i 1)) x (EuclideanSpace.single j 1)) S :=
    (hd1.continuousOn_fderiv_of_isOpen hS le_rfl).clm_apply continuousOn_const
  obtain ⟨hb, hh⟩ := hCb j i
  have hRi : 0 ≤ R⁻¹ ^ 2 := by positivity
  refine hasCkHolderOn_zero_iff.2 ⟨hDc, ⟨R⁻¹ ^ 2 * C, fun x hx => ?_⟩,
    ⟨R⁻¹ ^ 2 * (C * R⁻¹ ^ α), fun x hx y hy => ?_⟩⟩
  · change ‖boundaryNeumannC2Entry u x j i‖ ≤ _
    rw [hent x hx, Real.norm_eq_abs, abs_mul, abs_of_nonneg hRi]
    exact mul_le_mul_of_nonneg_left (hb _ (hmS hx)) hRi
  · change ‖boundaryNeumannC2Entry u x j i - boundaryNeumannC2Entry u y j i‖ ≤ _
    rw [hent x hx, hent y hy, ← mul_sub, Real.norm_eq_abs, abs_mul, abs_of_nonneg hRi]
    have h := hh _ (hmS hx) _ (hmS hy)
    rw [hdist, Real.mul_rpow (inv_nonneg.2 hR.le) dist_nonneg] at h
    exact (mul_le_mul_of_nonneg_left h hRi).trans (le_of_eq (by ring))

/-- Blueprint `thm:boundary-C2a` (flat Dirichlet, all orders): every level of the Dirichlet
boundary higher-regularity iteration holds. -/
theorem boundaryDirichletCkLevel_holds (k : ℕ) : BoundaryDirichletCkLevel k :=
  boundaryDirichletCkLevel_of_zero boundaryDirichletCkLevel_zero k

end LiquidDrop

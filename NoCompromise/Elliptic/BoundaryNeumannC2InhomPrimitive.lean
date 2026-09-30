module

public import NoCompromise.Elliptic.BoundaryNeumannC2InhomBounds
public import Mathlib.Analysis.Calculus.ParametricIntervalIntegral

@[expose] public section

/-! Smoothness of the existing vertical primitive, by differentiation under
the normalized integral over `[0,1]`. -/

noncomputable section
open Set Filter Metric MeasureTheory
open scoped Topology
namespace LiquidDrop

lemma boundary_neumann_c2_inhom_integral_continuousOn
    {d : ℕ} {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F] [CompleteSpace F]
    {G : EuclideanSpace ℝ (Fin d) × ℝ → F}
    {W : Set (EuclideanSpace ℝ (Fin d) × ℝ)} (hW : IsOpen W)
    (hsub : closedBall 0 1 ×ˢ Icc (0 : ℝ) 1 ⊆ W) (hG : ContinuousOn G W) :
    ContinuousOn (fun x => ∫ t in (0 : ℝ)..1, G (x, t)) (ball 0 1) := by
  obtain ⟨B, -, hB⟩ := (((isCompact_closedBall (0 : EuclideanSpace ℝ (Fin d)) 1).prod
    isCompact_Icc).image_of_continuousOn (hG.mono hsub)).isBounded.exists_pos_norm_le
  have hslice (x : EuclideanSpace ℝ (Fin d)) (hx : x ∈ ball 0 1) :
      ContinuousOn (fun t => G (x, t)) (Icc (0 : ℝ) 1) :=
    hG.comp (continuous_const.prodMk continuous_id).continuousOn
      (fun _ ht => hsub ⟨ball_subset_closedBall hx, ht⟩)
  intro x hx
  apply intervalIntegral.continuousWithinAt_of_dominated_interval
    (F := fun x t => G (x, t)) (s := ball 0 1) (x₀ := x) (bound := fun _ => B)
  · filter_upwards [self_mem_nhdsWithin] with y hy
    exact ((hslice y hy).mono (by simpa only [uIoc_of_le zero_le_one] using
      (Ioc_subset_Icc_self : Ioc (0 : ℝ) 1 ⊆ Icc 0 1))).aestronglyMeasurable measurableSet_uIoc
  · filter_upwards [self_mem_nhdsWithin] with y hy
    exact ae_of_all _ (fun t ht => hB _ (mem_image_of_mem _
      ⟨ball_subset_closedBall hy, by
        simpa only [uIcc_of_le zero_le_one] using uIoc_subset_uIcc ht⟩))
  · exact intervalIntegrable_const
  · refine ae_of_all _ (fun t ht => ?_)
    have ht' : t ∈ Icc (0 : ℝ) 1 := by
      simpa only [uIcc_of_le zero_le_one] using uIoc_subset_uIcc ht
    have hxt : (x, t) ∈ W := hsub ⟨ball_subset_closedBall hx, ht'⟩
    have hc : ContinuousAt G (x, t) := hG.continuousAt (hW.mem_nhds hxt)
    have hc' : ContinuousAt (fun y : EuclideanSpace ℝ (Fin d) => G (y, t)) x :=
      hc.comp (f := fun y : EuclideanSpace ℝ (Fin d) => (y, t))
        (continuousAt_id.prodMk continuousAt_const)
    exact hc'.continuousWithinAt

/-- Integration over a compact parameter interval preserves every finite
order of differentiability on the unit ball. The integrand is defined on an
open neighborhood of the full closed ball times the parameter interval. -/
theorem boundary_neumann_c2_inhom_integral_contDiffOn
    {d : ℕ} (n : ℕ) {F : Type*}
    [NormedAddCommGroup F] [NormedSpace ℝ F] [CompleteSpace F]
    {G : EuclideanSpace ℝ (Fin d) × ℝ → F}
    {W : Set (EuclideanSpace ℝ (Fin d) × ℝ)} (hW : IsOpen W)
    (hsub : closedBall 0 1 ×ˢ Icc (0 : ℝ) 1 ⊆ W) (hG : ContDiffOn ℝ n G W) :
    ContDiffOn ℝ n (fun x => ∫ t in (0 : ℝ)..1, G (x, t)) (ball 0 1) := by
  induction n generalizing F with
  | zero =>
    exact contDiffOn_zero.mpr
      (boundary_neumann_c2_inhom_integral_continuousOn hW hsub hG.continuousOn)
  | succ n ih =>
    let D (p : EuclideanSpace ℝ (Fin d) × ℝ) :=
      (fderiv ℝ G p).comp (ContinuousLinearMap.inl ℝ (EuclideanSpace ℝ (Fin d)) ℝ)
    have hD : ContDiffOn ℝ n D W :=
      (hG.fderiv_of_isOpen hW (by simp)).clm_comp contDiffOn_const
    have hDI := ih hD
    have hdc := hD.continuousOn
    obtain ⟨B, -, hB⟩ := (((isCompact_closedBall (0 : EuclideanSpace ℝ (Fin d)) 1).prod
      isCompact_Icc).image_of_continuousOn (hdc.mono hsub)).isBounded.exists_pos_norm_le
    have hslice (x : EuclideanSpace ℝ (Fin d)) (hx : x ∈ ball 0 1) :
        ContinuousOn (fun t => G (x, t)) (Icc (0 : ℝ) 1) :=
      hG.continuousOn.comp (continuous_const.prodMk continuous_id).continuousOn
        (fun _ ht => hsub ⟨ball_subset_closedBall hx, ht⟩)
    have hdslice (x : EuclideanSpace ℝ (Fin d)) (hx : x ∈ ball 0 1) :
        ContinuousOn (fun t => D (x, t)) (Icc (0 : ℝ) 1) :=
      hdc.comp (continuous_const.prodMk continuous_id).continuousOn
        (fun _ ht => hsub ⟨ball_subset_closedBall hx, ht⟩)
    have hd (x : EuclideanSpace ℝ (Fin d)) (hx : x ∈ ball 0 1) :
        HasFDerivAt (fun x => ∫ t in (0 : ℝ)..1, G (x, t))
          (∫ t in (0 : ℝ)..1, D (x, t)) x := by
      apply intervalIntegral.hasFDerivAt_integral_of_dominated_of_fderiv_le
        (s := ball 0 1) (bound := fun _ => B) (F' := fun x t => D (x, t))
        (isOpen_ball.mem_nhds hx)
      · filter_upwards [isOpen_ball.mem_nhds hx] with y hy
        exact ((hslice y hy).mono (by simpa only [uIoc_of_le zero_le_one] using
          (Ioc_subset_Icc_self : Ioc (0 : ℝ) 1 ⊆ Icc 0 1))).aestronglyMeasurable measurableSet_uIoc
      · apply ContinuousOn.intervalIntegrable
        simpa only [uIcc_of_le zero_le_one] using hslice x hx
      · exact ((hdslice x hx).mono (by simpa only [uIoc_of_le zero_le_one] using
          (Ioc_subset_Icc_self : Ioc (0 : ℝ) 1 ⊆ Icc 0 1))).aestronglyMeasurable measurableSet_uIoc
      · exact ae_of_all _ (fun t ht y hy => hB _ (mem_image_of_mem _
          ⟨ball_subset_closedBall hy, by
            simpa only [uIcc_of_le zero_le_one] using uIoc_subset_uIcc ht⟩))
      · exact intervalIntegrable_const
      · refine ae_of_all _ (fun t ht y hy => ?_)
        have ht' : t ∈ Icc (0 : ℝ) 1 := by
          simpa only [uIcc_of_le zero_le_one] using uIoc_subset_uIcc ht
        have hyt : (y, t) ∈ W := hsub ⟨ball_subset_closedBall hy, ht'⟩
        have hg : DifferentiableAt ℝ G (y, t) :=
          (hG.contDiffAt (hW.mem_nhds hyt)).differentiableAt (by simp)
        exact hg.hasFDerivAt.comp y (hasFDerivAt_prodMk_left y t)
    rw [show ((n + 1 : ℕ) : WithTop ℕ∞) = (n : WithTop ℕ∞) + 1 by simp]
    apply (contDiffOn_succ_iff_hasFDerivWithinAt_of_uniqueDiffOn isOpen_ball.uniqueDiffOn).mpr
    exact ⟨by simp, fun x => ∫ t in (0 : ℝ)..1, D (x, t), hDI,
      fun x hx => (hd x hx).hasFDerivWithinAt⟩

theorem boundaryNeumannPrimitive_smoothOn
    {f : EuclideanSpace ℝ (Fin 3) → ℝ} {O : Set (EuclideanSpace ℝ (Fin 3))}
    (hO : IsOpen O) (hsub : closedBall 0 1 ⊆ O)
    (hf : ContDiffOn ℝ (⊤ : ℕ∞) f O) :
    ContDiffOn ℝ (⊤ : ℕ∞) (boundaryNeumannPrimitive f) (ball 0 1) := by
  let V (p : EuclideanSpace ℝ (Fin 3) × ℝ) := boundaryNeumannVerticalContraction p.2 p.1
  have hV : ContDiff ℝ (⊤ : ℕ∞) V := by
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
  have hI : ContDiffOn ℝ (⊤ : ℕ∞)
      (fun x => ∫ t in (0 : ℝ)..1, f (boundaryNeumannVerticalContraction t x)) (ball 0 1) := by
    apply contDiffOn_infty.mpr
    intro n
    exact boundary_neumann_c2_inhom_integral_contDiffOn n
      (hO.preimage hV.continuous) hmaps
      ((hf.comp hV.contDiffOn (fun _ hx => hx)).of_le (by simp))
  have he : boundaryNeumannPrimitive f = fun x =>
      (x (Fin.last 2) * ∫ t in (0 : ℝ)..1, f (boundaryNeumannVerticalContraction t x)) •
        EuclideanSpace.single (Fin.last 2) 1 :=
    funext (boundaryNeumannPrimitive_normalized f)
  rw [he]
  exact ((EuclideanSpace.proj (Fin.last 2) :
    EuclideanSpace ℝ (Fin 3) →L[ℝ] ℝ).contDiff.contDiffOn.mul hI).smul contDiffOn_const

end LiquidDrop

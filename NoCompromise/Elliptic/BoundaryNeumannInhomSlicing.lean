module

public import NoCompromise.Elliptic.BoundaryNeumann
public import NoCompromise.DeGiorgi.SmoothGraph
public import NoCompromise.Area.Graph

@[expose] public section

/-!
# Vertical integration for the inhomogeneous conormal equation

The positive half-space has inward normal `e₃`. Consequently the integral of
a vertical test derivative equals minus its value on the flat face.
-/

noncomputable section
open MeasureTheory Filter Metric Set InnerProductSpace
open scoped ENNReal NNReal Topology Gradient RealInnerProductSpace
namespace LiquidDrop

lemma boundary_neumann_norm_projection_le (x : EuclideanSpace ℝ (Fin 3)) :
    ‖graphProjectionN 2 x‖ ≤ ‖x‖ := by
  have h := norm_sq_graphProjectionN x
  nlinarith [sq_nonneg (x (Fin.last 2)), norm_nonneg x,
    norm_nonneg (graphProjectionN 2 x)]

lemma boundary_neumann_vertical_hasDerivAt
    {φ : EuclideanSpace ℝ (Fin 3) → ℝ} (hφ : ContDiff ℝ 1 φ)
    (y : EuclideanSpace ℝ (Fin 2)) (t : ℝ) :
    HasDerivAt (fun s => φ (graphAppendN y s))
      (gradient φ (graphAppendN y t) (Fin.last 2)) t := by
  have ht : HasDerivAt (fun s : ℝ => graphAppendN y s)
      (EuclideanSpace.single (Fin.last 2) 1) t := by
    simpa only [graphAppendN, one_smul, id_eq] using
      ((hasDerivAt_id t).smul_const (EuclideanSpace.single (Fin.last 2) (1 : ℝ))).const_add
        (graphBaseN 2 y)
  simpa only [Function.comp_def, gradient_apply_eq_fderiv_single] using
    (hφ.differentiable one_ne_zero (graphAppendN y t)).hasFDerivAt.comp_hasDerivAt t ht

lemma boundary_neumann_vertical_integral
    {φ : EuclideanSpace ℝ (Fin 3) → ℝ} (hφ : ContDiff ℝ 1 φ)
    (hcφ : HasCompactSupport φ) (y : EuclideanSpace ℝ (Fin 2)) :
    (∫ t in Ioi (0 : ℝ), gradient φ (graphAppendN y t) (Fin.last 2)) =
      -φ (graphAppendN y 0) := by
  have hψ : ContDiff ℝ 1 (fun t : ℝ => φ (graphAppendN y t)) :=
    hφ.comp (contDiff_const.add (contDiff_id.smul contDiff_const))
  have hcψ : HasCompactSupport (fun t : ℝ => φ (graphAppendN y t)) := by
    simpa only [add_zero] using hasCompactSupport_smoothGraph_vertical
      (f := fun _ : EuclideanSpace ℝ (Fin 2) => (0 : ℝ)) continuous_const hcφ y
  simp_rw [← (boundary_neumann_vertical_hasDerivAt hφ y _).deriv]
  exact hcψ.integral_Ioi_deriv_eq hψ 0

/-- Fubini on the upper half-space, with the base coordinates first. -/
lemma boundary_neumann_integral_upper {g : EuclideanSpace ℝ (Fin 3) → ℝ}
    (hg : Integrable g) :
    (∫ x in {x : EuclideanSpace ℝ (Fin 3) | 0 < x (Fin.last 2)}, g x) =
      ∫ y : EuclideanSpace ℝ (Fin 2), ∫ t in Ioi (0 : ℝ), g (graphAppendN y t) := by
  let e := smoothGraphCoordinates (f := fun _ : EuclideanSpace ℝ (Fin 2) => (0 : ℝ))
    continuous_const
  have he : e ⁻¹' {x : EuclideanSpace ℝ (Fin 3) | 0 < x (Fin.last 2)} =
      univ ×ˢ Ioi (0 : ℝ) := by
    ext p
    simp only [e, mem_preimage, mem_ofPred_eq, smoothGraphCoordinates_apply,
      add_zero, graphAppendN_last, mem_prod, mem_univ, true_and, mem_Ioi]
  have hp := (smoothGraphCoordinates_measurePreserving
    (f := fun _ : EuclideanSpace ℝ (Fin 2) => (0 : ℝ)) continuous_const).restrict_preimage
      (s := {x : EuclideanSpace ℝ (Fin 3) | 0 < x (Fin.last 2)})
      (isOpen_lt continuous_const (EuclideanSpace.proj (Fin.last 2)).continuous).measurableSet
  change MeasurePreserving e _ _ at hp
  rw [he] at hp
  rw [← hp.integral_comp e.measurableEmbedding g]
  have hi : Integrable (g ∘ e) (volume.prod volume) :=
    (smoothGraphCoordinates_measurePreserving
      (f := fun _ : EuclideanSpace ℝ (Fin 2) => (0 : ℝ))
      continuous_const).integrable_comp_of_integrable hg
  simpa only [Function.comp_def, e, smoothGraphCoordinates_apply, add_zero,
    setIntegral_univ] using setIntegral_prod (s := univ) (t := Ioi (0 : ℝ))
      (g ∘ e) hi.integrableOn

/-- Localization of the half-space integral for tests supported inside the ball. -/
lemma boundary_neumann_integral_halfBall {g : EuclideanSpace ℝ (Fin 3) → ℝ}
    (hg : ∀ x ∉ ball (0 : EuclideanSpace ℝ (Fin 3)) 1, g x = 0) :
    (∫ x in boundaryHalfBall 1, g x) =
      ∫ x in {x : EuclideanSpace ℝ (Fin 3) | 0 < x (Fin.last 2)}, g x := by
  have he := setIntegral_eq_integral_of_forall_compl_eq_zero
    (μ := volume.restrict {x : EuclideanSpace ℝ (Fin 3) | 0 < x (Fin.last 2)}) hg
  simpa only [Measure.restrict_restrict measurableSet_ball, boundaryHalfBall] using he

/-- The boundary source identity, with only continuity on the closed disk. -/
theorem boundary_neumann_boundary_source_identity
    {h : EuclideanSpace ℝ (Fin 2) → ℝ}
    (hh : ContinuousOn h (closedBall 0 1))
    {φ : EuclideanSpace ℝ (Fin 3) → ℝ} (hφ : ContDiff ℝ 1 φ)
    (hcφ : HasCompactSupport φ) (hsφ : tsupport φ ⊆ ball 0 1) :
    (∫ x in boundaryHalfBall 1,
      h (graphProjectionN 2 x) * gradient φ x (Fin.last 2)) =
      -(∫ y in ball (0 : EuclideanSpace ℝ (Fin 2)) 1, h y * φ (graphBaseEmbedding y)) := by
  let g := fun x : EuclideanSpace ℝ (Fin 3) =>
    h (graphProjectionN 2 x) * gradient φ x (Fin.last 2)
  have hz (x : EuclideanSpace ℝ (Fin 3)) (hx : x ∉ ball 0 1) : g x = 0 := by
    dsimp only [g]
    rw [gradient_eq_zero_of_notMem_tsupport (fun ht => hx (hsφ ht))]
    simp
  have hproj : MapsTo (graphProjectionN 2) (closedBall 0 1) (closedBall 0 1) := by
    intro x hx
    simp only [mem_closedBall, dist_zero_right] at hx ⊢
    exact (boundary_neumann_norm_projection_le x).trans hx
  have hg : ContinuousOn g (closedBall 0 1) :=
    (hh.comp (graphProjectionN 2).continuous.continuousOn hproj).mul
      ((EuclideanSpace.proj (Fin.last 2)).continuous.comp
        (continuous_gradient_of_contDiff hφ)).continuousOn
  have hi : Integrable g := by
    apply (integrableOn_iff_integrable_of_support_subset (s := closedBall 0 1) ?_).mp
      (hg.integrableOn_compact (isCompact_closedBall 0 1))
    intro x hx
    apply ball_subset_closedBall
    by_contra hxb
    exact hx (hz x hxb)
  rw [boundary_neumann_integral_halfBall hz, boundary_neumann_integral_upper hi]
  simp_rw [g, graphProjectionN_append, integral_const_mul,
    boundary_neumann_vertical_integral hφ hcφ, mul_neg]
  rw [integral_neg]
  congr 1
  have hb (y : EuclideanSpace ℝ (Fin 2)) : graphAppendN y 0 = graphBaseEmbedding y := by
    ext i
    fin_cases i <;> simp [graphAppendN, graphBaseN]
  simp_rw [hb]
  symm
  apply setIntegral_eq_integral_of_forall_compl_eq_zero
  intro y hy
  have hn : graphBaseEmbedding y ∉ ball (0 : EuclideanSpace ℝ (Fin 3)) 1 := by
    simpa only [mem_ball, dist_zero_right, norm_graphBaseEmbedding] using hy
  rw [image_eq_zero_of_notMem_tsupport (fun ht => hn (hsφ ht)), mul_zero]

/-- The interior source identity on a single vertical segment. The only
regularity required of the source is continuity on the closed segment. -/
lemma boundary_neumann_primitive_slice {f : ℝ → ℝ} {T : ℝ} (hT : 0 ≤ T)
    (hf : ContinuousOn f (Icc 0 T))
    {φ : EuclideanSpace ℝ (Fin 3) → ℝ} (hφ : ContDiff ℝ 1 φ)
    (y : EuclideanSpace ℝ (Fin 2)) (htop : φ (graphAppendN y T) = 0) :
    (∫ t in (0 : ℝ)..T, (∫ s in (0 : ℝ)..t, f s) *
      gradient φ (graphAppendN y t) (Fin.last 2)) =
      -(∫ t in (0 : ℝ)..T, f t * φ (graphAppendN y t)) := by
  have hfu : ContinuousOn f (uIcc 0 T) := by rwa [uIcc_of_le hT]
  have hfi : IntervalIntegrable f volume 0 T := hfu.intervalIntegrable
  have hp := intervalIntegral.continuousOn_primitive_interval' hfi left_mem_uIcc
  have hc : Continuous (fun t : ℝ => graphAppendN y t) :=
    continuous_const.add (continuous_id.smul continuous_const)
  have hψ : Continuous (fun t => φ (graphAppendN y t)) := hφ.continuous.comp hc
  have hg : Continuous (fun t => gradient φ (graphAppendN y t) (Fin.last 2)) :=
    (EuclideanSpace.proj (Fin.last 2)).continuous.comp
      ((continuous_gradient_of_contDiff hφ).comp hc)
  have hd (t : ℝ) (ht : t ∈ Ioo (min 0 T) (max 0 T)) :
      HasDerivAt (fun t => ∫ s in (0 : ℝ)..t, f s) (f t) t := by
    have ht' : t ∈ Ioo 0 T := by simpa only [min_eq_left hT, max_eq_right hT] using ht
    have hi : IntervalIntegrable f volume 0 t := hfi.mono_set (by
      rw [uIcc_of_le ht'.1.le, uIcc_of_le hT]
      exact Icc_subset_Icc_right ht'.2.le)
    have hct : ContinuousAt f t := hf.continuousAt (Icc_mem_nhds ht'.1 ht'.2)
    have hm := hf.stronglyMeasurableAtFilter_nhdsWithin (μ := volume) measurableSet_Icc t
    rw [nhdsWithin_eq_nhds.mpr (Icc_mem_nhds ht'.1 ht'.2)] at hm
    exact intervalIntegral.integral_hasDerivAt_right hi hm hct
  have he := intervalIntegral.integral_deriv_mul_eq_sub_of_hasDerivAt hp
    hψ.continuousOn hd (fun t _ => boundary_neumann_vertical_hasDerivAt hφ y t)
    hfi (hg.intervalIntegrable 0 T)
  rw [intervalIntegral.integral_add (hfi.mul_continuousOn hψ.continuousOn)
    ((hg.intervalIntegrable 0 T).continuousOn_mul hp)] at he
  simp only [htop, mul_zero, intervalIntegral.integral_same, zero_mul, sub_zero] at he
  linarith

end LiquidDrop

module

public import NoCompromise.Elliptic.NeumannLocalize

@[expose] public section

/-!
# Smooth data in a placed normal chart

Smoothness means `ContDiff ℝ (⊤ : ℕ∞)`. For a general coordinate map the
coefficient results explicitly require smoothness of the map as well as
invertibility of its derivative. No regularity of the totalized inverse at
singular operators is asserted.
-/

noncomputable section

open Set Filter Metric InnerProductSpace MeasureTheory
open scoped Topology Gradient

namespace LiquidDrop

/-- Rigid placement preserves smoothness of the scaled normal coordinates. -/
theorem smooth_neumannLocalizeMap (c : C1BoundaryChart)
    (hψ : ContDiff ℝ (⊤ : ℕ∞) c.height) (a : EuclideanSpace ℝ (Fin 2)) (ρ : ℝ) :
    ContDiff ℝ (⊤ : ℕ∞) (neumannLocalizeMap c a ρ) := by
  have heq : (c.placement : AmbientSpace → AmbientSpace) =
      fun x => c.placement.linearIsometryEquiv x + c.placement 0 := by
    funext x
    simpa using c.placement.map_vadd (0 : AmbientSpace) x
  have hc : ContDiff ℝ (⊤ : ℕ∞) c.placement := by
    rw [heq]
    exact c.placement.linearIsometryEquiv.toContinuousLinearEquiv.contDiff.add contDiff_const
  exact hc.comp ((smooth_boundaryNormalChart hψ).comp
    (contDiff_const.add (contDiff_id.const_smul ρ)))

/-- The absolute Jacobian is smooth at every regular point of a smooth map. -/
theorem contDiffAt_neumannLocalizeJacobian
    {Θ : AmbientSpace → AmbientSpace} (hΘ : ContDiff ℝ (⊤ : ℕ∞) Θ)
    {y : AmbientSpace} (hy : (fderiv ℝ Θ y).IsInvertible) :
    ContDiffAt ℝ (⊤ : ℕ∞) (fun x => |(fderiv ℝ Θ x).det|) y := by
  exact (contDiffAt_abs (boundaryNormal_det_ne_zero hy)).comp y
    (boundaryNormal_contDiff_det.contDiffAt.comp y
      (hΘ.fderiv_right (by simp)).contDiffAt)

/-- The divergence coefficient is smooth at regular points of a smooth map. -/
theorem contDiffAt_neumannLocalizeCoefficient
    {Θ : AmbientSpace → AmbientSpace} (hΘ : ContDiff ℝ (⊤ : ℕ∞) Θ)
    {y : AmbientSpace} (hy : (fderiv ℝ Θ y).IsInvertible) :
    ContDiffAt ℝ (⊤ : ℕ∞) (neumannLocalizeCoefficient Θ) y := by
  have hD : ContDiff ℝ (⊤ : ℕ∞) (fderiv ℝ Θ) := hΘ.fderiv_right (by simp)
  have hI := hy.contDiffAt_map_inverse.comp y hD.contDiffAt
  have hA : ContDiff ℝ (⊤ : ℕ∞) (fun L : AmbientSpace →L[ℝ] AmbientSpace => L.adjoint) :=
    (ContinuousLinearMap.adjoint :
      (AmbientSpace →L[ℝ] AmbientSpace) ≃ₗᵢ[ℝ]
      (AmbientSpace →L[ℝ] AmbientSpace)).contDiff
  exact (contDiffAt_neumannLocalizeJacobian hΘ hy).smul
    (hI.clm_comp (hA.contDiffAt.comp y hI))

/-- Smoothness on any set where the smooth coordinate map is regular. -/
theorem contDiffOn_neumannLocalizeCoefficient
    {Θ : AmbientSpace → AmbientSpace} (hΘ : ContDiff ℝ (⊤ : ℕ∞) Θ)
    {U : Set AmbientSpace} (hreg : ∀ y ∈ U, (fderiv ℝ Θ y).IsInvertible) :
    ContDiffOn ℝ (⊤ : ℕ∞) (neumannLocalizeCoefficient Θ) U :=
  fun y hy => (contDiffAt_neumannLocalizeCoefficient hΘ (hreg y hy)).contDiffWithinAt

/-- In particular, the coefficient of the localization chart is smooth on
the full radius-two ball on which localization supplies regularity. -/
theorem smoothOn_neumannLocalizeCoefficient_ball
    (c : C1BoundaryChart) (hψ : ContDiff ℝ (⊤ : ℕ∞) c.height)
    (a : EuclideanSpace ℝ (Fin 2)) (ρ : ℝ)
    (hreg : ∀ y ∈ ball 0 2, (fderiv ℝ (neumannLocalizeMap c a ρ) y).IsInvertible) :
    ContDiffOn ℝ (⊤ : ℕ∞)
      (neumannLocalizeCoefficient (neumannLocalizeMap c a ρ)) (ball 0 2) :=
  contDiffOn_neumannLocalizeCoefficient (smooth_neumannLocalizeMap c hψ a ρ) hreg

/-- The exact quadratic form of the placed coefficient. -/
lemma neumannLocalizeCoefficient_quadratic (Θ : AmbientSpace → AmbientSpace)
    (y v : AmbientSpace) :
    inner ℝ (neumannLocalizeCoefficient Θ y v) v =
      |(fderiv ℝ Θ y).det| * ‖(fderiv ℝ Θ y).inverse.adjoint v‖ ^ 2 := by
  rw [real_inner_comm]
  simp only [neumannLocalizeCoefficient, smul_apply, ContinuousLinearMap.comp_apply,
    real_inner_smul_right]
  rw [← ContinuousLinearMap.adjoint_inner_left, real_inner_self_eq_norm_sq]

/-- Invertibility of the chart derivative gives strict positive definiteness. -/
theorem neumannLocalizeCoefficient_pos (Θ : AmbientSpace → AmbientSpace)
    {y : AmbientSpace} (hy : (fderiv ℝ Θ y).IsInvertible)
    {v : AmbientSpace} (hv : v ≠ 0) :
    0 < inner ℝ (neumannLocalizeCoefficient Θ y v) v := by
  rw [neumannLocalizeCoefficient_quadratic]
  apply mul_pos (abs_pos.mpr (boundaryNormal_det_ne_zero hy))
  apply sq_pos_of_pos
  apply norm_pos_iff.mpr
  exact fun h => hv ((boundaryNormal_adjoint_invertible hy.inverse).injective
    (h.trans (map_zero _).symm))

/-- Uniform ellipticity and operator bounds on compact sets of regular points. -/
theorem neumannLocalizeCoefficient_compact_bounds
    {Θ : AmbientSpace → AmbientSpace} (hΘ : ContDiff ℝ (⊤ : ℕ∞) Θ)
    {S : Set AmbientSpace} (hS : IsCompact S)
    (hreg : ∀ y ∈ S, (fderiv ℝ Θ y).IsInvertible) :
    ∃ lam > 0, ∃ cap > 0, ∀ y ∈ S,
      ‖neumannLocalizeCoefficient Θ y‖ ≤ cap ∧
      ∀ v : AmbientSpace,
        lam * ‖v‖ ^ 2 ≤ inner ℝ (neumannLocalizeCoefficient Θ y v) v := by
  have hA := (contDiffOn_neumannLocalizeCoefficient hΘ hreg).continuousOn
  have hQ : ContinuousOn (fun z : AmbientSpace × AmbientSpace =>
      inner ℝ (neumannLocalizeCoefficient Θ z.1 z.2) z.2) (S ×ˢ sphere 0 1) :=
    ((hA.comp continuous_fst.continuousOn (fun z hz => hz.1)).clm_apply
      continuous_snd.continuousOn).inner continuous_snd.continuousOn
  obtain ⟨lam, hlam, hlow⟩ := (hS.prod (isCompact_sphere 0 1)).exists_forall_le' hQ
    (show ∀ z ∈ S ×ˢ sphere (0 : AmbientSpace) 1,
      0 < inner ℝ (neumannLocalizeCoefficient Θ z.1 z.2) z.2 from by
      intro z hz
      apply neumannLocalizeCoefficient_pos Θ (hreg z.1 hz.1)
      intro he
      simpa [he] using hz.2)
  obtain ⟨cap, hcap, hupp⟩ := (hS.image_of_continuousOn hA).isBounded.exists_pos_norm_le
  refine ⟨lam, hlam, cap, hcap, fun y hy => ⟨hupp _ (mem_image_of_mem _ hy), ?_⟩⟩
  intro v
  by_cases hv : v = 0
  · simp [hv]
  let w := ‖v‖⁻¹ • v
  have hw : w ∈ sphere (0 : AmbientSpace) 1 := by
    rw [mem_sphere_zero_iff_norm]
    exact norm_smul_inv_norm hv
  have he : ‖v‖ ^ 2 * inner ℝ (neumannLocalizeCoefficient Θ y w) w =
      inner ℝ (neumannLocalizeCoefficient Θ y v) v := by
    dsimp only [w]
    rw [map_smul, real_inner_smul_left, real_inner_smul_right]
    field_simp
  calc
    lam * ‖v‖ ^ 2 = ‖v‖ ^ 2 * lam := mul_comm _ _
    _ ≤ ‖v‖ ^ 2 * inner ℝ (neumannLocalizeCoefficient Θ y w) w :=
      mul_le_mul_of_nonneg_left (hlow (y, w) ⟨hy, hw⟩) (sq_nonneg _)
    _ = _ := he

end LiquidDrop

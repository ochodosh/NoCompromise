module

public import NoCompromise.Elliptic.NeumannChartC1Smooth

@[expose] public section

/-!
# Finite regularity of normal coordinates and their coefficients
-/

noncomputable section

open Set Filter Metric InnerProductSpace MeasureTheory
open scoped Topology Gradient NNReal

namespace LiquidDrop

/-- A height of class C^(r+1) gives a local inverse of class C^r, for r ≥ 1. -/
theorem boundaryNormalChart_local_diffeomorphism_of_contDiff
    {ψ : EuclideanSpace ℝ (Fin 2) → ℝ} {r : WithTop ℕ∞} (hr : 1 ≤ r) (hψ : ContDiff ℝ (r + 1) ψ)
    (x : EuclideanSpace ℝ (Fin 2)) :
    ∃ e : OpenPartialHomeomorph (EuclideanSpace ℝ (Fin 3)) (EuclideanSpace ℝ (Fin 3)),
      (e : EuclideanSpace ℝ (Fin 3) → EuclideanSpace ℝ (Fin 3)) = boundaryNormalChart ψ ∧
      graphAppendN x 0 ∈ e.source ∧
      ContDiffAt ℝ r e.symm (graphMapN ψ x) := by
  have hψ2 : ContDiff ℝ 2 ψ := hψ.of_le (by
    convert add_le_add_right hr 1 using 1 <;> norm_num [add_comm])
  have hc := (contDiff_boundaryNormalChart hψ).contDiffAt (x := graphAppendN x 0)
  have hd : HasFDerivAt (boundaryNormalChart ψ)
      (boundaryNormalLinearEquiv (gradient ψ x) : EuclideanSpace ℝ (Fin 3) →L[ℝ]
        EuclideanSpace ℝ (Fin 3)) (graphAppendN x 0) :=
    hasFDerivAt_boundaryNormalChart_face hψ2 x
  have hn : r ≠ 0 := ne_of_gt (lt_of_lt_of_le zero_lt_one hr)
  refine ⟨hc.toOpenPartialHomeomorph _ hd hn, rfl,
    hc.mem_toOpenPartialHomeomorph_source hd hn, ?_⟩
  simpa only [ContDiffAt.localInverse, HasStrictFDerivAt.localInverse_def,
    ContDiffAt.toOpenPartialHomeomorph, boundaryNormalChart_face] using hc.to_localInverse hd hn

theorem isOpen_boundaryNormalChart_regular_c2
    {ψ : EuclideanSpace ℝ (Fin 2) → ℝ} (hψ : ContDiff ℝ 2 ψ) :
    IsOpen {x | (fderiv ℝ (boundaryNormalChart ψ) x).IsInvertible} := by
  have hD := (contDiff_boundaryNormalChart (r := 1) hψ).continuous_fderiv one_ne_zero
  have ho : IsOpen {t : ℝ | t ≠ 0} := isOpen_ne
  simp only [boundaryNormal_isInvertible_iff_det_ne_zero]
  convert! ho.preimage (ContinuousLinearMap.continuous_det.comp hD) using 1

/-- Restricting to regular points gives the inverse regularity on the whole target. -/
theorem boundaryNormalChart_local_diffeomorphism_on_of_contDiff
    {ψ : EuclideanSpace ℝ (Fin 2) → ℝ} {r : WithTop ℕ∞} (hr : 1 ≤ r) (hψ : ContDiff ℝ (r + 1) ψ)
    (x : EuclideanSpace ℝ (Fin 2)) :
    ∃ e : OpenPartialHomeomorph (EuclideanSpace ℝ (Fin 3)) (EuclideanSpace ℝ (Fin 3)),
      (e : EuclideanSpace ℝ (Fin 3) → EuclideanSpace ℝ (Fin 3)) = boundaryNormalChart ψ ∧
      graphAppendN x 0 ∈ e.source ∧
      ContDiffOn ℝ r e e.source ∧
      ContDiffOn ℝ r e.symm e.target ∧
      ∀ y ∈ e.source, (fderiv ℝ (boundaryNormalChart ψ) y).IsInvertible := by
  have hψ2 : ContDiff ℝ 2 ψ := hψ.of_le (by
    convert add_le_add_right hr 1 using 1 <;> norm_num [add_comm])
  have hn : r ≠ 0 := ne_of_gt (lt_of_lt_of_le zero_lt_one hr)
  obtain ⟨e₀, he₀, hx, _⟩ := boundaryNormalChart_local_diffeomorphism_of_contDiff hr hψ x
  let U := {y | (fderiv ℝ (boundaryNormalChart ψ) y).IsInvertible}
  let e := e₀.restrOpen U (isOpen_boundaryNormalChart_regular_c2 hψ2)
  have he : (e : EuclideanSpace ℝ (Fin 3) → EuclideanSpace ℝ (Fin 3)) =
      boundaryNormalChart ψ := he₀
  have hreg : ∀ y ∈ e.source, (fderiv ℝ (boundaryNormalChart ψ) y).IsInvertible :=
    fun y hy => hy.2
  refine ⟨e, he, ⟨hx, ?_⟩, ?_, ?_, hreg⟩
  · change (fderiv ℝ (boundaryNormalChart ψ) (graphAppendN x 0)).IsInvertible
    rw [fderiv_boundaryNormalChart_face_equiv hψ2]
    exact ContinuousLinearMap.isInvertible_equiv
  · rw [he]
    exact (contDiff_boundaryNormalChart hψ).contDiffOn
  · intro y hy
    obtain ⟨L, hL⟩ := hreg (e.symm y) (e.map_target hy)
    have hd : HasFDerivAt e (L : EuclideanSpace ℝ (Fin 3) →L[ℝ]
        EuclideanSpace ℝ (Fin 3)) (e.symm y) := by
      rw [he, hL]
      exact ((contDiff_boundaryNormalChart hψ).differentiable hn _).hasFDerivAt
    have hc : ContDiffAt ℝ r e (e.symm y) := by
      rw [he]
      exact (contDiff_boundaryNormalChart hψ).contDiffAt
    exact (e.contDiffAt_symm hy hd hc).contDiffWithinAt

theorem contDiff_neumannLocalizeMap_of_contDiff (c : C1BoundaryChart)
    {r : WithTop ℕ∞} (hψ : ContDiff ℝ (r + 1) c.height) (a : EuclideanSpace ℝ (Fin 2)) (ρ : ℝ) :
    ContDiff ℝ r (neumannLocalizeMap c a ρ) := by
  have heq : (c.placement : AmbientSpace → AmbientSpace) =
      fun x => c.placement.linearIsometryEquiv x + c.placement 0 := by
    funext x
    simpa using c.placement.map_vadd (0 : AmbientSpace) x
  have hc : ContDiff ℝ r c.placement := by
    rw [heq]
    exact c.placement.linearIsometryEquiv.toContinuousLinearEquiv.contDiff.add contDiff_const
  exact hc.comp ((contDiff_boundaryNormalChart hψ).comp
    (contDiff_const.add (contDiff_id.const_smul ρ)))

theorem contDiffAt_neumannLocalizeJacobian_of_contDiff
    {Θ : AmbientSpace → AmbientSpace} {r : ℕ∞} (hΘ : ContDiff ℝ (r + 1) Θ)
    {y : AmbientSpace} (hy : (fderiv ℝ Θ y).IsInvertible) :
    ContDiffAt ℝ r (fun x => |(fderiv ℝ Θ x).det|) y := by
  exact (contDiffAt_abs (boundaryNormal_det_ne_zero hy)).comp y
    (boundaryNormal_contDiff_det.contDiffAt.comp y
      (hΘ.fderiv_right le_rfl).contDiffAt)

theorem contDiffAt_neumannLocalizeCoefficient_of_contDiff
    {Θ : AmbientSpace → AmbientSpace} {r : ℕ∞} (hΘ : ContDiff ℝ (r + 1) Θ)
    {y : AmbientSpace} (hy : (fderiv ℝ Θ y).IsInvertible) :
    ContDiffAt ℝ r (neumannLocalizeCoefficient Θ) y := by
  have hD : ContDiff ℝ r (fderiv ℝ Θ) := hΘ.fderiv_right le_rfl
  have hI := hy.contDiffAt_map_inverse.comp y hD.contDiffAt
  have hA : ContDiff ℝ r (fun L : AmbientSpace →L[ℝ] AmbientSpace => L.adjoint) :=
    (ContinuousLinearMap.adjoint :
      (AmbientSpace →L[ℝ] AmbientSpace) ≃ₗᵢ[ℝ]
      (AmbientSpace →L[ℝ] AmbientSpace)).contDiff
  exact (contDiffAt_neumannLocalizeJacobian_of_contDiff hΘ hy).smul
    (hI.clm_comp (hA.contDiffAt.comp y hI))

theorem contDiffOn_neumannLocalizeCoefficient_of_contDiff
    {Θ : AmbientSpace → AmbientSpace} {r : ℕ∞} (hΘ : ContDiff ℝ (r + 1) Θ)
    {U : Set AmbientSpace} (hreg : ∀ y ∈ U, (fderiv ℝ Θ y).IsInvertible) :
    ContDiffOn ℝ r (neumannLocalizeCoefficient Θ) U :=
  fun y hy => (contDiffAt_neumannLocalizeCoefficient_of_contDiff hΘ (hreg y hy)).contDiffWithinAt

/-- Two derivatives of the height give a continuous coefficient; in general,
constructing the coefficient uses two derivatives of the height. -/
theorem contDiffAt_boundaryNormalCoefficient_of_contDiff
    {ψ : EuclideanSpace ℝ (Fin 2) → ℝ} {r : ℕ∞}
    (hψ : ContDiff ℝ ((r + 1) + 1) ψ) {y : AmbientSpace}
    (hy : (fderiv ℝ (boundaryNormalChart ψ) y).IsInvertible) :
    ContDiffAt ℝ r (boundaryNormalCoefficient ψ) y :=
  contDiffAt_neumannLocalizeCoefficient_of_contDiff
    (contDiff_boundaryNormalChart hψ) hy

theorem neumannLocalizeCoefficient_compact_bounds_c1
    {Θ : AmbientSpace → AmbientSpace} (hΘ : ContDiff ℝ 1 Θ)
    {S : Set AmbientSpace} (hS : IsCompact S)
    (hreg : ∀ y ∈ S, (fderiv ℝ Θ y).IsInvertible) :
    ∃ lam > 0, ∃ cap > 0, ∀ y ∈ S,
      ‖neumannLocalizeCoefficient Θ y‖ ≤ cap ∧
      ∀ v : AmbientSpace,
        lam * ‖v‖ ^ 2 ≤ inner ℝ (neumannLocalizeCoefficient Θ y v) v := by
  have hA := (contDiffOn_neumannLocalizeCoefficient_of_contDiff (r := 0) hΘ hreg).continuousOn
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

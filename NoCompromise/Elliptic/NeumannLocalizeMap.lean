module

public import NoCompromise.Elliptic.NeumannLocalizeBoundary
public import NoCompromise.Elliptic.NeumannLocalizeExtension
public import NoCompromise.Elliptic.BoundaryNormalChartChangeVariables
public import NoCompromise.Elliptic.BoundaryHolderDecayIntegrals
public import NoCompromise.BV.ExteriorGeometry

@[expose] public section

/-!
# A normal coordinate map on a fixed ball

Translation in the base and positive dilation put the normal chart on the
radius-two ball. The positive last coordinate points into the domain.
-/

noncomputable section

open Set Filter Metric InnerProductSpace MeasureTheory
open scoped Topology Gradient NNReal

namespace LiquidDrop

/-- Normal coordinates translated in the base, dilated, and rigidly placed. -/
def neumannLocalizeMap (c : C1BoundaryChart) (a : EuclideanSpace ℝ (Fin 2))
    (ρ : ℝ) (y : AmbientSpace) : AmbientSpace :=
  c.placement (boundaryNormalChart c.height (graphAppendN a 0 + ρ • y))

lemma contDiff_neumannLocalizeMap (c : C1BoundaryChart)
    (hψ : ContDiff ℝ (⊤ : ℕ∞) c.height) (a : EuclideanSpace ℝ (Fin 2)) (ρ : ℝ) :
    ContDiff ℝ 1 (neumannLocalizeMap c a ρ) := by
  apply (contDiff_rigidPlacement c.placement).comp
  apply ((smooth_boundaryNormalChart hψ).of_le (by simp : (1 : WithTop ℕ∞) ≤ ↑(⊤ : ℕ∞))).comp
  exact contDiff_const.add (contDiff_id.const_smul ρ)

lemma fderiv_neumannLocalizeMap (c : C1BoundaryChart)
    (hψ : ContDiff ℝ (⊤ : ℕ∞) c.height) (a : EuclideanSpace ℝ (Fin 2))
    (ρ : ℝ) (y : AmbientSpace) :
    fderiv ℝ (neumannLocalizeMap c a ρ) y =
      c.placement.linearIsometryEquiv.toContinuousLinearEquiv.toContinuousLinearMap.comp
        ((fderiv ℝ (boundaryNormalChart c.height) (graphAppendN a 0 + ρ • y)).comp
          (ρ • ContinuousLinearMap.id ℝ AmbientSpace)) := by
  have hs : HasFDerivAt (fun y : AmbientSpace => graphAppendN a 0 + ρ • y)
      (ρ • ContinuousLinearMap.id ℝ AmbientSpace) y :=
    ((hasFDerivAt_id y).const_smul ρ).const_add _
  exact ((hasFDerivAt_rigidPlacement c.placement _).comp y
    (((smooth_boundaryNormalChart hψ).differentiable (by simp) _).hasFDerivAt.comp y hs)).fderiv

lemma neumannLocalizeMap_regular (c : C1BoundaryChart)
    (hψ : ContDiff ℝ (⊤ : ℕ∞) c.height) (a : EuclideanSpace ℝ (Fin 2))
    {ρ : ℝ} (hρ : 0 < ρ) {y : AmbientSpace}
    (hy : (fderiv ℝ (boundaryNormalChart c.height) (graphAppendN a 0 + ρ • y)).IsInvertible) :
    (fderiv ℝ (neumannLocalizeMap c a ρ) y).IsInvertible := by
  rw [fderiv_neumannLocalizeMap c hψ]
  apply ContinuousLinearMap.isInvertible_equiv.comp
  apply hy.comp
  apply ContinuousLinearMap.IsInvertible.of_inverse
    (g := ρ⁻¹ • ContinuousLinearMap.id ℝ AmbientSpace)
  · ext v
    simp [hρ.ne']
  · ext v
    simp [hρ.ne']

/-- A boundary point has normal coordinates on the radius-two ball. In
particular the map is injective and regular throughout that ball, takes its
upper half into the domain, its lower half outside the closure, and its face
to the boundary. The image of the entire ball is open. -/
theorem C1BoundaryChart.IsChartFor.exists_neumannLocalizeMap
    {D : Set AmbientSpace} {c : C1BoundaryChart} (hc : c.IsChartFor D)
    (hψ : ContDiff ℝ (⊤ : ℕ∞) c.height) {p : AmbientSpace}
    (hp : p ∈ frontier D) (hpc : p ∈ c.region) :
    ∃ ρ > 0,
      let Θ := neumannLocalizeMap c (graphProjectionN 2 (c.placement.symm p)) ρ
      Θ 0 = p ∧ ContDiff ℝ 1 Θ ∧ InjOn Θ (ball 0 2) ∧
      (∀ y ∈ ball 0 2, (fderiv ℝ Θ y).IsInvertible) ∧
      Θ '' ball 0 2 ⊆ c.region ∧
      Θ '' boundaryHalfBall 2 ⊆ D ∧
      Disjoint (Θ '' (ball 0 2 ∩ {y | y (Fin.last 2) < 0})) (closure D) ∧
      Θ '' (ball 0 2 ∩ {y | y (Fin.last 2) = 0}) ⊆ frontier D ∧
      IsOpen (Θ '' ball 0 2) ∧
      ∃ (E : AmbientSpace ≃ₜ AmbientSpace) (C K : ℝ≥0),
        LipschitzWith C E ∧ LipschitzWith K E.symm ∧ EqOn Θ E (ball 0 2) := by
  let a := graphProjectionN 2 (c.placement.symm p)
  let b := graphAppendN a 0
  have hpa : c.placement (graphMapN c.height a) = p := by
    have hpg : p ∈ c.graphSurface :=
      (hc.frontier_inter_eq ▸ (show p ∈ frontier D ∩ c.region from ⟨hp, hpc⟩)).1
    obtain ⟨z, ⟨x, rfl⟩, rfl⟩ := hpg
    change c.placement (graphMapN c.height
      (graphProjectionN 2 (c.placement.symm (c.placement (graphMapN c.height x))))) = _
    rw [c.placement.symm_apply_apply]
    change c.placement (graphMapN c.height
      (graphProjectionN 2 (graphAppendN x (c.height x)))) = _
    rw [graphProjectionN_append]
  obtain ⟨e, he, hb, _, _, hreg⟩ :=
    boundaryNormalChart_local_diffeomorphism_on hψ a
  obtain ⟨E, C, K, U, hE, hEi, hU, hbU, hEq⟩ :=
    neumannLocalize_exists_bilipschitz_extension
      (((smooth_boundaryNormalChart hψ).of_le
        (by simp : (1 : WithTop ℕ∞) ≤ ↑(⊤ : ℕ∞))).contDiffAt) (hreg b hb)
  obtain ⟨δ, hδ, ε, hε, hsides⟩ := boundaryNormalChart_sides c.height_contDiff a
  let V := (e.source ∩ U) ∩
    (fun x => c.placement (boundaryNormalChart c.height x)) ⁻¹' c.region ∩
    (graphProjectionN 2) ⁻¹' ball a δ ∩
    (fun x : AmbientSpace => x (Fin.last 2)) ⁻¹' Ioo (-ε) ε
  have hV : IsOpen V :=
    (((e.open_source.inter hU).inter (c.isOpen_region.preimage
      (c.placement.continuous.comp (smooth_boundaryNormalChart hψ).continuous))).inter
      (isOpen_ball.preimage (graphProjectionN 2).continuous)).inter
        (isOpen_Ioo.preimage (EuclideanSpace.proj (Fin.last 2)).continuous)
  have hbV : b ∈ V := by
    refine ⟨⟨⟨⟨hb, hbU⟩, ?_⟩, ?_⟩, ?_⟩
    · change c.placement (boundaryNormalChart c.height (graphAppendN a 0)) ∈ c.region
      rwa [boundaryNormalChart_face, hpa]
    · change graphProjectionN 2 (graphAppendN a 0) ∈ ball a δ
      simpa only [graphProjectionN_append] using mem_ball_self hδ
    · change graphAppendN a 0 (Fin.last 2) ∈ Ioo (-ε) ε
      simpa only [graphAppendN_last] using
        (show (0 : ℝ) ∈ Ioo (-ε) ε from ⟨by linarith, hε⟩)
  obtain ⟨r, hr, hrV⟩ := Metric.mem_nhds_iff.mp (hV.mem_nhds hbV)
  let ρ := r / 3
  have hρ : 0 < ρ := div_pos hr (by norm_num)
  let S : AmbientSpace → AmbientSpace := fun y => b + ρ • y
  have hSV : MapsTo S (ball 0 2) V := by
    intro y hy
    apply hrV
    rw [mem_ball, dist_eq_norm, add_sub_cancel_left, norm_smul, Real.norm_of_nonneg hρ.le]
    have hy' : ‖y‖ < 2 := mem_ball_zero_iff.mp hy
    dsimp only [ρ]
    nlinarith
  have hSsource : S '' ball 0 2 ⊆ e.source := by
    rintro _ ⟨y, hy, rfl⟩
    exact (hSV hy).1.1.1.1
  have hSopen : IsOpen (S '' ball 0 2) :=
    ((isOpenMap_add_left b).comp (isOpenMap_smul₀ hρ.ne')) _ isOpen_ball
  have hSinj : Function.Injective S := by
    intro y z hyz
    exact (smul_right_injective _ hρ.ne') (add_left_cancel hyz)
  have hregion (y : AmbientSpace) (hy : y ∈ ball 0 2) :
      neumannLocalizeMap c a ρ y ∈ c.region := (hSV hy).1.1.2
  have hside (y : AmbientSpace) (hy : y ∈ ball 0 2) :=
    hsides (graphProjectionN 2 (S y)) (hSV hy).1.2
      (S y (Fin.last 2)) (hSV hy).2
  have hlast (y : AmbientSpace) : S y (Fin.last 2) = ρ * y (Fin.last 2) := by
    simp only [S, b, PiLp.add_apply, graphAppendN_last, PiLp.smul_apply,
      smul_eq_mul, zero_add]
  have hinside (y : AmbientSpace) (hy : y ∈ ball 0 2) :
      neumannLocalizeMap c a ρ y ∈ D ↔ 0 < y (Fin.last 2) := by
    rw [hc _ (hregion y hy)]
    change c.placement.symm (c.placement (boundaryNormalChart c.height (S y))) ∈
      smoothSubgraph c.height ↔ _
    rw [c.placement.symm_apply_apply]
    have h := (hside y hy).1
    rw [graphAppendN_projection, hlast, mul_pos_iff_of_pos_left hρ] at h
    exact h
  refine ⟨ρ, hρ, ?_⟩
  change neumannLocalizeMap c a ρ 0 = p ∧ _
  refine ⟨?_, contDiff_neumannLocalizeMap c hψ a ρ, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · simpa only [neumannLocalizeMap, smul_zero, add_zero, boundaryNormalChart_face] using hpa
  · intro y hy z hz heq
    apply hSinj
    apply e.injOn (hSV hy).1.1.1.1 (hSV hz).1.1.1.1
    rw [he]
    exact c.placement.injective heq
  · intro y hy
    exact neumannLocalizeMap_regular c hψ a hρ (hreg _ (hSV hy).1.1.1.1)
  · rintro _ ⟨y, hy, rfl⟩
    exact hregion y hy
  · rintro _ ⟨y, hy, rfl⟩
    exact (hinside y hy.1).mpr hy.2
  · rw [Set.disjoint_left]
    rintro _ ⟨y, hy, rfl⟩ hcl
    have hcl' : neumannLocalizeMap c a ρ y ∈ closure c.graphDomain :=
      (hc.closure_inter_eq ▸ (show neumannLocalizeMap c a ρ y ∈ closure D ∩ c.region
        from ⟨hcl, hregion y hy.1⟩)).1
    rw [c.mem_closure_graphDomain_iff] at hcl'
    change c.placement.symm (c.placement (boundaryNormalChart c.height (S y)))
      (Fin.last 2) ≤ c.height (graphProjectionN 2
        (c.placement.symm (c.placement (boundaryNormalChart c.height (S y))))) at hcl'
    simp only [c.placement.symm_apply_apply] at hcl'
    have h := (hside y hy.1).2
    rw [graphAppendN_projection, hlast] at h
    exact (not_lt_of_ge hcl') (h.mpr (mul_neg_of_pos_of_neg hρ hy.2))
  · rintro _ ⟨y, hy, rfl⟩
    have hzero : S y (Fin.last 2) = 0 := by rw [hlast, hy.2, mul_zero]
    have hface : boundaryNormalChart c.height (S y) =
        graphMapN c.height (graphProjectionN 2 (S y)) := by
      conv_lhs => rw [← graphAppendN_projection (S y), hzero]
      exact boundaryNormalChart_face _ _
    have hg : neumannLocalizeMap c a ρ y ∈ c.graphSurface :=
      ⟨boundaryNormalChart c.height (S y), ⟨graphProjectionN 2 (S y), hface.symm⟩, rfl⟩
    exact (hc.frontier_inter_eq.symm ▸
      (show neumannLocalizeMap c a ρ y ∈ c.graphSurface ∩ c.region from
        ⟨hg, hregion y hy.1⟩)).1
  · have ho := c.placement.toHomeomorph.isOpenMap _
      (e.isOpen_image_of_subset_source hSopen hSsource)
    change IsOpen (c.placement '' (e '' (S '' ball 0 2))) at ho
    rw [image_image, image_image, he] at ho
    exact ho
  · let T := neumannLocalizeDilation b hρ.ne'
    refine ⟨(T.trans E).trans c.placement.toHomeomorph, _, _,
      (c.placement.isometry.lipschitzWith.comp hE).comp
        (neumannLocalizeDilation_lipschitz b hρ.ne'),
      ((neumannLocalizeDilation_symm_lipschitz b hρ.ne').comp hEi).comp
        c.placement.symm.isometry.lipschitzWith, ?_⟩
    intro y hy
    exact congrArg c.placement (hEq (hSV hy).1.1.1.2)

end LiquidDrop

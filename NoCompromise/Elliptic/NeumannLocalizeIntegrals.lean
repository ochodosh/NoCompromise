module

public import NoCompromise.Elliptic.NeumannLocalizePullback
public import NoCompromise.Elliptic.FrozenDecayScaling
public import NoCompromise.Area.Graph

@[expose] public section

/-!
# Localization of volume and surface integrals
-/

noncomputable section

open Set Filter Metric InnerProductSpace MeasureTheory
open scoped Topology Gradient

namespace LiquidDrop

lemma neumannLocalize_mem_domain_iff
    {D : Set AmbientSpace} (hD : IsOpen D) {Θ : AmbientSpace → AmbientSpace}
    (hupper : Θ '' boundaryHalfBall 2 ⊆ D)
    (hlower : Disjoint (Θ '' (ball 0 2 ∩ {y | y (Fin.last 2) < 0})) (closure D))
    (hface : Θ '' (ball 0 2 ∩ {y | y (Fin.last 2) = 0}) ⊆ frontier D)
    {y : AmbientSpace} (hy : y ∈ ball 0 2) : Θ y ∈ D ↔ 0 < y (Fin.last 2) := by
  refine ⟨fun h => ?_, fun h => hupper ⟨y, ⟨hy, h⟩, rfl⟩⟩
  rcases lt_trichotomy (y (Fin.last 2)) 0 with hn | he | hp
  · exact False.elim ((Set.disjoint_left.mp hlower)
      (mem_image_of_mem _ ⟨hy, hn⟩) (subset_closure h))
  · have hf := hface (mem_image_of_mem _ ⟨hy, he⟩)
    rw [hD.frontier_eq] at hf
    exact False.elim (hf.2 h)
  · exact hp

lemma neumannLocalize_face_of_mem_frontier
    {D : Set AmbientSpace} (hD : IsOpen D) {Θ : AmbientSpace → AmbientSpace}
    (hupper : Θ '' boundaryHalfBall 2 ⊆ D)
    (hlower : Disjoint (Θ '' (ball 0 2 ∩ {y | y (Fin.last 2) < 0})) (closure D))
    {y : AmbientSpace} (hy : y ∈ ball 0 2) (hf : Θ y ∈ frontier D) :
    y (Fin.last 2) = 0 := by
  rcases lt_trichotomy (y (Fin.last 2)) 0 with hn | he | hp
  · exact False.elim ((Set.disjoint_left.mp hlower)
      (mem_image_of_mem _ ⟨hy, hn⟩) (frontier_subset_closure hf))
  · exact he
  · rw [hD.frontier_eq] at hf
    exact False.elim (hf.2 (hupper ⟨y, ⟨hy, hp⟩, rfl⟩))

/-- A supported volume integral may be restricted to the image of the upper
half ball. All integrals are totalized, so no integrability hypothesis is used. -/
lemma neumannLocalize_integral_domain
    {D : Set AmbientSpace} (hD : IsOpen D) {Θ : AmbientSpace → AmbientSpace}
    (E : AmbientSpace ≃ₜ AmbientSpace) (hEq : EqOn Θ E (ball 0 2))
    (hside : ∀ y ∈ ball 0 2, Θ y ∈ D ↔ 0 < y (Fin.last 2))
    {q : AmbientSpace → ℝ} (hq : tsupport q ⊆ Θ '' ball 0 1) :
    (∫ x in D, q x) = ∫ x in Θ '' boundaryHalfBall 1, q x := by
  classical
  have hball : ball (0 : AmbientSpace) 1 ⊆ ball 0 2 := ball_subset_ball (by norm_num)
  have himage : Θ '' boundaryHalfBall 1 = E '' boundaryHalfBall 1 :=
    Set.image_congr (fun y hy => hEq (hball hy.1))
  have hopen : IsOpen (Θ '' boundaryHalfBall 1) := by
    rw [himage]
    exact E.isOpenMap _ (isOpen_boundaryHalfBall 1)
  rw [← integral_indicator hD.measurableSet, ← integral_indicator hopen.measurableSet]
  apply integral_congr_ae
  filter_upwards with x
  change D.indicator q x = (Θ '' boundaryHalfBall 1).indicator q x
  by_cases hx : x ∈ tsupport q
  · have hmem : x ∈ D ↔ x ∈ Θ '' boundaryHalfBall 1 := by
      constructor
      · intro hd
        obtain ⟨y, hy, rfl⟩ := hq hx
        exact ⟨y, ⟨hy, (hside y (hball hy)).mp hd⟩, rfl⟩
      · rintro ⟨y, hy, rfl⟩
        exact (hside y (hball hy.1)).mpr hy.2
    simp only [indicator_apply, hmem]
  · simp [indicator_apply, image_eq_zero_of_notMem_tsupport hx]

lemma neumannLocalize_base_eq_append (y : EuclideanSpace ℝ (Fin 2)) :
    graphBaseEmbedding y = graphAppendN y 0 := by
  ext i
  fin_cases i <;> simp [graphAppendN, graphBaseN, graphBaseEmbedding]

lemma neumannLocalize_face (c : C1BoundaryChart) (a y : EuclideanSpace ℝ (Fin 2)) (ρ : ℝ) :
    neumannLocalizeMap c a ρ (graphBaseEmbedding y) =
      c.placement (graphMapN c.height (a + ρ • y)) := by
  have heq : graphAppendN a 0 + ρ • graphBaseEmbedding y = graphAppendN (a + ρ • y) 0 := by
    rw [neumannLocalize_base_eq_append]
    apply PiLp.ext
    intro i
    refine Fin.lastCases ?_ (fun j => ?_) i <;>
      simp only [PiLp.add_apply, PiLp.smul_apply, graphAppendN_last, graphAppendN_castSucc,
        smul_zero, add_zero]
  rw [neumannLocalizeMap, heq, boundaryNormalChart_face]

/-- The pushed test on the entire placed graph is its flat-face restriction,
including base points outside the chart support. -/
lemma neumannLocalize_graph_pushforward
    {D : Set AmbientSpace} {c : C1BoundaryChart} (hc : c.IsChartFor D)
    (a : EuclideanSpace ℝ (Fin 2)) {ρ : ℝ} (hρ : 0 < ρ)
    (E : AmbientSpace ≃ₜ AmbientSpace)
    (hEq : EqOn (neumannLocalizeMap c a ρ) E (ball 0 2))
    (hregion : neumannLocalizeMap c a ρ '' ball 0 2 ⊆ c.region)
    (hface : ∀ y ∈ ball 0 2, neumannLocalizeMap c a ρ y ∈ frontier D → y (Fin.last 2) = 0)
    {φ : AmbientSpace → ℝ} (hsφ : tsupport φ ⊆ ball 0 1) (t : EuclideanSpace ℝ (Fin 2)) :
    φ (E.symm (c.placement (graphMapN c.height (a + ρ • t)))) =
      φ (graphBaseEmbedding t) := by
  have hball : ball (0 : AmbientSpace) 1 ⊆ ball 0 2 := ball_subset_ball (by norm_num)
  by_cases ht : graphBaseEmbedding t ∈ ball 0 2
  · rw [← neumannLocalize_face c a t ρ, hEq ht, E.symm_apply_apply]
  · have hzero : φ (graphBaseEmbedding t) = 0 :=
      image_eq_zero_of_notMem_tsupport (fun h => ht (hball (hsφ h)))
    rw [hzero]
    by_contra hn
    let y := E.symm (c.placement (graphMapN c.height (a + ρ • t)))
    have hy : y ∈ ball 0 1 := hsφ (subset_tsupport φ hn)
    have hval : neumannLocalizeMap c a ρ y =
        c.placement (graphMapN c.height (a + ρ • t)) :=
      (hEq (hball hy)).trans (E.apply_symm_apply _)
    have hyfront : neumannLocalizeMap c a ρ y ∈ frontier D := by
      have hg : neumannLocalizeMap c a ρ y ∈ c.graphSurface := by
        rw [hval]
        exact ⟨_, ⟨a + ρ • t, rfl⟩, rfl⟩
      exact (hc.frontier_inter_eq.symm ▸
        (show neumannLocalizeMap c a ρ y ∈ c.graphSurface ∩ c.region from
          ⟨hg, hregion (mem_image_of_mem _ (hball hy))⟩)).1
    have hy0 := hface y (hball hy) hyfront
    have hybase : y = graphBaseEmbedding (graphProjectionN 2 y) := by
      rw [neumannLocalize_base_eq_append]
      simpa only [hy0] using (graphAppendN_projection y).symm
    have hbase : graphProjectionN 2 y = t := by
      rw [hybase, neumannLocalize_face] at hval
      have hg := c.placement.injective hval
      have hp := congrArg (graphProjectionN 2) hg
      change graphProjectionN 2 (graphAppendN (a + ρ • graphProjectionN 2 y)
        (c.height (a + ρ • graphProjectionN 2 y))) =
        graphProjectionN 2 (graphAppendN (a + ρ • t) (c.height (a + ρ • t))) at hp
      simp only [graphProjectionN_append] at hp
      exact (smul_right_injective _ hρ.ne') (add_left_cancel hp)
    exact ht (hybase.trans (congrArg graphBaseEmbedding hbase) ▸ hball hy)

/-- The surface integral in scaled normal coordinates, with its exact
two-dimensional area factor. -/
theorem neumannLocalize_boundary_integral
    {D : Set AmbientSpace} {c : C1BoundaryChart} (hc : c.IsChartFor D)
    (a : EuclideanSpace ℝ (Fin 2)) {ρ : ℝ} (hρ : 0 < ρ)
    (E : AmbientSpace ≃ₜ AmbientSpace)
    (hEq : EqOn (neumannLocalizeMap c a ρ) E (ball 0 2))
    (hregion : neumannLocalizeMap c a ρ '' ball 0 2 ⊆ c.region)
    (hface : ∀ y ∈ ball 0 2, neumannLocalizeMap c a ρ y ∈ frontier D → y (Fin.last 2) = 0)
    (h₀ : AmbientSpace → ℝ) {φ : AmbientSpace → ℝ} (hsφ : tsupport φ ⊆ ball 0 1) :
    (∫ x, h₀ x * φ (E.symm x) ∂(hausdorffMeasure2 3).restrict (frontier D)) =
      ∫ t in ball (0 : EuclideanSpace ℝ (Fin 2)) 1,
        h₀ (neumannLocalizeMap c a ρ (graphBaseEmbedding t)) * ρ ^ 2 *
          Real.sqrt (1 + ‖gradient c.height (a + ρ • t)‖ ^ 2) * φ (graphBaseEmbedding t) := by
  have hball : ball (0 : AmbientSpace) 1 ⊆ ball 0 2 := ball_subset_ball (by norm_num)
  have hs : tsupport (fun x => h₀ x * φ (E.symm x)) ⊆ c.region := by
    apply tsupport_mul_subset_right.trans
    intro x hx
    change x ∈ tsupport (φ ∘ E.symm) at hx
    rw [tsupport_comp_eq_preimage] at hx
    apply hregion
    exact ⟨E.symm x, hball (hsφ hx), (hEq (hball (hsφ hx))).trans (E.apply_symm_apply x)⟩
  rw [hc.boundary_integral_eq hs]
  let q : EuclideanSpace ℝ (Fin 2) → ℝ := fun t =>
    h₀ (c.placement (graphMapN c.height t)) * φ (E.symm (c.placement (graphMapN c.height t))) *
      Real.sqrt (1 + ‖gradient c.height t‖ ^ 2)
  change (∫ t, q t) = _
  calc
    _ = ρ ^ 2 * ∫ t, q (a + ρ • t) := by
      have hh := frozen_integral_comp_ballScaling q a hρ
      change (∫ t, q (a + ρ • t)) = (ρ ^ 2)⁻¹ * ∫ t, q t at hh
      rw [hh]
      field_simp [hρ.ne']
    _ = ∫ t : EuclideanSpace ℝ (Fin 2),
        h₀ (neumannLocalizeMap c a ρ (graphBaseEmbedding t)) * ρ ^ 2 *
          Real.sqrt (1 + ‖gradient c.height (a + ρ • t)‖ ^ 2) * φ (graphBaseEmbedding t) := by
      rw [← integral_const_mul]
      apply integral_congr_ae
      filter_upwards with t
      dsimp only [q]
      rw [neumannLocalize_graph_pushforward hc a hρ E hEq hregion hface hsφ t,
        neumannLocalize_face]
      ring
    _ = _ := by
      symm
      apply setIntegral_eq_integral_of_forall_compl_eq_zero
      intro t ht
      have hz : φ (graphBaseEmbedding t) = 0 := by
        apply image_eq_zero_of_notMem_tsupport
        intro h
        apply ht
        simpa only [mem_ball_zero_iff, norm_graphBaseEmbedding] using hsφ h
      rw [hz, mul_zero]

end LiquidDrop

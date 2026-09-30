module

public import NoCompromise.Regularity.RepresentativeBoundary
public import NoCompromise.Regularity.SlabGeometry
public import NoCompromise.DeGiorgi.SmoothGraph

@[expose] public section

/-!
# Phase identification for a local minimal graph

These are preparatory results for the weak minimal-surface equation. The two open
regions separated by a continuous graph in a cylinder are connected. For a
quasiminimizer whose density-one frontier is this graph, the regions have opposite
pure-density phases. No orientation of the graph is assumed.

`minimal_graph_ae_subgraph_or_epigraph` is the geometric phase-identification
step. `minimal_graph_weak_integral_localization` supplies a global C¹ height
without changing the desired weak integral. The weak minimal-surface equation
itself is not proved in this file: the localized first-variation and surface
measure/normal identification still have to be connected to that integral.
-/

noncomputable section
open MeasureTheory Set Filter Metric
open scoped Topology
namespace LiquidDrop

/-- A band between two continuous heights over a preconnected base is preconnected. -/
lemma isPreconnected_graph_band
    {U : Set (EuclideanSpace ℝ (Fin 2))} (hU : IsPreconnected U)
    {f g : EuclideanSpace ℝ (Fin 2) → ℝ}
    (hf : ContinuousOn f U) (hg : ContinuousOn g U)
    (hfg : ∀ y ∈ U, f y < g y) :
    IsPreconnected {z : AmbientSpace | graphProjectionN 2 z ∈ U ∧
      f (graphProjectionN 2 z) < z 2 ∧ z 2 < g (graphProjectionN 2 z)} := by
  let F : EuclideanSpace ℝ (Fin 2) × ℝ → AmbientSpace :=
    fun p => graphAppendN p.1 (f p.1 + (g p.1 - f p.1) * p.2)
  have hc : ContinuousOn F (U ×ˢ Ioo (0 : ℝ) 1) := by
    have hf' : ContinuousOn (fun p : EuclideanSpace ℝ (Fin 2) × ℝ => f p.1)
        (U ×ˢ Ioo (0 : ℝ) 1) := hf.comp continuousOn_fst (fun _ hp => hp.1)
    have hg' : ContinuousOn (fun p : EuclideanSpace ℝ (Fin 2) × ℝ => g p.1)
        (U ×ˢ Ioo (0 : ℝ) 1) := hg.comp continuousOn_fst (fun _ hp => hp.1)
    have ha : Continuous (fun p : EuclideanSpace ℝ (Fin 2) × ℝ =>
        graphAppendN p.1 p.2) := by
      unfold graphAppendN
      fun_prop
    exact ha.continuousOn.comp
      (continuousOn_fst.prodMk (hf'.add ((hg'.sub hf').mul continuousOn_snd)))
      (fun _ _ => mem_univ _)
  have he : F '' (U ×ˢ Ioo (0 : ℝ) 1) =
      {z : AmbientSpace | graphProjectionN 2 z ∈ U ∧
        f (graphProjectionN 2 z) < z 2 ∧ z 2 < g (graphProjectionN 2 z)} := by
    ext z
    constructor
    · rintro ⟨⟨y, t⟩, ⟨hy, ht⟩, rfl⟩
      change graphProjectionN 2 (graphAppendN y _) ∈ U ∧ _
      simp only [graphProjectionN_append, graphAppendN_height_three, F]
      have hd := hfg y hy
      exact ⟨hy, by nlinarith [mul_pos (sub_pos.mpr hd) ht.1],
        by nlinarith [mul_pos (sub_pos.mpr hd) (sub_pos.mpr ht.2)]⟩
    · rintro ⟨hz, hl, hu⟩
      have hd : 0 < g (graphProjectionN 2 z) - f (graphProjectionN 2 z) :=
        sub_pos.mpr (hfg _ hz)
      refine ⟨(graphProjectionN 2 z,
        (z 2 - f (graphProjectionN 2 z)) /
          (g (graphProjectionN 2 z) - f (graphProjectionN 2 z))),
        ⟨hz, div_pos (sub_pos.mpr hl) hd, (div_lt_one hd).mpr (by linarith)⟩, ?_⟩
      dsimp [F]
      rw [mul_div_cancel₀ _ (ne_of_gt hd)]
      rw [show f (graphProjectionN 2 z) + (z 2 - f (graphProjectionN 2 z)) = z 2 by ring]
      exact graphAppendN_projection z
  rw [← he]
  exact (hU.prod isPreconnected_Ioo).image F hc

/-- The lower component is preconnected with only local continuity of the height. -/
lemma isPreconnected_standardCylinder_subgraph {ρ : ℝ} (hρ : 0 < ρ)
    {f : EuclideanSpace ℝ (Fin 2) → ℝ}
    (hf : ∀ y ∈ ball (0 : EuclideanSpace ℝ (Fin 2)) ρ, |f y| < ρ / 2)
    (hc : ContinuousOn f (ball (0 : EuclideanSpace ℝ (Fin 2)) ρ)) :
    IsPreconnected (standardCylinder ρ ∩ smoothSubgraph f) := by
  have h := isPreconnected_graph_band isPreconnected_ball
    (f := fun _ => -ρ) continuousOn_const hc
    (fun y hy => by have := (abs_lt.mp (hf y hy)).1; linarith)
  convert h using 1
  ext z
  simp only [mem_inter_iff, standardCylinder, smoothSubgraph, mem_ofPred_eq,
    mem_ball, dist_zero_right, abs_lt]
  have hb : ‖graphProjectionN 2 z‖ < ρ → f (graphProjectionN 2 z) < ρ := by
    intro hz
    have := (abs_lt.mp (hf _ (by simpa using hz))).2
    linarith
  change (‖graphProjectionN 2 z‖ < ρ ∧ -ρ < z 2 ∧ z 2 < ρ) ∧
      z 2 < f (graphProjectionN 2 z) ↔ _
  constructor
  · rintro ⟨⟨hz, hl, _⟩, hu⟩; exact ⟨hz, hl, hu⟩
  · rintro ⟨hz, hl, hu⟩; exact ⟨⟨hz, hl, hu.trans (hb hz)⟩, hu⟩

/-- The upper component is preconnected with only local continuity of the height. -/
lemma isPreconnected_standardCylinder_epigraph {ρ : ℝ} (hρ : 0 < ρ)
    {f : EuclideanSpace ℝ (Fin 2) → ℝ}
    (hf : ∀ y ∈ ball (0 : EuclideanSpace ℝ (Fin 2)) ρ, |f y| < ρ / 2)
    (hc : ContinuousOn f (ball (0 : EuclideanSpace ℝ (Fin 2)) ρ)) :
    IsPreconnected (standardCylinder ρ ∩ smoothEpigraph f) := by
  have h := isPreconnected_graph_band isPreconnected_ball hc
    (g := fun _ => ρ) continuousOn_const
    (fun y hy => by have := (abs_lt.mp (hf y hy)).2; linarith)
  convert h using 1
  ext z
  simp only [mem_inter_iff, standardCylinder, smoothEpigraph, mem_ofPred_eq,
    mem_ball, dist_zero_right, abs_lt]
  have hb : ‖graphProjectionN 2 z‖ < ρ → -ρ < f (graphProjectionN 2 z) := by
    intro hz
    have := (abs_lt.mp (hf _ (by simpa using hz))).1
    linarith
  change (‖graphProjectionN 2 z‖ < ρ ∧ -ρ < z 2 ∧ z 2 < ρ) ∧
      f (graphProjectionN 2 z) < z 2 ↔ _
  constructor
  · rintro ⟨⟨hz, _, hu⟩, hl⟩; exact ⟨hz, hl, hu⟩
  · rintro ⟨hz, hl, hu⟩; exact ⟨⟨hz, (hb hz).trans hl, hu⟩, hl⟩

/-- In the cylinder, the frontier condition is exactly equality to the graph height. -/
lemma mem_frontier_iff_height_of_graph {E : Set AmbientSpace} {ρ : ℝ}
    {f : EuclideanSpace ℝ (Fin 2) → ℝ}
    (hgraph : frontier (densityOne E) ∩ standardCylinder ρ =
      (fun y => graphAppendN y (f y)) '' ball (0 : EuclideanSpace ℝ (Fin 2)) ρ)
    {z : AmbientSpace} (hz : z ∈ standardCylinder ρ) :
    z ∈ frontier (densityOne E) ↔ z 2 = f (graphProjectionN 2 z) := by
  constructor
  · intro he
    have hm : z ∈ (fun y => graphAppendN y (f y)) '' ball 0 ρ := by
      rw [← hgraph]
      exact ⟨he, hz⟩
    obtain ⟨y, _, rfl⟩ := hm
    simp only [graphProjectionN_append, graphAppendN_height_three]
  · intro he
    have hm : z ∈ frontier (densityOne E) ∩ standardCylinder ρ := by
      rw [hgraph]
      refine ⟨graphProjectionN 2 z, ?_, ?_⟩
      · simpa only [mem_ball, dist_zero_right] using hz.1
      · change graphAppendN (graphProjectionN 2 z) (f (graphProjectionN 2 z)) = z
        rw [← he]
        exact graphAppendN_projection z
    exact hm.1

/-- A preconnected set avoiding the essential boundary lies in one pure-density phase. -/
lemma IsOmegaMinimal.pure_phase_of_isPreconnected {E S : Set AmbientSpace} {ω : ℝ}
    (hE : IsOmegaMinimal E ω) (hS : IsPreconnected S)
    (hdisj : Disjoint S (essentialBoundary E)) :
    S ⊆ densityZero E ∨ S ⊆ densityOne E := by
  apply hS.subset_or_subset hE.isOpen_densityZero hE.isOpen_densityOne
    (disjoint_densityZero_densityOne E)
  intro z hz
  by_contra hn
  exact disjoint_left.mp hdisj hz hn

/-- The two sides of a local boundary graph have opposite pure-density phases.
This proves the phase-identification step without choosing an orientation. -/
theorem minimal_graph_opposite_phases {E : Set AmbientSpace} {ω : ℝ}
    (hE : IsOmegaMinimal E ω) {ρ : ℝ} (hρ : 0 < ρ)
    {f : EuclideanSpace ℝ (Fin 2) → ℝ}
    (hgraph : frontier (densityOne E) ∩ standardCylinder ρ =
      (fun y => graphAppendN y (f y)) '' ball (0 : EuclideanSpace ℝ (Fin 2)) ρ)
    (hf : ∀ y ∈ ball (0 : EuclideanSpace ℝ (Fin 2)) ρ, |f y| < ρ / 2)
    (hc : ContinuousOn f (ball (0 : EuclideanSpace ℝ (Fin 2)) ρ)) :
    ((standardCylinder ρ ∩ smoothSubgraph f ⊆ densityOne E) ∧
      (standardCylinder ρ ∩ smoothEpigraph f ⊆ densityZero E)) ∨
    ((standardCylinder ρ ∩ smoothSubgraph f ⊆ densityZero E) ∧
      (standardCylinder ρ ∩ smoothEpigraph f ⊆ densityOne E)) := by
  have hl := hE.pure_phase_of_isPreconnected
    (isPreconnected_standardCylinder_subgraph hρ hf hc)
    (show Disjoint (standardCylinder ρ ∩ smoothSubgraph f) (essentialBoundary E) from by
      apply disjoint_left.mpr
      intro z hz he
      rw [← hE.frontier_densityOne] at he
      have hh := (mem_frontier_iff_height_of_graph hgraph hz.1).mp he
      exact (ne_of_lt hz.2) hh)
  have hu := hE.pure_phase_of_isPreconnected
    (isPreconnected_standardCylinder_epigraph hρ hf hc)
    (show Disjoint (standardCylinder ρ ∩ smoothEpigraph f) (essentialBoundary E) from by
      apply disjoint_left.mpr
      intro z hz he
      rw [← hE.frontier_densityOne] at he
      have hh := (mem_frontier_iff_height_of_graph hgraph hz.1).mp he
      exact (ne_of_gt hz.2) hh)
  have hp : graphAppendN (0 : EuclideanSpace ℝ (Fin 2)) (f 0) ∈
      frontier (densityOne E) ∩ standardCylinder ρ := by
    rw [hgraph]
    exact ⟨0, mem_ball_self hρ, rfl⟩
  have hp0 : graphAppendN (0 : EuclideanSpace ℝ (Fin 2)) (f 0) ∈
      frontier (densityZero E) := by
    rw [← densityOne_compl hE.nullMeasurable, hE.compl.frontier_densityOne,
      essentialBoundary_compl hE.nullMeasurable, ← hE.frontier_densityOne]
    exact hp.1
  obtain ⟨a, haC, ha1⟩ := mem_closure_iff.mp (frontier_subset_closure hp.1)
    _ (isOpen_standardCylinder ρ) hp.2
  obtain ⟨b, hbC, hb0⟩ := mem_closure_iff.mp (frontier_subset_closure hp0)
    _ (isOpen_standardCylinder ρ) hp.2
  have hcover : ∀ z ∈ standardCylinder ρ, z ∈ densityZero E ∪ densityOne E →
      z ∈ standardCylinder ρ ∩ smoothSubgraph f ∪
        standardCylinder ρ ∩ smoothEpigraph f := by
    intro z hz he
    rcases lt_trichotomy (z 2) (f (graphProjectionN 2 z)) with hh | hh | hh
    · exact Or.inl ⟨hz, hh⟩
    · have hess : z ∈ essentialBoundary E := by
        rw [← hE.frontier_densityOne]
        exact (mem_frontier_iff_height_of_graph hgraph hz).mpr hh
      exact False.elim (hess he)
    · exact Or.inr ⟨hz, hh⟩
  rcases hl with hl | hl <;> rcases hu with hu | hu
  · have ha0 : a ∈ densityZero E :=
      (hcover a haC (Or.inr ha1)).elim (fun hz => hl hz) (fun hz => hu hz)
    exact False.elim (disjoint_left.mp (disjoint_densityZero_densityOne E) ha0 ha1)
  · exact Or.inr ⟨hl, hu⟩
  · exact Or.inl ⟨hl, hu⟩
  · have hb1 : b ∈ densityOne E :=
      (hcover b hbC (Or.inl hb0)).elim (fun hz => hl hz) (fun hz => hu hz)
    exact False.elim (disjoint_left.mp (disjoint_densityZero_densityOne E) hb0 hb1)

/-- Exact identification of the open density-one representative inside the cylinder. -/
theorem minimal_graph_densityOne_dichotomy {E : Set AmbientSpace} {ω : ℝ}
    (hE : IsOmegaMinimal E ω) {ρ : ℝ} (hρ : 0 < ρ)
    {f : EuclideanSpace ℝ (Fin 2) → ℝ}
    (hgraph : frontier (densityOne E) ∩ standardCylinder ρ =
      (fun y => graphAppendN y (f y)) '' ball (0 : EuclideanSpace ℝ (Fin 2)) ρ)
    (hf : ∀ y ∈ ball (0 : EuclideanSpace ℝ (Fin 2)) ρ, |f y| < ρ / 2)
    (hc : ContinuousOn f (ball (0 : EuclideanSpace ℝ (Fin 2)) ρ)) :
    densityOne E ∩ standardCylinder ρ = standardCylinder ρ ∩ smoothSubgraph f ∨
      densityOne E ∩ standardCylinder ρ = standardCylinder ρ ∩ smoothEpigraph f := by
  have hsplit : ∀ z ∈ standardCylinder ρ, z ∈ densityOne E →
      z ∈ standardCylinder ρ ∩ smoothSubgraph f ∪
        standardCylinder ρ ∩ smoothEpigraph f := by
    intro z hz he
    rcases lt_trichotomy (z 2) (f (graphProjectionN 2 z)) with hh | hh | hh
    · exact Or.inl ⟨hz, hh⟩
    · have hess : z ∈ essentialBoundary E := by
        rw [← hE.frontier_densityOne]
        exact (mem_frontier_iff_height_of_graph hgraph hz).mpr hh
      exact False.elim (hess (Or.inr he))
    · exact Or.inr ⟨hz, hh⟩
  rcases minimal_graph_opposite_phases hE hρ hgraph hf hc with ⟨hl, hu⟩ | ⟨hl, hu⟩
  · left
    ext z
    constructor
    · rintro ⟨he, hz⟩
      rcases hsplit z hz he with hs | hs
      · exact hs
      · exact False.elim (disjoint_left.mp (disjoint_densityZero_densityOne E) (hu hs) he)
    · intro hz
      exact ⟨hl hz, hz.1⟩
  · right
    ext z
    constructor
    · rintro ⟨he, hz⟩
      rcases hsplit z hz he with hs | hs
      · exact False.elim (disjoint_left.mp (disjoint_densityZero_densityOne E) (hl hs) he)
      · exact hs
    · intro hz
      exact ⟨hu hz, hz.1⟩

/-- A quasiminimizer with this local graph boundary agrees almost everywhere with
either the subgraph or the epigraph, throughout the cylinder. -/
theorem minimal_graph_ae_subgraph_or_epigraph {E : Set AmbientSpace} {ω : ℝ}
    (hE : IsOmegaMinimal E ω) {ρ : ℝ} (hρ : 0 < ρ)
    {f : EuclideanSpace ℝ (Fin 2) → ℝ}
    (hgraph : frontier (densityOne E) ∩ standardCylinder ρ =
      (fun y => graphAppendN y (f y)) '' ball (0 : EuclideanSpace ℝ (Fin 2)) ρ)
    (hf : ∀ y ∈ ball (0 : EuclideanSpace ℝ (Fin 2)) ρ, |f y| < ρ / 2)
    (hc : ContinuousOn f (ball (0 : EuclideanSpace ℝ (Fin 2)) ρ)) :
    E =ᵐ[volume.restrict (standardCylinder ρ)] smoothSubgraph f ∨
      E =ᵐ[volume.restrict (standardCylinder ρ)] smoothEpigraph f := by
  have ha : ∀ S : Set AmbientSpace,
      densityOne E ∩ standardCylinder ρ = standardCylinder ρ ∩ S →
      E =ᵐ[volume.restrict (standardCylinder ρ)] S := by
    intro S hs
    filter_upwards [ae_restrict_of_ae (densityOne_ae_eq (by norm_num : 0 < 3)
      hE.nullMeasurable), ae_restrict_mem (isOpen_standardCylinder ρ).measurableSet]
      with z hz hzC
    have hh := congrArg (fun A : Set AmbientSpace => z ∈ A) hs
    simp only [mem_inter_iff, hzC, and_true, true_and] at hh
    exact hz.symm.trans hh
  exact (minimal_graph_densityOne_dichotomy hE hρ hgraph hf hc).imp (ha _) (ha _)

/-- The exact weak graph integrand is unchanged by a global C¹ replacement near
the support of the test. This isolates the local-to-global regularity issue. -/
lemma minimal_graph_weak_integral_localization {ρ : ℝ}
    {f : EuclideanSpace ℝ (Fin 2) → ℝ}
    (hC1 : ContDiffOn ℝ 1 f (ball (0 : EuclideanSpace ℝ (Fin 2)) ρ))
    {φ : EuclideanSpace ℝ (Fin 2) → ℝ} (hcφ : HasCompactSupport φ)
    (hsφ : tsupport φ ⊆ ball (0 : EuclideanSpace ℝ (Fin 2)) ρ) :
    ∃ g : EuclideanSpace ℝ (Fin 2) → ℝ, ContDiff ℝ 1 g ∧
      (∀ y ∈ tsupport φ, g =ᶠ[𝓝 y] f) ∧
      (∫ y, inner ℝ (gradient f y) (gradient φ y) /
        Real.sqrt (1 + ‖gradient f y‖ ^ 2)) =
      ∫ y, inner ℝ (gradient g y) (gradient φ y) /
        Real.sqrt (1 + ‖gradient g y‖ ^ 2) := by
  obtain ⟨g, hg, he⟩ := exists_contDiff_height_eq_near_compact isOpen_ball hcφ hsφ hC1
  refine ⟨g, hg, he, ?_⟩
  apply integral_congr_ae
  filter_upwards with y
  by_cases hy : y ∈ tsupport φ
  · rw [(he y hy).gradient_eq]
  · rw [gradient_eq_zero_of_notMem_tsupport hy, inner_zero_right, inner_zero_right,
      zero_div, zero_div]

end LiquidDrop

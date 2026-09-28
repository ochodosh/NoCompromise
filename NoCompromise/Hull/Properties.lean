import NoCompromise.Hull.Defs
import NoCompromise.Sobolev.C1Domain
import NoCompromise.Stationary.Defs
import NoCompromise.BV.GluingLocalTraces

/-! # Properties of the filled hull (blueprint `lem:hull-properties`) -/

noncomputable section
open Set Metric Topology
namespace LiquidDrop

lemma hull_isPreconnected_compl_ball (R : ℝ) :
    IsPreconnected ((ball (0 : AmbientSpace) R)ᶜ) := by
  by_cases hR : R ≤ 0
  · simpa [ball_eq_empty.mpr hR] using
      (isPreconnected_univ : IsPreconnected (univ : Set AmbientSpace))
  have hR : 0 < R := lt_of_not_ge hR
  have hrank : 1 < Module.rank ℝ AmbientSpace := by
    rw [← Module.finrank_eq_rank]
    simp [AmbientSpace]
  have hs := (isConnected_sphere hrank (0 : AmbientSpace) (by norm_num : (0 : ℝ) ≤ 1)).2
  have hp := (isPreconnected_Ici (a := R)).prod hs
  have himage : (fun q : ℝ × AmbientSpace => q.1 • q.2) ''
      (Ici R ×ˢ sphere (0 : AmbientSpace) 1) = (ball (0 : AmbientSpace) R)ᶜ := by
    ext x
    constructor
    · rintro ⟨⟨t, z⟩, ⟨ht, hz⟩, rfl⟩
      have hz : ‖z‖ = 1 := by simpa using hz
      simpa [mem_ball, dist_zero_right, norm_smul, hz,
        Real.norm_eq_abs, abs_of_nonneg (hR.le.trans ht)] using ht
    · intro hx
      have hx : R ≤ ‖x‖ := by simpa using hx
      have hn : 0 < ‖x‖ := hR.trans_le hx
      refine ⟨(‖x‖, ‖x‖⁻¹ • x), ⟨hx, ?_⟩, ?_⟩
      · simp [norm_smul, hn.ne']
      · simp [smul_smul, hn.ne']
  rw [← himage]
  exact hp.image _ (continuous_fst.smul continuous_snd).continuousOn

lemma hull_not_isBounded_compl_ball (R : ℝ) :
    ¬ Bornology.IsBounded ((ball (0 : AmbientSpace) R)ᶜ) := by
  intro h
  obtain ⟨M, hM⟩ := isBounded_iff_forall_norm_le.mp h
  obtain ⟨x, hx⟩ := NormedSpace.exists_lt_norm ℝ AmbientSpace (max R M)
  exact (not_lt_of_ge (hM x (by simpa using (le_max_left R M).trans hx.le)))
    ((le_max_right R M).trans_lt hx)

lemma hullExterior_subset_compl_closure (Ω : Set AmbientSpace) :
    hullExterior Ω ⊆ (closure Ω)ᶜ := by
  intro x hx
  by_contra hn
  exact hx (by rw [connectedComponentIn_eq_empty hn]; exact Bornology.isBounded_empty)

lemma hullExterior_component_subset {Ω : Set AmbientSpace} {x : AmbientSpace}
    (hx : x ∈ hullExterior Ω) : connectedComponentIn (closure Ω)ᶜ x ⊆ hullExterior Ω := by
  intro y hy
  change ¬ Bornology.IsBounded _
  rw [← connectedComponentIn_eq hy]
  exact hx

lemma hullExterior_isOpen (Ω : Set AmbientSpace) : IsOpen (hullExterior Ω) := by
  apply isOpen_iff_forall_mem_open.mpr
  intro x hx
  exact ⟨connectedComponentIn (closure Ω)ᶜ x, hullExterior_component_subset hx,
    isClosed_closure.isOpen_compl.connectedComponentIn,
    mem_connectedComponentIn (hullExterior_subset_compl_closure Ω hx)⟩

lemma hullExterior_eq_connectedComponentIn {Ω : Set AmbientSpace}
    (_hb : Bornology.IsBounded Ω) {R : ℝ} (hR : closure Ω ⊆ ball 0 R)
    {x : AmbientSpace} (hx : R ≤ ‖x‖) :
    hullExterior Ω = connectedComponentIn (closure Ω)ᶜ x := by
  have hsub : (ball (0 : AmbientSpace) R)ᶜ ⊆ (closure Ω)ᶜ := compl_subset_compl.mpr hR
  have hxout : x ∈ (ball (0 : AmbientSpace) R)ᶜ := by simpa using hx
  have hlarge := (hull_isPreconnected_compl_ball R).subset_connectedComponentIn hxout hsub
  have hxu : x ∈ hullExterior Ω := fun h => hull_not_isBounded_compl_ball R (h.subset hlarge)
  apply Subset.antisymm
  · intro y hy
    have hnot : ¬ connectedComponentIn (closure Ω)ᶜ y ⊆ ball 0 R :=
      fun h => hy (isBounded_ball.subset h)
    obtain ⟨z, hz, hzout⟩ := not_subset.mp hnot
    have hzx : z ∈ connectedComponentIn (closure Ω)ᶜ x := hlarge hzout
    rw [connectedComponentIn_eq hzx, ← connectedComponentIn_eq hz]
    exact mem_connectedComponentIn (hullExterior_subset_compl_closure Ω hy)
  · exact hullExterior_component_subset hxu

lemma filledHull_subset_ball {Ω : Set AmbientSpace} {R : ℝ}
    (hR : closure Ω ⊆ ball 0 R) : filledHull Ω ⊆ ball 0 R := by
  intro x hx
  by_contra hn
  have hb : Bornology.IsBounded Ω := isBounded_ball.subset (subset_closure.trans hR)
  have heq := hullExterior_eq_connectedComponentIn hb hR (x := x) (by simpa using hn)
  exact hx (heq ▸ mem_connectedComponentIn ((compl_subset_compl.mpr hR) hn))

lemma filledHull_isClosed (Ω : Set AmbientSpace) : IsClosed (filledHull Ω) :=
  (hullExterior_isOpen Ω).isClosed_compl

lemma filledHull_isCompact {Ω : Set AmbientSpace} (hb : Bornology.IsBounded Ω) :
    IsCompact (filledHull Ω) := by
  obtain ⟨R, hR⟩ := hb.closure.subset_ball (0 : AmbientSpace)
  exact isCompact_iff_isClosed_bounded.mpr ⟨filledHull_isClosed Ω,
    isBounded_ball.subset (filledHull_subset_ball hR)⟩

lemma filledHull_closure_subset (Ω : Set AmbientSpace) : closure Ω ⊆ filledHull Ω := by
  intro x hx hxu
  exact hullExterior_subset_compl_closure Ω hxu hx

lemma hullExterior_isConnected {Ω : Set AmbientSpace} (hb : Bornology.IsBounded Ω) :
    IsConnected (hullExterior Ω) := by
  obtain ⟨R, hR⟩ := hb.closure.subset_ball (0 : AmbientSpace)
  obtain ⟨x, hx⟩ := NormedSpace.exists_lt_norm ℝ AmbientSpace R
  rw [hullExterior_eq_connectedComponentIn hb hR hx.le]
  exact isConnected_connectedComponentIn_iff.mpr
    (fun h => (not_lt_of_ge hx.le) (by simpa using hR h))

lemma filledHull_isConnected_compl {Ω : Set AmbientSpace} (hb : Bornology.IsBounded Ω) :
    IsConnected (filledHull Ω)ᶜ := by
  simpa [filledHull] using hullExterior_isConnected hb

lemma filledHull_component_subset {Ω : Set AmbientSpace} {x : AmbientSpace}
    (hx : x ∈ filledHull Ω) : connectedComponentIn (closure Ω)ᶜ x ⊆ filledHull Ω := by
  intro y hy
  change ¬ ¬ Bornology.IsBounded _ at hx ⊢
  rwa [← connectedComponentIn_eq hy]

lemma filledHull_component_subset_interior {Ω : Set AmbientSpace} {x : AmbientSpace}
    (hx : x ∈ filledHull Ω) :
    connectedComponentIn (closure Ω)ᶜ x ⊆ interior (filledHull Ω) :=
  interior_maximal (filledHull_component_subset hx)
    isClosed_closure.isOpen_compl.connectedComponentIn

lemma filledHull_subset_interior_of_mem_compl_closure {Ω : Set AmbientSpace}
    {x : AmbientSpace} (hx : x ∈ filledHull Ω) (hxo : x ∈ (closure Ω)ᶜ) :
    x ∈ interior (filledHull Ω) :=
  filledHull_component_subset_interior hx (mem_connectedComponentIn hxo)

lemma filledHull_subset_interior {Ω : Set AmbientSpace} (ho : IsOpen Ω) :
    Ω ⊆ interior (filledHull Ω) :=
  interior_maximal (subset_closure.trans (filledHull_closure_subset Ω)) ho

lemma filledHull_frontier_subset {Ω : Set AmbientSpace} (ho : IsOpen Ω) :
    frontier (filledHull Ω) ⊆ frontier Ω := by
  intro x hx
  rw [ho.frontier_eq]
  have hxK : x ∈ filledHull Ω := (filledHull_isClosed Ω).closure_eq ▸ hx.1
  refine ⟨?_, fun hxΩ => hx.2 (filledHull_subset_interior ho hxΩ)⟩
  by_contra hn
  exact hx.2 (filledHull_subset_interior_of_mem_compl_closure hxK hn)

lemma filledHull_eq_closure_interior {Ω : Set AmbientSpace} (ho : IsOpen Ω) :
    filledHull Ω = closure (interior (filledHull Ω)) := by
  apply Subset.antisymm
  · intro x hx
    by_cases hc : x ∈ closure Ω
    · exact closure_mono (filledHull_subset_interior ho) hc
    · exact subset_closure (filledHull_subset_interior_of_mem_compl_closure hx hc)
  · exact (filledHull_isClosed Ω).closure_interior_subset

lemma filledHull_frontier_interior {Ω : Set AmbientSpace} (ho : IsOpen Ω) :
    frontier (interior (filledHull Ω)) = frontier (filledHull Ω) := by
  rw [frontier, frontier, interior_interior, ← filledHull_eq_closure_interior ho,
    (filledHull_isClosed Ω).closure_eq]

lemma hull_frontier_connectedComponentIn_subset {U : Set AmbientSpace} (hU : IsOpen U)
    (x : AmbientSpace) : frontier (connectedComponentIn U x) ⊆ frontier U := by
  intro p hp
  rw [hU.frontier_eq]
  refine ⟨closure_mono (connectedComponentIn_subset U x) hp.1, ?_⟩
  intro hpU
  have hopen : IsOpen (connectedComponentIn U p) := hU.connectedComponentIn
  obtain ⟨z, hzp, hzx⟩ := mem_closure_iff.mp hp.1 _ hopen (mem_connectedComponentIn hpU)
  have heq := (connectedComponentIn_eq hzp).trans (connectedComponentIn_eq hzx).symm
  have hpc : p ∈ connectedComponentIn U x := heq ▸ mem_connectedComponentIn hpU
  apply hp.2
  rwa [(hU.connectedComponentIn (x := x)).interior_eq]

lemma hull_frontier_complement_component_subset {Ω : Set AmbientSpace}
    (x : AmbientSpace) :
    frontier (connectedComponentIn (closure Ω)ᶜ x) ⊆ closure Ω := by
  have h := hull_frontier_connectedComponentIn_subset
    (U := (closure Ω)ᶜ) isClosed_closure.isOpen_compl x
  rw [frontier_compl] at h
  exact h.trans (frontier_subset_closure.trans_eq closure_closure)

lemma hull_bounded_component_frontier_nonempty {Ω : Set AmbientSpace}
    {x : AmbientSpace} (hx : x ∈ (closure Ω)ᶜ)
    (hb : Bornology.IsBounded (connectedComponentIn (closure Ω)ᶜ x)) :
    (frontier (connectedComponentIn (closure Ω)ᶜ x)).Nonempty := by
  apply nonempty_frontier_iff.mpr
  refine ⟨⟨x, mem_connectedComponentIn hx⟩, ?_⟩
  intro heq
  have hball : (ball (0 : AmbientSpace) 0)ᶜ ⊆ connectedComponentIn (closure Ω)ᶜ x := by
    rw [heq]; exact subset_univ _
  exact hull_not_isBounded_compl_ball 0 (hb.subset hball)

lemma filledHull_isConnected {Ω : Set AmbientSpace} (hc : IsConnected Ω)
    (_hb : Bornology.IsBounded Ω) : IsConnected (filledHull Ω) := by
  obtain ⟨a, ha⟩ := hc.nonempty
  refine ⟨⟨a, filledHull_closure_subset Ω (subset_closure ha)⟩,
    isPreconnected_of_forall a ?_⟩
  intro x hx
  by_cases hxc : x ∈ closure Ω
  · exact ⟨closure Ω, filledHull_closure_subset Ω, subset_closure ha, hxc, hc.2.closure⟩
  have hbC : Bornology.IsBounded (connectedComponentIn (closure Ω)ᶜ x) :=
    Classical.not_not.mp hx
  obtain ⟨p, hp⟩ := hull_bounded_component_frontier_nonempty hxc hbC
  refine ⟨closure Ω ∪ closure (connectedComponentIn (closure Ω)ᶜ x),
    union_subset (filledHull_closure_subset Ω)
      (closure_minimal (filledHull_component_subset hx) (filledHull_isClosed Ω)),
    Or.inl (subset_closure ha), Or.inr (subset_closure (mem_connectedComponentIn hxc)), ?_⟩
  exact hc.2.closure.union p (hull_frontier_complement_component_subset x hp) hp.1
    isPreconnected_connectedComponentIn.closure

lemma hull_isOpenMap_proj (i : Fin 3) :
    IsOpenMap (fun y : AmbientSpace => y i) :=
  PiLp.isOpenMap_apply 2 (fun _ : Fin 3 => ℝ) i

lemma hull_closure_coordinate_pos (i : Fin 3) :
    closure {y : AmbientSpace | 0 < y i} = {y | 0 ≤ y i} := by
  have h := (hull_isOpenMap_proj i).preimage_closure_eq_closure_preimage
    (EuclideanSpace.proj i).continuous (Ioi 0)
  rw [closure_Ioi] at h
  exact h.symm

lemma hull_closure_coordinate_neg (i : Fin 3) :
    closure {y : AmbientSpace | y i < 0} = {y | y i ≤ 0} := by
  have h := (hull_isOpenMap_proj i).preimage_closure_eq_closure_preimage
    (EuclideanSpace.proj i).continuous (Iio 0)
  rw [closure_Iio] at h
  exact h.symm

lemma hull_chart_mem_closure_iff {Ω : Set AmbientSpace} {d : LipschitzGraphChart 3}
    (hd : d.IsChartFor Ω) {y : AmbientSpace} (hy : y ∈ coordinateCube 3 d.radius) :
    d.homeomorph y ∈ closure Ω ↔ 0 ≤ y d.normal := by
  have hyr : d.homeomorph y ∈ d.region := ⟨y, hy, rfl⟩
  constructor
  · intro hc
    have hc' := d.isOpen_region.closure_inter ⟨hc, hyr⟩
    rw [← hd, LipschitzGraphChart.upperRegion, ← d.homeomorph.image_closure] at hc'
    have hh : y ∈ closure (coordinateHalfCube d.normal d.radius) := by
      simpa only [mem_image, d.homeomorph.injective.eq_iff, exists_eq_right] using hc'
    exact closure_lt_subset_le continuous_const (EuclideanSpace.proj d.normal).continuous
      (closure_mono inter_subset_right hh)
  · intro hn
    have hh : y ∈ closure (coordinateHalfCube d.normal d.radius) :=
      (isOpen_coordinateCube 3 d.radius).inter_closure
        ⟨hy, (hull_closure_coordinate_pos d.normal).symm ▸ hn⟩
    have hh' : d.homeomorph y ∈ closure d.upperRegion := by
      rw [LipschitzGraphChart.upperRegion, ← d.homeomorph.image_closure]
      exact mem_image_of_mem _ hh
    rw [hd] at hh'
    exact closure_mono inter_subset_left hh'

lemma hull_exists_nhds_outer {Ω : Set AmbientSpace} (h1 : HasC1Boundary Ω)
    (ho : IsOpen Ω) {p : AmbientSpace} (hp : p ∈ frontier Ω) :
    ∃ W : Set AmbientSpace, IsOpen W ∧ p ∈ W ∧ IsPreconnected (W ∩ (closure Ω)ᶜ) ∧
      W ∩ frontier Ω ⊆ closure (W ∩ (closure Ω)ᶜ) := by
  obtain ⟨c, hc, hpc⟩ := h1 p hp
  obtain ⟨d, hd, hpd⟩ := hc.exists_lipschitzGraphChart hp hpc
  have heq : d.region ∩ (closure Ω)ᶜ = d.homeomorph ''
      (coordinateCube 3 d.radius ∩ {y | y d.normal < 0}) := by
    ext z
    constructor
    · rintro ⟨⟨y, hy, rfl⟩, hz⟩
      exact ⟨y, ⟨hy, lt_of_not_ge (fun hn => hz ((hull_chart_mem_closure_iff hd hy).mpr hn))⟩,
        rfl⟩
    · rintro ⟨y, ⟨hy, hn⟩, rfl⟩
      exact ⟨⟨y, hy, rfl⟩, fun hz => (not_le_of_gt hn) ((hull_chart_mem_closure_iff hd hy).mp hz)⟩
  refine ⟨d.region, d.isOpen_region, hpd, ?_, ?_⟩
  · rw [heq]
    apply IsPreconnected.image _ _ d.homeomorph.continuous.continuousOn
    apply Convex.isPreconnected
    apply (convex_coordinateCube 3 d.radius).inter
    intro x hx y hy a b ha hb hab
    change (a • x + b • y) d.normal < 0
    simp only [PiLp.add_apply, PiLp.smul_apply, smul_eq_mul]
    change x d.normal < 0 at hx
    change y d.normal < 0 at hy
    rcases lt_or_eq_of_le ha with ha | rfl
    · exact add_neg_of_neg_of_nonpos (mul_neg_of_pos_of_neg ha hx)
        (mul_nonpos_of_nonneg_of_nonpos hb hy.le)
    · simpa [show b = 1 by linarith] using hy
  · rintro z ⟨⟨y, hy, rfl⟩, hz⟩
    have hn : y d.normal ≤ 0 := by
      by_contra h
      have hu : d.homeomorph y ∈ d.upperRegion := ⟨y, ⟨hy, lt_of_not_ge h⟩, rfl⟩
      rw [hd] at hu
      exact (ho.frontier_eq ▸ hz).2 hu.1
    have hcl : y ∈ closure (coordinateCube 3 d.radius ∩ {y | y d.normal < 0}) :=
      (isOpen_coordinateCube 3 d.radius).inter_closure
        ⟨hy, (hull_closure_coordinate_neg d.normal).symm ▸ hn⟩
    rw [heq, ← d.homeomorph.image_closure]
    exact mem_image_of_mem _ hcl

lemma hull_outer_patch_subset_exterior {Ω W : Set AmbientSpace} (hW : IsOpen W)
    (hpre : IsPreconnected (W ∩ (closure Ω)ᶜ)) {p : AmbientSpace}
    (hp : p ∈ frontier (filledHull Ω)) (hpW : p ∈ W) :
    W ∩ (closure Ω)ᶜ ⊆ hullExterior Ω := by
  have hpcl : p ∈ closure (hullExterior Ω) := by
    have hp' : p ∈ frontier (hullExterior Ω) := by simpa [filledHull] using hp
    exact hp'.1
  obtain ⟨x, hxW, hx⟩ := mem_closure_iff.mp hpcl W hW hpW
  exact (hpre.subset_connectedComponentIn
    ⟨hxW, hullExterior_subset_compl_closure Ω hx⟩ inter_subset_right).trans
      (hullExterior_component_subset hx)

lemma hull_exists_nhds_interior_eq {Ω : Set AmbientSpace} (ho : IsOpen Ω)
    (h1 : HasC1Boundary Ω) {p : AmbientSpace} (hp : p ∈ frontier (filledHull Ω)) :
    ∃ W : Set AmbientSpace, IsOpen W ∧ p ∈ W ∧
      W ∩ interior (filledHull Ω) = W ∩ Ω := by
  obtain ⟨W, hW, hpW, hpre, hfront⟩ :=
    hull_exists_nhds_outer h1 ho (filledHull_frontier_subset ho hp)
  have hsub := hull_outer_patch_subset_exterior hW hpre hp hpW
  refine ⟨W, hW, hpW, Subset.antisymm ?_ (inter_subset_inter_right W
    (filledHull_subset_interior ho))⟩
  rintro x ⟨hxW, hxK⟩
  refine ⟨hxW, ?_⟩
  have hxcl : x ∉ closure (hullExterior Ω) := by
    simpa only [filledHull, interior_compl, mem_compl_iff] using hxK
  by_contra hxΩ
  by_cases hxc : x ∈ closure Ω
  · exact hxcl (closure_mono hsub (hfront ⟨hxW, ho.frontier_eq ▸ ⟨hxc, hxΩ⟩⟩))
  · exact hxcl (subset_closure (hsub ⟨hxW, hxc⟩))

lemma hull_chart_of_chart {Ω : Set AmbientSpace} (ho : IsOpen Ω)
    (h1 : HasC1Boundary Ω) {c : C1BoundaryChart} (hc : c.IsChartFor Ω)
    {p : AmbientSpace} (hp : p ∈ frontier (filledHull Ω)) (hpc : p ∈ c.region) :
    ∃ c' : C1BoundaryChart, c'.height = c.height ∧ c'.placement = c.placement ∧
      c'.region ⊆ c.region ∧ p ∈ c'.region ∧ c'.IsChartFor (interior (filledHull Ω)) := by
  obtain ⟨W, hW, hpW, heq⟩ := hull_exists_nhds_interior_eq ho h1 hp
  refine ⟨{ c with
    region := c.region ∩ W
    isOpen_region := c.isOpen_region.inter hW
    bounded_region := c.bounded_region.subset inter_subset_left },
    rfl, rfl, inter_subset_left, ⟨hpc, hpW⟩, ?_⟩
  intro z hz
  change z ∈ interior (filledHull Ω) ↔ c.placement.symm z ∈ smoothSubgraph c.height
  rw [← hc z hz.1]
  exact ⟨fun h => (heq ▸ (show z ∈ W ∩ interior (filledHull Ω) from ⟨hz.2, h⟩)).2,
    fun h => filledHull_subset_interior ho h⟩

lemma filledHull_hasC1Boundary_interior {Ω : Set AmbientSpace} (ho : IsOpen Ω)
    (h1 : HasC1Boundary Ω) : HasC1Boundary (interior (filledHull Ω)) := by
  intro p hp
  rw [filledHull_frontier_interior ho] at hp
  obtain ⟨c, hc, hpc⟩ := h1 p (filledHull_frontier_subset ho hp)
  obtain ⟨c', _, _, _, hp', hc'⟩ := hull_chart_of_chart ho h1 hc hp hpc
  exact ⟨c', hc', hp'⟩

lemma filledHull_hasCkBoundary_interior {Ω : Set AmbientSpace} {k : ℕ∞}
    (h : HasCkBoundary k Ω) (ho : IsOpen Ω) : HasCkBoundary k (interior (filledHull Ω)) := by
  intro p hp
  rw [filledHull_frontier_interior ho] at hp
  obtain ⟨c, hc, hpc, hk⟩ := h p (filledHull_frontier_subset ho hp)
  obtain ⟨c', hh, _, _, hp', hc'⟩ := hull_chart_of_chart ho h.hasC1Boundary hc hp hpc
  exact ⟨c', hc', hp', hh.symm ▸ hk⟩

lemma filledHull_perimeter_interior_le {Ω : Set AmbientSpace} (ho : IsOpen Ω)
    (_hb : Bornology.IsBounded Ω) (h1 : HasC1Boundary Ω) :
    perimeter (interior (filledHull Ω)) ≤ perimeter Ω := by
  rw [(filledHull_hasC1Boundary_interior ho h1).perimeter_eq_boundaryArea isOpen_interior,
    h1.perimeter_eq_boundaryArea ho, filledHull_frontier_interior ho]
  exact MeasureTheory.measure_mono (filledHull_frontier_subset ho)

lemma hull_bounded_component_frontier_disjoint {Ω : Set AmbientSpace} (ho : IsOpen Ω)
    (h1 : HasC1Boundary Ω) {x : AmbientSpace}
    (hbC : Bornology.IsBounded (connectedComponentIn (closure Ω)ᶜ x)) :
    Disjoint (frontier (connectedComponentIn (closure Ω)ᶜ x)) (frontier (filledHull Ω)) := by
  apply disjoint_left.mpr
  intro p hpC hpK
  obtain ⟨W, hW, hpW, hpre, _⟩ :=
    hull_exists_nhds_outer h1 ho (filledHull_frontier_subset ho hpK)
  have hsub := hull_outer_patch_subset_exterior hW hpre hpK hpW
  obtain ⟨z, hzW, hzC⟩ := mem_closure_iff.mp hpC.1 W hW hpW
  have hzu := hsub ⟨hzW, connectedComponentIn_subset _ _ hzC⟩
  exact hzu ((connectedComponentIn_eq hzC) ▸ hbC)

lemma hull_bounded_component_closure_subset_interior {Ω : Set AmbientSpace}
    (ho : IsOpen Ω) (h1 : HasC1Boundary Ω) {x : AmbientSpace}
    (hx : x ∈ filledHull Ω) :
    closure (connectedComponentIn (closure Ω)ᶜ x) ⊆ interior (filledHull Ω) := by
  have hbC : Bornology.IsBounded (connectedComponentIn (closure Ω)ᶜ x) :=
    Classical.not_not.mp hx
  have hcl : closure (connectedComponentIn (closure Ω)ᶜ x) ⊆ filledHull Ω :=
    closure_minimal (filledHull_component_subset hx) (filledHull_isClosed Ω)
  intro p hp
  apply (mem_interior_iff_notMem_frontier (hcl hp)).mpr
  intro hpK
  have hpC : p ∈ frontier (connectedComponentIn (closure Ω)ᶜ x) := by
    refine ⟨hp, ?_⟩
    intro hpi
    exact hpK.2 (filledHull_component_subset_interior hx (interior_subset hpi))
  exact (hull_bounded_component_frontier_disjoint ho h1 hbC).le_bot ⟨hpC, hpK⟩

lemma filledHull_isConnected_interior {Ω : Set AmbientSpace} (hc : IsConnected Ω)
    (ho : IsOpen Ω) (_hb : Bornology.IsBounded Ω) (h1 : HasC1Boundary Ω) :
    IsConnected (interior (filledHull Ω)) := by
  obtain ⟨a, ha⟩ := hc.nonempty
  refine ⟨⟨a, filledHull_subset_interior ho ha⟩, isPreconnected_of_forall a ?_⟩
  intro x hx
  have hattach (p : AmbientSpace) (hp : p ∈ closure Ω) : IsPreconnected (Ω ∪ {p}) :=
    hc.2.subset_closure subset_union_left
      (union_subset subset_closure (singleton_subset_iff.mpr hp))
  by_cases hxc : x ∈ closure Ω
  · refine ⟨Ω ∪ {x}, union_subset (filledHull_subset_interior ho)
      (singleton_subset_iff.mpr hx), Or.inl ha, Or.inr (mem_singleton x), hattach x hxc⟩
  have hxK := interior_subset hx
  have hbC : Bornology.IsBounded (connectedComponentIn (closure Ω)ᶜ x) :=
    Classical.not_not.mp hxK
  obtain ⟨p, hp⟩ := hull_bounded_component_frontier_nonempty hxc hbC
  have hcl := hull_bounded_component_closure_subset_interior ho h1 hxK
  refine ⟨(Ω ∪ {p}) ∪ closure (connectedComponentIn (closure Ω)ᶜ x),
    union_subset (union_subset (filledHull_subset_interior ho)
      (singleton_subset_iff.mpr (hcl hp.1))) hcl,
    Or.inl (Or.inl ha), Or.inr (subset_closure (mem_connectedComponentIn hxc)), ?_⟩
  exact (hattach p (hull_frontier_complement_component_subset x hp)).union p
    (Or.inr (mem_singleton p)) hp.1 isPreconnected_connectedComponentIn.closure

/-- Near a point of `∂K` the boundary of the hull coincides with `∂Ω`. -/
lemma hull_exists_nhds_frontier_eq {Ω : Set AmbientSpace} (ho : IsOpen Ω)
    (h1 : HasC1Boundary Ω) {p : AmbientSpace} (hp : p ∈ frontier (filledHull Ω)) :
    ∃ W : Set AmbientSpace, IsOpen W ∧ p ∈ W ∧
      frontier (filledHull Ω) ∩ W = frontier Ω ∩ W := by
  obtain ⟨W, hW, hpW, heq⟩ := hull_exists_nhds_interior_eq ho h1 hp
  have h' : interior (filledHull Ω) ∩ W = Ω ∩ W := by
    rw [inter_comm, heq, inter_comm]
  refine ⟨W, hW, hpW, ?_⟩
  calc frontier (filledHull Ω) ∩ W = frontier (interior (filledHull Ω)) ∩ W := by
        rw [filledHull_frontier_interior ho]
    _ = frontier (interior (filledHull Ω) ∩ W) ∩ W := (frontier_inter_open_inter hW).symm
    _ = frontier (Ω ∩ W) ∩ W := by rw [h']
    _ = frontier Ω ∩ W := frontier_inter_open_inter hW

/-- A boundary chart of `int K` at a point of `∂K` restricts to a boundary chart of `Ω` with the
same height and placement. -/
lemma hull_chart_of_hull_chart {Ω : Set AmbientSpace} (ho : IsOpen Ω)
    (h1 : HasC1Boundary Ω) {c : C1BoundaryChart}
    (hc : c.IsChartFor (interior (filledHull Ω)))
    {p : AmbientSpace} (hp : p ∈ frontier (filledHull Ω)) (hpc : p ∈ c.region) :
    ∃ c' : C1BoundaryChart, c'.height = c.height ∧ c'.placement = c.placement ∧
      c'.region ⊆ c.region ∧ p ∈ c'.region ∧ c'.IsChartFor Ω := by
  obtain ⟨W, hW, hpW, heq⟩ := hull_exists_nhds_interior_eq ho h1 hp
  refine ⟨{ c with
    region := c.region ∩ W
    isOpen_region := c.isOpen_region.inter hW
    bounded_region := c.bounded_region.subset inter_subset_left },
    rfl, rfl, inter_subset_left, ⟨hpc, hpW⟩, ?_⟩
  intro z hz
  change z ∈ Ω ↔ c.placement.symm z ∈ smoothSubgraph c.height
  rw [← hc z hz.1]
  have hiff : z ∈ W ∩ interior (filledHull Ω) ↔ z ∈ W ∩ Ω := by rw [heq]
  exact ⟨fun h => (hiff.mpr ⟨hz.2, h⟩).2, fun h => (hiff.mp ⟨hz.2, h⟩).2⟩

/-- The intrinsic tangent plane depends only on the germ of the surface at the point. -/
theorem hull_tangentPlane_congr {S T : Set AmbientSpace} {p : AmbientSpace}
    (h : 𝓝[S] p = 𝓝[T] p) : tangentPlane S p = tangentPlane T p := by
  simp only [tangentPlane, h]

/-- The mean curvature depends only on the germ of the surface at the point. -/
theorem hull_meanCurvature_congr {S T : Set AmbientSpace} {n : AmbientSpace → AmbientSpace}
    {p : AmbientSpace} (h : 𝓝[S] p = 𝓝[T] p) :
    meanCurvature S n p = meanCurvature T n p := by
  have key : ∀ P Q : Submodule ℝ AmbientSpace, P = Q →
      LinearMap.trace ℝ P
          (P.orthogonalProjectionOnto ∘L shapeOperator n p ∘L P.subtypeL).toLinearMap =
        LinearMap.trace ℝ Q
          (Q.orthogonalProjectionOnto ∘L shapeOperator n p ∘L Q.subtypeL).toLinearMap := by
    rintro P Q rfl
    rfl
  exact key _ _ (hull_tangentPlane_congr h)

/-- The Gauss curvature depends only on the germ of the surface at the point. -/
theorem hull_gaussCurvature_congr {S T : Set AmbientSpace} {n : AmbientSpace → AmbientSpace}
    {p : AmbientSpace} (h : 𝓝[S] p = 𝓝[T] p) :
    gaussCurvature S n p = gaussCurvature T n p := by
  have key : ∀ P Q : Submodule ℝ AmbientSpace, P = Q →
      LinearMap.det
          (P.orthogonalProjectionOnto ∘L shapeOperator n p ∘L P.subtypeL).toLinearMap =
        LinearMap.det
          (Q.orthogonalProjectionOnto ∘L shapeOperator n p ∘L Q.subtypeL).toLinearMap := by
    rintro P Q rfl
    rfl
  exact key _ _ (hull_tangentPlane_congr h)

/-- `lem:hull-properties`: the curvatures of `K` and `Ω` agree on `∂K`. -/
theorem filledHull_meanCurvature_eq {Ω : Set AmbientSpace} (ho : IsOpen Ω)
    (h1 : HasC1Boundary Ω) {p : AmbientSpace} (hp : p ∈ frontier (filledHull Ω))
    (n : AmbientSpace → AmbientSpace) :
    meanCurvature (frontier (filledHull Ω)) n p = meanCurvature (frontier Ω) n p ∧
      gaussCurvature (frontier (filledHull Ω)) n p = gaussCurvature (frontier Ω) n p := by
  obtain ⟨W, hW, hpW, heq⟩ := hull_exists_nhds_frontier_eq ho h1 hp
  have h : 𝓝[frontier (filledHull Ω)] p = 𝓝[frontier Ω] p := by
    rw [nhdsWithin_restrict' _ (hW.mem_nhds hpW), heq, ← nhdsWithin_restrict' _ (hW.mem_nhds hpW)]
  exact ⟨hull_meanCurvature_congr h, hull_gaussCurvature_congr h⟩

/-- `eq:hull-perimeter`: `Per(K) ≤ Per(Ω)` for the hull itself (`∂K` is Lebesgue-null). -/
theorem filledHull_perimeter_le {Ω : Set AmbientSpace} (ho : IsOpen Ω)
    (hb : Bornology.IsBounded Ω) (h1 : HasC1Boundary Ω) :
    perimeter (filledHull Ω) ≤ perimeter Ω := by
  have hC1 := filledHull_hasC1Boundary_interior ho h1
  have hcpt : IsCompact (frontier (interior (filledHull Ω))) := by
    rw [filledHull_frontier_interior ho]
    exact (filledHull_isCompact hb).of_isClosed_subset isClosed_frontier
      (frontier_subset_closure.trans (filledHull_isClosed Ω).closure_subset)
  have hnull : MeasureTheory.volume (frontier (filledHull Ω)) = 0 := by
    rw [← filledHull_frontier_interior ho]
    exact hC1.volume_frontier_eq_zero hcpt
  have hK : interior (filledHull Ω) ∪ frontier (filledHull Ω) = filledHull Ω := by
    rw [← closure_eq_interior_union_frontier, (filledHull_isClosed Ω).closure_eq]
  have hae := MeasureTheory.union_ae_eq_left_of_ae_eq_empty (s := interior (filledHull Ω))
    (MeasureTheory.ae_eq_empty.mpr hnull)
  rw [hK] at hae
  rw [perimeter_congr_ae hae]
  exact filledHull_perimeter_interior_le ho hb h1

/-- `lem:hull-properties` for a stationary domain (`not:stationary`): the boundary of the hull
is `C³`, and the Euler--Lagrange equation `H + v_Ω = λ` holds on `∂K` in every `C²` boundary
chart of `int K`, with the curvature of `∂K` and the chart's outward normal of `K`. -/
theorem IsStationaryDomain.filledHull_boundary {V lam : ℝ} {Ω : Set AmbientSpace}
    (h : IsStationaryDomain V lam Ω) :
    HasCkBoundary 3 (interior (filledHull Ω)) ∧
    ∀ p ∈ frontier (filledHull Ω), ∀ c : C1BoundaryChart,
      c.IsChartFor (interior (filledHull Ω)) → p ∈ c.region → ContDiff ℝ 2 c.height →
      meanCurvature (frontier (filledHull Ω)) c.outwardNormal p +
        (coulombPotential Ω p).toReal = lam := by
  refine ⟨filledHull_hasCkBoundary_interior h.boundary_C3 h.isOpen, ?_⟩
  intro p hp c hc hpc hc2
  obtain ⟨c', hh, hpl, -, hpc', hc'⟩ :=
    hull_chart_of_hull_chart h.isOpen h.hasC1Boundary hc hp hpc
  have hn : c'.outwardNormal = c.outwardNormal := by
    funext z
    simp only [C1BoundaryChart.outwardNormal, hh, hpl]
  have hEL := h.eulerLagrange p (filledHull_frontier_subset h.isOpen hp) c' hc' hpc'
    (by rw [hh]; exact hc2)
  rw [hn] at hEL
  rw [(filledHull_meanCurvature_eq h.isOpen h.hasC1Boundary hp _).1]
  exact hEL

private theorem hull_isConnected_subtype_preimage {A B : Set AmbientSpace} (hA : IsConnected A)
    (hAB : A ⊆ B) : IsConnected ((Subtype.val : B → AmbientSpace) ⁻¹' A) := by
  refine ⟨?_, Topology.IsInducing.subtypeVal.isPreconnected_image.mp ?_⟩
  · obtain ⟨x, hx⟩ := hA.nonempty
    exact ⟨⟨x, hAB hx⟩, hx⟩
  · simpa only [Subtype.image_preimage_coe, inter_eq_right.mpr hAB] using hA.isPreconnected

/-- `ℝ³ ∖ ∂K` has exactly two components, `int K` and `ℝ³ ∖ K`. -/
theorem filledHull_card_connectedComponents_compl_frontier {Ω : Set AmbientSpace}
    (hc : IsConnected Ω) (ho : IsOpen Ω) (hb : Bornology.IsBounded Ω) (h1 : HasC1Boundary Ω) :
    Nat.card (ConnectedComponents ((frontier (filledHull Ω))ᶜ : Set AmbientSpace)) = 2 := by
  let B := (frontier (filledHull Ω))ᶜ
  let U : Bool → Set B := fun b =>
    if b then (Subtype.val : B → AmbientSpace) ⁻¹' interior (filledHull Ω)
    else (Subtype.val : B → AmbientSpace) ⁻¹' (filledHull Ω)ᶜ
  have hmem : ∀ x : B, x.1 ∈ interior (filledHull Ω) ∨ x.1 ∈ (filledHull Ω)ᶜ := by
    intro x
    by_cases hx : x.1 ∈ filledHull Ω
    · left
      by_contra hi
      exact x.2 ⟨subset_closure hx, hi⟩
    · exact Or.inr hx
  have hdisj0 : ∀ x : AmbientSpace, x ∈ interior (filledHull Ω) → x ∉ (filledHull Ω)ᶜ :=
    fun x hx hxc => hxc (interior_subset hx)
  have hUopen : ∀ b, IsOpen (U b) := by
    intro b
    cases b
    · exact (filledHull_isClosed Ω).isOpen_compl.preimage continuous_subtype_val
    · exact isOpen_interior.preimage continuous_subtype_val
  have hUcompl : ∀ b, (U b)ᶜ = U (!b) := by
    intro b
    ext x
    rcases hmem x with h | h <;> cases b <;>
      simp only [U, Bool.not_false, Bool.not_true, ite_true, mem_compl_iff,
        mem_preimage] <;> tauto
  have hUclopen : ∀ b, IsClopen (U b) := fun b =>
    ⟨isOpen_compl_iff.mp (hUcompl b ▸ hUopen (!b)), hUopen b⟩
  have hdisj : Pairwise (Function.onFun Disjoint U) := by
    intro i j hij
    cases i <;> cases j <;> try exact (hij rfl).elim
    all_goals
      apply Set.disjoint_left.mpr
      intro x h₁ h₂
      simp only [U, ite_true, mem_preimage] at h₁ h₂
      first | exact hdisj0 _ h₁ h₂ | exact hdisj0 _ h₂ h₁
  have hcover : ⋃ b, U b = univ := by
    ext x
    simp only [mem_iUnion, mem_univ, iff_true]
    rcases hmem x with h | h
    · exact ⟨true, h⟩
    · exact ⟨false, h⟩
  have hUconn : ∀ b, IsConnected (U b) := by
    intro b
    cases b
    · refine hull_isConnected_subtype_preimage (filledHull_isConnected_compl hb) ?_
      intro x hx hxf
      exact hx ((filledHull_isClosed Ω).frontier_subset hxf)
    · refine hull_isConnected_subtype_preimage (filledHull_isConnected_interior hc ho hb h1) ?_
      intro x hx hxf
      rw [← filledHull_frontier_interior ho] at hxf
      exact hxf.2 (by rwa [interior_interior])
  have he := ConnectedComponents.equivOfIsClopenOfIsConnected hUclopen hdisj hcover hUconn
  exact (Nat.card_congr he).trans (by simp)

/-- `lem:hull-properties` (`∂K` connected), conditional on `thm:component-count` for the
surface `∂K`: if `ℝ³ ∖ ∂K` has one more component than `∂K` (proved on another branch for
compact `C^∞` surfaces; `∂K` is only known to be `C³`), then `∂K` is connected. -/
theorem filledHull_frontier_isConnected_of_count {Ω : Set AmbientSpace}
    (hc : IsConnected Ω) (ho : IsOpen Ω) (hb : Bornology.IsBounded Ω) (h1 : HasC1Boundary Ω)
    (hcount : Nat.card (ConnectedComponents ((frontier (filledHull Ω))ᶜ : Set AmbientSpace)) =
      Nat.card (ConnectedComponents (frontier (filledHull Ω))) + 1) :
    IsConnected (frontier (filledHull Ω)) := by
  rw [filledHull_card_connectedComponents_compl_frontier hc ho hb h1] at hcount
  have hone : Nat.card (ConnectedComponents (frontier (filledHull Ω))) = 1 := by omega
  have : Subsingleton (ConnectedComponents (frontier (filledHull Ω))) :=
    (Nat.card_eq_one_iff_unique.mp hone).1
  have hp : PreconnectedSpace (frontier (filledHull Ω)) := by
    apply preconnectedSpace_iff_connectedComponent.mpr
    intro x
    apply Set.eq_univ_of_forall
    intro y
    exact ConnectedComponents.coe_eq_coe'.mp (Subsingleton.elim
      (ConnectedComponents.mk y) (ConnectedComponents.mk x))
  refine ⟨?_, isPreconnected_iff_preconnectedSpace.mpr hp⟩
  have hne : (Nat.card (ConnectedComponents (frontier (filledHull Ω)))) ≠ 0 := by omega
  obtain ⟨x⟩ := (Nat.card_ne_zero.mp hne).1
  obtain ⟨y, -⟩ := ConnectedComponents.surjective_coe x
  exact ⟨y.1, y.2⟩

/-- The hull properties of blueprint `lem:hull-properties`, apart from the
separate component-count argument for connectedness of the boundary. -/
theorem filledHull_properties {Ω : Set AmbientSpace} (ho : IsOpen Ω)
    (hb : Bornology.IsBounded Ω) (hc : IsConnected Ω) (h1 : HasC1Boundary Ω) :
    IsCompact (filledHull Ω) ∧
    closure Ω ⊆ filledHull Ω ∧
    IsConnected (filledHull Ω)ᶜ ∧
    frontier (filledHull Ω) ⊆ frontier Ω ∧
    IsConnected (filledHull Ω) ∧
    Ω ⊆ interior (filledHull Ω) ∧
    filledHull Ω = closure (interior (filledHull Ω)) ∧
    frontier (interior (filledHull Ω)) = frontier (filledHull Ω) ∧
    IsConnected (interior (filledHull Ω)) ∧
    perimeter (interior (filledHull Ω)) ≤ perimeter Ω ∧
    HasC1Boundary (interior (filledHull Ω)) := by
  exact ⟨filledHull_isCompact hb, filledHull_closure_subset Ω, filledHull_isConnected_compl hb,
    filledHull_frontier_subset ho, filledHull_isConnected hc hb, filledHull_subset_interior ho,
    filledHull_eq_closure_interior ho, filledHull_frontier_interior ho,
    filledHull_isConnected_interior hc ho hb h1, filledHull_perimeter_interior_le ho hb h1,
    filledHull_hasC1Boundary_interior ho h1⟩

end LiquidDrop

module

public import NoCompromise.Topology.Transversality

@[expose] public section

/-!
# Evenness of the boundary of a compact one-manifold

The theorem `even_ncard_oneManifoldBoundary` completes the evenness assertion of
`lem:handshake`. A finite set of vertices, containing the manifold boundary,
cuts the manifold into open chart arcs. Each vertex has one local side at a
boundary point and two otherwise. Chart transitions are locally strictly
monotone or antitone, so each arc receives exactly one side at each of its two
distinct endpoints. Counting these sides proves evenness.
-/

noncomputable section
open Set Filter Function
open scoped Topology NNReal
attribute [local instance] Classical.propDecidable

namespace LiquidDrop

variable {X : Type*} [TopologicalSpace X]

/-- In any chart, the boundary is precisely the inverse image of zero. -/
theorem oneManifoldBoundary_mem_iff_chart_eq_zero {C : Set X} {x : C}
    (e : OpenPartialHomeomorph C ℝ≥0) (hx : x ∈ e.source) :
    (x : X) ∈ oneManifoldBoundary C ↔ e x = 0 := by
  constructor
  · exact fun h => oneManifoldBoundary_chart_eq_zero h e hx
  · exact fun h => ⟨x.property, e, hx, h⟩

/-- Passing to the manifold subtype preserves the boundary cardinality. -/
theorem oneManifoldBoundary_subtype_ncard {C : Set X} :
    (((↑) : C → X) ⁻¹' oneManifoldBoundary C).ncard =
      (oneManifoldBoundary C).ncard := by
  have himage : ((↑) : C → X) '' (((↑) : C → X) ⁻¹' oneManifoldBoundary C) =
      oneManifoldBoundary C := by
    apply Subset.antisymm (image_preimage_subset _ _)
    intro x hx
    exact ⟨⟨x, hx.choose⟩, hx, rfl⟩
  calc
    _ = (((↑) : C → X) '' (((↑) : C → X) ⁻¹' oneManifoldBoundary C)).ncard :=
      (ncard_image_of_injective _ Subtype.val_injective).symm
    _ = _ := congrArg Set.ncard himage

/-- Every point of a half-line chart lies in the interior of a closed chart arc.
The interval is taken in `ℝ≥0`, so this also covers boundary points. -/
theorem exists_closed_chart_arc (e : OpenPartialHomeomorph X ℝ≥0)
    {x : X} (hx : x ∈ e.source) :
    ∃ a b : ℝ≥0, a ≤ b ∧ Icc a b ⊆ e.target ∧
      x ∈ interior (e.symm '' Icc a b) := by
  obtain ⟨a, b, hab, hn, ht⟩ :=
    exists_Icc_mem_subset_of_mem_nhds (e.open_target.mem_nhds (e.map_source hx))
  refine ⟨a, b, hab.1.trans hab.2, ht, mem_interior_iff_mem_nhds.mpr ?_⟩
  simpa only [e.left_inv hx] using e.symm.image_mem_nhds (e.map_source hx) hn

/-- A compact one-manifold has a finite cover by interiors of closed chart arcs. -/
theorem exists_finite_closed_chart_arc_cover {C : Set X}
    (hC : IsCompact C) (hM : IsOneManifoldWithBoundary C) :
    ∃ (t : Finset C) (e : C → OpenPartialHomeomorph C ℝ≥0) (a b : C → ℝ≥0),
      (∀ x, a x ≤ b x ∧ Icc (a x) (b x) ⊆ (e x).target) ∧
      ∀ y : C, ∃ x ∈ t, y ∈ interior ((e x).symm '' Icc (a x) (b x)) := by
  classical
  let : CompactSpace C := isCompact_iff_compactSpace.mp hC
  choose e he using hM
  choose a b hab ht hx using fun x => exists_closed_chart_arc (e x) (he x)
  obtain ⟨t, hcover⟩ := isCompact_univ.elim_finite_subcover
    (fun x : C => interior ((e x).symm '' Icc (a x) (b x)))
    (fun _ => isOpen_interior) (fun x _ => mem_iUnion.mpr ⟨x, hx x⟩)
  refine ⟨t, e, a, b, fun x => ⟨hab x, ht x⟩, ?_⟩
  intro y
  obtain ⟨x, hx, hy⟩ := mem_iUnion₂.mp (hcover (mem_univ y))
  exact ⟨x, hx, hy⟩

/-- A closed chart arc has compact image. -/
theorem isCompact_closed_chart_arc (e : OpenPartialHomeomorph X ℝ≥0)
    {a b : ℝ≥0} (ht : Icc a b ⊆ e.target) :
    IsCompact (e.symm '' Icc a b) :=
  isCompact_Icc.image_of_continuousOn (e.symm.continuousOn.mono ht)

/-- The open part of a chart arc is open and preconnected. -/
theorem open_chart_arc_open_preconnected (e : OpenPartialHomeomorph X ℝ≥0)
    {a b : ℝ≥0} (ht : Icc a b ⊆ e.target) :
    IsOpen (e.symm '' Ioo a b) ∧ IsPreconnected (e.symm '' Ioo a b) := by
  have hsub : Ioo a b ⊆ e.target := Ioo_subset_Icc_self.trans ht
  exact ⟨e.isOpen_image_symm_of_subset_target isOpen_Ioo hsub,
    isPreconnected_Ioo.image _ (e.symm.continuousOn.mono hsub)⟩

/-- In a Hausdorff space, closing an open chart arc adds its two endpoints. -/
theorem closure_open_chart_arc [T2Space X] (e : OpenPartialHomeomorph X ℝ≥0)
    {a b : ℝ≥0} (hab : a < b) (ht : Icc a b ⊆ e.target) :
    closure (e.symm '' Ioo a b) = e.symm '' Icc a b := by
  apply Subset.antisymm
  · exact closure_minimal (image_mono Ioo_subset_Icc_self)
      (isCompact_closed_chart_arc e ht).isClosed
  · have hc : ContinuousOn e.symm (closure (Ioo a b)) := by
      rw [closure_Ioo hab.ne]
      exact e.symm.continuousOn.mono ht
    simpa only [closure_Ioo hab.ne] using hc.image_closure

/-- The complement of the open arc in the closed arc consists of two distinct points. -/
theorem closed_chart_arc_sdiff_open_chart_arc (e : OpenPartialHomeomorph X ℝ≥0)
    {a b : ℝ≥0} (hab : a < b) (ht : Icc a b ⊆ e.target) :
    (e.symm '' Icc a b) \ (e.symm '' Ioo a b) = {e.symm a, e.symm b} ∧
      e.symm a ≠ e.symm b := by
  have ha : a ∈ e.target := ht ⟨le_rfl, hab.le⟩
  have hb : b ∈ e.target := ht ⟨hab.le, le_rfl⟩
  constructor
  · apply Subset.antisymm
    · calc
        (e.symm '' Icc a b) \ (e.symm '' Ioo a b) ⊆
            e.symm '' (Icc a b \ Ioo a b) := subset_image_sdiff _ _ _
        _ = {e.symm a, e.symm b} := by rw [Icc_sdiff_Ioo_same hab.le, image_pair]
    · intro x hx
      rcases hx with rfl | hx
      · refine ⟨mem_image_of_mem _ ⟨le_rfl, hab.le⟩, ?_⟩
        rintro ⟨y, hy, heq⟩
        have hya := e.symm.injOn (ht ⟨hy.1.le, hy.2.le⟩) ha heq
        exact hy.1.ne hya.symm
      · have hxb : x = e.symm b := hx
        subst x
        refine ⟨mem_image_of_mem _ ⟨hab.le, le_rfl⟩, ?_⟩
        rintro ⟨y, hy, heq⟩
        have hyb := e.symm.injOn (ht ⟨hy.1.le, hy.2.le⟩) hb heq
        exact hy.2.ne hyb
  · exact fun h => hab.ne (e.symm.injOn ha hb h)

/-- An open chart arc avoiding `F`, with both endpoints in `F`, is an entire
connected component of the complement of `F`. -/
theorem open_chart_arc_eq_connectedComponentIn [T2Space X]
    (e : OpenPartialHomeomorph X ℝ≥0) {a b : ℝ≥0} (hab : a < b)
    (ht : Icc a b ⊆ e.target) {F : Set X}
    (ha : e.symm a ∈ F) (hb : e.symm b ∈ F)
    (havoid : e.symm '' Ioo a b ⊆ Fᶜ) {y : X}
    (hy : y ∈ e.symm '' Ioo a b) :
    e.symm '' Ioo a b = connectedComponentIn Fᶜ y := by
  obtain ⟨ho, hp⟩ := open_chart_arc_open_preconnected e ht
  apply Subset.antisymm (hp.subset_connectedComponentIn hy havoid)
  apply isPreconnected_connectedComponentIn.subset_of_closure_inter_subset ho
    ⟨y, mem_connectedComponentIn (havoid hy), hy⟩
  intro z hz
  by_contra hzA
  have hzK : z ∈ e.symm '' Icc a b := by
    simpa only [closure_open_chart_arc e hab ht] using hz.1
  have hzends : z ∈ ({e.symm a, e.symm b} : Set X) := by
    rw [← (closed_chart_arc_sdiff_open_chart_arc e hab ht).1]
    exact ⟨hzK, hzA⟩
  have hzF : z ∈ F := by
    rcases hzends with rfl | hzends
    · exact ha
    · exact hzends.symm ▸ hb
  exact connectedComponentIn_subset Fᶜ y hz.2 hzF

/-- A point outside a finite ordered set lies between consecutive elements,
provided that the set has an element on each side. -/
theorem exists_gap_of_finite {α : Type*} [LinearOrder α] {P : Set α}
    (hP : P.Finite) {a b q : α} (ha : a ∈ P) (hb : b ∈ P)
    (haq : a ≤ q) (hqb : q ≤ b) (hq : q ∉ P) :
    ∃ s r, s ∈ P ∧ r ∈ P ∧ a ≤ s ∧ r ≤ b ∧ s < q ∧ q < r ∧
      ∀ p ∈ Ioo s r, p ∉ P := by
  obtain ⟨s, hs, hmax⟩ := exists_max_image (P ∩ Iic q) id (hP.inter_of_left _)
    ⟨a, ha, haq⟩
  obtain ⟨r, hr, hmin⟩ := exists_min_image (P ∩ Ici q) id (hP.inter_of_left _)
    ⟨b, hb, hqb⟩
  have hsq : s < q := lt_of_le_of_ne hs.2 (fun he => hq (he ▸ hs.1))
  have hqr : q < r := lt_of_le_of_ne hr.2 (fun he => hq (he.symm ▸ hr.1))
  refine ⟨s, r, hs.1, hr.1, hmax a ⟨ha, haq⟩, hmin b ⟨hb, hqb⟩,
    hsq, hqr, ?_⟩
  intro p hp hpP
  rcases le_total p q with hpq | hqp
  · exact (not_le_of_gt hp.1) (hmax p ⟨hpP, hpq⟩)
  · exact (not_le_of_gt hp.2) (hmin p ⟨hpP, hqp⟩)

/-- Removing finitely many points from a closed chart arc leaves an open chart
arc around each remaining point, provided the two outer endpoints were removed.
This smaller arc is an entire component of the complement in the ambient space. -/
theorem exists_chart_arc_connectedComponentIn [T2Space X]
    {F : Set X} (hF : F.Finite) (e : OpenPartialHomeomorph X ℝ≥0)
    {a b : ℝ≥0} (ht : Icc a b ⊆ e.target)
    (ha : e.symm a ∈ F) (hb : e.symm b ∈ F)
    {y : X} (hy : y ∈ e.symm '' Icc a b) (hyF : y ∉ F) :
    ∃ s r : ℝ≥0, s < r ∧ Icc s r ⊆ e.target ∧
      e.symm s ∈ F ∧ e.symm r ∈ F ∧
      e.symm '' Ioo s r = connectedComponentIn Fᶜ y := by
  obtain ⟨q, hq, rfl⟩ := hy
  have hqa : a ∈ e.target := ht ⟨le_rfl, hq.1.trans hq.2⟩
  have hqb : b ∈ e.target := ht ⟨hq.1.trans hq.2, le_rfl⟩
  let P := e '' (F ∩ e.source)
  have hP : P.Finite := (hF.inter_of_left _).image e
  have haP : a ∈ P := ⟨e.symm a, ⟨ha, e.map_target hqa⟩, e.right_inv hqa⟩
  have hbP : b ∈ P := ⟨e.symm b, ⟨hb, e.map_target hqb⟩, e.right_inv hqb⟩
  have hqP : q ∉ P := by
    rintro ⟨z, hz, heq⟩
    have hzq : z = e.symm q := by
      rw [← heq, e.left_inv hz.2]
    exact hyF (hzq ▸ hz.1)
  obtain ⟨s, r, hsP, hrP, has, hrb, hsq, hqr, hgap⟩ :=
    exists_gap_of_finite hP haP hbP hq.1 hq.2 hqP
  have hsr : s < r := hsq.trans hqr
  have hsub : Icc s r ⊆ e.target := by
    intro z hz
    exact ht ⟨has.trans hz.1, hz.2.trans hrb⟩
  have hsF : e.symm s ∈ F := by
    obtain ⟨z, hz, rfl⟩ := hsP
    simpa only [e.left_inv hz.2] using hz.1
  have hrF : e.symm r ∈ F := by
    obtain ⟨z, hz, rfl⟩ := hrP
    simpa only [e.left_inv hz.2] using hz.1
  refine ⟨s, r, hsr, hsub, hsF, hrF,
    open_chart_arc_eq_connectedComponentIn e hsr hsub hsF hrF ?_
      (mem_image_of_mem _ ⟨hsq, hqr⟩)⟩
  rintro z ⟨p, hp, rfl⟩ hpF
  have hpt : p ∈ e.target := hsub ⟨hp.1.le, hp.2.le⟩
  exact hgap p hp ⟨e.symm p, ⟨hpF, e.map_target hpt⟩, e.right_inv hpt⟩

/-- There is a finite vertex set containing the manifold boundary such that every
component of its complement is an open chart arc with both endpoints among the
vertices. -/
theorem exists_finite_chart_arc_decomposition [T2Space X] {C : Set X}
    (hC : IsCompact C) (hM : IsOneManifoldWithBoundary C) :
    ∃ F : Set C, F.Finite ∧ (((↑) : C → X) ⁻¹' oneManifoldBoundary C) ⊆ F ∧
      ∀ y ∉ F, ∃ (e : OpenPartialHomeomorph C ℝ≥0) (s r : ℝ≥0),
        s < r ∧ Icc s r ⊆ e.target ∧ e.symm s ∈ F ∧ e.symm r ∈ F ∧
          e.symm '' Ioo s r = connectedComponentIn Fᶜ y := by
  classical
  obtain ⟨t, e, a, b, ht, hcover⟩ := exists_finite_closed_chart_arc_cover hC hM
  let B := ((↑) : C → X) ⁻¹' oneManifoldBoundary C
  have hB : B.Finite := (oneManifoldBoundary_finite hC hM).preimage
    Subtype.val_injective.injOn
  let F := (B ∪ (fun x => (e x).symm (a x)) '' (t : Set C)) ∪
    (fun x => (e x).symm (b x)) '' (t : Set C)
  have hF : F.Finite := (hB.union (t.finite_toSet.image _)).union
    (t.finite_toSet.image _)
  refine ⟨F, hF, fun _ h => Or.inl (Or.inl h), ?_⟩
  intro y hy
  obtain ⟨x, hx, hyx⟩ := hcover y
  have haF : (e x).symm (a x) ∈ F := Or.inl (Or.inr ⟨x, hx, rfl⟩)
  have hbF : (e x).symm (b x) ∈ F := Or.inr ⟨x, hx, rfl⟩
  obtain ⟨s, r, hsr, hsub, hsF, hrF, heq⟩ :=
    exists_chart_arc_connectedComponentIn hF (e x) (ht x).2 haF hbF
      (interior_subset hyx) hy
  exact ⟨e x, s, r, hsr, hsub, hsF, hrF, heq⟩

/-- A chart at a vertex can be restricted so that it contains no other vertex. -/
theorem exists_isolating_vertex_chart [T1Space X] {C : Set X}
    (hM : IsOneManifoldWithBoundary C) {F : Set C} (hF : F.Finite)
    {v : C} (hv : v ∈ F) :
    ∃ e : OpenPartialHomeomorph C ℝ≥0, v ∈ e.source ∧ e.source ∩ F = {v} := by
  obtain ⟨c, hc⟩ := hM v
  have ho : IsOpen (F \ {v})ᶜ := (hF.subset sdiff_subset).isClosed.isOpen_compl
  refine ⟨c.restr (F \ {v})ᶜ, ?_, ?_⟩
  · rw [c.restr_source' _ ho]
    exact ⟨hc, fun h => h.2 rfl⟩
  · rw [c.restr_source' _ ho]
    ext x
    constructor
    · intro hx
      have h : x = v := by
        by_contra hne
        exact hx.1.2 ⟨hx.2, hne⟩
      exact h
    · rintro rfl
      exact ⟨⟨hc, fun h => h.2 rfl⟩, hv⟩

/-- A right-hand closed interval can be chosen inside any half-line neighborhood. -/
theorem exists_right_interval_in_nhds {q : ℝ≥0} {U : Set ℝ≥0} (hU : U ∈ 𝓝 q) :
    ∃ r : ℝ≥0, q < r ∧ Icc q r ⊆ U := by
  obtain ⟨b, hqb, hb⟩ := exists_Ico_subset_of_mem_nhds hU (exists_gt q)
  obtain ⟨r, hqr, hrb⟩ := exists_between hqb
  exact ⟨r, hqr, fun _ hp => hb ⟨hp.1, hp.2.trans_lt hrb⟩⟩

/-- A positive coordinate also has a left-hand closed interval in every neighborhood. -/
theorem exists_left_interval_in_nhds {q : ℝ≥0} (hq : q ≠ 0)
    {U : Set ℝ≥0} (hU : U ∈ 𝓝 q) :
    ∃ l : ℝ≥0, l < q ∧ Icc l q ⊆ U := by
  have hqpos : 0 < q := lt_of_le_of_ne (zero_le : 0 ≤ q) hq.symm
  obtain ⟨a, haq, ha⟩ := exists_Ioc_subset_of_mem_nhds hU ⟨0, hqpos⟩
  obtain ⟨l, hal, hlq⟩ := exists_between haq
  exact ⟨l, hlq, fun _ hp => ha ⟨hal.trans_le hp.1, hp.2⟩⟩

/-- In a chart that isolates a vertex, intervals avoiding its coordinate avoid
all vertices. -/
theorem chart_interval_avoids_vertices (e : OpenPartialHomeomorph X ℝ≥0)
    {F : Set X} {v : X} (hF : e.source ∩ F = {v})
    {s : Set ℝ≥0} (hst : s ⊆ e.target) (hs : e v ∉ s) :
    e.symm '' s ⊆ Fᶜ := by
  rintro _ ⟨q, hq, rfl⟩ hqF
  have heq : e.symm q = v := by
    have : e.symm q ∈ e.source ∩ F := ⟨e.map_target (hst hq), hqF⟩
    simpa only [hF, mem_singleton_iff] using this
  have hqeq : q = e v := by
    rw [← heq, e.right_inv (hst hq)]
  exact hs (hqeq ▸ hq)

/-- The right side of an isolated vertex is a nonempty preconnected open set
avoiding all vertices, and accumulates at the vertex. -/
theorem exists_right_vertex_side [T2Space X] (e : OpenPartialHomeomorph X ℝ≥0)
    {F : Set X} {v : X} (hv : v ∈ e.source) (hF : e.source ∩ F = {v}) :
    ∃ r : ℝ≥0, e v < r ∧ Icc (e v) r ⊆ e.target ∧
      IsOpen (e.symm '' Ioo (e v) r) ∧
      IsConnected (e.symm '' Ioo (e v) r) ∧
      e.symm '' Ioo (e v) r ⊆ Fᶜ ∧
      v ∈ closure (e.symm '' Ioo (e v) r) := by
  obtain ⟨r, hvr, ht⟩ := exists_right_interval_in_nhds
    (e.open_target.mem_nhds (e.map_source hv))
  obtain ⟨ho, hp⟩ := open_chart_arc_open_preconnected e ht
  refine ⟨r, hvr, ht, ho, ⟨(nonempty_Ioo.mpr hvr).image _, hp⟩,
    chart_interval_avoids_vertices e hF (Ioo_subset_Icc_self.trans ht)
      (fun h => h.1.false), ?_⟩
  rw [closure_open_chart_arc e hvr ht]
  exact ⟨e v, ⟨le_rfl, hvr.le⟩, e.left_inv hv⟩

/-- The left side exists when the isolated vertex has nonzero chart coordinate. -/
theorem exists_left_vertex_side [T2Space X] (e : OpenPartialHomeomorph X ℝ≥0)
    {F : Set X} {v : X} (hv : v ∈ e.source) (hF : e.source ∩ F = {v})
    (hvzero : e v ≠ 0) :
    ∃ l : ℝ≥0, l < e v ∧ Icc l (e v) ⊆ e.target ∧
      IsOpen (e.symm '' Ioo l (e v)) ∧
      IsConnected (e.symm '' Ioo l (e v)) ∧
      e.symm '' Ioo l (e v) ⊆ Fᶜ ∧
      v ∈ closure (e.symm '' Ioo l (e v)) := by
  obtain ⟨l, hlv, ht⟩ := exists_left_interval_in_nhds hvzero
    (e.open_target.mem_nhds (e.map_source hv))
  obtain ⟨ho, hp⟩ := open_chart_arc_open_preconnected e ht
  refine ⟨l, hlv, ht, ho, ⟨(nonempty_Ioo.mpr hlv).image _, hp⟩,
    chart_interval_avoids_vertices e hF (Ioo_subset_Icc_self.trans ht)
      (fun h => h.2.false), ?_⟩
  rw [closure_open_chart_arc e hlv ht]
  exact ⟨e v, ⟨hlv.le, le_rfl⟩, e.left_inv hv⟩

/-- A chart transition cannot send both sides of an interior point into the
interior of an interval while sending the point itself to an endpoint. This is
the local obstruction to an arc receiving both ends at the same vertex. -/
theorem chart_transition_endpoint_obstruction
    (c e : OpenPartialHomeomorph X ℝ≥0) {v : X}
    (hv : v ∈ c.source) {a b s r : ℝ≥0}
    (ha : a < c v) (hb : c v < b)
    (ht : Icc a b ⊆ (c.symm.trans e).source)
    (hea : e (c.symm a) ∈ Ioo s r) (heb : e (c.symm b) ∈ Ioo s r)
    (hev : e v = s ∨ e v = r) : False := by
  let f := c.symm.trans e
  have hab : a ≤ b := (ha.trans hb).le
  have haI : a ∈ Icc a b := ⟨le_rfl, hab⟩
  have hbI : b ∈ Icc a b := ⟨hab, le_rfl⟩
  have hvI : c v ∈ Icc a b := ⟨ha.le, hb.le⟩
  have hfv : f (c v) = e v := by
    simp only [f, OpenPartialHomeomorph.trans_apply, c.left_inv hv]
  rcases (f.continuousOn.mono ht).strictMonoOn_of_injOn_Icc' hab
      (f.injOn.mono ht) with hm | hm
  · rcases hev with hev | hev
    · have h := hm haI hvI ha
      rw [hfv, hev] at h
      exact (not_lt_of_ge hea.1.le) h
    · have h := hm hvI hbI hb
      rw [hfv, hev] at h
      exact (not_lt_of_ge heb.2.le) h
  · rcases hev with hev | hev
    · have h := hm hvI hbI hb
      rw [hfv, hev] at h
      exact (not_lt_of_ge heb.1.le) h
    · have h := hm haI hvI ha
      rw [hfv, hev] at h
      exact (not_lt_of_ge hea.2.le) h

/-- A preconnected side meeting a component of `G` lies entirely in that component. -/
theorem vertex_side_subset_component {G S : Set X} (hS : IsPreconnected S)
    (hSG : S ⊆ G) {y : X} (hmeet : (S ∩ connectedComponentIn G y).Nonempty) :
    S ⊆ connectedComponentIn G y := by
  obtain ⟨z, hzS, hzC⟩ := hmeet
  rw [connectedComponentIn_eq hzC]
  exact hS.subset_connectedComponentIn hzS hSG

/-- A vertex with a side inside an arc must be one of its endpoints. -/
theorem vertex_side_base_is_arc_endpoint [T2Space X]
    (e : OpenPartialHomeomorph X ℝ≥0) {s r : ℝ≥0} (hsr : s < r)
    (ht : Icc s r ⊆ e.target) {F S : Set X} {v : X}
    (hv : v ∈ F) (havoid : e.symm '' Ioo s r ⊆ Fᶜ)
    (hS : S ⊆ e.symm '' Ioo s r) (hclosure : v ∈ closure S) :
    v = e.symm s ∨ v = e.symm r := by
  have hvcl : v ∈ closure (e.symm '' Ioo s r) := closure_mono hS hclosure
  rw [closure_open_chart_arc e hsr ht] at hvcl
  have hdiff : v ∈ (e.symm '' Icc s r) \ (e.symm '' Ioo s r) :=
    ⟨hvcl, fun h => havoid h hv⟩
  rw [(closed_chart_arc_sdiff_open_chart_arc e hsr ht).1] at hdiff
  exact hdiff

/-- An arc cannot contain both local sides of a vertex which is one of its endpoints. -/
theorem chart_arc_cannot_contain_both_vertex_sides
    (c e : OpenPartialHomeomorph X ℝ≥0) {v : X}
    (hvc : v ∈ c.source) (hve : v ∈ e.source) {l b s r : ℝ≥0}
    (hl : l < c v) (hb : c v < b) (ht : Icc s r ⊆ e.target)
    (hleft : c.symm '' Ioo l (c v) ⊆ e.symm '' Ioo s r)
    (hright : c.symm '' Ioo (c v) b ⊆ e.symm '' Ioo s r)
    (hev : e v = s ∨ e v = r) : False := by
  let f := c.symm.trans e
  have hvf : c v ∈ f.source := by
    refine ⟨c.map_source hvc, ?_⟩
    change c.symm (c v) ∈ e.source
    simpa only [c.left_inv hvc] using hve
  have hU : f.source ∩ Ioo l b ∈ 𝓝 (c v) :=
    (f.open_source.inter isOpen_Ioo).mem_nhds ⟨hvf, hl, hb⟩
  have hvzero : c v ≠ 0 := ne_of_gt ((zero_le : 0 ≤ l).trans_lt hl)
  obtain ⟨a, hav, haU⟩ := exists_left_interval_in_nhds hvzero hU
  obtain ⟨d, hvd, hdU⟩ := exists_right_interval_in_nhds hU
  have had : Icc a d ⊆ f.source := by
    rw [← Icc_union_Icc_eq_Icc hav.le hvd.le]
    exact union_subset (fun _ h => (haU h).1) (fun _ h => (hdU h).1)
  have hea : e (c.symm a) ∈ Ioo s r := by
    have haL : a ∈ Ioo l (c v) := ⟨(haU ⟨le_rfl, hav.le⟩).2.1, hav⟩
    obtain ⟨q, hq, heq⟩ := hleft (mem_image_of_mem _ haL)
    rw [← heq, e.right_inv (ht ⟨hq.1.le, hq.2.le⟩)]
    exact hq
  have hed : e (c.symm d) ∈ Ioo s r := by
    have hdR : d ∈ Ioo (c v) b := ⟨hvd, (hdU ⟨hvd.le, le_rfl⟩).2.2⟩
    obtain ⟨q, hq, heq⟩ := hright (mem_image_of_mem _ hdR)
    rw [← heq, e.right_inv (ht ⟨hq.1.le, hq.2.le⟩)]
    exact hq
  exact chart_transition_endpoint_obstruction c e hvc hav hvd had hea hed hev

/-- The two local sides together with their base point form a neighborhood.
At coordinate zero, the right side alone suffices. -/
theorem vertex_sides_mem_nhds (e : OpenPartialHomeomorph X ℝ≥0)
    {v : X} (hv : v ∈ e.source) {l r : ℝ≥0}
    (hl : l < e v ∨ e v = 0) (hr : e v < r) :
    ({v} ∪ (e.symm '' Ioo l (e v)) ∪ (e.symm '' Ioo (e v) r)) ∈ 𝓝 v := by
  rcases hl with hl | hzero
  · have hn := e.symm.image_mem_nhds (e.map_source hv) (Ioo_mem_nhds hl hr)
    rw [e.left_inv hv] at hn
    apply mem_of_superset hn
    rintro _ ⟨q, hq, rfl⟩
    rcases lt_trichotomy q (e v) with hlt | heq | hgt
    · exact Or.inl (Or.inr (mem_image_of_mem _ ⟨hq.1, hlt⟩))
    · exact Or.inl (Or.inl (by simpa only [heq, e.left_inv hv] using mem_singleton v))
    · exact Or.inr (mem_image_of_mem _ ⟨hgt, hq.2⟩)
  · have hn := e.symm.image_mem_nhds (e.map_source hv) (Iio_mem_nhds hr)
    rw [e.left_inv hv] at hn
    apply mem_of_superset hn
    rintro _ ⟨q, hq, rfl⟩
    by_cases heq : q = e v
    · exact Or.inl (Or.inl (by simpa only [heq, e.left_inv hv] using mem_singleton v))
    · have hgt : e v < q := lt_of_le_of_ne (by rw [hzero]; exact zero_le) (Ne.symm heq)
      exact Or.inr (mem_image_of_mem _ ⟨hgt, hq⟩)

/-- Every set accumulating at a vertex without containing it meets at least one
of the vertex's two local sides. -/
theorem vertex_sides_meet_of_mem_closure (e : OpenPartialHomeomorph X ℝ≥0)
    {v : X} (hv : v ∈ e.source) {l r : ℝ≥0}
    (hl : l < e v ∨ e v = 0) (hr : e v < r) {A : Set X}
    (hvcl : v ∈ closure A) (hvA : v ∉ A) :
    (A ∩ (e.symm '' Ioo l (e v))).Nonempty ∨
      (A ∩ (e.symm '' Ioo (e v) r)).Nonempty := by
  obtain ⟨x, hx, hxA⟩ := mem_closure_iff_nhds.mp hvcl _
    (vertex_sides_mem_nhds e hv hl hr)
  rcases hx with (hx | hx) | hx
  · have hxv : x = v := hx
    exact False.elim (hvA (hxv ▸ hxA))
  · exact Or.inl ⟨x, hxA, hx⟩
  · exact Or.inr ⟨x, hxA, hx⟩

/-- The finite set of potential ends: a right end at every vertex and a left end
at every vertex outside the distinguished boundary subset. -/
def handshakeEnds {α : Type*} (F B : Finset α) : Finset (α × Bool) := by
  classical
  exact (F ×ˢ {true}) ∪ ((F \ B) ×ˢ {false})

/-- The number of ends is the boundary cardinality plus twice the number of
remaining vertices. -/
theorem card_handshakeEnds {α : Type*} (F B : Finset α) (hBF : B ⊆ F) :
    (handshakeEnds F B).card = B.card + 2 * (F \ B).card := by
  classical
  have hd : Disjoint (F ×ˢ ({true} : Finset Bool)) ((F \ B) ×ˢ {false}) := by
    apply Finset.disjoint_left.mpr
    intro x hx hy
    have hxtrue : x.2 = true := Finset.mem_singleton.mp (Finset.mem_product.mp hx).2
    have hxfalse : x.2 = false := Finset.mem_singleton.mp (Finset.mem_product.mp hy).2
    exact Bool.noConfusion (hxtrue.symm.trans hxfalse)
  rw [handshakeEnds, Finset.card_union_of_disjoint hd]
  simp only [Finset.card_product, Finset.card_singleton, mul_one]
  have hcard := Finset.card_sdiff_add_card_eq_card hBF
  omega

/-- The finite counting step of the handshake argument. Once an end map has
two-element fibers over its image, the distinguished boundary has even cardinality. -/
theorem even_card_of_handshake_fibers {α β : Type*} (F B : Finset α)
    (hBF : B ⊆ F) (f : α × Bool → β)
    (hf : ∀ b ∈ (handshakeEnds F B).image f,
      ((handshakeEnds F B).filter (fun a => f a = b)).card = 2) :
    Even B.card := by
  classical
  have hcount : (handshakeEnds F B).card =
      2 * ((handshakeEnds F B).image f).card := by
    calc
      _ = ∑ b ∈ (handshakeEnds F B).image f,
          ((handshakeEnds F B).filter (fun a => f a = b)).card :=
        Finset.card_eq_sum_card_image f _
      _ = ∑ _b ∈ (handshakeEnds F B).image f, 2 :=
        Finset.sum_congr rfl hf
      _ = _ := by simp [mul_comm]
  rw [card_handshakeEnds F B hBF] at hcount
  refine ⟨((handshakeEnds F B).image f).card - (F \ B).card, ?_⟩
  omega

/-- Simultaneous choices of isolating charts and left/right coordinate intervals. -/
theorem exists_handshake_vertex_coordinates {C : Set X}
    [T1Space X] (hM : IsOneManifoldWithBoundary C) {F : Set C} (hF : F.Finite) :
    ∃ (e : C → OpenPartialHomeomorph C ℝ≥0) (l r : C → ℝ≥0),
      (∀ v, v ∈ (e v).source) ∧
      (∀ v ∈ F, (e v).source ∩ F = {v}) ∧
      (∀ v, l v < e v v ∨ e v v = 0) ∧
      (∀ v, e v v < r v) ∧
      (∀ v, Icc (l v) (e v v) ⊆ (e v).target) ∧
      (∀ v, Icc (e v v) (r v) ⊆ (e v).target) := by
  have hc : ∀ v : C, ∃ e : OpenPartialHomeomorph C ℝ≥0,
      v ∈ e.source ∧ (v ∈ F → e.source ∩ F = {v}) := by
    intro v
    by_cases hv : v ∈ F
    · obtain ⟨e, he, his⟩ := exists_isolating_vertex_chart hM hF hv
      exact ⟨e, he, fun _ => his⟩
    · obtain ⟨e, he⟩ := hM v
      exact ⟨e, he, fun h => False.elim (hv h)⟩
  choose e he his using hc
  choose r hr hrt using fun v => exists_right_interval_in_nhds
    ((e v).open_target.mem_nhds ((e v).map_source (he v)))
  have hleft : ∀ v : C, ∃ l : ℝ≥0,
      (l < e v v ∨ e v v = 0) ∧ Icc l (e v v) ⊆ (e v).target := by
    intro v
    by_cases hz : e v v = 0
    · refine ⟨0, Or.inr hz, ?_⟩
      simpa [hz] using (e v).map_source (he v)
    · obtain ⟨l, hl, hlt⟩ := exists_left_interval_in_nhds hz
        ((e v).open_target.mem_nhds ((e v).map_source (he v)))
      exact ⟨l, Or.inl hl, hlt⟩
  choose l hl hlt using hleft
  exact ⟨e, l, r, he, his, hl, hr, hlt, hrt⟩

/-- The boundary of a compact Hausdorff one-manifold with boundary has even cardinality. -/
theorem even_ncard_oneManifoldBoundary {X : Type*} [TopologicalSpace X] [T2Space X]
    {C : Set X} (hC : IsCompact C) (hM : IsOneManifoldWithBoundary C) :
    Even (oneManifoldBoundary C).ncard := by
  classical
  obtain ⟨F, hF, hBF, hdecomp⟩ := exists_finite_chart_arc_decomposition hC hM
  let B := ((↑) : C → X) ⁻¹' oneManifoldBoundary C
  have hB : B.Finite := (oneManifoldBoundary_finite hC hM).preimage
    Subtype.val_injective.injOn
  let FF := hF.toFinset
  let BB := hB.toFinset
  have hBFfin : BB ⊆ FF := by
    intro v hv
    exact hF.mem_toFinset.mpr (hBF (hB.mem_toFinset.mp hv))
  let E := handshakeEnds FF BB
  have hmem (p : C × Bool) : p ∈ E ↔
      p.1 ∈ F ∧ (p.2 = true ∨ (p.1 : X) ∉ oneManifoldBoundary C) := by
    rcases p with ⟨v, b⟩
    cases b <;> simp [E, handshakeEnds, FF, BB, B]
  obtain ⟨e, l, r, he, his, hl, hr, hlt, hrt⟩ :=
    exists_handshake_vertex_coordinates hM hF
  -- The Boolean records the right side (`true`) or left side (`false`).
  let S : C × Bool → Set C := fun p =>
    if p.2 = true then (e p.1).symm '' Ioo (e p.1 p.1) (r p.1)
    else (e p.1).symm '' Ioo (l p.1) (e p.1 p.1)
  have hS : ∀ p ∈ E, IsConnected (S p) ∧ S p ⊆ Fᶜ ∧ p.1 ∈ closure (S p) := by
    rintro ⟨v, b⟩ hp
    have hp' := (hmem (v, b)).mp hp
    cases b with
    | false =>
      have hvn : (v : X) ∉ oneManifoldBoundary C := hp'.2.resolve_left (by simp)
      have hqne : e v v ≠ 0 :=
        (oneManifoldBoundary_mem_iff_chart_eq_zero (e v) (he v)).not.mp hvn
      have hlv : l v < e v v := (hl v).resolve_right hqne
      change IsConnected ((e v).symm '' Ioo (l v) (e v v)) ∧ _
      refine ⟨⟨(nonempty_Ioo.mpr hlv).image _,
        (open_chart_arc_open_preconnected (e v) (hlt v)).2⟩,
        chart_interval_avoids_vertices (e v) (his v hp'.1)
          (Ioo_subset_Icc_self.trans (hlt v)) (fun h => h.2.false), ?_⟩
      change v ∈ closure ((e v).symm '' Ioo (l v) (e v v))
      rw [closure_open_chart_arc (e v) hlv (hlt v)]
      exact ⟨e v v, ⟨hlv.le, le_rfl⟩, (e v).left_inv (he v)⟩
    | true =>
      change IsConnected ((e v).symm '' Ioo (e v v) (r v)) ∧ _
      refine ⟨⟨(nonempty_Ioo.mpr (hr v)).image _,
        (open_chart_arc_open_preconnected (e v) (hrt v)).2⟩,
        chart_interval_avoids_vertices (e v) (his v hp'.1)
          (Ioo_subset_Icc_self.trans (hrt v)) (fun h => h.1.false), ?_⟩
      change v ∈ closure ((e v).symm '' Ioo (e v v) (r v))
      rw [closure_open_chart_arc (e v) (hr v) (hrt v)]
      exact ⟨e v v, ⟨le_rfl, (hr v).le⟩, (e v).left_inv (he v)⟩
  have hfalse (v : C) (hv : (v : X) ∈ oneManifoldBoundary C) :
      S (v, false) = ∅ := by
    have hz := oneManifoldBoundary_chart_eq_zero hv (e v) (he v)
    simp [S, hz]
  let point : C × Bool → C := fun p => if h : (S p).Nonempty then h.choose else p.1
  have hpoint (p : C × Bool) (hp : p ∈ E) : point p ∈ S p := by
    have hn := (hS p hp).1.nonempty
    simpa only [point, dite_eq_left hn] using hn.choose_spec
  let f : C × Bool → Set C := fun p => connectedComponentIn Fᶜ (point p)
  have hsub (p : C × Bool) (hp : p ∈ E) : S p ⊆ f p :=
    (hS p hp).1.isPreconnected.subset_connectedComponentIn (hpoint p hp) (hS p hp).2.1
  have hf : ∀ A ∈ E.image f, (E.filter (fun p => f p = A)).card = 2 := by
    -- Projection to the base vertex identifies this fiber with the two arc endpoints.
    intro A hA
    obtain ⟨p, hp, hfp⟩ := Finset.mem_image.mp hA
    have hyp : point p ∉ F := (hS p hp).2.1 (hpoint p hp)
    obtain ⟨d, a, b, hab, ht, haF, hbF, hArc⟩ := hdecomp (point p) hyp
    have hArcA : d.symm '' Ioo a b = A := hArc.trans hfp
    have havoid : A ⊆ Fᶜ := by
      rw [← hfp]
      exact connectedComponentIn_subset Fᶜ (point p)
    let T := E.filter (fun q => f q = A)
    have hsideA (q : C × Bool) (hq : q ∈ T) : S q ⊆ A := by
      obtain ⟨hqE, hqA⟩ := Finset.mem_filter.mp hq
      exact hqA ▸ hsub q hqE
    have hbase (q : C × Bool) (hq : q ∈ T) :
        q.1 = d.symm a ∨ q.1 = d.symm b := by
      have hqE := (Finset.mem_filter.mp hq).1
      apply vertex_side_base_is_arc_endpoint d hab ht ((hmem q).mp hqE).1
        (by simpa only [hArcA] using havoid)
        (by simpa only [hArcA] using hsideA q hq) (hS q hqE).2.2
    have hnotboth (v : C)
        (hvn : (v : X) ∉ oneManifoldBoundary C)
        (hvend : v = d.symm a ∨ v = d.symm b)
        (hleft : S (v, false) ⊆ A) (hright : S (v, true) ⊆ A) : False := by
      have hqne : e v v ≠ 0 :=
        (oneManifoldBoundary_mem_iff_chart_eq_zero (e v) (he v)).not.mp hvn
      have hvev : v ∈ d.source ∧ (d v = a ∨ d v = b) := by
        rcases hvend with rfl | rfl
        · exact ⟨d.map_target (ht ⟨le_rfl, hab.le⟩),
            Or.inl (d.right_inv (ht ⟨le_rfl, hab.le⟩))⟩
        · exact ⟨d.map_target (ht ⟨hab.le, le_rfl⟩),
            Or.inr (d.right_inv (ht ⟨hab.le, le_rfl⟩))⟩
      apply chart_arc_cannot_contain_both_vertex_sides (e v) d (he v) hvev.1
        ((hl v).resolve_right hqne) (hr v) ht
        (by simpa only [S, Bool.false_eq_true, ↓reduceIte, hArcA] using hleft)
        (by simpa only [S, ↓reduceIte, hArcA] using hright) hvev.2
    have hinj : Set.InjOn Prod.fst (T : Set (C × Bool)) := by
      rintro ⟨v, bv⟩ hv ⟨w, bw⟩ hw hvw
      change v = w at hvw
      subst w
      cases bv with
      | false =>
        cases bw with
        | false => rfl
        | true =>
          have hv' := (hmem (v, false)).mp (Finset.mem_filter.mp hv).1
          exact False.elim (hnotboth v (hv'.2.resolve_left (by simp))
            (hbase (v, false) hv) (hsideA (v, false) hv) (hsideA (v, true) hw))
      | true =>
        cases bw with
        | false =>
          have hw' := (hmem (v, false)).mp (Finset.mem_filter.mp hw).1
          exact False.elim (hnotboth v (hw'.2.resolve_left (by simp))
            (hbase (v, false) hw) (hsideA (v, false) hw) (hsideA (v, true) hv))
        | true => rfl
    have hproduce (v : C) (c : Bool) (hvc : (v, c) ∈ E)
        (hmeet : (A ∩ S (v, c)).Nonempty) : v ∈ T.image Prod.fst := by
      obtain ⟨z, hzA, hzS⟩ := hmeet
      have hzq : z ∈ f (v, c) := hsub (v, c) hvc hzS
      have hzp : z ∈ f p := hfp.symm ▸ hzA
      have hfq : f (v, c) = A := calc
        f (v, c) = connectedComponentIn Fᶜ z := connectedComponentIn_eq hzq
        _ = f p := (connectedComponentIn_eq hzp).symm
        _ = A := hfp
      exact Finset.mem_image.mpr ⟨(v, c), Finset.mem_filter.mpr ⟨hvc, hfq⟩, rfl⟩
    have himage : T.image Prod.fst = {d.symm a, d.symm b} := by
      apply Finset.Subset.antisymm
      · intro v hv
        obtain ⟨q, hq, rfl⟩ := Finset.mem_image.mp hv
        simpa only [Finset.mem_insert, Finset.mem_singleton] using hbase q hq
      · intro v hv
        have hvend : v = d.symm a ∨ v = d.symm b := by
          simpa only [Finset.mem_insert, Finset.mem_singleton] using hv
        have hvF : v ∈ F := hvend.elim (fun h => h.symm ▸ haF) (fun h => h.symm ▸ hbF)
        have hvcl : v ∈ closure A := by
          rw [← hArcA, closure_open_chart_arc d hab ht]
          rcases hvend with rfl | rfl
          · exact mem_image_of_mem _ ⟨le_rfl, hab.le⟩
          · exact mem_image_of_mem _ ⟨hab.le, le_rfl⟩
        have hvA : v ∉ A := fun h => havoid h hvF
        have hmeet := vertex_sides_meet_of_mem_closure (e v) (he v) (hl v) (hr v) hvcl hvA
        change (A ∩ S (v, false)).Nonempty ∨ (A ∩ S (v, true)).Nonempty at hmeet
        rcases hmeet with hmeet | hmeet
        · have hvn : (v : X) ∉ oneManifoldBoundary C := by
            intro hvB
            simp only [hfalse v hvB, inter_empty, Set.not_nonempty_empty] at hmeet
          exact hproduce v false ((hmem (v, false)).mpr ⟨hvF, Or.inr hvn⟩) hmeet
        · exact hproduce v true ((hmem (v, true)).mpr ⟨hvF, Or.inl rfl⟩) hmeet
    change T.card = 2
    rw [← Finset.card_image_of_injOn hinj, himage]
    exact Finset.card_pair_eq_two_iff.mpr (closed_chart_arc_sdiff_open_chart_arc d hab ht).2
  have heven : Even BB.card := even_card_of_handshake_fibers FF BB hBFfin f hf
  rw [← ncard_eq_toFinset_card B hB] at heven
  simpa only [B, oneManifoldBoundary_subtype_ncard] using heven

end LiquidDrop

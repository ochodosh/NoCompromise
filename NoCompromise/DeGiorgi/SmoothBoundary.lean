import NoCompromise.DeGiorgi.SmoothGraph
import NoCompromise.DeGiorgi.AmbientPolar
import NoCompromise.Sobolev.RelativeCubes

/-!
# C¹ boundary charts and classical perimeter

The geometric boundary condition is a local one-sided graph condition in rigid
coordinates. The graph height may be extended away from the local chart by a
compact cutoff; no global regularity or finite-perimeter premise is imposed on
the original domain.
-/

noncomputable section
open MeasureTheory Set Filter Metric Topology InnerProductSpace
open scoped Topology ENNReal NNReal Gradient
namespace LiquidDrop
set_option maxSynthPendingDepth 8

/-- Relative perimeter is invariant under a rigid change of coordinates on a
finite-volume open region. -/
lemma perimeterIn_preimage_affineIsometry_eq {n : ℕ}
    {D : Set (EuclideanSpace ℝ (Fin n))} (hD : IsOpen D) (hvol : volume D ≠ ∞)
    (a : EuclideanSpace ℝ (Fin n) ≃ᵃⁱ[ℝ] EuclideanSpace ℝ (Fin n))
    {E : Set (EuclideanSpace ℝ (Fin n))} (hE : NullMeasurableSet E volume) :
    perimeterIn (a ⁻¹' E) D = perimeterIn E (a '' D) := by
  apply le_antisymm (perimeterIn_preimage_affineIsometry_le hD hvol a hE)
  have ho : IsOpen (a '' D) := a.toHomeomorph.isOpenMap D hD
  have hv : volume (a '' D) ≠ ∞ := by rwa [volume_image_affineIsometry]
  have h := perimeterIn_preimage_affineIsometry_le ho hv a.symm
    (hE.preimage (measurePreserving_affineIsometry a).quasiMeasurePreserving)
  have heq : a.symm ⁻¹' (a ⁻¹' E) = E := by ext x; simp
  have hD' : a.symm '' (a '' D) = D := by rw [image_image]; simp
  simpa only [heq, hD'] using h

/-- Normalized Hausdorff area on a rigidly moved set is the pushforward area. -/
lemma hausdorffMeasure2_restrict_affineIsometry_image
    (a : AmbientSpace ≃ᵃⁱ[ℝ] AmbientSpace) (S : Set AmbientSpace) :
    (hausdorffMeasure2 3).restrict (a '' S) =
      Measure.map a ((hausdorffMeasure2 3).restrict S) := by
  ext B hB
  rw [Measure.restrict_apply hB, Measure.map_apply a.continuous.measurable hB,
    Measure.restrict_apply (hB.preimage a.continuous.measurable)]
  rw [show B ∩ a '' S = a '' (a ⁻¹' B ∩ S) from (image_preimage_inter _ _ _).symm]
  exact a.isometry.euclideanHausdorffMeasure_image _

/-- A bounded open neighborhood in rigid graph coordinates. -/
structure C1BoundaryChart where
  height : EuclideanSpace ℝ (Fin 2) → ℝ
  height_contDiff : ContDiff ℝ 1 height
  placement : AmbientSpace ≃ᵃⁱ[ℝ] AmbientSpace
  region : Set AmbientSpace
  isOpen_region : IsOpen region
  bounded_region : Bornology.IsBounded region

/-- The domain occupies the subgraph side inside the chart neighborhood. -/
def C1BoundaryChart.IsChartFor (c : C1BoundaryChart) (E : Set AmbientSpace) : Prop :=
  ∀ z ∈ c.region, z ∈ E ↔ c.placement.symm z ∈ smoothSubgraph c.height

/-- Every topological boundary point has a one-sided C¹ graph neighborhood. -/
def HasC1Boundary (E : Set AmbientSpace) : Prop :=
  ∀ x ∈ frontier E, ∃ c : C1BoundaryChart, c.IsChartFor E ∧ x ∈ c.region

/-- The complete graph domain in the chart's ambient placement. -/
def C1BoundaryChart.graphDomain (c : C1BoundaryChart) : Set AmbientSpace :=
  c.placement '' smoothSubgraph c.height

/-- The complete graph surface in the chart's ambient placement. -/
def C1BoundaryChart.graphSurface (c : C1BoundaryChart) : Set AmbientSpace :=
  c.placement '' range (graphMapN c.height)

lemma C1BoundaryChart.isOpen_graphDomain (c : C1BoundaryChart) : IsOpen c.graphDomain :=
  c.placement.toHomeomorph.isOpenMap _ (isOpen_smoothSubgraph c.height_contDiff.continuous)

lemma C1BoundaryChart.frontier_graphDomain (c : C1BoundaryChart) :
    frontier c.graphDomain = c.graphSurface := by
  change frontier (c.placement.toHomeomorph '' smoothSubgraph c.height) = _
  rw [← c.placement.toHomeomorph.image_frontier,
    frontier_smoothSubgraph c.height_contDiff.continuous]
  rfl

lemma C1BoundaryChart.IsChartFor.inter_eq {c : C1BoundaryChart} {E : Set AmbientSpace}
    (hc : c.IsChartFor E) : E ∩ c.region = c.graphDomain ∩ c.region := by
  ext z
  simp only [mem_inter_iff]
  constructor
  · rintro ⟨hz, hr⟩
    exact ⟨⟨c.placement.symm z, (hc z hr).mp hz, c.placement.apply_symm_apply z⟩, hr⟩
  · rintro ⟨⟨y, hy, rfl⟩, hr⟩
    exact ⟨(hc _ hr).mpr (by simpa using hy), hr⟩

lemma C1BoundaryChart.IsChartFor.frontier_inter_eq {c : C1BoundaryChart}
    {E : Set AmbientSpace} (hc : c.IsChartFor E) :
    frontier E ∩ c.region = c.graphSurface ∩ c.region := by
  have h := congrArg (fun S : Set AmbientSpace => frontier S ∩ c.region) hc.inter_eq
  simpa only [frontier_inter_open_inter c.isOpen_region, c.frontier_graphDomain] using h

/-- Perimeter in a rigid graph chart is the actual area of the topological boundary. -/
theorem C1BoundaryChart.IsChartFor.perimeterIn_eq {c : C1BoundaryChart}
    {E O : Set AmbientSpace} (hc : c.IsChartFor E)
    (hO : IsOpen O) (hOc : O ⊆ c.region) :
    perimeterIn E O = hausdorffMeasure2 3 (O ∩ frontier E) := by
  have hvol : volume O ≠ ∞ :=
    (lt_of_le_of_lt (measure_mono hOc) c.bounded_region.measure_lt_top).ne
  have heq : E =ᵐ[volume.restrict O] c.graphDomain := by
    filter_upwards [ae_restrict_mem hO.measurableSet] with z hz
    apply propext
    refine (hc z (hOc hz)).trans ?_
    change c.placement.symm z ∈ smoothSubgraph c.height ↔
      z ∈ c.placement '' smoothSubgraph c.height
    constructor
    · intro hz'
      exact ⟨c.placement.symm z, hz', c.placement.apply_symm_apply z⟩
    · rintro ⟨y, hy, rfl⟩
      simpa using hy
  rw [perimeterIn_congr_ae O heq]
  have hpre : c.placement ⁻¹' c.graphDomain = smoothSubgraph c.height := by
    exact preimage_image_eq _ c.placement.injective
  have him : c.placement '' (c.placement ⁻¹' O) = O :=
    image_preimage_eq _ c.placement.surjective
  have hv : volume (c.placement ⁻¹' O) ≠ ∞ := by
    rw [← volume_image_affineIsometry c.placement (c.placement ⁻¹' O), him]
    exact hvol
  have hp := perimeterIn_preimage_affineIsometry_eq (hO.preimage c.placement.continuous) hv
    c.placement c.isOpen_graphDomain.measurableSet.nullMeasurableSet
  rw [hpre, him, perimeterIn_smoothSubgraph c.height_contDiff
    (hO.preimage c.placement.continuous)] at hp
  rw [← hp, smoothGraphArea,
    Measure.restrict_apply (hO.preimage c.placement.continuous).measurableSet]
  have hs : O ∩ frontier E =
      c.placement '' (c.placement ⁻¹' O ∩ range (graphMapN c.height)) := by
    rw [image_preimage_inter]
    change O ∩ frontier E = O ∩ c.graphSurface
    ext z
    constructor
    · rintro ⟨hz, hb⟩
      exact ⟨hz, (hc.frontier_inter_eq ▸ (show z ∈ frontier E ∩ c.region from ⟨hb, hOc hz⟩)).1⟩
    · rintro ⟨hz, hb⟩
      exact ⟨hz, (hc.frontier_inter_eq.symm ▸
        (show z ∈ c.graphSurface ∩ c.region from ⟨hb, hOc hz⟩)).1⟩
  rw [hs]
  exact (c.placement.isometry.euclideanHausdorffMeasure_image _).symm

/-- The geometric outward normal obtained from the graph and its rigid placement. -/
def C1BoundaryChart.outwardNormal (c : C1BoundaryChart) (z : AmbientSpace) : AmbientSpace :=
  c.placement.linearIsometryEquiv (smoothSubgraphNormal c.height (c.placement.symm z))

lemma C1BoundaryChart.continuous_outwardNormal (c : C1BoundaryChart) :
    Continuous c.outwardNormal :=
  c.placement.linearIsometryEquiv.continuous.comp
    ((continuous_smoothSubgraphNormal c.height_contDiff).comp c.placement.symm.continuous)

lemma C1BoundaryChart.norm_outwardNormal (c : C1BoundaryChart) (z : AmbientSpace) :
    ‖c.outwardNormal z‖ = 1 := by
  rw [outwardNormal, c.placement.linearIsometryEquiv.norm_map]
  exact norm_smoothGraphUnitNormal _

lemma C1BoundaryChart.graphArea_regular (c : C1BoundaryChart) :
    ((hausdorffMeasure2 3).restrict c.graphSurface).Regular := by
  let : ((hausdorffMeasure2 3).restrict (range (graphMapN c.height))).Regular :=
    smoothGraphArea_regular c.height_contDiff
  rw [graphSurface, hausdorffMeasure2_restrict_affineIsometry_image]
  exact Measure.Regular.map c.placement.toHomeomorph

/-- Local heights need not be defined smoothly away from their open base. A
compact cutoff produces the equivalent global-height chart realization. -/
theorem hasC1Boundary_of_local_graphs {E : Set AmbientSpace}
    (h : ∀ x ∈ frontier E,
      ∃ (a : AmbientSpace ≃ᵃⁱ[ℝ] AmbientSpace) (f : EuclideanSpace ℝ (Fin 2) → ℝ)
        (U : Set (EuclideanSpace ℝ (Fin 2))) (W : Set AmbientSpace),
        IsOpen U ∧ ContDiffOn ℝ 1 f U ∧ graphProjectionN 2 (a.symm x) ∈ U ∧
        IsOpen W ∧ x ∈ W ∧
        ∀ z ∈ W, z ∈ E ↔ a.symm z (Fin.last 2) < f (graphProjectionN 2 (a.symm z))) :
    HasC1Boundary E := by
  intro x hx
  obtain ⟨a, f, U, W, hU, hf, hxU, hW, hxW, hgraph⟩ := h x hx
  obtain ⟨g, hg, hgf⟩ := exists_contDiff_height_eq_near_compact hU
    (isCompact_singleton (x := graphProjectionN 2 (a.symm x))) (singleton_subset_iff.mpr hxU) hf
  have hnear := hgf _ (mem_singleton _)
  obtain ⟨V, hV, hVo, hxV⟩ := _root_.mem_nhds_iff.mp hnear
  let N := W ∩ (fun z => graphProjectionN 2 (a.symm z)) ⁻¹' V ∩ ball x 1
  have hN : IsOpen N :=
    (hW.inter (hVo.preimage ((graphProjectionN 2).continuous.comp a.symm.continuous))).inter
      isOpen_ball
  let c : C1BoundaryChart := ⟨g, hg, a, N, hN, isBounded_ball.subset inter_subset_right⟩
  refine ⟨c, ?_, ⟨⟨hxW, hxV⟩, mem_ball_self zero_lt_one⟩⟩
  intro z hz
  rw [hgraph z hz.1.1]
  change (a.symm z (Fin.last 2) < f (graphProjectionN 2 (a.symm z))) ↔
    a.symm z (Fin.last 2) < g (graphProjectionN 2 (a.symm z))
  rw [hV hz.1.2]

lemma perimeterIn_eq_zero_of_subset {n : ℕ}
    {E O : Set (EuclideanSpace ℝ (Fin n))} (hE : NullMeasurableSet E volume)
    (hO : IsOpen O) (hOE : O ⊆ E) : perimeterIn E O = 0 := by
  rw [← perimeterIn_compl hE hO]
  exact perimeterIn_eq_zero_of_disjoint hO.measurableSet
    (disjoint_compl_left.mono_right hOE)

/-- Every point has a bounded open neighborhood on which relative perimeter
equals boundary area on all open subregions, and both masses are finite. -/
theorem HasC1Boundary.exists_local_perimeter_area {E : Set AmbientSpace}
    (h : HasC1Boundary E) (hE : IsOpen E) (x : AmbientSpace) :
    ∃ V : Set AmbientSpace, IsOpen V ∧ x ∈ V ∧
      hausdorffMeasure2 3 (V ∩ frontier E) < ∞ ∧
      ∀ O, IsOpen O → O ⊆ V → perimeterIn E O = hausdorffMeasure2 3 (O ∩ frontier E) := by
  by_cases hx : x ∈ frontier E
  · obtain ⟨c, hc, hxc⟩ := h x hx
    let := c.graphArea_regular
    refine ⟨c.region, c.isOpen_region, hxc, ?_, fun O hO hOc => hc.perimeterIn_eq hO hOc⟩
    have hregion : c.region ∩ frontier E = c.region ∩ c.graphSurface := by
      simpa only [inter_comm] using hc.frontier_inter_eq
    rw [hregion, ← Measure.restrict_apply c.isOpen_region.measurableSet]
    exact c.bounded_region.measure_lt_top
  · by_cases hxE : x ∈ E
    · let V := E ∩ ball x 1
      have hV : IsOpen V := hE.inter isOpen_ball
      have hdis : Disjoint V (frontier E) := by
        rw [Set.disjoint_iff_inter_eq_empty]
        apply eq_empty_of_subset_empty
        calc
          V ∩ frontier E ⊆ E ∩ frontier E := inter_subset_inter_left _ inter_subset_left
          _ = ∅ := hE.inter_frontier_eq
      refine ⟨V, hV, ⟨hxE, mem_ball_self zero_lt_one⟩, ?_, ?_⟩
      · rw [hdis.inter_eq, measure_empty]
        exact ENNReal.zero_lt_top
      · intro O hO hOV
        rw [perimeterIn_eq_zero_of_subset hE.measurableSet.nullMeasurableSet hO
          (hOV.trans inter_subset_left), (hdis.mono_left hOV).inter_eq, measure_empty]
    · have hxcl : x ∉ closure E := by
        intro hxcl
        exact hx (by rw [hE.frontier_eq]; exact ⟨hxcl, hxE⟩)
      let V := (closure E)ᶜ ∩ ball x 1
      have hV : IsOpen V := isClosed_closure.isOpen_compl.inter isOpen_ball
      have hdis : Disjoint V (frontier E) :=
        (disjoint_compl_left.mono_right frontier_subset_closure).mono_left inter_subset_left
      refine ⟨V, hV, ⟨hxcl, mem_ball_self zero_lt_one⟩, ?_, ?_⟩
      · rw [hdis.inter_eq, measure_empty]
        exact ENNReal.zero_lt_top
      · intro O hO hOV
        have hd : Disjoint E O := by
          apply Set.disjoint_left.mpr
          intro z hzE hzO
          exact (hOV hzO).1 (subset_closure hzE)
        rw [perimeterIn_eq_zero_of_disjoint hO.measurableSet hd,
          (hdis.mono_left hOV).inter_eq, measure_empty]

/-- C¹ boundary area is locally finite, without a boundedness hypothesis on the domain. -/
theorem HasC1Boundary.boundaryArea_finiteOnCompacts {E : Set AmbientSpace}
    (h : HasC1Boundary E) (hE : IsOpen E) :
    IsFiniteMeasureOnCompacts ((hausdorffMeasure2 3).restrict (frontier E)) := by
  let ρ := (hausdorffMeasure2 3).restrict (frontier E)
  have hi : IsLocallyFiniteMeasure ρ := by
    refine ⟨fun x => ?_⟩
    obtain ⟨V, hV, hxV, hfin, _⟩ := h.exists_local_perimeter_area hE x
    refine ⟨V, hV.mem_nhds hxV, ?_⟩
    rwa [show ρ = (hausdorffMeasure2 3).restrict (frontier E) from rfl,
      Measure.restrict_apply hV.measurableSet]
  exact inferInstance

/-- The geometric C¹ boundary condition implies local finite perimeter. -/
theorem HasC1Boundary.hasLocallyFinitePerimeter {E : Set AmbientSpace}
    (h : HasC1Boundary E) (hE : IsOpen E) : HasLocallyFinitePerimeter E := by
  obtain ⟨μ, hμ⟩ := exists_perimeter_measure hE.measurableSet.nullMeasurableSet
  let : IsLocallyFiniteMeasure μ := by
    refine ⟨fun x => ?_⟩
    obtain ⟨V, hV, hxV, hfin, heq⟩ := h.exists_local_perimeter_area hE x
    refine ⟨V, hV.mem_nhds hxV, ?_⟩
    rw [← hμ V hV, heq V hV Subset.rfl]
    exact hfin
  intro O hO hcO
  rw [hμ O hO]
  exact (measure_mono subset_closure).trans_lt hcO.measure_lt_top

/-- Canonical perimeter is normalized Hausdorff area on the topological C¹ boundary. -/
theorem HasC1Boundary.canonicalPerimeterMeasure_eq {E : Set AmbientSpace}
    (h : HasC1Boundary E) (hE : IsOpen E) (hP : HasLocallyFinitePerimeter E) :
    canonicalPerimeterMeasure E hP hE.measurableSet.nullMeasurableSet =
      (hausdorffMeasure2 3).restrict (frontier E) := by
  classical
  let μ := canonicalPerimeterMeasure E hP hE.measurableSet.nullMeasurableSet
  let ρ := (hausdorffMeasure2 3).restrict (frontier E)
  let : μ.Regular := (canonicalPerimeterPolar E hP hE.measurableSet.nullMeasurableSet).regular
  let : IsFiniteMeasureOnCompacts ρ := h.boundaryArea_finiteOnCompacts hE
  choose V hV hxV hfin heq using h.exists_local_perimeter_area hE
  have hcover : (univ : Set AmbientSpace) ⊆ ⋃ x, V x := by
    intro x _
    exact mem_iUnion.mpr ⟨x, hxV x⟩
  obtain ⟨I, hI, hcoverI⟩ := isLindelof_univ.elim_countable_subcover V hV hcover
  have huniv : (⋃ x ∈ I, V x) = univ := eq_univ_of_univ_subset hcoverI
  apply Measure.ext_of_biUnion_eq_univ hI huniv
  intro x _
  apply Measure.OuterRegular.ext_isOpen
  intro O hO
  rw [Measure.restrict_apply hO.measurableSet, Measure.restrict_apply hO.measurableSet]
  change μ (O ∩ V x) = ρ (O ∩ V x)
  rw [show μ (O ∩ V x) = perimeterIn E (O ∩ V x) from
    canonicalPerimeterMeasure_open E hP hE.measurableSet.nullMeasurableSet (hO.inter (hV x))]
  exact (heq x (O ∩ V x) (hO.inter (hV x)) inter_subset_right).trans
    (Measure.restrict_apply (hO.inter (hV x)).measurableSet).symm

/-- The smooth-boundary relative perimeter formula on arbitrary open regions. -/
theorem HasC1Boundary.perimeterIn_eq_boundaryArea {E : Set AmbientSpace}
    (h : HasC1Boundary E) (hE : IsOpen E) {O : Set AmbientSpace} (hO : IsOpen O) :
    perimeterIn E O = hausdorffMeasure2 3 (O ∩ frontier E) := by
  rw [← canonicalPerimeterMeasure_open E (h.hasLocallyFinitePerimeter hE)
    hE.measurableSet.nullMeasurableSet hO, h.canonicalPerimeterMeasure_eq hE,
    Measure.restrict_apply hO.measurableSet]

/-- Reduced-boundary points lie on the topological C¹ boundary. -/
theorem HasC1Boundary.reducedBoundary_subset_frontier {E : Set AmbientSpace}
    (h : HasC1Boundary E) (hE : IsOpen E) (hP : HasLocallyFinitePerimeter E) :
    reducedBoundary E hP hE.measurableSet.nullMeasurableSet ⊆ frontier E := by
  intro x hx
  have hxμ := hx.1
  change x ∈ (canonicalPerimeterMeasure E hP hE.measurableSet.nullMeasurableSet).support at hxμ
  rw [h.canonicalPerimeterMeasure_eq hE hP] at hxμ
  have hc := (Measure.support_restrict_subset hxμ).1
  simpa only [isClosed_frontier.closure_eq] using hc

/-- The topological boundary outside the reduced boundary has zero normalized area. -/
theorem HasC1Boundary.boundary_difference_reduced_null {E : Set AmbientSpace}
    (h : HasC1Boundary E) (hE : IsOpen E) (hP : HasLocallyFinitePerimeter E) :
    hausdorffMeasure2 3
      (frontier E \ reducedBoundary E hP hE.measurableSet.nullMeasurableSet) = 0 := by
  have hz := measure_compl_reducedBoundary E hP hE.measurableSet.nullMeasurableSet
  rw [h.canonicalPerimeterMeasure_eq hE hP, Measure.restrict_apply
    (measurableSet_reducedBoundary E hP hE.measurableSet.nullMeasurableSet).compl] at hz
  simpa only [sdiff_eq_compl_inter] using hz

/-- Topological and reduced boundaries agree up to normalized Hausdorff null sets. -/
theorem HasC1Boundary.boundary_ae_eq_reducedBoundary {E : Set AmbientSpace}
    (h : HasC1Boundary E) (hE : IsOpen E) (hP : HasLocallyFinitePerimeter E) :
    frontier E =ᵐ[hausdorffMeasure2 3]
      reducedBoundary E hP hE.measurableSet.nullMeasurableSet := by
  have hz := h.boundary_difference_reduced_null hE hP
  have hae := (measure_eq_zero_iff_ae_notMem.mp hz)
  filter_upwards [hae] with x hx
  apply propext
  exact ⟨fun hxf => by_contra fun hxr => hx ⟨hxf, hxr⟩,
    fun hxr => h.reducedBoundary_subset_frontier hE hP hxr⟩

/-- The unchanged perimeter definition equals topological C¹ boundary area. -/
theorem HasC1Boundary.perimeter_eq_boundaryArea {E : Set AmbientSpace}
    (h : HasC1Boundary E) (hE : IsOpen E) :
    perimeter E = hausdorffMeasure2 3 (frontier E) := by
  rw [← perimeterN_eq_perimeter E hE.measurableSet.nullMeasurableSet]
  simpa only [perimeterN, univ_inter] using h.perimeterIn_eq_boundaryArea hE isOpen_univ

/-- A bounded C¹ domain has finite classical boundary area and finite perimeter. -/
theorem HasC1Boundary.hasFinitePerimeter {E : Set AmbientSpace}
    (h : HasC1Boundary E) (hE : IsOpen E) (hbE : Bornology.IsBounded E) :
    HasFinitePerimeter E := by
  let := h.boundaryArea_finiteOnCompacts hE
  have hc : IsCompact (frontier E) :=
    hbE.isCompact_closure.of_isClosed_subset isClosed_frontier frontier_subset_closure
  have hfin := hc.measure_lt_top (μ := (hausdorffMeasure2 3).restrict (frontier E))
  rw [Measure.restrict_apply isClosed_frontier.measurableSet, inter_self] at hfin
  change perimeterIn E univ < ∞
  rw [h.perimeterIn_eq_boundaryArea hE isOpen_univ, univ_inter]
  exact hfin

lemma contDiff_rigidPlacement (a : AmbientSpace ≃ᵃⁱ[ℝ] AmbientSpace) : ContDiff ℝ 1 a := by
  have heq : (a : AmbientSpace → AmbientSpace) =
      fun x => a.linearIsometryEquiv x + a 0 := by
    funext x
    simpa using a.map_vadd (0 : AmbientSpace) x
  rw [heq]
  exact a.linearIsometryEquiv.toContinuousLinearEquiv.contDiff.add contDiff_const

lemma hasFDerivAt_rigidPlacement (a : AmbientSpace ≃ᵃⁱ[ℝ] AmbientSpace) (x : AmbientSpace) :
    HasFDerivAt a a.linearIsometryEquiv.toContinuousLinearEquiv.toContinuousLinearMap x := by
  have heq : (a : AmbientSpace → AmbientSpace) =
      fun y => a.linearIsometryEquiv y + a 0 := by
    funext y
    simpa using a.map_vadd (0 : AmbientSpace) y
  rw [heq]
  exact a.linearIsometryEquiv.toContinuousLinearEquiv.toContinuousLinearMap.hasFDerivAt.add_const _

/-- A rigid graph domain has its geometric chart normal as its true distributional normal. -/
theorem C1BoundaryChart.graphDomain_directional_pairing (c : C1BoundaryChart)
    {φ : AmbientSpace → ℝ} (hφ : ContDiff ℝ 1 φ) (hcφ : HasCompactSupport φ)
    (v : AmbientSpace) :
    (∫ z in c.graphDomain, fderiv ℝ φ z v) =
      ∫ z, φ z * inner ℝ v (c.outwardNormal z)
        ∂(hausdorffMeasure2 3).restrict c.graphSurface := by
  let a := c.placement
  let L := a.linearIsometryEquiv
  let ψ : AmbientSpace → ℝ := φ ∘ a
  have hψ : ContDiff ℝ 1 ψ := hφ.comp (contDiff_rigidPlacement a)
  have hcψ : HasCompactSupport ψ := hcφ.comp_homeomorph a.toHomeomorph
  have hd (y : AmbientSpace) : fderiv ℝ ψ y (L.symm v) = fderiv ℝ φ (a y) v := by
    have hder := (hφ.differentiable one_ne_zero (a y)).hasFDerivAt.comp y
      (hasFDerivAt_rigidPlacement a y)
    have hv := congrArg (fun M => M (L.symm v)) hder.fderiv
    change fderiv ℝ ψ y (L.symm v) = fderiv ℝ φ (a y) (L (L.symm v)) at hv
    simpa only [L.apply_symm_apply] using hv
  have hp := (measurePreserving_affineIsometry a).restrict_preimage
    c.isOpen_graphDomain.measurableSet
  have heq : a ⁻¹' c.graphDomain = smoothSubgraph c.height :=
    preimage_image_eq _ a.injective
  rw [heq] at hp
  rw [← hp.integral_comp a.toHomeomorph.measurableEmbedding (fun z => fderiv ℝ φ z v)]
  simp_rw [← hd]
  rw [smoothSubgraph_directional_pairing_surface c.height_contDiff hψ hcψ]
  have ha : MeasurableEmbedding (c.placement : AmbientSpace → AmbientSpace) :=
    c.placement.toHomeomorph.measurableEmbedding
  rw [graphSurface, hausdorffMeasure2_restrict_affineIsometry_image, ha.integral_map]
  change (∫ z, φ (a z) * inner ℝ (L.symm v) (smoothSubgraphNormal c.height z)
    ∂smoothGraphArea c.height) =
      ∫ z, φ (a z) * inner ℝ v (c.outwardNormal (a z)) ∂smoothGraphArea c.height
  apply integral_congr_ae
  filter_upwards with z
  congr 1
  change inner ℝ (L.symm v) (smoothSubgraphNormal c.height z) =
    inner ℝ v (L (smoothSubgraphNormal c.height (a.symm (a z))))
  rw [a.symm_apply_apply]
  exact (L.inner_map_map (L.symm v) (smoothSubgraphNormal c.height z)).symm.trans
    (by rw [L.apply_symm_apply])

/-- The boundary pairing is local in the chart neighborhood. -/
theorem C1BoundaryChart.IsChartFor.directional_pairing {c : C1BoundaryChart}
    {E : Set AmbientSpace} (hc : c.IsChartFor E) (hE : MeasurableSet E)
    {φ : AmbientSpace → ℝ} (hφ : ContDiff ℝ 1 φ) (hcφ : HasCompactSupport φ)
    (hsφ : tsupport φ ⊆ c.region) (v : AmbientSpace) :
    (∫ z in E, fderiv ℝ φ z v) =
      ∫ z, φ z * inner ℝ v (c.outwardNormal z)
        ∂(hausdorffMeasure2 3).restrict c.graphSurface := by
  classical
  rw [← c.graphDomain_directional_pairing hφ hcφ v,
    ← integral_indicator hE, ← integral_indicator c.isOpen_graphDomain.measurableSet]
  apply integral_congr_ae
  filter_upwards with z
  by_cases hz : z ∈ tsupport φ
  · have heq : z ∈ E ↔ z ∈ c.graphDomain := by
      have h := hc.inter_eq
      exact ⟨fun he => (h ▸ (show z ∈ E ∩ c.region from ⟨he, hsφ hz⟩)).1,
        fun he => (h.symm ▸ (show z ∈ c.graphDomain ∩ c.region from ⟨he, hsφ hz⟩)).1⟩
    simp only [indicator_apply, heq]
  · simp [indicator_apply, fderiv_of_notMem_tsupport ℝ hz]

/-- The area measures from the whole boundary and a chart agree on that chart. -/
lemma C1BoundaryChart.IsChartFor.boundaryArea_restrict {c : C1BoundaryChart}
    {E : Set AmbientSpace} (hc : c.IsChartFor E) :
    ((hausdorffMeasure2 3).restrict (frontier E)).restrict c.region =
      ((hausdorffMeasure2 3).restrict c.graphSurface).restrict c.region := by
  rw [Measure.restrict_restrict c.isOpen_region.measurableSet,
    Measure.restrict_restrict c.isOpen_region.measurableSet]
  congr 1
  simpa only [inter_comm] using hc.frontier_inter_eq

/-- The geometric chart normal agrees locally almost everywhere with the canonical polar. -/
theorem C1BoundaryChart.IsChartFor.canonical_normal_eq_ae {c : C1BoundaryChart}
    {E : Set AmbientSpace} (hc : c.IsChartFor E) (h : HasC1Boundary E) (hE : IsOpen E)
    (hP : HasLocallyFinitePerimeter E) :
    ∀ᵐ z ∂canonicalPerimeterMeasure E hP hE.measurableSet.nullMeasurableSet,
      z ∈ c.region → canonicalOutwardPolarDensity E hP hE.measurableSet.nullMeasurableSet z =
        c.outwardNormal z := by
  let μ := canonicalPerimeterMeasure E hP hE.measurableSet.nullMeasurableSet
  let ρ := (hausdorffMeasure2 3).restrict c.graphSurface
  let ν := canonicalOutwardPolarDensity E hP hE.measurableSet.nullMeasurableSet
  have hpolar := canonicalPerimeterPolar E hP hE.measurableSet.nullMeasurableSet
  let : μ.Regular := hpolar.regular
  have hre : μ.restrict c.region = ρ.restrict c.region := by
    rw [show μ = (hausdorffMeasure2 3).restrict (frontier E) from
      h.canonicalPerimeterMeasure_eq hE hP]
    exact hc.boundaryArea_restrict
  have hint (q : AmbientSpace → ℝ) (hq : ∀ z ∉ c.region, q z = 0) :
      (∫ z, q z ∂μ) = ∫ z, q z ∂ρ := by
    rw [← setIntegral_eq_integral_of_forall_compl_eq_zero hq,
      ← setIntegral_eq_integral_of_forall_compl_eq_zero (μ := ρ) hq]
    rw [hre]
  have hi (i : Fin 3) : LocallyIntegrable (fun z => ν z i) μ := by
    apply locallyIntegrable_iff.mpr
    intro K hK
    simpa only [Function.comp_def] using!
      (EuclideanSpace.proj i : AmbientSpace →L[ℝ] ℝ).integrable_comp
        (hpolar.locallyIntegrable.integrableOn_isCompact hK)
  have hj (i : Fin 3) : LocallyIntegrable (fun z => c.outwardNormal z i) μ :=
    ((EuclideanSpace.proj i).continuous.comp c.continuous_outwardNormal).locallyIntegrable
  have ha (i : Fin 3) : ∀ᵐ z ∂μ, z ∈ c.region → ν z i = c.outwardNormal z i := by
    have hz := c.isOpen_region.ae_eq_zero_of_integral_contDiff_smul_eq_zero
      (((hi i).sub (hj i)).locallyIntegrableOn c.region) ?_
    · filter_upwards [hz] with z hz
      intro hzc
      exact sub_eq_zero.mp (hz hzc)
    intro g hg hgc hgs
    let φ : CompactlySupportedContinuousMap AmbientSpace ℝ := ⟨⟨g, hg.continuous⟩, hgc⟩
    have hφ : ContDiff ℝ 1 φ := hg.of_le (by simp)
    have hpair := hpolar.coordinate_eq i φ hφ
    have heq : (fun z => E.indicator (fun _ => (1 : ℝ)) z *
        fderiv ℝ φ z (EuclideanSpace.single i 1)) =
        E.indicator (fun z => fderiv ℝ φ z (EuclideanSpace.single i 1)) := by
      funext z
      by_cases hz : z ∈ E <;> simp [hz]
    rw [heq, integral_indicator hE.measurableSet] at hpair
    simp only [mul_neg, integral_neg, neg_inj] at hpair
    have hchart := hc.directional_pairing hE.measurableSet hφ hgc hgs
      (EuclideanSpace.single i 1)
    simp only [EuclideanSpace.inner_single_left, map_one, one_mul] at hchart
    have htrans := hint (fun z => g z * c.outwardNormal z i) (by
      intro z hz
      rw [image_eq_zero_of_notMem_tsupport (fun hs => hz (hgs hs)), zero_mul])
    have heqint : (∫ z, g z * ν z i ∂μ) = ∫ z, g z * c.outwardNormal z i ∂μ :=
      hpair.symm.trans (hchart.trans htrans.symm)
    have hgi : Integrable (fun z => g z * ν z i) μ :=
      (hi i).integrable_smul_left_of_hasCompactSupport hg.continuous hgc
    have hgj : Integrable (fun z => g z * c.outwardNormal z i) μ :=
      (hj i).integrable_smul_left_of_hasCompactSupport hg.continuous hgc
    simp only [smul_eq_mul, Pi.sub_apply, mul_sub, integral_sub hgi hgj, heqint, sub_self]
  filter_upwards [ae_all_iff.mpr ha] with z hz
  intro hzc
  exact PiLp.ext (fun i => hz i hzc)

/-- The reduced normal is the classical outward normal in every C¹ chart. -/
theorem C1BoundaryChart.IsChartFor.reduced_normal_eq_ae {c : C1BoundaryChart}
    {E : Set AmbientSpace} (hc : c.IsChartFor E) (h : HasC1Boundary E) (hE : IsOpen E)
    (hP : HasLocallyFinitePerimeter E) :
    ∀ᵐ z ∂(hausdorffMeasure2 3).restrict (frontier E), z ∈ c.region →
      reducedNormal E hP hE.measurableSet.nullMeasurableSet z = c.outwardNormal z := by
  rw [← h.canonicalPerimeterMeasure_eq hE hP]
  filter_upwards [reducedNormal_ae_eq_polarDensity E hP hE.measurableSet.nullMeasurableSet,
    hc.canonical_normal_eq_ae h hE hP] with z hz hzc
  intro hcZ
  exact hz.trans (hzc hcZ)

/-- Two geometric chart normals agree almost everywhere on their common boundary patch. -/
theorem C1BoundaryChart.IsChartFor.outwardNormal_agree_ae {c d : C1BoundaryChart}
    {E : Set AmbientSpace} (hc : c.IsChartFor E) (hd : d.IsChartFor E)
    (h : HasC1Boundary E) (hE : IsOpen E) :
    ∀ᵐ z ∂(hausdorffMeasure2 3).restrict (frontier E), z ∈ c.region ∩ d.region →
      c.outwardNormal z = d.outwardNormal z := by
  let hP := h.hasLocallyFinitePerimeter hE
  filter_upwards [hc.reduced_normal_eq_ae h hE hP, hd.reduced_normal_eq_ae h hE hP] with z hcZ hdZ
  intro hz
  exact (hcZ hz.1).symm.trans (hdZ hz.2)

/-- A continuous field is recovered by shrinking ball averages at every support point. -/
lemma tendsto_average_ball_continuous (μ : Measure AmbientSpace) [IsLocallyFiniteMeasure μ]
    {g : AmbientSpace → AmbientSpace} (hg : Continuous g) (x : AmbientSpace)
    (hx : x ∈ μ.support) :
    Tendsto (fun r : ℝ => ⨍ y in ball x r, g y ∂μ) (𝓝[>] 0) (𝓝 (g x)) := by
  apply Metric.tendsto_nhds.mpr
  intro ε hε
  obtain ⟨δ, hδ, hd⟩ := Metric.continuousAt_iff.mp hg.continuousAt (ε / 2) (by positivity)
  filter_upwards [self_mem_nhdsWithin, (eventually_lt_nhds hδ).filter_mono nhdsWithin_le_nhds]
    with r hr hrd
  have hr0 : 0 < r := hr
  have hfin : μ (ball x r) < ∞ := isBounded_ball.measure_lt_top
  have hpos : 0 < μ (ball x r) :=
    (Measure.mem_support_iff_forall x).mp hx _ (ball_mem_nhds x hr0)
  have hi : IntegrableOn g (ball x r) μ :=
    (hg.locallyIntegrable.integrableOn_isCompact (isCompact_closedBall x r)).mono_set
      ball_subset_closedBall
  have hc : IntegrableOn (fun _ : AmbientSpace => g x) (ball x r) μ :=
    integrableOn_const hfin.ne
  have heq := setAverage_fun_sub hi hc
  rw [setAverage_const hpos.ne' hfin.ne] at heq
  have hn : 0 ≤ μ.real (ball x r) := ENNReal.toReal_nonneg
  rw [dist_eq_norm, ← heq, setAverage_eq, norm_smul, Real.norm_eq_abs,
    abs_of_nonneg (inv_nonneg.mpr hn)]
  calc
    _ ≤ (μ.real (ball x r))⁻¹ * ((ε / 2) * μ.real (ball x r)) := by
      apply mul_le_mul_of_nonneg_left _ (inv_nonneg.mpr ENNReal.toReal_nonneg)
      apply norm_setIntegral_le_of_norm_le_const hfin
      intro y hy
      exact (hd (mem_ball.mp ((ball_subset_ball hrd.le) hy))).le
    _ = ε / 2 := by
      have hm : μ.real (ball x r) ≠ 0 := ENNReal.toReal_ne_zero.mpr ⟨hpos.ne', hfin.ne⟩
      field_simp
    _ < ε := by linarith

/-- At each reduced-boundary point in a C¹ chart the outward normal is the
classical geometric normal, with no exceptional set inside the reduced boundary. -/
theorem C1BoundaryChart.IsChartFor.reduced_normal_eq {c : C1BoundaryChart}
    {E : Set AmbientSpace} (hc : c.IsChartFor E) (h : HasC1Boundary E) (hE : IsOpen E)
    (hP : HasLocallyFinitePerimeter E) {x : AmbientSpace}
    (hx : x ∈ reducedBoundary E hP hE.measurableSet.nullMeasurableSet)
    (hxc : x ∈ c.region) :
    reducedNormal E hP hE.measurableSet.nullMeasurableSet x = c.outwardNormal x := by
  let μ := canonicalPerimeterMeasure E hP hE.measurableSet.nullMeasurableSet
  let ν := canonicalOutwardPolarDensity E hP hE.measurableSet.nullMeasurableSet
  let : μ.Regular := (canonicalPerimeterPolar E hP hE.measurableSet.nullMeasurableSet).regular
  have hlim := tendsto_average_ball_continuous μ c.continuous_outwardNormal.neg x hx.1
  obtain ⟨δ, hδ, hsub⟩ := Metric.mem_nhds_iff.mp (c.isOpen_region.mem_nhds hxc)
  have heq : (fun r : ℝ => ⨍ y in ball x r, -ν y ∂μ) =ᶠ[𝓝[>] 0]
      (fun r : ℝ => ⨍ y in ball x r, -c.outwardNormal y ∂μ) := by
    filter_upwards [(eventually_lt_nhds hδ).filter_mono nhdsWithin_le_nhds] with r hr
    simp only [setAverage_eq]
    congr 1
    apply integral_congr_ae
    filter_upwards [ae_restrict_of_ae (hc.canonical_normal_eq_ae h hE hP),
      ae_restrict_mem measurableSet_ball] with y hy hyb
    exact congrArg Neg.neg (hy (hsub ((ball_subset_ball hr.le) hyb)))
  have hlim' : Tendsto (fun r : ℝ => ⨍ y in ball x r, -ν y ∂μ) (𝓝[>] 0)
      (𝓝 (-c.outwardNormal x)) := hlim.congr' heq.symm
  have hnormal := tendsto_average_reducedNormalOfPolar μ (-ν) hx
  exact neg_injective (tendsto_nhds_unique hnormal hlim')

/-- The smooth-boundary corollary, with the classical normal specified in every chart. -/
theorem smooth_perimeter {E : Set AmbientSpace} (hE : IsOpen E)
    (hbE : Bornology.IsBounded E) (h : HasC1Boundary E) :
    ∃ hP : HasLocallyFinitePerimeter E,
      HasFinitePerimeter E ∧
      (frontier E =ᵐ[hausdorffMeasure2 3]
        reducedBoundary E hP hE.measurableSet.nullMeasurableSet) ∧
      perimeter E = hausdorffMeasure2 3 (frontier E) ∧
      ∀ (c : C1BoundaryChart), c.IsChartFor E →
        ∀ x ∈ reducedBoundary E hP hE.measurableSet.nullMeasurableSet, x ∈ c.region →
          reducedNormal E hP hE.measurableSet.nullMeasurableSet x = c.outwardNormal x := by
  let hP := h.hasLocallyFinitePerimeter hE
  exact ⟨hP, h.hasFinitePerimeter hE hbE, h.boundary_ae_eq_reducedBoundary hE hP,
    h.perimeter_eq_boundaryArea hE, fun _ hc _ hx hxc => hc.reduced_normal_eq h hE hP hx hxc⟩

end LiquidDrop

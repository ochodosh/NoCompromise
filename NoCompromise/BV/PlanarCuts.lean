module

public import NoCompromise.BV.TraceAlmostEverywhere
public import NoCompromise.BV.GraphCutPerimeter

@[expose] public section

/-!
# Almost every planar cut

Flat essential traces in orthogonal coordinates agree with the density-one
representative for almost every height. Exact perimeter formulas follow from
the actual graph trace pairing and disjoint bulk and surface measures.
-/

noncomputable section
open MeasureTheory Set Filter Metric
open scoped ENNReal Topology Gradient
namespace LiquidDrop
set_option maxSynthPendingDepth 8

/-- A complete flat graph in an arbitrary orthogonal frame. The bounded chart
region is irrelevant to its complete graph domain and surface. -/
def planarBoundaryChart
    (e : AmbientSpace ≃ₗᵢ[ℝ] AmbientSpace) (a : ℝ) : C1BoundaryChart where
  height := fun _ => a
  height_contDiff := contDiff_const
  placement := e.toAffineIsometryEquiv
  region := ball 0 1
  isOpen_region := isOpen_ball
  bounded_region := isBounded_ball

lemma planarBoundaryChart_graphDomain
    (e : AmbientSpace ≃ₗᵢ[ℝ] AmbientSpace) (a : ℝ) :
    (planarBoundaryChart e a).graphDomain = {z | e.symm z (Fin.last 2) < a} := by
  ext z
  change (z ∈ e '' {y : AmbientSpace | y (Fin.last 2) < a}) ↔ _
  constructor
  · rintro ⟨y, hy, rfl⟩
    simpa only [mem_ofPred_eq, e.symm_apply_apply] using hy
  · intro hz
    exact ⟨e.symm z, hz, e.apply_symm_apply z⟩

lemma planarBoundaryChart_graphSurface
    (e : AmbientSpace ≃ₗᵢ[ℝ] AmbientSpace) (a : ℝ) :
    (planarBoundaryChart e a).graphSurface = {z | e.symm z (Fin.last 2) = a} := by
  ext z
  change (z ∈ e '' range (graphMapN (fun _ => a))) ↔ _
  constructor
  · rintro ⟨y, ⟨x, rfl⟩, rfl⟩
    simp only [e.symm_apply_apply, mem_ofPred_eq, graphMapN_last]
  · intro hz
    refine ⟨graphMapN (fun _ => a) (graphProjectionN 2 (e.symm z)), ⟨_, rfl⟩, ?_⟩
    apply e.symm.injective
    rw [e.symm_apply_apply]
    change graphAppendN (graphProjectionN 2 (e.symm z)) a = e.symm z
    rw [← hz, graphAppendN_projection]

lemma planarBoundaryChart_area_eq_map
    (e : AmbientSpace ≃ₗᵢ[ℝ] AmbientSpace) (a : ℝ) :
    (hausdorffMeasure2 3).restrict (planarBoundaryChart e a).graphSurface =
      Measure.map (fun x : EuclideanSpace ℝ (Fin 2) => e (graphAppendN x a)) volume := by
  rw [C1BoundaryChart.graphSurface, hausdorffMeasure2_restrict_affineIsometry_image]
  change Measure.map e (smoothGraphArea (fun _ : EuclideanSpace ℝ (Fin 2) => a)) = _
  rw [smoothGraphArea_eq_map contDiff_const]
  have hg (x : EuclideanSpace ℝ (Fin 2)) :
      gradient (fun _ : EuclideanSpace ℝ (Fin 2) => a) x = 0 := by
    simp [gradient]
  simp only [hg, norm_zero, zero_pow (by norm_num : 2 ≠ 0), add_zero, Real.sqrt_one,
    ENNReal.ofReal_one]
  rw [withDensity_const, one_smul]
  rw [Measure.map_map e.continuous.measurable
    (isClosedEmbedding_smoothGraphMap continuous_const).continuous.measurable]
  rfl

lemma HasBVLeftTrace.comp_add_zero {f : ℝ → ℝ} {a L : ℝ}
    (h : HasBVLeftTrace f a L) : HasBVLeftTrace (fun t => f (t + a)) 0 L := by
  apply h.comp
  have ht : Tendsto (fun t : ℝ => t + a) (𝓝[<] 0) (𝓝[<] a) := by
    apply tendsto_nhdsWithin_iff.mpr
    constructor
    · simpa only [zero_add, id_eq] using
        ((tendsto_id : Tendsto (fun t : ℝ => t) (𝓝 0) (𝓝 0)).add_const a).mono_left
          nhdsWithin_le_nhds
    · filter_upwards [self_mem_nhdsWithin] with t ht
      change t + a < a
      change t < 0 at ht
      linarith
  exact ht.inf
    (measurePreserving_add_right volume a).quasiMeasurePreserving.tendsto_ae

/-- Actual flat chart traces agree with any Borel representative at almost
every translated plane in a fixed orthogonal frame. -/
theorem IsLocallyBVOn.ae_planarBoundaryChart_trace {f g : AmbientSpace → ℝ}
    (hf : IsLocallyBVOn f univ) (hg : Measurable g) (he : f =ᵐ[volume] g)
    (e : AmbientSpace ≃ₗᵢ[ℝ] AmbientSpace) :
    ∀ᵐ a : ℝ, (planarBoundaryChart e a).lowerBVTrace f =ᵐ[(hausdorffMeasure2 3).restrict
      (planarBoundaryChart e a).graphSurface] g := by
  have hfe := hf.comp_linearIsometryEquiv_univ e
  have hge : Measurable (g ∘ e) := hg.comp e.continuous.measurable
  have hee := e.measurePreserving.quasiMeasurePreserving.ae_eq_comp he
  filter_upwards [hfe.ae_flatBVTraces_eq_of_ae hge hee] with a ha
  rw [planarBoundaryChart_area_eq_map]
  have hem := e.toHomeomorph.measurableEmbedding.comp
    (isClosedEmbedding_graphAppendN 2 a).measurableEmbedding
  change MeasurableEmbedding
    (fun x : EuclideanSpace ℝ (Fin 2) => e (graphAppendN x a)) at hem
  change ∀ᵐ z ∂Measure.map (fun x : EuclideanSpace ℝ (Fin 2) =>
    e (graphAppendN x a)) volume, (planarBoundaryChart e a).lowerBVTrace f z = g z
  rw [hem.ae_map_iff]
  filter_upwards [ha, hfe.ae_line_oneSided_traces] with x hx hxt
  have ht := ((hxt a).1.comp_add_zero).eq_bvLeftTrace
  change bvLeftTrace (fun t => f (e (graphAppendN
    (graphProjectionN 2 (e.symm (e (graphAppendN x a)))) (t + a)))) 0 =
      g (e (graphAppendN x a))
  rw [e.symm_apply_apply, graphProjectionN_append]
  exact ht.trans hx.1

/-- Every locally finite measure gives zero mass to almost every parallel plane. -/
lemma ae_measure_planarBoundaryChart_graphSurface_eq_zero
    (μ : Measure AmbientSpace) [SFinite μ] (e : AmbientSpace ≃ₗᵢ[ℝ] AmbientSpace) :
    ∀ᵐ a : ℝ, μ (planarBoundaryChart e a).graphSurface = 0 := by
  have hm : Measurable (fun z : AmbientSpace => e.symm z (Fin.last 2)) :=
    (EuclideanSpace.proj (𝕜 := ℝ) (Fin.last 2)).measurable.comp e.symm.continuous.measurable
  have hc := Measure.countable_meas_level_set_pos (μ := μ) hm
  filter_upwards [hc.ae_notMem volume] with a ha
  rw [planarBoundaryChart_graphSurface]
  exact nonpos_iff_eq_zero.mp (le_of_not_gt ha)

lemma inner_frame_last (e : AmbientSpace ≃ₗᵢ[ℝ] AmbientSpace) (z : AmbientSpace) :
    inner ℝ (e (EuclideanSpace.single (Fin.last 2) 1)) z = e.symm z (Fin.last 2) := by
  simpa only [e.apply_symm_apply, EuclideanSpace.inner_single_left, map_one, one_mul] using
    e.inner_map_map (EuclideanSpace.single (Fin.last 2) 1) (e.symm z)

lemma volume_plane_eq_zero {ν : AmbientSpace} (hν : ‖ν‖ = 1) (a : ℝ) :
    volume {z : AmbientSpace | inner ℝ ν z = a} = 0 := by
  obtain ⟨e, he⟩ := exists_line_direction_frame hν
  have hcoord (z : AmbientSpace) : e.symm z (Fin.last 2) = inner ℝ ν z := by
    rw [← inner_frame_last, he]
  simpa only [planarBoundaryChart_graphSurface, hcoord] using
    (planarBoundaryChart e a).volume_graphSurface

/-- Almost every plane has the exact interior-cut formula in every open test
region. The trace equality is proved from BV slicing, not assumed. -/
theorem ae_perimeterIn_halfspace_inter {E : Set AmbientSpace}
    (hE : HasLocallyFinitePerimeter E) (hmE : NullMeasurableSet E volume)
    {ν : AmbientSpace} (hν : ‖ν‖ = 1) :
    ∀ᵐ a : ℝ, ∀ U : Set AmbientSpace, IsOpen U →
      perimeterIn (E ∩ {z | inner ℝ ν z < a}) U =
        perimeterIn E (U ∩ {z | inner ℝ ν z < a}) +
          hausdorffMeasure2 3 (U ∩ (densityOne E ∩ {z | inner ℝ ν z = a})) := by
  obtain ⟨e, he⟩ := exists_line_direction_frame hν
  have hf := hE.isLocallyBVOn_indicator hmE univ
  have hg : Measurable ((densityOne E).indicator (fun _ => (1 : ℝ))) :=
    measurable_const.indicator (measurableSet_densityOne hmE)
  have heq : E.indicator (fun _ => (1 : ℝ)) =ᵐ[volume]
      (densityOne E).indicator (fun _ => (1 : ℝ)) := by
    filter_upwards [densityOne_ae_eq (by norm_num : 0 < 3) hmE] with z hz
    by_cases hze : z ∈ E
    · have hzd : z ∈ densityOne E := (Iff.of_eq hz).mpr hze
      simp only [indicator_of_mem hze, indicator_of_mem hzd]
    · have hzd : z ∉ densityOne E := fun h => hze ((Iff.of_eq hz).mp h)
      simp only [indicator_of_notMem hze, indicator_of_notMem hzd]
  filter_upwards [hf.ae_planarBoundaryChart_trace hg heq e] with a ha
  intro U hU
  have hcoord (z : AmbientSpace) : e.symm z (Fin.last 2) = inner ℝ ν z := by
    rw [← inner_frame_last, he]
  simpa only [planarBoundaryChart_graphDomain, planarBoundaryChart_graphSurface, hcoord] using
    (planarBoundaryChart e a).perimeterIn_cut_eq_of_trace hE hmE ha hU

/-- The two corresponding exact halfspace identities in every open region.
The separating plane is negligible for ambient volume, so the exterior cut
may include that plane. All perimeter terms may be infinite. -/
theorem ae_perimeterIn_halfspace_cut_identities {E : Set AmbientSpace}
    (hE : HasLocallyFinitePerimeter E) (hmE : NullMeasurableSet E volume)
    {ν : AmbientSpace} (hν : ‖ν‖ = 1) :
    ∀ᵐ a : ℝ, ∀ U : Set AmbientSpace, IsOpen U →
      (perimeterIn (E ∩ {z | inner ℝ ν z < a}) U =
        perimeterIn E (U ∩ {z | inner ℝ ν z < a}) +
          hausdorffMeasure2 3 (U ∩ (densityOne E ∩ {z | inner ℝ ν z = a}))) ∧
      perimeterIn (E \ {z | inner ℝ ν z < a}) U =
        perimeterIn E (U ∩ {z | a < inner ℝ ν z}) +
          hausdorffMeasure2 3 (U ∩ (densityOne E ∩ {z | inner ℝ ν z = a})) := by
  have hn : ‖-ν‖ = 1 := by simpa using hν
  have hm := (Measure.measurePreserving_neg (volume : Measure ℝ)).quasiMeasurePreserving.ae
    (ae_perimeterIn_halfspace_inter hE hmE hn)
  filter_upwards [ae_perimeterIn_halfspace_inter hE hmE hν, hm] with a ha hma
  intro U hU
  refine ⟨ha U hU, ?_⟩
  have he : E \ {z | inner ℝ ν z < a} =ᵐ[volume]
      (E ∩ {z | a < inner ℝ ν z} : Set AmbientSpace) := by
    filter_upwards [(measure_eq_zero_iff_ae_notMem).mp (volume_plane_eq_zero hν a)] with z hz
    apply propext
    change (z ∈ E ∧ ¬inner ℝ ν z < a) ↔ (z ∈ E ∧ a < inner ℝ ν z)
    have hne : inner ℝ ν z ≠ a := hz
    exact and_congr Iff.rfl ⟨fun h => lt_of_le_of_ne (not_lt.mp h) hne.symm,
      fun h => not_lt.mpr h.le⟩
  apply (perimeterIn_congr_ae U (ae_restrict_of_ae he)).trans
  simpa only [inner_neg_left, neg_lt_neg_iff, neg_inj] using hma U hU

/-- Blueprint `prop:cut-identities`, the halfspace clause, for each fixed unit
normal and almost every translation height. -/
theorem ae_perimeter_halfspace_cut_identities {E : Set AmbientSpace}
    (hE : HasLocallyFinitePerimeter E) (hmE : NullMeasurableSet E volume)
    {ν : AmbientSpace} (hν : ‖ν‖ = 1) :
    ∀ᵐ a : ℝ,
      (perimeter (E ∩ {z | inner ℝ ν z < a}) =
        perimeterIn E {z | inner ℝ ν z < a} +
          hausdorffMeasure2 3 (densityOne E ∩ {z | inner ℝ ν z = a})) ∧
      perimeter (E \ {z | inner ℝ ν z < a}) =
        perimeterIn E {z | a < inner ℝ ν z} +
          hausdorffMeasure2 3 (densityOne E ∩ {z | inner ℝ ν z = a}) := by
  filter_upwards [ae_perimeterIn_halfspace_cut_identities hE hmE hν] with a ha
  have hH : MeasurableSet {z : AmbientSpace | inner ℝ ν z < a} :=
    measurableSet_lt (continuous_const.inner continuous_id).measurable measurable_const
  rw [← perimeterN_eq_perimeter _ (hmE.inter hH.nullMeasurableSet),
    ← perimeterN_eq_perimeter _ (hmE.diff hH.nullMeasurableSet)]
  simpa only [perimeterN, univ_inter] using ha univ isOpen_univ

end LiquidDrop

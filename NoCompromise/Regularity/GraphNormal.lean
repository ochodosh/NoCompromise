module

public import NoCompromise.Regularity.GraphNormalGeometry
public import NoCompromise.Regularity.GraphNormalDensity

@[expose] public section

/-!
# The actual reduced normal on a Lipschitz graph piece

Cone concentration for canonical perimeter and density one in the graph base
force the classical graph tangent to be perpendicular to the actual reduced
normal. Thus the reduced normal agrees, up to sign, with the graph normal
almost everywhere. No tangent-plane or normal identification is a hypothesis.
-/

noncomputable section
open MeasureTheory Set Filter Metric InnerProductSpace
open scoped Topology ENNReal NNReal Gradient
namespace LiquidDrop

/-- At every differentiability and base-density point, graph tangents are
orthogonal to the actual reduced normal. -/
theorem reducedNormal_orthogonal_graphTangentMap (E : Set AmbientSpace)
    (hE : HasLocallyFinitePerimeter E) (hmE : NullMeasurableSet E volume)
    {f : EuclideanSpace ℝ (Fin 2) → ℝ} {K : ℝ≥0} (hf : LipschitzWith K f)
    {G : Set (EuclideanSpace ℝ (Fin 2))} (hG : MeasurableSet G)
    (hred : graphMap f '' G ⊆ reducedBoundary E hE hmE)
    {x : EuclideanSpace ℝ (Fin 2)} (hx : x ∈ G) (hxd : x ∈ densityOne G)
    (hdf : DifferentiableAt ℝ f x) (v : EuclideanSpace ℝ (Fin 2)) :
    inner ℝ (reducedNormal E hE hmE (graphMap f x))
      (graphTangentMap (gradient f x) v) = 0 := by
  by_contra hv
  let μ := canonicalPerimeterMeasure E hE hmE
  let ν := reducedNormal E hE hmE (graphMap f x)
  let := (canonicalPerimeterPolar E hE hmE).finiteOnCompacts
  have hxred := hred ⟨x, hx, rfl⟩
  obtain ⟨δ, ε, R, hδ, hε, _hR, hpatch⟩ :=
    graphNormal_exists_off_cone_patch hdf ν hv
  have ht := tendsto_blowupPolarMeasure_ball_sdiff_cone E hE hmE hxred hε R
  have he : ∀ᶠ r in 𝓝[>] (0 : ℝ), Real.pi * δ ^ 2 / 2 ≤
      (blowupPolarMeasure μ (graphMap f x) r).real
        (ball 0 R \ normalPlaneCone 0 ν ε) := by
    filter_upwards [self_mem_nhdsWithin, hpatch,
      graphNormal_eventually_base_mass_lower hG hxd v hδ] with r hr hp hm
    change 0 < r at hr
    let B := ball (x + r • v) (r * δ)
    let A := ball (graphMap f x) (r * R) \ normalPlaneCone (graphMap f x) ν ε
    have himage : (fun w => x + r • w) '' ball v δ = B := by
      rw [← image_image (fun w => x + w) (fun w => r • w),
        Metric.smul_image_ball hr.ne']
      simp only [Real.norm_eq_abs, abs_of_pos hr]
      exact (IsometryEquiv.addLeft x).image_ball (r • v) (r * δ)
    have hGA : graphMap f '' (G ∩ B) ⊆ A := by
      rintro y ⟨z, hz, rfl⟩
      obtain ⟨w, hw, rfl⟩ := himage.symm ▸ hz.2
      exact hp w hw
    have hA : MeasurableSet A :=
      measurableSet_ball.diff (isOpen_normalPlaneCone _ _ _).measurableSet
    have hred' : graphMap f '' (G ∩ B) ⊆ reducedBoundary E hE hmE :=
      (image_mono inter_subset_left).trans hred
    have harea := graphNormal_base_area_le_perimeter E hE hmE hf
      (hG.inter measurableSet_ball) hred' hA hGA
    have hfin : μ A ≠ ∞ :=
      ((measure_mono (sdiff_subset.trans ball_subset_closedBall)).trans_lt
        (isCompact_closedBall (graphMap f x) (r * R)).measure_lt_top).ne
    have hb : Real.pi * δ ^ 2 / 2 * r ^ 2 ≤ μ.real A :=
      hm.trans (ENNReal.toReal_mono hfin harea)
    rw [blowupPolarMeasure_real_ball_sdiff_cone _ _ _ _ _ hr]
    have hh := mul_le_mul_of_nonneg_left hb (sq_nonneg r⁻¹)
    convert hh using 1 <;> first | rfl | (field_simp [hr.ne'])
  have hc := le_of_tendsto_of_tendsto tendsto_const_nhds ht he
  have hpos : 0 < Real.pi * δ ^ 2 / 2 := by positivity
  exact (not_le.mpr hpos) hc

/-- The actual reduced normal is one of the two classical graph normals at
every differentiability and base-density point of the graph piece. -/
theorem reducedNormal_eq_graphUnitNormal_or_neg (E : Set AmbientSpace)
    (hE : HasLocallyFinitePerimeter E) (hmE : NullMeasurableSet E volume)
    {f : EuclideanSpace ℝ (Fin 2) → ℝ} {K : ℝ≥0} (hf : LipschitzWith K f)
    {G : Set (EuclideanSpace ℝ (Fin 2))} (hG : MeasurableSet G)
    (hred : graphMap f '' G ⊆ reducedBoundary E hE hmE)
    {x : EuclideanSpace ℝ (Fin 2)} (hx : x ∈ G) (hxd : x ∈ densityOne G)
    (hdf : DifferentiableAt ℝ f x) :
    reducedNormal E hE hmE (graphMap f x) = graphUnitNormal (gradient f x) ∨
      reducedNormal E hE hmE (graphMap f x) = -graphUnitNormal (gradient f x) :=
  graphNormal_eq_or_neg_of_orthogonal _
    (norm_reducedNormal E hE hmE (hred ⟨x, hx, rfl⟩))
    (reducedNormal_orthogonal_graphTangentMap E hE hmE hf hG hred hx hxd hdf)

/-- Normal identification almost everywhere on the Borel graph base. -/
theorem ae_reducedNormal_eq_graphUnitNormal_or_neg_base (E : Set AmbientSpace)
    (hE : HasLocallyFinitePerimeter E) (hmE : NullMeasurableSet E volume)
    {f : EuclideanSpace ℝ (Fin 2) → ℝ} {K : ℝ≥0} (hf : LipschitzWith K f)
    {G : Set (EuclideanSpace ℝ (Fin 2))} (hG : MeasurableSet G)
    (hred : graphMap f '' G ⊆ reducedBoundary E hE hmE) :
    ∀ᵐ x ∂volume.restrict G,
      reducedNormal E hE hmE (graphMap f x) = graphUnitNormal (gradient f x) ∨
        reducedNormal E hE hmE (graphMap f x) = -graphUnitNormal (gradient f x) := by
  filter_upwards [ae_restrict_mem hG, ae_mem_densityOne (by norm_num : 0 < 2) G,
    ae_restrict_of_ae hf.ae_differentiableAt] with x hx hxd hdf
  exact reducedNormal_eq_graphUnitNormal_or_neg E hE hmE hf hG hred hx hxd hdf

/-- Normal identification almost everywhere for the actual Hausdorff area of
the graph piece. The base point and its classical derivative are retained. -/
theorem ae_reducedNormal_eq_graphUnitNormal_or_neg (E : Set AmbientSpace)
    (hE : HasLocallyFinitePerimeter E) (hmE : NullMeasurableSet E volume)
    {f : EuclideanSpace ℝ (Fin 2) → ℝ} {K : ℝ≥0} (hf : LipschitzWith K f)
    {G : Set (EuclideanSpace ℝ (Fin 2))} (hG : MeasurableSet G)
    (hred : graphMap f '' G ⊆ reducedBoundary E hE hmE) :
    ∀ᵐ y ∂(hausdorffMeasure2 3).restrict (graphMap f '' G),
      ∃ x ∈ G, graphMap f x = y ∧ DifferentiableAt ℝ f x ∧
        (reducedNormal E hE hmE y = graphUnitNormal (gradient f x) ∨
          reducedNormal E hE hmE y = -graphUnitNormal (gradient f x)) := by
  rw [hausdorffMeasure2_restrict_graphMap_image hf hG,
    (measurableEmbedding_graphMap hf).ae_map_iff]
  have ha := (ae_restrict_mem hG).and ((ae_restrict_of_ae hf.ae_differentiableAt).and
    (ae_reducedNormal_eq_graphUnitNormal_or_neg_base E hE hmE hf hG hred))
  filter_upwards [(withDensity_absolutelyContinuous (volume.restrict G)
    (fun x => ENNReal.ofReal (Real.sqrt (1 + ‖gradient f x‖ ^ 2)))).ae_le ha] with x hx
  exact ⟨x, hx.1, rfl, hx.2.1, hx.2.2⟩

end LiquidDrop

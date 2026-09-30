module

public import NoCompromise.Stationary.MinimizerContext
public import NoCompromise.Stationary.ChartLocalize
public import NoCompromise.BV.ExteriorGeometry
public import NoCompromise.Regularity.PenalizationQuasiminimal
public import NoCompromise.Regularity.RepresentativeBoundary
public import NoCompromise.Regularity.IsometryDensity
public import NoCompromise.Regularity.ExcessDecayCoordinates
public import NoCompromise.Regularity.EpsRegularityMain
public import NoCompromise.Stationary.BootstrapC2Chart

@[expose] public section

/-!
# The C¹,¹ᐟ² boundary of the minimizer

Blueprint `not:minimizer-rep`, via `thm:eps-regularity`. The given open C¹
representative equals its density-one representative, and its topological and
reduced boundaries agree pointwise. Continuity of chart normals and the
quasiminimal perimeter bound give small excess. ε-regularity then makes the
chart normal one-half Hölder; local Lipschitz inversion of the normal-to-slope
map upgrades the same chart height to C¹,¹ᐟ².
-/

noncomputable section
open Set MeasureTheory Filter Metric InnerProductSpace
open scoped Topology ENNReal Gradient

namespace LiquidDrop

/-- Blueprint `not:minimizer-rep`: an open C¹ domain is the interior of its closure. -/
theorem HasC1Boundary.interior_closure_eq {E : Set AmbientSpace}
    (h : HasC1Boundary E) (hE : IsOpen E) : interior (closure E) = E := by
  apply Subset.antisymm
  · intro x hx
    by_contra hxE
    have hxf : x ∈ frontier E := by
      rw [hE.frontier_eq]
      exact ⟨interior_subset hx, hxE⟩
    have hf : frontier (closure E) = frontier E := by
      simpa only [frontier_compl] using h.frontier_exterior
    have hx' : x ∈ frontier (closure E) := hf.symm ▸ hxf
    exact hx'.2 hx
  · exact hE.subset_interior_iff.mpr subset_closure

/-- Blueprint `not:minimizer-rep`: interior points of an open set have density one. -/
theorem isOpen_subset_densityOne {E : Set AmbientSpace} (hE : IsOpen E) :
    E ⊆ densityOne E := by
  intro x hx
  obtain ⟨r, hr, hsub⟩ := Metric.isOpen_iff.mp hE x hx
  apply mem_densityOne_of_compl_inter_ball_eq_zero hE.measurableSet.nullMeasurableSet hr
  have he : Eᶜ ∩ ball x r = ∅ := by
    exact eq_empty_iff_forall_notMem.mpr fun y hy => hy.1 (hsub hy.2)
  rw [he, measure_empty]

/-- Blueprint `not:minimizer-rep`: density-one points lie in the topological closure. -/
theorem densityOne_subset_closure (E : Set AmbientSpace) : densityOne E ⊆ closure E := by
  intro x hx
  by_contra hxc
  obtain ⟨r, hr, hsub⟩ := Metric.isOpen_iff.mp isClosed_closure.isOpen_compl x hxc
  have he : E ∩ ball x r = ∅ := by
    exact eq_empty_iff_forall_notMem.mpr fun y hy => hsub hy.2 (subset_closure hy.1)
  have hz : x ∈ densityZero E :=
    mem_densityZero_of_measure_inter_ball_eq_zero hr (by rw [he, measure_empty])
  exact disjoint_left.mp (disjoint_densityZero_densityOne E) hz hx

/-- Blueprint `not:minimizer-rep`: an open C¹ quasiminimizer equals its density-one set. -/
theorem HasC1Boundary.densityOne_eq {E : Set AmbientSpace} {ω : ℝ}
    (h : HasC1Boundary E) (hE : IsOpen E) (hω : IsOmegaMinimal E ω) :
    densityOne E = E := by
  apply Subset.antisymm
  · have hs := hω.isOpen_densityOne.subset_interior_iff.mpr (densityOne_subset_closure E)
    rwa [h.interior_closure_eq hE] at hs
  · exact isOpen_subset_densityOne hE

/-- Blueprint `not:minimizer-rep`: the fixed minimizer is exactly its density-one representative. -/
theorem MinimizerRep.densityOne_eq {V : ℝ} {Ω : Set AmbientSpace}
    (h : MinimizerRep V Ω) : densityOne Ω = Ω :=
  h.c1Boundary.densityOne_eq h.isOpen (h.minimizer.isOmegaMinimal h.volume_pos)

/-- Blueprint `not:minimizer-rep`: the two boundary representatives agree everywhere. -/
theorem MinimizerRep.frontier_densityOne_eq {V : ℝ} {Ω : Set AmbientSpace}
    (h : MinimizerRep V Ω) : frontier (densityOne Ω) = frontier Ω := by
  rw [h.densityOne_eq]

/-- Blueprint `not:minimizer-rep`: rigid coordinates preserve the exact representative. -/
theorem MinimizerRep.densityOne_preimage_eq {V : ℝ} {Ω : Set AmbientSpace}
    (h : MinimizerRep V Ω) (a : AmbientSpace ≃ᵃⁱ[ℝ] AmbientSpace) :
    densityOne (a ⁻¹' Ω) = a ⁻¹' Ω := by
  rw [densityOne_preimage_affineIsometry, h.densityOne_eq]

/-- Blueprint `not:minimizer-rep`: rigid coordinates identify the two boundaries everywhere. -/
theorem MinimizerRep.frontier_densityOne_preimage_eq {V : ℝ} {Ω : Set AmbientSpace}
    (h : MinimizerRep V Ω) (a : AmbientSpace ≃ᵃⁱ[ℝ] AmbientSpace) :
    frontier (densityOne (a ⁻¹' Ω)) = a ⁻¹' frontier Ω := by
  rw [frontier_densityOne_preimage_affineIsometry, h.frontier_densityOne_eq]

/-- Blueprint `not:minimizer-rep`: a boundary point moved to the origin meets the
boundary-point hypothesis of ε-regularity. -/
theorem MinimizerRep.zero_mem_frontier_densityOne_preimage {V : ℝ} {Ω : Set AmbientSpace}
    (h : MinimizerRep V Ω) {p : AmbientSpace} (hp : p ∈ frontier Ω)
    (a : AmbientSpace ≃ᵃⁱ[ℝ] AmbientSpace) (ha : a 0 = p) :
    (0 : AmbientSpace) ∈ frontier (densityOne (a ⁻¹' Ω)) := by
  rw [h.frontier_densityOne_preimage_eq, mem_preimage, ha]
  exact hp

/-- Blueprint `not:minimizer-rep`: uniform normal oscillation bounds the excess integral
by the actual perimeter mass of the ball. -/
theorem normalExcessIntegral_ball_le_of_bound {E : Set AmbientSpace}
    (hE : HasLocallyFinitePerimeter E) (hmE : NullMeasurableSet E volume)
    (p ν : AmbientSpace) (r b : ℝ)
    (hb : ∀ y ∈ reducedBoundary E hE hmE, y ∈ ball p r →
      ‖reducedNormal E hE hmE y - ν‖ ^ 2 ≤ b) :
    normalExcessIntegral E hE hmE (ball p r) ν ≤
      b * (perimeterIn E (ball p r)).toReal := by
  let μ := (hausdorffMeasure2 3).restrict (reducedBoundary E hE hmE)
  let : IsFiniteMeasureOnCompacts μ :=
    (reducedBoundary_outwardPerimeterPolar E hE hmE).finiteOnCompacts
  have hfin : μ (ball p r) < ∞ := isBounded_ball.measure_lt_top
  have hc : IntegrableOn (fun _ : AmbientSpace => b) (ball p r) μ :=
    integrableOn_const hfin.ne
  have hi := integrableOn_normal_excess E hE hmE (U := ball p r) isBounded_ball ν
  have hle : normalExcessIntegral E hE hmE (ball p r) ν ≤ ∫ _ in ball p r, b ∂μ := by
    apply integral_mono_ae hi hc
    filter_upwards [ae_restrict_mem measurableSet_ball,
      ae_restrict_of_ae (ae_restrict_mem (measurableSet_reducedBoundary E hE hmE))] with y hy hyr
    exact hb y hyr hy
  have hm : μ (ball p r) = perimeterIn E (ball p r) := by
    dsimp [μ]
    rw [← canonicalPerimeterMeasure_eq_reducedBoundary_area E hE hmE]
    exact canonicalPerimeterMeasure_open E hE hmE isOpen_ball
  simpa only [integral_const, Measure.restrict_apply_univ, smul_eq_mul,
    measureReal_def, hm, mul_comm] using hle

/-- Blueprint `not:minimizer-rep`: at every point of a C¹ chart, the cylindrical
excess in the chart-normal direction, plus the quasiminimality error, is small
at all sufficiently small positive radii. -/
theorem C1BoundaryChart.IsChartFor.exists_small_excess {E : Set AmbientSpace} {ω : ℝ}
    {c : C1BoundaryChart} (hc : c.IsChartFor E) (h : HasC1Boundary E)
    (hE : IsOpen E) (hω : IsOmegaMinimal E ω) {p : AmbientSpace} (hpc : p ∈ c.region)
    {ε : ℝ} (hε : 0 < ε) :
    ∃ ρ > 0, ρ ≤ 1 ∧ ∀ r, 0 < r → r ≤ ρ →
      cylindricalExcess E hω.locallyFinite hω.nullMeasurable p r (c.outwardNormal p) +
        ω * r ≤ ε := by
  let K := 4 * (4 * Real.pi + ω * (4 * Real.pi / 3))
  have hω0 := hω.nonneg
  have hK : 0 < K := by dsimp [K]; positivity
  have hb : 0 < ε / (4 * K) := by positivity
  have hcont : Continuous (fun y => ‖c.outwardNormal y - c.outwardNormal p‖ ^ 2) :=
    (c.continuous_outwardNormal.sub continuous_const).norm.pow 2
  have hn : ∀ᶠ y in 𝓝 p, ‖c.outwardNormal y - c.outwardNormal p‖ ^ 2 < ε / (4 * K) :=
    hcont.continuousAt.eventually_lt_const (by simpa using hb)
  obtain ⟨δ, hδ, hδsub⟩ := Metric.mem_nhds_iff.mp
    (inter_mem (c.isOpen_region.mem_nhds hpc) hn)
  let ρ := min (min (δ / 4) (1 / 4)) (ε / (2 * (ω + 1)))
  have hω1 : 0 < ω + 1 := by linarith [hω.nonneg]
  have hρ : 0 < ρ := by dsimp [ρ]; positivity
  have hρδ : ρ ≤ δ / 4 := (min_le_left _ _).trans (min_le_left _ _)
  have hρ4 : ρ ≤ 1 / 4 := (min_le_left _ _).trans (min_le_right _ _)
  have hρε : ρ ≤ ε / (2 * (ω + 1)) := min_le_right _ _
  refine ⟨ρ, hρ, by linarith, ?_⟩
  intro r hr hrρ
  have hsqrt : Real.sqrt 2 ≤ 2 := by
    nlinarith [Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 2), Real.sqrt_nonneg 2]
  have hs : 0 < Real.sqrt 2 * r := mul_pos (Real.sqrt_pos.mpr (by norm_num)) hr
  have hsδ : Real.sqrt 2 * r < δ := by
    have := mul_le_mul_of_nonneg_right hsqrt hr.le
    linarith [hrρ.trans hρδ]
  have hs1 : Real.sqrt 2 * r ≤ 1 / 2 := by
    have := mul_le_mul_of_nonneg_right hsqrt hr.le
    linarith [hrρ.trans hρ4]
  have hint := normalExcessIntegral_ball_le_of_bound hω.locallyFinite hω.nullMeasurable
    p (c.outwardNormal p) (Real.sqrt 2 * r) (ε / (4 * K)) (by
      intro y hyr hy
      have hyδ := hδsub ((ball_subset_ball hsδ.le) hy)
      rw [hc.reduced_normal_eq h hE hω.locallyFinite hyr hyδ.1]
      exact hyδ.2.le)
  have hper := hω.perimeterIn_ball_upper p hs hs1
  have hsph : sphericalExcess E hω.locallyFinite hω.nullMeasurable p
      (Real.sqrt 2 * r) (c.outwardNormal p) ≤ ε / 4 := by
    unfold sphericalExcess
    apply (div_le_iff₀ (sq_pos_of_pos hs)).mpr
    calc
      _ ≤ ε / (4 * K) * (perimeterIn E (ball p (Real.sqrt 2 * r))).toReal := hint
      _ ≤ ε / (4 * K) * (K * (Real.sqrt 2 * r) ^ 2) :=
        mul_le_mul_of_nonneg_left hper hb.le
      _ = ε / 4 * (Real.sqrt 2 * r) ^ 2 := by field_simp
  have hcyl := (excess_ball_cylinder_comparison E hω.locallyFinite hω.nullMeasurable
    p hr (c.norm_outwardNormal p)).2
  have herr : ω * r ≤ ε / 2 := by
    have hh := (le_div_iff₀ (by positivity : 0 < 2 * (ω + 1))).mp (hrρ.trans hρε)
    nlinarith [hω.nonneg]
  linarith

/-- Blueprint `not:minimizer-rep`: a rigid motion centered at the specified boundary
point aligns its chart normal with the vertical axis and makes the exact
ε-regularity excess hypothesis hold at every sufficiently small radius. -/
theorem MinimizerRep.exists_small_excess_rigid {V : ℝ} {Ω : Set AmbientSpace}
    (h : MinimizerRep V Ω) {p : AmbientSpace} (hp : p ∈ frontier Ω)
    {ε : ℝ} (hε : 0 < ε) :
    ∃ c : C1BoundaryChart, c.IsChartFor Ω ∧ p ∈ c.region ∧
      ∃ a : AmbientSpace ≃ᵃⁱ[ℝ] AmbientSpace,
        a 0 = p ∧ a.linearIsometryEquiv (EuclideanSpace.single 2 1) = c.outwardNormal p ∧
        ∃ ω : ℝ, ∃ hω : IsOmegaMinimal (a ⁻¹' Ω) ω,
          (0 : AmbientSpace) ∈ frontier (densityOne (a ⁻¹' Ω)) ∧
          ∃ ρ > 0, ρ ≤ 1 ∧ ∀ r, 0 < r → r ≤ ρ →
            cylindricalExcess (a ⁻¹' Ω) hω.locallyFinite hω.nullMeasurable 0 r
              (EuclideanSpace.single 2 1) + ω * r ≤ ε := by
  obtain ⟨c, hc, hpc⟩ := h.c1Boundary p hp
  let Q := verticalAxisIsometry (c.outwardNormal p)
  let a := Q.toAffineIsometryEquiv.trans (AffineIsometryEquiv.vaddConst ℝ p)
  have ha : a 0 = p := by simp [a]
  have hlin : a.linearIsometryEquiv (EuclideanSpace.single 2 1) = c.outwardNormal p := by
    change Q (EuclideanSpace.single 2 1) = c.outwardNormal p
    exact verticalAxisIsometry_apply_vertical (c.norm_outwardNormal p)
  let ω := coulombBoundConstant *
    (V + volume.real (ball (0 : AmbientSpace) 1)) ^ ((2 : ℝ) / 3) +
      62 * (energy Ω).toReal / V
  have hω : IsOmegaMinimal Ω ω := h.minimizer.isOmegaMinimal h.volume_pos
  have hF := hω.preimage_affineIsometry a
  have he : excessDecayCoordinates Ω p 1 (c.outwardNormal p) = a ⁻¹' Ω := by
    ext y
    simp [excessDecayCoordinates, blowupSet, a, Q, add_comm]
  obtain ⟨ρ, hρ, hρ1, hsmall⟩ := hc.exists_small_excess h.c1Boundary h.isOpen hω hpc hε
  refine ⟨c, hc, hpc, a, ha, hlin, ω, hF,
    h.zero_mem_frontier_densityOne_preimage hp a ha, ρ, hρ, hρ1, ?_⟩
  intro r hr hrρ
  have hexc := cylindricalExcess_excessDecayCoordinates hω p (c.outwardNormal p)
    (r := 1) zero_lt_one le_rfl r (EuclideanSpace.single 2 1)
  simp only [he, one_mul, verticalAxisIsometry_apply_vertical (c.norm_outwardNormal p)] at hexc
  rw [hexc]
  exact hsmall r hr hrρ

/-- Blueprint `not:minimizer-rep`: an open C¹ quasiminimizer has no exceptional
topological boundary points outside its reduced boundary. -/
theorem HasC1Boundary.reducedBoundary_eq_frontier {E : Set AmbientSpace} {ω : ℝ}
    (h : HasC1Boundary E) (hE : IsOpen E) (hω : IsOmegaMinimal E ω) :
    reducedBoundary E hω.locallyFinite hω.nullMeasurable = frontier E := by
  apply Subset.antisymm (h.reducedBoundary_subset_frontier hE hω.locallyFinite)
  intro x hx
  let μ := canonicalPerimeterMeasure E hω.locallyFinite hω.nullMeasurable
  let ν := canonicalOutwardPolarDensity E hω.locallyFinite hω.nullMeasurable
  let : μ.Regular := (canonicalPerimeterPolar E hω.locallyFinite hω.nullMeasurable).regular
  have hclosure : closure (reducedBoundary E hω.locallyFinite hω.nullMeasurable) =
      frontier E := by
    rw [hω.closure_reducedBoundary, ← hω.frontier_densityOne, h.densityOne_eq hE hω]
  have hsupport : x ∈ μ.support := by
    apply closure_minimal (s := reducedBoundary E hω.locallyFinite hω.nullMeasurable)
      (fun y hy => hy.1) μ.isClosed_support
    rwa [hclosure]
  obtain ⟨c, hc, hxc⟩ := h x hx
  have hlim := tendsto_average_ball_continuous μ c.continuous_outwardNormal.neg x hsupport
  obtain ⟨δ, hδ, hsub⟩ := Metric.mem_nhds_iff.mp (c.isOpen_region.mem_nhds hxc)
  have heq : (fun r : ℝ => ⨍ y in ball x r, -ν y ∂μ) =ᶠ[𝓝[>] 0]
      (fun r : ℝ => ⨍ y in ball x r, -c.outwardNormal y ∂μ) := by
    filter_upwards [(eventually_lt_nhds hδ).filter_mono nhdsWithin_le_nhds] with r hr
    simp only [setAverage_eq]
    congr 1
    apply integral_congr_ae
    filter_upwards [ae_restrict_of_ae (hc.canonical_normal_eq_ae h hE hω.locallyFinite),
      ae_restrict_mem measurableSet_ball] with y hy hyb
    exact congrArg Neg.neg (hy (hsub ((ball_subset_ball hr.le) hyb)))
  exact ⟨hsupport, -c.outwardNormal x, by rw [norm_neg, c.norm_outwardNormal],
    hlim.congr' heq.symm⟩

/-- Blueprint `not:minimizer-rep`: every boundary point of the fixed representative
is a reduced-boundary point, with the existing perimeter witnesses. -/
theorem MinimizerRep.reducedBoundary_eq_frontier {V : ℝ} {Ω : Set AmbientSpace}
    (h : MinimizerRep V Ω) :
    reducedBoundary Ω h.hasLocallyFinitePerimeter h.nullMeasurableSet = frontier Ω :=
  h.c1Boundary.reducedBoundary_eq_frontier h.isOpen (h.minimizer.isOmegaMinimal h.volume_pos)

/-- Blueprint `not:minimizer-rep`: the same graph chart in rigidly changed coordinates. -/
def C1BoundaryChart.preimage (c : C1BoundaryChart)
    (a : AmbientSpace ≃ᵃⁱ[ℝ] AmbientSpace) : C1BoundaryChart where
  height := c.height
  height_contDiff := c.height_contDiff
  placement := c.placement.trans a.symm
  region := a ⁻¹' c.region
  isOpen_region := c.isOpen_region.preimage a.continuous
  bounded_region := a.isometry.antilipschitzWith.isBounded_preimage c.bounded_region

/-- Blueprint `not:minimizer-rep`: rigid pullback preserves the one-sided chart condition. -/
theorem C1BoundaryChart.IsChartFor.preimage {E : Set AmbientSpace} {c : C1BoundaryChart}
    (hc : c.IsChartFor E) (a : AmbientSpace ≃ᵃⁱ[ℝ] AmbientSpace) :
    (c.preimage a).IsChartFor (a ⁻¹' E) := by
  intro z hz
  exact hc (a z) hz

/-- Blueprint `not:minimizer-rep`: rigid pullback preserves C¹ boundary. -/
theorem HasC1Boundary.preimage_affineIsometry {E : Set AmbientSpace}
    (h : HasC1Boundary E) (a : AmbientSpace ≃ᵃⁱ[ℝ] AmbientSpace) :
    HasC1Boundary (a ⁻¹' E) := by
  intro p hp
  have hp' : a p ∈ frontier E := by
    change p ∈ a.toHomeomorph ⁻¹' frontier E
    rw [a.toHomeomorph.preimage_frontier]
    exact hp
  obtain ⟨c, hc, hpc⟩ := h (a p) hp'
  exact ⟨c.preimage a, hc.preimage a, hpc⟩

/-- Blueprint `not:minimizer-rep`: chart normals transform by the inverse orthogonal map. -/
theorem C1BoundaryChart.outwardNormal_preimage (c : C1BoundaryChart)
    (a : AmbientSpace ≃ᵃⁱ[ℝ] AmbientSpace) (z : AmbientSpace) :
    (c.preimage a).outwardNormal z = a.linearIsometryEquiv.symm (c.outwardNormal (a z)) := by
  rfl

/-- Blueprint `not:minimizer-rep`: ε-regularity upgrades a chart normal to
one-half Hölder continuity on the boundary in a neighborhood of its center. -/
theorem MinimizerRep.exists_chart_normal_holder {V : ℝ} {Ω : Set AmbientSpace}
    (h : MinimizerRep V Ω) {p : AmbientSpace} (hp : p ∈ frontier Ω) :
    ∃ c : C1BoundaryChart, c.IsChartFor Ω ∧ p ∈ c.region ∧
      ∃ δ > 0, ball p δ ⊆ c.region ∧ ∃ M ≥ 0,
        ∀ x ∈ frontier Ω ∩ ball p δ, ∀ y ∈ frontier Ω ∩ ball p δ,
          ‖c.outwardNormal x - c.outwardNormal y‖ ≤ M * Real.sqrt ‖x - y‖ := by
  obtain ⟨ε, hε, C, hC, hreg⟩ := eps_regularity
  obtain ⟨c, hc, hpc, a, ha, _, ω, hω, h0, r, hr, hr1, hsmall⟩ :=
    h.exists_small_excess_rigid hp hε
  obtain ⟨f, ν, _, _, _, _, _, hred, hhold⟩ :=
    hreg (a ⁻¹' Ω) ω hω r h0 hr hr1 (hsmall r hr le_rfl)
  have hD := h.c1Boundary.preimage_affineIsometry a
  have ho := h.isOpen.preimage a.continuous
  have hdeq : densityOne (a ⁻¹' Ω) = a ⁻¹' Ω := h.densityOne_preimage_eq a
  have hrbeq := hD.reducedBoundary_eq_frontier ho hω
  obtain ⟨t, ht, htreg⟩ := Metric.mem_nhds_iff.mp (c.isOpen_region.mem_nhds hpc)
  let δ := min t (r / 4)
  have hδ : 0 < δ := lt_min ht (by positivity)
  have hδreg : ball p δ ⊆ c.region :=
    (ball_subset_ball (min_le_left _ _)).trans htreg
  let X := cylindricalExcess (a ⁻¹' Ω) hω.locallyFinite hω.nullMeasurable 0 r
    (EuclideanSpace.single 2 1) + ω * r
  let M := C * Real.sqrt X / Real.sqrt r
  have hM : 0 ≤ M := by dsimp [M]; positivity
  have hpoint (x : AmbientSpace) (hx : x ∈ frontier Ω ∩ ball p δ) :
      a.symm x ∈ frontier (densityOne (a ⁻¹' Ω)) ∩ standardCylinder (r / 4) := by
    refine ⟨?_, ?_⟩
    · rw [h.frontier_densityOne_preimage_eq]
      simpa only [mem_preimage, a.apply_symm_apply] using hx.1
    · rw [standardCylinder_eq_cylinder]
      apply ball_subset_cylinder 0 (r / 4) (by simp)
      have hd : dist (a.symm x) 0 = dist x p := by
        rw [← a.dist_map, a.apply_symm_apply, ha]
      rw [mem_ball, hd]
      exact (mem_ball.mp hx.2).trans_le (min_le_right _ _)
  have hnormal (x : AmbientSpace) (hx : x ∈ frontier Ω ∩ ball p δ) :
      ν (a.symm x) = (c.preimage a).outwardNormal (a.symm x) := by
    have hxp := hpoint x hx
    have hxr : a.symm x ∈ reducedBoundary (a ⁻¹' Ω) hω.locallyFinite hω.nullMeasurable := by
      rw [hrbeq]
      simpa only [hdeq] using hxp.1
    exact (hred _ ⟨hxr, hxp.2⟩).trans
      ((hc.preimage a).reduced_normal_eq hD ho hω.locallyFinite hxr
        (by simpa only [C1BoundaryChart.preimage, mem_preimage, a.apply_symm_apply]
            using hδreg hx.2))
  refine ⟨c, hc, hpc, δ, hδ, hδreg, M, hM, ?_⟩
  intro x hx y hy
  have hh := hhold _ (hpoint x hx) _ (hpoint y hy)
  rw [hnormal x hx, hnormal y hy, c.outwardNormal_preimage, c.outwardNormal_preimage,
    a.apply_symm_apply, a.apply_symm_apply, ← map_sub, a.linearIsometryEquiv.symm.norm_map] at hh
  have hdist : ‖a.symm x - a.symm y‖ = ‖x - y‖ := by
    simpa only [dist_eq_norm] using a.symm.dist_map x y
  rw [hdist, Real.sqrt_div (norm_nonneg _)] at hh
  calc
    _ ≤ C * (Real.sqrt ‖x - y‖ / Real.sqrt r) * Real.sqrt X := hh
    _ = M * Real.sqrt ‖x - y‖ := by dsimp [M]; ring

/-- Blueprint `not:minimizer-rep`: recover a graph derivative from its upward unit normal. -/
def normalGraphSlope (v : AmbientSpace) : EuclideanSpace ℝ (Fin 2) →L[ℝ] ℝ :=
  -(v 2)⁻¹ • innerSL ℝ (graphProjectionN 2 v)

/-- Blueprint `not:minimizer-rep`: the normal-to-slope map is C¹ off the vertical equator. -/
theorem contDiffAt_normalGraphSlope {v : AmbientSpace} (hv : v 2 ≠ 0) :
    ContDiffAt ℝ 1 normalGraphSlope v := by
  exact (((EuclideanSpace.proj (2 : Fin 3) : AmbientSpace →L[ℝ] ℝ).contDiff.contDiffAt.inv
    hv).neg).smul
    (((innerSL ℝ (E := EuclideanSpace ℝ (Fin 2))).restrictScalars ℝ).contDiff.contDiffAt.comp v
      (graphProjectionN 2).contDiff.contDiffAt)

/-- Blueprint `not:minimizer-rep`: the normal-to-slope formula inverts the graph normal. -/
theorem normalGraphSlope_smoothGraphUnitNormal (v : EuclideanSpace ℝ (Fin 2)) :
    normalGraphSlope (smoothGraphUnitNormal v) = innerSL ℝ v := by
  have hs : Real.sqrt (1 + ‖v‖ ^ 2) ≠ 0 := ne_of_gt (Real.sqrt_pos.mpr (by positivity))
  simp [normalGraphSlope, smoothGraphUnitNormal, map_smul, smul_smul, hs]

/-- Blueprint `not:minimizer-rep`: a one-half Hölder chart normal makes the same
chart height C¹,¹ᐟ² on a sufficiently small disk. -/
theorem C1BoundaryChart.IsChartFor.height_hasC1HolderOn_of_normal_holder
    {E : Set AmbientSpace} {c : C1BoundaryChart} (hc : c.IsChartFor E)
    {p : AmbientSpace} (hp : p ∈ frontier E) (hpc : p ∈ c.region)
    {δ M : ℝ} (hδ : 0 < δ) (hδreg : ball p δ ⊆ c.region) (hM : 0 ≤ M)
    (hhold : ∀ x ∈ frontier E ∩ ball p δ, ∀ y ∈ frontier E ∩ ball p δ,
      ‖c.outwardNormal x - c.outwardNormal y‖ ≤ M * Real.sqrt ‖x - y‖) :
    ∃ ρ > 0, HasC1HolderOn (1 / 2) c.height
      (ball (graphProjectionN 2 (c.placement.symm p)) ρ) := by
  let y0 := graphProjectionN 2 (c.placement.symm p)
  let F := fun y => c.placement (graphMapN c.height y)
  let N := fun y => c.placement.linearIsometryEquiv.symm (c.outwardNormal (F y))
  have hF : ContDiff ℝ 1 F :=
    (contDiff_rigidPlacement c.placement).comp (contDiffOn_univ.mp
      (contDiffOn_graphMapN c.height_contDiff.contDiffOn))
  have hN : Continuous N := c.placement.linearIsometryEquiv.symm.continuous.comp
    (c.continuous_outwardNormal.comp hF.continuous)
  have hFy0 : F y0 = p := by
    have hpg : p ∈ c.graphSurface :=
      (hc.frontier_inter_eq ▸ (show p ∈ frontier E ∩ c.region from ⟨hp, hpc⟩)).1
    obtain ⟨_, ⟨y, rfl⟩, hy⟩ := hpg
    dsimp [F, y0]
    rw [← hy, c.placement.symm_apply_apply]
    change c.placement (graphMapN c.height
      (graphProjectionN 2 (graphAppendN y (c.height y)))) = c.placement (graphMapN c.height y)
    rw [graphProjectionN_append]
  have hNformula (y : EuclideanSpace ℝ (Fin 2)) :
      N y = smoothGraphUnitNormal (gradient c.height y) := by
    dsimp only [N, F, C1BoundaryChart.outwardNormal, smoothSubgraphNormal]
    rw [c.placement.symm_apply_apply, c.placement.linearIsometryEquiv.symm_apply_apply]
    change smoothGraphUnitNormal (gradient c.height
      (graphProjectionN 2 (graphAppendN y (c.height y)))) = _
    rw [graphProjectionN_append]
  have hN0 : N y0 2 ≠ 0 := by
    rw [hNformula]
    have hs : (Real.sqrt (1 + ‖gradient c.height y0‖ ^ 2))⁻¹ ≠ 0 := by positivity
    simpa [smoothGraphUnitNormal] using hs
  have hslope (y : EuclideanSpace ℝ (Fin 2)) :
      normalGraphSlope (N y) = fderiv ℝ c.height y := by
    rw [hNformula, normalGraphSlope_smoothGraphUnitNormal]
    exact toDual_gradient
  obtain ⟨K, U, hU, hLip⟩ := (contDiffAt_normalGraphSlope hN0).exists_lipschitzOnWith
  have hnear : {y | N y ∈ U ∧ F y ∈ ball p δ} ∈ 𝓝 y0 := by
    have hnU : {y | N y ∈ U} ∈ 𝓝 y0 := hN.continuousAt hU
    have hfU : {y | F y ∈ ball p δ} ∈ 𝓝 y0 := by
      apply hF.continuous.continuousAt
      rw [hFy0]
      exact ball_mem_nhds p hδ
    exact inter_mem hnU hfU
  obtain ⟨ρ, hρ, hρsub⟩ := Metric.mem_nhds_iff.mp hnear
  obtain ⟨L, hL⟩ := hF.contDiffOn.exists_lipschitzOnWith one_ne_zero
    (convex_closedBall y0 ρ) (isCompact_closedBall y0 ρ)
  have hpoint (y : EuclideanSpace ℝ (Fin 2)) (hy : y ∈ ball y0 ρ) :
      F y ∈ frontier E ∩ ball p δ := by
    have hyball := (hρsub hy).2
    refine ⟨?_, hyball⟩
    have hyg : F y ∈ c.graphSurface ∩ c.region :=
      ⟨⟨graphMapN c.height y, mem_range_self y, rfl⟩, hδreg hyball⟩
    exact (hc.frontier_inter_eq.symm ▸ hyg).1
  have hderiv (x : EuclideanSpace ℝ (Fin 2)) (hx : x ∈ ball y0 ρ)
      (y : EuclideanSpace ℝ (Fin 2)) (hy : y ∈ ball y0 ρ) :
      ‖fderiv ℝ c.height x - fderiv ℝ c.height y‖ ≤
        ((K : ℝ) * M * Real.sqrt (L : ℝ)) * Real.sqrt ‖x - y‖ := by
    have hSl := hLip.dist_le_mul (N x) (hρsub hx).1 (N y) (hρsub hy).1
    have hSl' : ‖fderiv ℝ c.height x - fderiv ℝ c.height y‖ ≤ (K : ℝ) * ‖N x - N y‖ := by
      simpa only [dist_eq_norm, hslope] using hSl
    have hn : ‖N x - N y‖ = ‖c.outwardNormal (F x) - c.outwardNormal (F y)‖ := by
      dsimp [N]
      rw [← map_sub, c.placement.linearIsometryEquiv.symm.norm_map]
    rw [hn] at hSl'
    have hNl := hhold _ (hpoint x hx) _ (hpoint y hy)
    have hFl : ‖F x - F y‖ ≤ (L : ℝ) * ‖x - y‖ := by
      simpa only [dist_eq_norm] using
        hL.dist_le_mul x (ball_subset_closedBall hx) y (ball_subset_closedBall hy)
    calc
      _ ≤ (K : ℝ) * ‖c.outwardNormal (F x) - c.outwardNormal (F y)‖ := hSl'
      _ ≤ (K : ℝ) * (M * Real.sqrt ‖F x - F y‖) :=
        mul_le_mul_of_nonneg_left hNl K.coe_nonneg
      _ ≤ (K : ℝ) * (M * Real.sqrt ((L : ℝ) * ‖x - y‖)) :=
        mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left
          (Real.sqrt_le_sqrt hFl) hM) K.coe_nonneg
      _ = _ := by rw [Real.sqrt_mul L.coe_nonneg]; ring
  obtain ⟨B, hB⟩ := (isCompact_closedBall y0 ρ).exists_bound_of_continuousOn
    (c.height_contDiff.continuous_fderiv one_ne_zero).continuousOn
  refine ⟨ρ, hρ, c.height_contDiff.contDiffOn,
    bootstrap_holder_of_contDiffOn_closedBall (by norm_num) (by norm_num)
      y0 ρ c.height_contDiff.contDiffOn, ?_⟩
  apply HasFiniteHolderNormOn.of_bounds (A := max 0 B)
    (B := (K : ℝ) * M * Real.sqrt (L : ℝ)) (le_max_left _ _) (by positivity)
  · intro x hx
    exact (hB x (ball_subset_closedBall hx)).trans (le_max_right _ _)
  · intro x hx y hy
    rw [← Real.sqrt_eq_rpow]
    by_cases hxy : x = y
    · subst y
      simp only [sub_self, norm_zero, Real.sqrt_zero, div_zero]
      positivity
    · exact (div_le_iff₀ (Real.sqrt_pos.mpr (norm_pos_iff.mpr (sub_ne_zero.mpr hxy)))).mpr
        (hderiv x hx y hy)

/-- Blueprint `not:minimizer-rep`: the fixed minimizer has C¹,¹ᐟ² boundary,
by `thm:eps-regularity` and the given C¹ charts. -/
theorem MinimizerRep.hasC1HolderBoundary {V : ℝ} {Ω : Set AmbientSpace}
    (h : MinimizerRep V Ω) : HasC1HolderBoundary (1 / 2) Ω := by
  intro p hp
  obtain ⟨c, hc, hpc, δ, hδ, hδreg, M, hM, hhold⟩ := h.exists_chart_normal_holder hp
  exact ⟨c, hc, hpc, hc.height_hasC1HolderOn_of_normal_holder hp hpc hδ hδreg hM hhold⟩

end LiquidDrop

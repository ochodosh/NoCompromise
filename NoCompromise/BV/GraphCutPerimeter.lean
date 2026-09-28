import NoCompromise.BV.RadialCuts

/-!
# Exact perimeter of a complete graph cut

A genuine trace which equals the density-one representative gives the exact
bulk-plus-surface perimeter measure. Complete graph domains may be unbounded.
-/

noncomputable section
open MeasureTheory Set Filter Metric
open scoped ENNReal Topology
namespace LiquidDrop
set_option maxSynthPendingDepth 8

lemma C1BoundaryChart.graphArea_finiteOnCompacts (c : C1BoundaryChart) :
    IsFiniteMeasureOnCompacts ((hausdorffMeasure2 3).restrict c.graphSurface) := by
  let : IsFiniteMeasureOnCompacts (smoothGraphArea c.height) :=
    smoothGraphArea_finiteOnCompacts c.height_contDiff
  rw [C1BoundaryChart.graphSurface, hausdorffMeasure2_restrict_affineIsometry_image]
  exact Measure.IsFiniteMeasureOnCompacts.map (smoothGraphArea c.height) c.placement.toHomeomorph

lemma C1BoundaryChart.volume_graphSurface (c : C1BoundaryChart) :
    volume c.graphSurface = 0 := by
  rw [C1BoundaryChart.graphSurface, volume_image_affineIsometry]
  exact volume_range_smoothGraph c.height_contDiff.continuous

/-- Coordinate distributional pairings suffice for an exact disjoint positive
bulk-plus-surface perimeter measure. -/
lemma perimeterIn_eq_of_disjoint_coordinate_pairing
    {F D : Set AmbientSpace} (hmF : NullMeasurableSet F volume) (hD : MeasurableSet D)
    {μ ρ : Measure AmbientSpace} [IsFiniteMeasureOnCompacts μ] [IsFiniteMeasureOnCompacts ρ]
    {ν η : AmbientSpace → AmbientSpace} (hν : Measurable ν) (hη : Measurable η)
    (hnν : ∀ᵐ x ∂μ, ‖ν x‖ = 1) (hnη : ∀ᵐ x ∂ρ, ‖η x‖ = 1)
    (hρD : ρ D = 0)
    (hpair : ∀ (i : Fin 3) (φ : CompactlySupportedContinuousMap AmbientSpace ℝ),
      ContDiff ℝ 1 φ →
        (∫ x in F, fderiv ℝ φ x (EuclideanSpace.single i 1)) =
          (∫ x in D, φ x * ν x i ∂μ) + ∫ x, φ x * η x i ∂ρ)
    {U : Set AmbientSpace} (hU : IsOpen U) :
    perimeterIn F U = (μ.restrict D + ρ) U := by
  classical
  have hνi : LocallyIntegrable ν μ :=
    locallyIntegrable_of_ae_norm_le μ hν.aestronglyMeasurable (hnν.mono fun _ hx => hx.le)
  have hηi : LocallyIntegrable η ρ :=
    locallyIntegrable_of_ae_norm_le ρ hη.aestronglyMeasurable (hnη.mono fun _ hx => hx.le)
  let μs : Bool → Measure AmbientSpace := fun b => if b then ρ else μ.restrict D
  let σs : Bool → AmbientSpace → AmbientSpace := fun b => if b then -η else -ν
  have his (b : Bool) : LocallyIntegrable (σs b) (μs b) := by
    cases b
    · exact hνi.neg.mono_measure Measure.restrict_le_self
    · exact hηi.neg
  apply perimeterIn_eq_of_disjoint_divergence_pairing hmF hD hν hη
    (ae_restrict_of_ae hnν) hnη hρD _ hU
  intro X hX hcX
  have hi : LocallyIntegrable (F.indicator (fun _ => (1 : ℝ))) volume :=
    locallyIntegrable_indicator_one hmF
  have ht := integral_divergence_eq_sum_of_coordinate_pairings hi his
    (fun i φ hφ => by
      have he := hpair i φ hφ
      have hid : (fun x => F.indicator (fun _ => (1 : ℝ)) x *
          fderiv ℝ φ x (EuclideanSpace.single i 1)) =
          F.indicator (fun x => fderiv ℝ φ x (EuclideanSpace.single i 1)) := by
        funext x
        by_cases hx : x ∈ F <;> simp [hx]
      rw [hid, integral_indicator₀ hmF]
      simpa only [μs, σs, Fintype.sum_bool, Bool.false_eq_true, ↓reduceIte,
        Pi.neg_apply, PiLp.neg_apply, mul_neg, integral_neg, add_comm, neg_add_rev] using
        congrArg Neg.neg he) hX hcX
  have hid : (fun x => F.indicator (fun _ => (1 : ℝ)) x * divergenceN X x) =
      F.indicator (divergenceN X) := by
    funext x
    by_cases hx : x ∈ F <;> simp [hx]
  rw [hid, integral_indicator₀ hmF] at ht
  simp only [μs, σs, Fintype.sum_bool, Bool.false_eq_true, ↓reduceIte,
    Pi.neg_apply, inner_neg_right, integral_neg] at ht
  linarith

/-- The local graph trace determines the exact interior-cut perimeter on every
open test region. No global mass or boundedness assumption is imposed. -/
theorem C1BoundaryChart.perimeterIn_cut_eq_of_trace (c : C1BoundaryChart)
    {E : Set AmbientSpace} (hE : HasLocallyFinitePerimeter E)
    (hmE : NullMeasurableSet E volume)
    (htrace : c.lowerBVTrace (E.indicator (fun _ => (1 : ℝ))) =ᵐ[(hausdorffMeasure2 3).restrict
      c.graphSurface]
        (densityOne E).indicator (fun _ => (1 : ℝ)))
    {U : Set AmbientSpace} (hU : IsOpen U) :
    perimeterIn (E ∩ c.graphDomain) U = perimeterIn E (U ∩ c.graphDomain) +
      hausdorffMeasure2 3 (U ∩ (densityOne E ∩ c.graphSurface)) := by
  have hp := canonicalPerimeterPolar E hE hmE
  let := hp.regular
  let := hp.finiteOnCompacts
  let := c.graphArea_finiteOnCompacts
  let S := densityOne E ∩ c.graphSurface
  let ρ := (hausdorffMeasure2 3).restrict S
  have hρeq : ρ = ((hausdorffMeasure2 3).restrict c.graphSurface).restrict (densityOne E) := by
    rw [Measure.restrict_restrict (measurableSet_densityOne hmE)]
  let : IsFiniteMeasureOnCompacts ρ := by rw [hρeq]; infer_instance
  have hρD : ρ c.graphDomain = 0 := by
    rw [Measure.restrict_apply c.isOpen_graphDomain.measurableSet]
    apply measure_mono_null (t := ∅) _ (measure_empty)
    intro x hx
    have hxf : x ∈ frontier c.graphDomain := c.frontier_graphDomain.symm ▸ hx.2.2
    exact ((disjoint_frontier_iff_isOpen.mpr c.isOpen_graphDomain).le_bot
      ⟨hxf, hx.1⟩).elim
  have ht := perimeterIn_eq_of_disjoint_coordinate_pairing
    (hmE.inter c.isOpen_graphDomain.measurableSet.nullMeasurableSet)
    c.isOpen_graphDomain.measurableSet hp.measurable c.continuous_outwardNormal.measurable
    hp.norm_ae (ae_of_all ρ c.norm_outwardNormal) hρD
    (fun i φ hφ => by
      have hh := c.cut_pairing_of_coordinate_polar (hE.isLocallyBVOn_indicator hmE univ)
        hp.locallyIntegrable.neg (fun j ψ hψ => hp.coordinate_eq j ψ hψ)
        (EuclideanSpace.single i 1) hφ φ.hasCompactSupport
      have hid : (fun x => E.indicator (fun _ => (1 : ℝ)) x *
          fderiv ℝ φ x (EuclideanSpace.single i 1)) =
          E.indicator (fun x => fderiv ℝ φ x (EuclideanSpace.single i 1)) := by
        funext x
        by_cases hx : x ∈ E <;> simp [hx]
      rw [hid, setIntegral_indicator_eq_inter_of_nullMeasurable hmE] at hh
      simp only [Pi.neg_apply, inner_neg_right, mul_neg, integral_neg, neg_neg,
        EuclideanSpace.inner_single_left, map_one, one_mul] at hh
      rw [hh]
      congr 1
      calc
        _ = ∫ x in c.graphSurface, (densityOne E).indicator
            (fun x => φ x * c.outwardNormal x i) x ∂hausdorffMeasure2 3 := by
          apply integral_congr_ae
          filter_upwards [htrace] with x hx
          rw [hx]
          by_cases he : x ∈ densityOne E <;> simp [he]
        _ = _ := setIntegral_indicator_eq_inter_of_nullMeasurable
          (measurableSet_densityOne hmE).nullMeasurableSet _) hU
  rw [ht, Measure.add_apply, Measure.restrict_apply hU.measurableSet,
    Measure.restrict_apply hU.measurableSet,
    hp.open_eq _ (hU.inter c.isOpen_graphDomain)]

end LiquidDrop

module

public import NoCompromise.Energy.PotentialRegularity
public import NoCompromise.DeGiorgi.Structure
public import NoCompromise.DeGiorgi.SmoothBoundary

@[expose] public section

/-!
# Boundary first variation of Coulomb energy

The established bulk first variation is the divergence integral of `v_E X`.
The potential of a bounded source is already proved C¹ on all of space, so
Gauss–Green applies directly to this compactly supported C¹ field. This yields
the actual reduced-boundary formula for bounded locally finite-perimeter sets,
and the topological-boundary formula for bounded C¹ domains. Classical normal
conventions are specified by the existing outward graph-chart normals.
-/

noncomputable section
open Set Filter MeasureTheory Metric
open scoped Topology NNReal ENNReal RealInnerProductSpace Gradient
namespace LiquidDrop

/-- The already constructed classical gradient gives the exact scalar force
pairing at every point, with an absolutely convergent kernel integral. -/
lemma inner_gradient_coulombPotential_of_isBounded {E : Set AmbientSpace}
    (hEb : Bornology.IsBounded E) (x v : AmbientSpace) :
    inner ℝ (gradient (fun a => (coulombPotential E a).toReal) x) v =
      -(∫ y in E, inner ℝ (x - y) v / ‖x - y‖ ^ 3) := by
  rw [real_inner_comm, gradient_coulombPotential_of_isBounded hEb x]
  change (innerSL ℝ v) (∫ y in E, -(‖x - y‖ ^ 3)⁻¹ • (x - y)) = _
  rw [← (innerSL ℝ v).integral_comp_comm
    (integrableOn_newtonGradientKernel E hEb.measure_lt_top x), ← integral_neg]
  apply integral_congr_ae
  filter_upwards [] with y
  simp only [innerSL_apply_apply, inner_smul_right, div_eq_mul_inv,
    real_inner_comm v (x - y)]
  ring

/-- The complete unsymmetrized Coulomb bulk integrand is the divergence of the
C¹ field formed from the actual potential and the ambient perturbation. -/
lemma integral_coulombBulkSingleIntegrand_eq_divergence {E : Set AmbientSpace}
    (hEb : Bornology.IsBounded E) {X : AmbientSpace → AmbientSpace}
    (hX : ContDiff ℝ 1 X) (hcX : HasCompactSupport X) :
    (∫ p in E ×ˢ E, coulombBulkSingleIntegrand X p) =
      ∫ x in E, divergenceN (fun y => (coulombPotential E y).toReal • X y) x := by
  have hp := contDiff_one_coulombPotential_of_isBounded hEb
  have hd : Continuous (divergenceN X) :=
    continuous_standardMatrix3.matrix_trace.comp (hX.continuous_fderiv (by simp))
  have hiD : IntegrableOn (fun x => (coulombPotential E x).toReal * divergenceN X x) E :=
    ((hp.continuous.mul hd).continuousOn.integrableOn_compact hEb.isCompact_closure).mono_set
      subset_closure
  have hGc : Continuous (fun x => inner ℝ
      (gradient (fun a => (coulombPotential E a).toReal) x) (X x)) :=
    (continuous_gradient_coulombPotential_of_isBounded hEb).inner hX.continuous
  have hiG : IntegrableOn (fun x => inner ℝ
      (gradient (fun a => (coulombPotential E a).toReal) x) (X x)) E :=
    (hGc.continuousOn.integrableOn_compact hEb.isCompact_closure).mono_set subset_closure
  rw [integral_coulombBulkSingleIntegrand_eq_potential hX hcX hEb.measure_lt_top]
  simp_rw [divergenceN_smul hp hX]
  rw [integral_add hiD hiG]
  simp_rw [inner_gradient_coulombPotential_of_isBounded hEb]
  rw [integral_neg]
  simp only [mul_comm (coulombPotential E _).toReal, sub_eq_add_neg]

/-- The boundary Coulomb flux is absolutely integrable, even when the bounded
set has only local finite perimeter. -/
lemma integrableOn_coulomb_boundary_flux {E : Set AmbientSpace}
    (hE : HasLocallyFinitePerimeter E) (hmE : NullMeasurableSet E volume)
    (hEb : Bornology.IsBounded E) {X : AmbientSpace → AmbientSpace}
    (hX : Continuous X) (hcX : HasCompactSupport X) :
    IntegrableOn (fun x => (coulombPotential E x).toReal *
      inner ℝ (X x) (reducedNormal E hE hmE x)) (reducedBoundary E hE hmE)
        (hausdorffMeasure2 3) := by
  have h := reducedBoundary_outwardPerimeterPolar E hE hmE
  let μ := (hausdorffMeasure2 3).restrict (reducedBoundary E hE hmE)
  let := h.finiteOnCompacts
  have hw : Continuous (fun x => (coulombPotential E x).toReal • X x) :=
    (contDiff_one_coulombPotential_of_isBounded hEb).continuous.smul hX
  have hcw : HasCompactSupport (fun x => (coulombPotential E x).toReal • X x) := by
    exact hcX.smul_left (f := fun x => (coulombPotential E x).toReal)
  have hm : Measurable (fun x => inner ℝ ((coulombPotential E x).toReal • X x)
      (reducedNormal E hE hmE x)) :=
    (continuous_inner (𝕜 := ℝ)).measurable.comp (hw.measurable.prodMk h.measurable)
  have hi : Integrable (fun x => inner ℝ ((coulombPotential E x).toReal • X x)
      (reducedNormal E hE hmE x)) μ := by
    apply (hw.norm.integrable_of_hasCompactSupport hcw.norm).mono' hm.aestronglyMeasurable
    filter_upwards [h.norm_ae] with x hx
    simpa only [hx, mul_one] using norm_inner_le_norm (𝕜 := ℝ)
      ((coulombPotential E x).toReal • X x) (reducedNormal E hE hmE x)
  simpa only [real_inner_smul_left, μ, IntegrableOn] using hi

/-- Coulomb first variation for bounded, Lebesgue-measurable sets of locally
finite perimeter, with the true outward reduced normal and normalized H². -/
theorem first_variation_coulomb {E : Set AmbientSpace}
    (hE : HasLocallyFinitePerimeter E) (hmE : NullMeasurableSet E volume)
    (hEb : Bornology.IsBounded E) {X : AmbientSpace → AmbientSpace}
    (hX : ContDiff ℝ 1 X) (hcX : HasCompactSupport X) :
    HasDerivAt (fun t : ℝ => (coulombEnergy (straightPerturbation X t '' E)).toReal)
      (∫ x in reducedBoundary E hE hmE, (coulombPotential E x).toReal *
        inner ℝ (X x) (reducedNormal E hE hmE x) ∂hausdorffMeasure2 3) 0 := by
  have hp := contDiff_one_coulombPotential_of_isBounded hEb
  have hd := hasDerivAt_coulombEnergy_straightPerturbation_single_of_finiteVolume
    hX hcX hmE hEb.measure_lt_top
  rw [integral_coulombBulkSingleIntegrand_eq_divergence hEb hX hcX] at hd
  have hprod : ContDiff ℝ 1 (fun x => (coulombPotential E x).toReal • X x) := hp.smul hX
  have hcprod : HasCompactSupport (fun x => (coulombPotential E x).toReal • X x) :=
    hcX.smul_left (f := fun x => (coulombPotential E x).toReal)
  have hgg := gauss_green E hE hmE (fun x => (coulombPotential E x).toReal • X x) hprod hcprod
  simp only [real_inner_smul_left] at hgg
  rw [hgg] at hd
  exact hd


/-- A classical normal specified by its outward graph-chart values agrees with
the actual reduced normal at every reduced-boundary point. -/
lemma HasC1Boundary.reducedNormal_eq_of_chart_normal {E : Set AmbientSpace}
    (h : HasC1Boundary E) (hE : IsOpen E) (hP : HasLocallyFinitePerimeter E)
    {ν : AmbientSpace → AmbientSpace}
    (hν : ∀ c : C1BoundaryChart, c.IsChartFor E →
      ∀ x ∈ frontier E, x ∈ c.region → ν x = c.outwardNormal x)
    {x : AmbientSpace} (hx : x ∈ reducedBoundary E hP hE.measurableSet.nullMeasurableSet) :
    reducedNormal E hP hE.measurableSet.nullMeasurableSet x = ν x := by
  have hxf := h.reducedBoundary_subset_frontier hE hP hx
  obtain ⟨c, hc, hxc⟩ := h x hxf
  exact (hc.reduced_normal_eq h hE hP hx hxc).trans (hν c hc x hxf hxc).symm

/-- Hausdorff integration on the entire C¹ frontier equals the canonical
reduced-boundary integral for any explicitly chart-compatible normal. -/
lemma integral_coulomb_flux_frontier_eq_reducedBoundary {E : Set AmbientSpace}
    (h : HasC1Boundary E) (hE : IsOpen E) (hP : HasLocallyFinitePerimeter E)
    {ν X : AmbientSpace → AmbientSpace}
    (hν : ∀ c : C1BoundaryChart, c.IsChartFor E →
      ∀ x ∈ frontier E, x ∈ c.region → ν x = c.outwardNormal x) :
    (∫ x in frontier E, (coulombPotential E x).toReal * inner ℝ (X x) (ν x)
      ∂hausdorffMeasure2 3) =
      ∫ x in reducedBoundary E hP hE.measurableSet.nullMeasurableSet,
        (coulombPotential E x).toReal *
          inner ℝ (X x) (reducedNormal E hP hE.measurableSet.nullMeasurableSet x)
            ∂hausdorffMeasure2 3 := by
  rw [Measure.restrict_congr_set (h.boundary_ae_eq_reducedBoundary hE hP)]
  apply integral_congr_ae
  filter_upwards [ae_restrict_mem
    (measurableSet_reducedBoundary E hP hE.measurableSet.nullMeasurableSet)] with x hx
  rw [h.reducedNormal_eq_of_chart_normal hE hP hν hx]

/-- Absolute integrability of the classical Coulomb boundary flux; no independent
surface-kernel integrability or trace premise is needed. -/
lemma integrableOn_coulomb_flux_frontier {E : Set AmbientSpace}
    (h : HasC1Boundary E) (hE : IsOpen E) (hEb : Bornology.IsBounded E)
    {ν X : AmbientSpace → AmbientSpace}
    (hν : ∀ c : C1BoundaryChart, c.IsChartFor E →
      ∀ x ∈ frontier E, x ∈ c.region → ν x = c.outwardNormal x)
    (hX : Continuous X) (hcX : HasCompactSupport X) :
    IntegrableOn (fun x => (coulombPotential E x).toReal * inner ℝ (X x) (ν x))
      (frontier E) (hausdorffMeasure2 3) := by
  let hP := h.hasLocallyFinitePerimeter hE
  have hi := integrableOn_coulomb_boundary_flux hP hE.measurableSet.nullMeasurableSet hEb hX hcX
  rw [IntegrableOn, Measure.restrict_congr_set (h.boundary_ae_eq_reducedBoundary hE hP)]
  apply hi.congr
  filter_upwards [ae_restrict_mem
    (measurableSet_reducedBoundary E hP hE.measurableSet.nullMeasurableSet)] with x hx
  rw [h.reducedNormal_eq_of_chart_normal hE hP hν hx]

/-- The full classical Coulomb first-variation formula for bounded C¹ domains.
The normal's convention is explicit through agreement with outward graph-chart
normals. C¹ compactly supported perturbing fields suffice. -/
theorem first_variation_coulomb_of_hasC1Boundary {E : Set AmbientSpace}
    (h : HasC1Boundary E) (hE : IsOpen E) (hEb : Bornology.IsBounded E)
    {ν X : AmbientSpace → AmbientSpace}
    (hν : ∀ c : C1BoundaryChart, c.IsChartFor E →
      ∀ x ∈ frontier E, x ∈ c.region → ν x = c.outwardNormal x)
    (hX : ContDiff ℝ 1 X) (hcX : HasCompactSupport X) :
    HasDerivAt (fun t : ℝ => (coulombEnergy (straightPerturbation X t '' E)).toReal)
      (∫ x in frontier E, (coulombPotential E x).toReal * inner ℝ (X x) (ν x)
        ∂hausdorffMeasure2 3) 0 := by
  rw [integral_coulomb_flux_frontier_eq_reducedBoundary h hE
    (h.hasLocallyFinitePerimeter hE) hν]
  exact first_variation_coulomb (h.hasLocallyFinitePerimeter hE)
    hE.measurableSet.nullMeasurableSet hEb hX hcX


/-- A bounded C¹ domain needs no independent normal-field input: the canonical
normal, already identified with graph normals on the reduced boundary, may be
integrated over the whole frontier because the two boundaries agree H²-a.e. -/
theorem first_variation_coulomb_frontier {E : Set AmbientSpace}
    (h : HasC1Boundary E) (hE : IsOpen E) (hEb : Bornology.IsBounded E)
    {X : AmbientSpace → AmbientSpace} (hX : ContDiff ℝ 1 X) (hcX : HasCompactSupport X) :
    HasDerivAt (fun t : ℝ => (coulombEnergy (straightPerturbation X t '' E)).toReal)
      (∫ x in frontier E, (coulombPotential E x).toReal *
        inner ℝ (X x) (reducedNormal E (h.hasLocallyFinitePerimeter hE)
          hE.measurableSet.nullMeasurableSet x) ∂hausdorffMeasure2 3) 0 := by
  rw [Measure.restrict_congr_set
    (h.boundary_ae_eq_reducedBoundary hE (h.hasLocallyFinitePerimeter hE))]
  exact first_variation_coulomb (h.hasLocallyFinitePerimeter hE)
    hE.measurableSet.nullMeasurableSet hEb hX hcX

end LiquidDrop

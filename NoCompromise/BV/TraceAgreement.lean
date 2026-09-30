module

public import NoCompromise.BV.ChartTraces

@[expose] public section

/-!
# Agreement of actual BV traces on C¹ chart overlaps

The two chart cut identities have the same original bulk derivative. Local
uniqueness therefore identifies the boundary trace vectors. Agreement of the
geometric unit normals gives agreement of the scalar traces.
-/

noncomputable section
open MeasureTheory Set Filter Metric
open scoped ENNReal Topology
namespace LiquidDrop
set_option maxSynthPendingDepth 8

/-- The lower trace vector, restricted to the bounded chart region. -/
def C1BoundaryChart.lowerTraceVector (c : C1BoundaryChart) (f : AmbientSpace → ℝ) :
    AmbientSpace → AmbientSpace :=
  c.region.indicator (fun z => c.lowerBVTrace f z • c.outwardNormal z)

lemma C1BoundaryChart.IsChartFor.integrable_lowerTraceVector {c : C1BoundaryChart}
    {E : Set AmbientSpace} (hc : c.IsChartFor E)
    {f : AmbientSpace → ℝ} (hf : IsLocallyBVOn f univ) :
    Integrable (c.lowerTraceVector f) ((hausdorffMeasure2 3).restrict (frontier E)) := by
  have hi := (hc.integrableOn_BVTraces hf).1.smul_bdd 1
    c.continuous_outwardNormal.aestronglyMeasurable
    (ae_of_all _ fun z => (c.norm_outwardNormal z).le)
  apply (integrable_indicator_iff c.isOpen_region.measurableSet).mpr
  exact hi

lemma C1BoundaryChart.integral_lowerTraceVector_component (c : C1BoundaryChart)
    (f : AmbientSpace → ℝ) (μ : Measure AmbientSpace) (i : Fin 3)
    (φ : AmbientSpace → ℝ) (hsφ : tsupport φ ⊆ c.region) :
    (∫ z, φ z * c.lowerTraceVector f z i ∂μ) =
      ∫ z, c.lowerBVTrace f z * (φ z * c.outwardNormal z i) ∂μ := by
  classical
  apply integral_congr_ae
  exact ae_of_all _ fun z => by
    by_cases hz : z ∈ c.region
    · simp only [lowerTraceVector, Set.indicator_of_mem hz, PiLp.smul_apply, smul_eq_mul]
      ring
    · have hzero : φ z = 0 := image_eq_zero_of_notMem_tsupport (fun h => hz (hsφ h))
      simp only [hzero, zero_mul, mul_zero]

/-- The constructed lower traces agree almost everywhere on every chart overlap. -/
theorem C1BoundaryChart.IsChartFor.lowerBVTrace_agree_ae {c d : C1BoundaryChart}
    {E : Set AmbientSpace} (hc : c.IsChartFor E) (hd : d.IsChartFor E)
    (h : HasC1Boundary E) (hE : IsOpen E)
    {f : AmbientSpace → ℝ} (hf : IsLocallyBVOn f univ) :
    ∀ᵐ z ∂(hausdorffMeasure2 3).restrict (frontier E), z ∈ c.region ∩ d.region →
      c.lowerBVTrace f z = d.lowerBVTrace f z := by
  obtain ⟨μ, σ, hμ, hμfin, _, _, hσ, hp, _⟩ := hf.exists_ambient_scalar_polar
  let : μ.Regular := hμ
  let : IsFiniteMeasureOnCompacts μ := hμfin
  have hpair (i : Fin 3) (φ : CompactlySupportedContinuousMap AmbientSpace ℝ)
      (hφ : ContDiff ℝ 1 φ) (hsφ : tsupport φ ⊆ c.region ∩ d.region) :
      (∫ z, φ z * c.lowerTraceVector f z i
        ∂(hausdorffMeasure2 3).restrict (frontier E)) =
      ∫ z, φ z * d.lowerTraceVector f z i
        ∂(hausdorffMeasure2 3).restrict (frontier E) := by
    have hsc : tsupport φ ⊆ c.region := hsφ.trans inter_subset_left
    have hsd : tsupport φ ⊆ d.region := hsφ.trans inter_subset_right
    rw [c.integral_lowerTraceVector_component f _ i φ hsc,
      d.integral_lowerTraceVector_component f _ i φ hsd]
    have hpc := hc.cut_pairing hE.measurableSet hf hσ hp (EuclideanSpace.single i 1)
      hφ φ.hasCompactSupport hsc
    have hpd := hd.cut_pairing hE.measurableSet hf hσ hp (EuclideanSpace.single i 1)
      hφ φ.hasCompactSupport hsd
    simp only [EuclideanSpace.inner_single_left, map_one, one_mul] at hpc hpd
    linarith
  have heq := ae_eq_density_on_of_coordinate_pairings (c.isOpen_region.inter d.isOpen_region)
    (hc.integrable_lowerTraceVector hf).locallyIntegrable
    (hd.integrable_lowerTraceVector hf).locallyIntegrable hpair
  have heq' := (ae_restrict_iff' (c.isOpen_region.inter d.isOpen_region).measurableSet).mp heq
  filter_upwards [heq', hc.outwardNormal_agree_ae hd h hE] with z hz hn
  intro hzd
  have hv := hz hzd
  change c.region.indicator (fun z => c.lowerBVTrace f z • c.outwardNormal z) z =
    d.region.indicator (fun z => d.lowerBVTrace f z • d.outwardNormal z) z at hv
  rw [Set.indicator_of_mem hzd.1, Set.indicator_of_mem hzd.2, ← hn hzd] at hv
  have hi := congrArg (fun w => inner ℝ w (c.outwardNormal z)) hv
  simpa only [real_inner_smul_left, real_inner_self_eq_norm_sq, c.norm_outwardNormal z,
    one_pow, mul_one] using hi

end LiquidDrop

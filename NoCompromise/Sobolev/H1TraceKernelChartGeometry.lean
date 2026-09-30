module

public import NoCompromise.Sobolev.H1TraceKernelChartMeasure
public import NoCompromise.Sobolev.H1TraceBoundaryGeometry

@[expose] public section

/-!
# Boundary-chart geometry for the trace kernel

The central plane is precisely the boundary inside a valid chart. The
Lipschitz inverse therefore controls parameter integrals by surface integrals.
-/

noncomputable section
open MeasureTheory Set Filter Metric
open scoped ENNReal NNReal Topology
namespace LiquidDrop
set_option maxSynthPendingDepth 8

lemma LipschitzGraphChart.mem_frontier_of_normal_eq_zero {n : ℕ}
    {D : Set (EuclideanSpace ℝ (Fin n))} (hD : IsOpen D)
    (c : LipschitzGraphChart n) (hc : c.IsChartFor D)
    {x : EuclideanSpace ℝ (Fin n)} (hxr : x ∈ c.region)
    (hx0 : c.homeomorph.symm x c.normal = 0) : x ∈ frontier D := by
  let y := c.homeomorph.symm x
  have hy : y ∈ coordinateCube n c.radius := by
    obtain ⟨z, hz, rfl⟩ := hxr
    simpa only [y, c.homeomorph.symm_apply_apply] using hz
  let z (j : ℕ) := y + (1 / ((j : ℝ) + 1)) • EuclideanSpace.single c.normal (1 : ℝ)
  have hz : Tendsto z atTop (𝓝 y) := by
    simpa only [zero_smul, add_zero] using
      tendsto_const_nhds.add ((tendsto_one_div_add_atTop_nhds_zero_nat (𝕜 := ℝ)).smul
        (tendsto_const_nhds (x := EuclideanSpace.single c.normal (1 : ℝ))))
  have hzD : ∀ᶠ j in atTop, c.homeomorph (z j) ∈ D := by
    filter_upwards [hz.eventually ((isOpen_coordinateCube n c.radius).mem_nhds hy)]
      with j hj
    have hpos : 0 < z j c.normal := by
      simp only [z, PiLp.add_apply, PiLp.smul_apply, PiLp.single_apply,
        ite_true, smul_eq_mul, mul_one, show y c.normal = 0 from hx0, zero_add]
      positivity
    exact (hc ▸ (show c.homeomorph (z j) ∈ c.upperRegion from
      ⟨z j, ⟨hj, hpos⟩, rfl⟩)).1
  have hcl : x ∈ closure D := by
    have ht := (c.homeomorph.continuous.tendsto y).comp hz
    rw [show c.homeomorph y = x from c.homeomorph.apply_symm_apply x] at ht
    exact mem_closure_of_tendsto ht hzD
  refine ⟨hcl, ?_⟩
  rw [hD.interior_eq]
  intro hxD
  have hxup : x ∈ c.upperRegion := hc.symm ▸ ⟨hxD, hxr⟩
  obtain ⟨w, hw, heq⟩ := hxup
  have hw0 : w c.normal = 0 := by
    rw [← heq, c.homeomorph.symm_apply_apply] at hx0
    exact hx0
  exact (ne_of_gt hw.2) hw0

lemma LipschitzGraphChart.plane_inter_region_subset_frontier {k : ℕ}
    {D : Set (EuclideanSpace ℝ (Fin (k + 1)))} (hD : IsOpen D)
    (c : LipschitzGraphChart (k + 1)) (hc : c.IsChartFor D) :
    range (fun x => c.boundaryPlaneChart (graphAppendN x 0)) ∩ c.region ⊆ frontier D := by
  rintro _ ⟨⟨x, rfl⟩, hxr⟩
  apply c.mem_frontier_of_normal_eq_zero hD hc hxr
  change c.homeomorph.symm (c.homeomorph (coareaSwap c.normal (graphAppendN x 0)))
    c.normal = 0
  simp only [c.homeomorph.symm_apply_apply, coareaSwap_apply,
    Equiv.swap_apply_left, graphAppendN_last]

lemma lipschitzWith_graphProjectionN (k : ℕ) : LipschitzWith 1 (graphProjectionN k) := by
  apply LipschitzWith.of_dist_le_mul
  intro x y
  simp only [dist_eq_norm, ← map_sub, NNReal.coe_one, one_mul]
  have h := norm_sq_graphProjectionN (x - y)
  nlinarith only [h, sq_nonneg ((x - y) (Fin.last k)), norm_nonneg (x - y),
    norm_nonneg (graphProjectionN k (x - y))]

lemma memLp_chart_parameter_of_surface {k : ℕ}
    (e : EuclideanSpace ℝ (Fin (k + 1)) ≃ₜ EuclideanSpace ℝ (Fin (k + 1)))
    {K : ℝ≥0} (hi : LipschitzWith K e.symm)
    {f : EuclideanSpace ℝ (Fin (k + 1)) → ℝ}
    (hf : MemLp f 2 ((Measure.euclideanHausdorffMeasure k).restrict
      (range (fun x => e (graphAppendN x 0))))) :
    MemLp (fun x => f (e (graphAppendN x 0))) 2 volume ∧
      lpNorm (fun x => f (e (graphAppendN x 0))) 2 volume ^ 2 ≤
        (K : ℝ) ^ k * lpNorm f 2 ((Measure.euclideanHausdorffMeasure k).restrict
          (range (fun x => e (graphAppendN x 0)))) ^ 2 := by
  have hm : MeasurableEmbedding (fun x => e (graphAppendN x 0)) := by
    simpa only [graphAppendN, zero_smul, add_zero, Function.comp_def] using
      e.isClosedEmbedding.measurableEmbedding.comp
        (isometry_graphBaseN k).isClosedEmbedding.measurableEmbedding
  have hq : LipschitzWith K (fun z => graphProjectionN k (e.symm z)) := by
    simpa only [one_mul, Function.comp_def] using (lipschitzWith_graphProjectionN k).comp hi
  exact memLp_parameter_of_lipschitz_inverse hm hq
    (fun x => by simp only [e.symm_apply_apply, graphProjectionN_append]) hf

end LiquidDrop

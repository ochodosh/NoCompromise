import NoCompromise.DeGiorgi.SmoothBoundary
import Mathlib.Analysis.Calculus.FDeriv.Affine
import Mathlib.Analysis.Calculus.Deriv.Slope

/-!
# Pointwise agreement of classical boundary normals

The one-sided graph definition fixes the orientation at every boundary point.
The proof uses directional derivatives of graph defining functions and does not
identify the normals through perimeter measures.
-/

noncomputable section
open MeasureTheory Set Filter Metric Topology InnerProductSpace
open scoped Topology ENNReal NNReal Gradient
namespace LiquidDrop
set_option maxSynthPendingDepth 8

/-- The negative side of this defining function is the chart's graph domain. -/
def C1BoundaryChart.definingFunction (c : C1BoundaryChart) (z : AmbientSpace) : ℝ :=
  c.placement.symm z (Fin.last 2) - c.height (graphProjectionN 2 (c.placement.symm z))

lemma C1BoundaryChart.IsChartFor.mem_iff_definingFunction_neg {c : C1BoundaryChart}
    {D : Set AmbientSpace} (hc : c.IsChartFor D) {z : AmbientSpace} (hz : z ∈ c.region) :
    z ∈ D ↔ c.definingFunction z < 0 := by
  simpa only [C1BoundaryChart.definingFunction, sub_neg, smoothSubgraph, mem_ofPred_eq]
    using hc z hz

lemma C1BoundaryChart.IsChartFor.definingFunction_eq_zero {c : C1BoundaryChart}
    {D : Set AmbientSpace} (hc : c.IsChartFor D) {z : AmbientSpace}
    (hz : z ∈ frontier D) (hr : z ∈ c.region) : c.definingFunction z = 0 := by
  have hs : z ∈ c.graphSurface := (hc.frontier_inter_eq ▸
    (show z ∈ frontier D ∩ c.region from ⟨hz, hr⟩)).1
  obtain ⟨y, ⟨x, rfl⟩, rfl⟩ := hs
  simp only [C1BoundaryChart.definingFunction, c.placement.symm_apply_apply]
  rw [graphMapN_last, show graphProjectionN 2 (graphMapN c.height x) = x from
    graphProjectionN_append x (c.height x), sub_self]

lemma C1BoundaryChart.hasDerivAt_definingFunction_line (c : C1BoundaryChart)
    (z v : AmbientSpace) :
    HasDerivAt (fun t : ℝ => c.definingFunction (z + t • v))
      (Real.sqrt (1 + ‖gradient c.height (graphProjectionN 2 (c.placement.symm z))‖ ^ 2) *
        inner ℝ v (c.outwardNormal z)) 0 := by
  let L := c.placement.symm.linearIsometryEquiv
  have hline : HasDerivAt (fun t : ℝ => c.placement.symm (z + t • v)) (L v) 0 := by
    have heq : (fun t : ℝ => c.placement.symm (z + t • v)) =
        fun t : ℝ => t • L v + c.placement.symm z := by
      funext t
      simpa only [L, add_comm z, ← vadd_eq_add, map_smul] using
        c.placement.symm.map_vadd z (t • v)
    rw [heq]
    simpa using ((hasDerivAt_id (0 : ℝ)).smul_const (L v)).add_const (c.placement.symm z)
  have hp := (EuclideanSpace.proj (Fin.last 2)).hasFDerivAt.comp_hasDerivAt 0 hline
  have hq := (graphProjectionN 2).hasFDerivAt.comp_hasDerivAt 0 hline
  have hh := (c.height_contDiff.differentiable one_ne_zero _).hasFDerivAt.comp_hasDerivAt 0 hq
  have hd : HasDerivAt (fun t : ℝ => c.definingFunction (z + t • v))
      (L v (Fin.last 2) - fderiv ℝ c.height
        (graphProjectionN 2 (c.placement.symm z)) (graphProjectionN 2 (L v))) 0 := by
    convert! hp.sub hh using 1
    simp
  have heq : Real.sqrt
      (1 + ‖gradient c.height (graphProjectionN 2 (c.placement.symm z))‖ ^ 2) *
      inner ℝ v (c.outwardNormal z) =
      L v (Fin.last 2) - fderiv ℝ c.height
        (graphProjectionN 2 (c.placement.symm z)) (graphProjectionN 2 (L v)) := by
    rw [← inner_gradient_left, ← inner_smoothGraphUnitNormal]
    congr 1
    change inner ℝ v (c.placement.linearIsometryEquiv _) = inner ℝ (L v) _
    rw [real_inner_comm _ v, c.placement.linearIsometryEquiv.inner_map_eq_flip,
      real_inner_comm]
    rfl
  rwa [heq]

/-- A positive derivative at a zero gives positive values immediately to the right. -/
lemma classicalNormal_eventually_pos_of_hasDerivAt {f : ℝ → ℝ} {a : ℝ}
    (hf : HasDerivAt f a 0) (hzero : f 0 = 0) (ha : 0 < a) :
    ∀ᶠ t in 𝓝[>] (0 : ℝ), 0 < f t := by
  have hs := (tendsto_order.mp hf.tendsto_slope_zero_right).1 0 ha
  filter_upwards [hs, self_mem_nhdsWithin] with t ht htp
  simp only [zero_add, hzero, sub_zero, smul_eq_mul] at ht
  exact (mul_pos_iff_of_pos_left (inv_pos.mpr htp)).mp ht

/-- A negative derivative at a zero gives negative values immediately to the right. -/
lemma classicalNormal_eventually_neg_of_hasDerivAt {f : ℝ → ℝ} {a : ℝ}
    (hf : HasDerivAt f a 0) (hzero : f 0 = 0) (ha : a < 0) :
    ∀ᶠ t in 𝓝[>] (0 : ℝ), f t < 0 := by
  have h := classicalNormal_eventually_pos_of_hasDerivAt hf.neg
    (by simp [hzero]) (neg_pos.mpr ha)
  simpa only [Pi.neg_apply, neg_pos] using h

/-- Valid one-sided C¹ charts have the same oriented unit normal at every
boundary point of their overlap. This is a pointwise geometric statement. -/
theorem C1BoundaryChart.IsChartFor.outwardNormal_agree {c d : C1BoundaryChart}
    {D : Set AmbientSpace} (hc : c.IsChartFor D) (hd : d.IsChartFor D)
    {z : AmbientSpace} (hz : z ∈ frontier D) (hzc : z ∈ c.region) (hzd : z ∈ d.region) :
    c.outwardNormal z = d.outwardNormal z := by
  by_contra hne
  let v := c.outwardNormal z - d.outwardNormal z
  have hinner : inner ℝ (c.outwardNormal z) (d.outwardNormal z) < 1 := by
    have hp : 0 < ‖c.outwardNormal z - d.outwardNormal z‖ ^ 2 :=
      sq_pos_of_pos (norm_pos_iff.mpr (sub_ne_zero.mpr hne))
    rw [norm_sub_sq_real, c.norm_outwardNormal, d.norm_outwardNormal] at hp
    nlinarith
  have hcpos : 0 < inner ℝ v (c.outwardNormal z) := by
    simp only [v, inner_sub_left, real_inner_self_eq_norm_sq, c.norm_outwardNormal]
    rw [real_inner_comm (c.outwardNormal z) (d.outwardNormal z)]
    nlinarith
  have hdneg : inner ℝ v (d.outwardNormal z) < 0 := by
    simp only [v, inner_sub_left, real_inner_self_eq_norm_sq, d.norm_outwardNormal]
    nlinarith
  have hpc := classicalNormal_eventually_pos_of_hasDerivAt
    (c.hasDerivAt_definingFunction_line z v)
    (by simpa using hc.definingFunction_eq_zero hz hzc)
    (mul_pos (Real.sqrt_pos.mpr (by positivity)) hcpos)
  have hpd := classicalNormal_eventually_neg_of_hasDerivAt
    (d.hasDerivAt_definingFunction_line z v)
    (by simpa using hd.definingFunction_eq_zero hz hzd)
    (mul_neg_of_pos_of_neg (Real.sqrt_pos.mpr (by positivity)) hdneg)
  have ht : Tendsto (fun t : ℝ => z + t • v) (𝓝[>] 0) (𝓝 z) := by
    have hh : Continuous (fun t : ℝ => z + t • v) := by fun_prop
    simpa using (hh.continuousAt (x := (0 : ℝ))).tendsto.mono_left nhdsWithin_le_nhds
  have hr := ht ((c.isOpen_region.inter d.isOpen_region).mem_nhds ⟨hzc, hzd⟩)
  obtain ⟨t, htc, htd, htr⟩ := (hpc.and (hpd.and hr)).exists
  have hm : z + t • v ∈ D := (hd.mem_iff_definingFunction_neg htr.2).mpr htd
  exact (not_lt_of_gt htc) ((hc.mem_iff_definingFunction_neg htr.1).mp hm)

end LiquidDrop

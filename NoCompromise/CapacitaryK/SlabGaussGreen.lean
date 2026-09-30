module

public import NoCompromise.CapacitaryK.Calculus
public import Mathlib.Analysis.Calculus.LocalExtr.Basic
public import NoCompromise.BV.SmoothApproxLevelCharts
public import NoCompromise.Elliptic.ClassicalGaussGreen
public import NoCompromise.Elliptic.ClassicalNormalGeometry

@[expose] public section

/-!
# Gauss-Green on a regular slab (chapter 31, input to `lem:K-slab-H` and `lem:K-slab-F`)

For `u` of class `C¹` on an open set `U`, and `a < b` regular values whose slab
`S = U ∩ {a < u < b}` is bounded with closure in `U`, the slab is a bounded open set with
`C¹` boundary `U ∩ {u = a} ∪ U ∩ {u = b}`, whose outward normal is `∇u/|∇u|` on the upper
level and `-∇u/|∇u|` on the lower one (`thm:W11-gauss-green` applied to `S`).
-/

noncomputable section

open Set MeasureTheory Filter Metric InnerProductSpace
open scoped Topology
open scoped Gradient RealInnerProductSpace

namespace LiquidDrop.CapacitaryK

/-- The divergence of a vector field on `ℝ³`, as the trace of its derivative in the standard
basis. -/
def vecDiv (X : E3 → E3) (x : E3) : ℝ := ∑ i : Fin 3, fderiv ℝ X x (basisVec i) i

/-- Frontier of a regular slab. -/
theorem slab_frontier_eq {U : Set E3} (hU : IsOpen U) {u : E3 → ℝ} (hu : ContDiffOn ℝ 1 u U)
    {a b : ℝ} (hab : a < b) (hcl : closure (U ∩ u ⁻¹' Ioo a b) ⊆ U)
    (hreg : ∀ x ∈ U, (u x = a ∨ u x = b) → gradient u x ≠ 0) :
    frontier (U ∩ u ⁻¹' Ioo a b) = (U ∩ u ⁻¹' {a}) ∪ (U ∩ u ⁻¹' {b}) := by
  have hS : IsOpen (U ∩ u ⁻¹' Ioo a b) :=
    hu.continuousOn.isOpen_inter_preimage hU isOpen_Ioo
  have hmaps : MapsTo u (U ∩ u ⁻¹' Ioo a b) (Ioo a b) := fun _ hx => hx.2
  ext x
  rw [hS.frontier_eq]
  constructor
  · rintro ⟨hxc, hxs⟩
    have hxU := hcl hxc
    have hxval := hmaps.closure_of_continuousOn (hu.continuousOn.mono hcl) hxc
    rw [closure_Ioo hab.ne] at hxval
    have hends : u x = a ∨ u x = b := by
      by_contra h
      push Not at h
      exact hxs ⟨hxU, lt_of_le_of_ne hxval.1 (Ne.symm h.1),
        lt_of_le_of_ne hxval.2 h.2⟩
    rcases hends with h | h
    · exact Or.inl ⟨hxU, h⟩
    · exact Or.inr ⟨hxU, h⟩
  · intro hx
    have hxU : x ∈ U := hx.elim And.left And.left
    have hends : u x = a ∨ u x = b := hx.elim (fun h => Or.inl h.2) (fun h => Or.inr h.2)
    refine ⟨?_, ?_⟩
    · by_contra hxc
      have hnear : ∀ᶠ y in 𝓝 x, y ∉ closure (U ∩ u ⁻¹' Ioo a b) :=
        isClosed_closure.isOpen_compl.mem_nhds hxc
      have huc : ContinuousAt u x := hu.continuousOn.continuousAt (hU.mem_nhds hxU)
      apply hreg x hxU hends
      rcases hends with ha | hb
      · have hlt : ∀ᶠ y in 𝓝 x, u y < b := huc.eventually (gt_mem_nhds (ha ▸ hab))
        have hm : IsLocalMax u x := by
          filter_upwards [hnear, hU.mem_nhds hxU, hlt] with y hy hyU hyb
          rw [ha]
          by_contra hya
          exact hy (subset_closure ⟨hyU, lt_of_not_ge hya, hyb⟩)
        simp only [gradient, hm.fderiv_eq_zero, map_zero]
      · have hlt : ∀ᶠ y in 𝓝 x, a < u y := huc.eventually (lt_mem_nhds (hb ▸ hab))
        have hm : IsLocalMin u x := by
          filter_upwards [hnear, hU.mem_nhds hxU, hlt] with y hy hyU hya
          rw [hb]
          by_contra hyb
          exact hy (subset_closure ⟨hyU, hya, lt_of_not_ge hyb⟩)
        simp only [gradient, hm.fderiv_eq_zero, map_zero]
    · rintro ⟨_, hxa, hxb⟩
      rcases hends with ha | hb
      · exact (ne_of_gt hxa) ha
      · exact (ne_of_lt hxb) hb

/-- A negative final partial produces the actual one-sided superlevel graph
on an open neighborhood, with a C¹ height on its open base. -/
theorem exists_c1_superlevel_graph_of_last_neg {u : AmbientSpace → ℝ}
    (hu : ContDiff ℝ 1 u) {x : AmbientSpace}
    (hx : gradient u x (Fin.last 2) < 0) :
    ∃ (f : EuclideanSpace ℝ (Fin 2) → ℝ)
      (U : Set (EuclideanSpace ℝ (Fin 2))) (W : Set AmbientSpace),
      IsOpen U ∧ ContDiffOn ℝ 1 f U ∧ graphProjectionN 2 x ∈ U ∧
      IsOpen W ∧ x ∈ W ∧
      ∀ z ∈ W, u x < u z ↔ z (Fin.last 2) < f (graphProjectionN 2 z) := by
  have hg : Continuous (fun z => gradient u z (Fin.last 2)) :=
    (EuclideanSpace.proj (Fin.last 2)).continuous.comp
      (continuous_gradient_of_contDiff hu)
  have hV : IsOpen {z | gradient u z (Fin.last 2) < 0} := isOpen_lt hg continuous_const
  obtain ⟨R, hR, hRV⟩ := Metric.isOpen_iff.mp hV x hx
  obtain ⟨d, hxd, hdb⟩ := exists_scalarCoareaChart isOpen_ball
    hu.contDiffOn (mem_ball_self hR) hx.ne
  have hxD : graphProjectionN 2 x ∈ d.levelDomain (u x) := by
    change graphAppendN (graphProjectionN 2 x) (u x) ∈ d.chart.target
    rw [← coareaCoordinateMap, ← d.forward_eq]
    exact d.chart.map_source hxd
  let W : Set AmbientSpace := ball x R ∩ (graphProjectionN 2) ⁻¹' d.levelDomain (u x)
  have hW : IsOpen W := isOpen_ball.inter
    ((d.isOpen_levelDomain (u x)).preimage (graphProjectionN 2).continuous)
  refine ⟨d.levelHeight (u x), d.levelDomain (u x), W, d.isOpen_levelDomain _,
    d.contDiffOn_levelHeight _, hxD, hW, ⟨mem_ball_self hR, hxD⟩, ?_⟩
  intro z hz
  let y := graphProjectionN 2 z
  let I : Set ℝ := {s | graphAppendN y s ∈ ball x R}
  have hy : y ∈ d.levelDomain (u x) := hz.2
  have hgraph : graphAppendN y (d.levelHeight (u x) y) ∈ ball x R := by
    change graphMapN (d.levelHeight (u x)) y ∈ ball x R
    rw [← d.inverse_eq_graphMapN hy]
    exact hdb (d.chart.map_target hy)
  have hstrict : StrictAntiOn (fun s => u (graphAppendN y s)) I := by
    apply strictAntiOn_of_deriv_neg (convex_verticalSlice_ball x R y)
      (hu.continuous.comp (by unfold graphAppendN; fun_prop)).continuousOn
    intro s hs
    change deriv (fun q => u (graphAppendN y q)) s < 0
    rw [deriv_verticalSlice_eq (hu.differentiable (by simp))]
    exact hRV ((interior_subset : interior I ⊆ I) hs)
  have hzI : z (Fin.last 2) ∈ I := by
    dsimp only [I, y, mem_ofPred_eq]
    rw [graphAppendN_projection]
    exact hz.1
  have hgI : d.levelHeight (u x) y ∈ I := hgraph
  have hlevel : u (graphAppendN y (d.levelHeight (u x) y)) = u x := by
    change u (graphMapN (d.levelHeight (u x)) y) = u x
    rw [← d.inverse_eq_graphMapN hy]
    exact d.u_inverse_eq hy
  have heq := hstrict.lt_iff_gt hgI hzI
  rw [hlevel] at heq
  simpa only [y, graphAppendN_projection] using heq

/-- A regular C¹ superlevel has a rigid local subgraph description. -/
lemma exists_c1_superlevel_graph {U : Set E3} (hU : IsOpen U)
    {u : E3 → ℝ} (hu : ContDiffOn ℝ 1 u U) {x : E3} (hx : x ∈ U)
    (hreg : gradient u x ≠ 0) :
    ∃ (a : E3 ≃ᵃⁱ[ℝ] E3) (f : EuclideanSpace ℝ (Fin 2) → ℝ)
      (B : Set (EuclideanSpace ℝ (Fin 2))) (W : Set E3),
      IsOpen B ∧ ContDiffOn ℝ 1 f B ∧ graphProjectionN 2 (a.symm x) ∈ B ∧
      IsOpen W ∧ x ∈ W ∧
      ∀ z ∈ W, u x < u z ↔ a.symm z (Fin.last 2) < f (graphProjectionN 2 (a.symm z)) := by
  obtain ⟨g, hg, hgu⟩ := exists_contDiff_height_eq_near_compact hU
    (isCompact_singleton (x := x)) (singleton_subset_iff.mpr hx) hu
  have heq := hgu x (mem_singleton x)
  obtain ⟨N, hN, hNo, hxN⟩ := _root_.mem_nhds_iff.mp heq
  have hrg : gradient g x ≠ 0 := heq.gradient_eq ▸ hreg
  obtain ⟨e, he⟩ := exists_frame_with_negative_last_gradient
    (hg.differentiable (by norm_num) x) hrg
  obtain ⟨f, B, W, hB, hf, hxB, hW, hxW, hgraph⟩ :=
    exists_c1_superlevel_graph_of_last_neg
      (hg.comp e.toContinuousLinearEquiv.contDiff) he
  refine ⟨e.toAffineIsometryEquiv, f, B, (e '' W) ∩ N, hB, hf, hxB,
    (e.toHomeomorph.isOpenMap _ hW).inter hNo,
    ⟨⟨e.symm x, hxW, e.apply_symm_apply x⟩, hxN⟩, ?_⟩
  rintro z ⟨⟨y, hy, rfl⟩, hzN⟩
  have hh := hgraph y hy
  change (g (e (e.symm x)) < g (e y)) ↔
    y (Fin.last 2) < f (graphProjectionN 2 y) at hh
  change (u x < u (e y)) ↔
    e.symm (e y) (Fin.last 2) < f (graphProjectionN 2 (e.symm (e y)))
  have hxg : g x = u x := hN hxN
  have hzg : g (e y) = u (e y) := hN hzN
  simpa only [e.apply_symm_apply, e.symm_apply_apply, hxg, hzg] using hh

/-- C¹ boundary of a regular slab. -/
theorem slab_hasC1Boundary {U : Set E3} (hU : IsOpen U) {u : E3 → ℝ} (hu : ContDiffOn ℝ 1 u U)
    {a b : ℝ} (hab : a < b) (hcl : closure (U ∩ u ⁻¹' Ioo a b) ⊆ U)
    (hreg : ∀ x ∈ U, (u x = a ∨ u x = b) → gradient u x ≠ 0) :
    HasC1Boundary (U ∩ u ⁻¹' Ioo a b) := by
  apply hasC1Boundary_of_local_graphs
  intro x hx
  rw [slab_frontier_eq hU hu hab hcl hreg] at hx
  rcases hx with ⟨hxU, ha⟩ | ⟨hxU, hb⟩
  · change u x = a at ha
    obtain ⟨e, f, B, W, hB, hf, hxB, hW, hxW, hgraph⟩ :=
      exists_c1_superlevel_graph hU hu hxU (hreg x hxU (Or.inl ha))
    refine ⟨e, f, B, W ∩ (U ∩ u ⁻¹' Iio b), hB, hf, hxB,
      hW.inter (hu.continuousOn.isOpen_inter_preimage hU isOpen_Iio),
      ⟨hxW, hxU, by simpa only [mem_preimage, mem_Iio, ha] using hab⟩, ?_⟩
    intro z hz
    rw [← hgraph z hz.1, ha]
    exact ⟨fun h => h.2.1, fun h => ⟨hz.2.1, h, hz.2.2⟩⟩
  · change u x = b at hb
    have hr : gradient (fun z => -u z) x ≠ 0 := by
      rw [gradient, show (fun z => -u z) = -u from rfl, fderiv_neg, map_neg]
      exact neg_ne_zero.mpr (hreg x hxU (Or.inr hb))
    obtain ⟨e, f, B, W, hB, hf, hxB, hW, hxW, hgraph⟩ :=
      exists_c1_superlevel_graph hU hu.neg hxU hr
    refine ⟨e, f, B, W ∩ (U ∩ u ⁻¹' Ioi a), hB, hf, hxB,
      hW.inter (hu.continuousOn.isOpen_inter_preimage hU isOpen_Ioi),
      ⟨hxW, hxU, by simpa only [mem_preimage, mem_Ioi, hb] using hab⟩, ?_⟩
    intro z hz
    rw [← hgraph z hz.1, neg_lt_neg_iff, hb]
    exact ⟨fun h => h.2.2, fun h => ⟨hz.2.1, hz.2.2, h⟩⟩

/-- The level normal of the slab: `∇u/|∇u|` on the upper level `u = b`,
`-∇u/|∇u|` elsewhere. -/
def slabNormal (u : E3 → ℝ) (b : ℝ) (x : E3) : E3 :=
  if u x = b then (gradNorm u x)⁻¹ • gradient u x else -((gradNorm u x)⁻¹ • gradient u x)

/-- A local defining function with nonzero gradient determines the chart normal. -/
lemma chart_outwardNormal_eq_normalized_gradient {D : Set E3}
    (c : C1BoundaryChart) (hc : c.IsChartFor D) {x : E3}
    (hx : x ∈ frontier D) (hxr : x ∈ c.region)
    {u : E3 → ℝ} (hu : DifferentiableAt ℝ u x) (hreg : gradient u x ≠ 0)
    (hlocal : ∀ᶠ z in 𝓝 x, z ∈ D ↔ u z < u x) :
    c.outwardNormal x = ‖gradient u x‖⁻¹ • gradient u x := by
  let N := ‖gradient u x‖⁻¹ • gradient u x
  have hnorm : 0 < ‖gradient u x‖ := norm_pos_iff.mpr hreg
  have hN : ‖N‖ = 1 := by
    dsimp only [N]
    rw [norm_smul, Real.norm_of_nonneg (inv_nonneg.mpr hnorm.le),
      inv_mul_cancel₀ hnorm.ne']
  change c.outwardNormal x = N
  by_contra hne
  let v := c.outwardNormal x - N
  have hinner : inner ℝ (c.outwardNormal x) N < 1 := by
    have hp : 0 < ‖c.outwardNormal x - N‖ ^ 2 :=
      sq_pos_of_pos (norm_pos_iff.mpr (sub_ne_zero.mpr hne))
    rw [norm_sub_sq_real, c.norm_outwardNormal, hN] at hp
    nlinarith
  have hcpos : 0 < inner ℝ v (c.outwardNormal x) := by
    simp only [v, inner_sub_left, real_inner_self_eq_norm_sq, c.norm_outwardNormal]
    rw [real_inner_comm]
    nlinarith
  have hNneg : inner ℝ v N < 0 := by
    simp only [v, inner_sub_left, real_inner_self_eq_norm_sq, hN]
    nlinarith
  have hpc := classicalNormal_eventually_pos_of_hasDerivAt
    (c.hasDerivAt_definingFunction_line x v)
    (by simpa using hc.definingFunction_eq_zero hx hxr)
    (mul_pos (Real.sqrt_pos.mpr (by positivity)) hcpos)
  have hline : HasDerivAt (fun t : ℝ => x + t • v) v 0 := by
    simpa using ((hasDerivAt_id (0 : ℝ)).smul_const v).const_add x
  have hdu : HasDerivAt (fun t : ℝ => u (x + t • v) - u x)
      (‖gradient u x‖ * inner ℝ v N) 0 := by
    have hux : HasFDerivAt u (fderiv ℝ u x) (x + (0 : ℝ) • v) := by
      simpa using hu.hasFDerivAt
    have hh := (hux.comp_hasDerivAt (0 : ℝ) hline).sub_const (u x)
    convert! hh using 1
    rw [← inner_gradient_left]
    simp only [N, inner_smul_right, ← mul_assoc, mul_inv_cancel₀ hnorm.ne', one_mul]
    exact real_inner_comm _ _
  have hpu := classicalNormal_eventually_neg_of_hasDerivAt hdu (by simp)
    (mul_neg_of_pos_of_neg hnorm hNneg)
  have ht : Tendsto (fun t : ℝ => x + t • v) (𝓝[>] 0) (𝓝 x) := by
    have hh : Continuous (fun t : ℝ => x + t • v) := by fun_prop
    simpa using (hh.continuousAt (x := (0 : ℝ))).tendsto.mono_left nhdsWithin_le_nhds
  have hr : ∀ᶠ t in 𝓝[>] (0 : ℝ), x + t • v ∈ c.region :=
    ht (c.isOpen_region.mem_nhds hxr)
  have hl : ∀ᶠ t in 𝓝[>] (0 : ℝ), x + t • v ∈ D ↔ u (x + t • v) < u x := ht hlocal
  obtain ⟨t, htc, htu, htr, htl⟩ := (hpc.and (hpu.and (hr.and hl))).exists
  have hm : x + t • v ∈ D := htl.mpr (sub_neg.mp htu)
  exact (not_lt_of_gt htc) ((hc.mem_iff_definingFunction_neg htr).mp hm)

/-- Every boundary chart of the slab has outward normal `slabNormal`. -/
theorem slab_chart_outwardNormal {U : Set E3} (hU : IsOpen U) {u : E3 → ℝ} (hu : ContDiffOn ℝ 1 u U)
    {a b : ℝ} (hab : a < b) (hcl : closure (U ∩ u ⁻¹' Ioo a b) ⊆ U)
    (hreg : ∀ x ∈ U, (u x = a ∨ u x = b) → gradient u x ≠ 0)
    (c : C1BoundaryChart) (hc : c.IsChartFor (U ∩ u ⁻¹' Ioo a b))
    {x : E3} (hx : x ∈ frontier (U ∩ u ⁻¹' Ioo a b)) (hxr : x ∈ c.region) :
    c.outwardNormal x = slabNormal u b x := by
  have hends := (slab_frontier_eq hU hu hab hcl hreg).subset hx
  have hxU : x ∈ U := hcl (frontier_subset_closure hx)
  have hdu := (hu.differentiableOn one_ne_zero x hxU).differentiableAt (hU.mem_nhds hxU)
  have huc := hdu.continuousAt
  rcases hends with ⟨_, ha⟩ | ⟨_, hb⟩
  · change u x = a at ha
    have hr : gradient (-u) x = -gradient u x := by
      simp only [gradient, fderiv_neg, map_neg]
    have hn := chart_outwardNormal_eq_normalized_gradient c hc hx hxr hdu.neg
      (by rw [hr]; exact neg_ne_zero.mpr (hreg x hxU (Or.inl ha)))
    have hlocal : ∀ᶠ z in 𝓝 x, z ∈ U ∩ u ⁻¹' Ioo a b ↔ -u z < -u x := by
      filter_upwards [hU.mem_nhds hxU, huc.eventually (gt_mem_nhds (ha ▸ hab))]
        with z hzU hzb
      simp only [mem_inter_iff, mem_preimage, mem_Ioo, hzU, true_and, hzb, and_true,
        neg_lt_neg_iff, ha]
    have hh := hn hlocal
    rw [hr, norm_neg, smul_neg] at hh
    simpa [slabNormal, ha, hab.ne, gradNorm] using hh
  · change u x = b at hb
    have hn := chart_outwardNormal_eq_normalized_gradient c hc hx hxr hdu
      (hreg x hxU (Or.inr hb))
    have hlocal : ∀ᶠ z in 𝓝 x, z ∈ U ∩ u ⁻¹' Ioo a b ↔ u z < u x := by
      filter_upwards [hU.mem_nhds hxU, huc.eventually (lt_mem_nhds (hb ▸ hab))]
        with z hzU hza
      simp only [mem_inter_iff, mem_preimage, mem_Ioo, hzU, true_and, hza, hb]
    simpa [slabNormal, hb, gradNorm] using hn hlocal

/-- The slab normal is continuous along the frontier. -/
lemma slabNormal_continuousOn_frontier {U : Set E3} (hU : IsOpen U)
    {u : E3 → ℝ} (hu : ContDiffOn ℝ 1 u U) {a b : ℝ} (hab : a < b)
    (hcl : closure (U ∩ u ⁻¹' Ioo a b) ⊆ U)
    (hreg : ∀ x ∈ U, (u x = a ∨ u x = b) → gradient u x ≠ 0) :
    ContinuousOn (slabNormal u b) (frontier (U ∩ u ⁻¹' Ioo a b)) := by
  intro x hx
  obtain ⟨c, hc, hxr⟩ := slab_hasC1Boundary hU hu hab hcl hreg x hx
  apply c.continuous_outwardNormal.continuousAt.continuousWithinAt.congr_of_eventuallyEq_of_mem
    (hx := hx)
  have hr : ∀ᶠ y in 𝓝 x, y ∈ c.region := c.isOpen_region.mem_nhds hxr
  filter_upwards [self_mem_nhdsWithin, hr.filter_mono nhdsWithin_le_nhds] with y hy hyr
  exact (slab_chart_outwardNormal hU hu hab hcl hreg c hc hy hyr).symm

/-- `thm:W11-gauss-green` on a regular slab, for a vector field C¹ near its closure. -/
theorem slab_gauss_green {U : Set E3} (hU : IsOpen U) {u : E3 → ℝ} (hu : ContDiffOn ℝ 1 u U)
    {a b : ℝ} (hab : a < b) (hbdd : Bornology.IsBounded (U ∩ u ⁻¹' Ioo a b))
    (hcl : closure (U ∩ u ⁻¹' Ioo a b) ⊆ U)
    (hreg : ∀ x ∈ U, (u x = a ∨ u x = b) → gradient u x ≠ 0)
    {V : Set E3} (hV : IsOpen V) (hSV : closure (U ∩ u ⁻¹' Ioo a b) ⊆ V)
    {X : E3 → E3} (hX : ContDiffOn ℝ 1 X V) :
    ∫ x in U ∩ u ⁻¹' Ioo a b, vecDiv X x =
      (∫ x in U ∩ u ⁻¹' {b}, ⟪X x, gradient u x⟫ / gradNorm u x
          ∂(Measure.euclideanHausdorffMeasure 2)) -
        ∫ x in U ∩ u ⁻¹' {a}, ⟪X x, gradient u x⟫ / gradNorm u x
          ∂(Measure.euclideanHausdorffMeasure 2) := by
  classical
  let S := U ∩ u ⁻¹' Ioo a b
  let ν := slabNormal u b
  let μ := (hausdorffMeasure2 3).restrict (frontier S)
  have hS : IsOpen S := hu.continuousOn.isOpen_inter_preimage hU isOpen_Ioo
  have hC1 : HasC1Boundary S := slab_hasC1Boundary hU hu hab hcl hreg
  have hνm : AEStronglyMeasurable ν μ :=
    (slabNormal_continuousOn_frontier hU hu hab hcl hreg).aestronglyMeasurable
      isClosed_frontier.measurableSet
  have hn : ∀ᵐ x ∂μ, ‖ν x‖ ≤ 1 := by
    filter_upwards [ae_restrict_mem isClosed_frontier.measurableSet] with x hx
    obtain ⟨c, hc, hxr⟩ := hC1 x hx
    dsimp only [ν]
    rw [← slab_chart_outwardNormal hU hu hab hcl hreg c hc hx hxr,
      c.norm_outwardNormal]
  have hν : ∀ c : C1BoundaryChart, c.IsChartFor S →
      ∀ᵐ x ∂μ, x ∈ c.region → ν x = c.outwardNormal x := by
    intro c hc
    filter_upwards [ae_restrict_mem isClosed_frontier.measurableSet] with x hx
    intro hxr
    exact (slab_chart_outwardNormal hU hu hab hcl hreg c hc hx hxr).symm
  obtain ⟨ζ, hζ, hcζ, hsζ, hζone, _⟩ :=
    exists_smooth_cutoff_one_near_compact hbdd.isCompact_closure hV hSV
  let Y : E3 → E3 := fun x => ζ x • X x
  have hY : ContDiff ℝ 1 Y := by
    rw [contDiff_iff_contDiffAt]
    intro x
    by_cases hx : x ∈ V
    · exact (hζ.of_le (by simp)).contDiffAt.smul (hX.contDiffAt (hV.mem_nhds hx))
    · have hz : ζ =ᶠ[𝓝 x] (fun _ => 0) :=
        notMem_tsupport_iff_eventuallyEq.mp (fun h => hx (hsζ h))
      apply (contDiffAt_const (c := (0 : E3))).congr_of_eventuallyEq
      filter_upwards [hz] with y hy
      simp [Y, hy]
  have hcY : HasCompactSupport Y := hcζ.smul_right
  have hYX (x) (hx : x ∈ closure S) : Y =ᶠ[𝓝 x] X := by
    filter_upwards [hζone.filter_mono (nhds_le_nhdsSet hx)] with y hy
    simp only [Y, hy, one_smul]
  let φ (i : Fin 3) (x : E3) : ℝ := Y x i
  have hφ (i : Fin 3) : ContDiff ℝ 1 (φ i) :=
    (EuclideanSpace.proj i : E3 →L[ℝ] ℝ).contDiff.comp hY
  have hcφ (i) : HasCompactSupport (φ i) :=
    hcY.comp_left (g := fun z : E3 => z i) rfl
  have hder (i : Fin 3) (x : E3) :
      fderiv ℝ (φ i) x (basisVec i) = fderiv ℝ Y x (basisVec i) i := by
    have hh := ((EuclideanSpace.proj i).hasFDerivAt.comp x
      (hY.differentiable one_ne_zero x).hasFDerivAt).fderiv
    exact congrArg (fun L : E3 →L[ℝ] ℝ => L (basisVec i)) hh
  have hvol (i : Fin 3) : IntegrableOn (fun x => fderiv ℝ (φ i) x (basisVec i)) S :=
    (Continuous.integrable_of_hasCompactSupport
      (((hφ i).continuous_fderiv one_ne_zero).clm_apply continuous_const)
      ((hcφ i).fderiv_apply ℝ (basisVec i))).integrableOn
  have hsurf (i : Fin 3) : Integrable (fun x => φ i x * inner ℝ (basisVec i) (ν x)) μ :=
    integrable_boundary_pairing_of_contDiff_compact hS hbdd hC1 hνm hn
      (hφ i) (hcφ i) (basisVec i)
  have hsum (x : E3) : (∑ i : Fin 3, φ i x * inner ℝ (basisVec i) (ν x)) =
      inner ℝ (Y x) (ν x) := by
    simp [φ, basisVec, PiLp.inner_apply, mul_comm]
  have hbi : Integrable (fun x => inner ℝ (Y x) (ν x)) μ := by
    simpa only [hsum] using integrable_finsetSum Finset.univ (fun i _ => hsurf i)
  have hgg : (∫ x in S, vecDiv X x) = ∫ x, inner ℝ (Y x) (ν x) ∂μ := by
    calc
      _ = ∫ x in S, ∑ i : Fin 3, fderiv ℝ (φ i) x (basisVec i) := by
        apply setIntegral_congr_fun hS.measurableSet
        intro x hx
        simp only [hder, vecDiv, (hYX x (subset_closure hx)).fderiv_eq]
      _ = ∑ i : Fin 3, ∫ x in S, fderiv ℝ (φ i) x (basisVec i) :=
        integral_finsetSum _ (fun i _ => hvol i)
      _ = ∑ i : Fin 3, ∫ x, φ i x * inner ℝ (basisVec i) (ν x) ∂μ := by
        apply Finset.sum_congr rfl
        intro i _
        exact classical_directional_gauss_green hS hbdd hC1 hνm hn hν (hφ i) (basisVec i)
      _ = ∫ x, ∑ i : Fin 3, φ i x * inner ℝ (basisVec i) (ν x) ∂μ :=
        (integral_finsetSum _ (fun i _ => hsurf i)).symm
      _ = _ := by simp only [hsum]
  have hfront : frontier S = (U ∩ u ⁻¹' {a}) ∪ (U ∩ u ⁻¹' {b}) :=
    slab_frontier_eq hU hu hab hcl hreg
  have hmeas (t : ℝ) : MeasurableSet (U ∩ u ⁻¹' {t}) := by
    have ho := hu.continuousOn.isOpen_inter_preimage hU (isClosed_singleton (x := t)).isOpen_compl
    have heq : U ∩ u ⁻¹' {t} = U \ (U ∩ u ⁻¹' ({t} : Set ℝ)ᶜ) := by
      ext x
      simp only [mem_inter_iff, mem_preimage, mem_singleton_iff, Set.mem_sdiff, mem_compl_iff]
      tauto
    rw [heq]
    exact hU.measurableSet.diff ho.measurableSet
  have hdis : Disjoint (U ∩ u ⁻¹' {a}) (U ∩ u ⁻¹' {b}) := by
    apply disjoint_left.mpr
    intro x hxa hxb
    exact hab.ne (hxa.2.symm.trans hxb.2)
  have hba : IntegrableOn (fun x => inner ℝ (Y x) (ν x))
      (U ∩ u ⁻¹' {a}) (hausdorffMeasure2 3) :=
    IntegrableOn.mono_set hbi (hfront.symm ▸ subset_union_left)
  have hbb : IntegrableOn (fun x => inner ℝ (Y x) (ν x))
      (U ∩ u ⁻¹' {b}) (hausdorffMeasure2 3) :=
    IntegrableOn.mono_set hbi (hfront.symm ▸ subset_union_right)
  have hflux (x : E3) (hx : x ∈ frontier S) :
      inner ℝ (Y x) (ν x) =
        if u x = b then inner ℝ (X x) (gradient u x) / gradNorm u x
        else -(inner ℝ (X x) (gradient u x) / gradNorm u x) := by
    rw [(hYX x (frontier_subset_closure hx)).eq_of_nhds]
    dsimp only [ν, slabNormal]
    split_ifs <;> simp [inner_neg_right, inner_smul_right, div_eq_mul_inv, mul_comm]
  rw [hgg]
  change (∫ x in frontier S, inner ℝ (Y x) (ν x) ∂(hausdorffMeasure2 3)) = _
  rw [hfront, setIntegral_union hdis (hmeas b) hba hbb]
  have haint : (∫ x in U ∩ u ⁻¹' {a}, inner ℝ (Y x) (ν x) ∂(hausdorffMeasure2 3)) =
      -(∫ x in U ∩ u ⁻¹' {a}, inner ℝ (X x) (gradient u x) / gradNorm u x
        ∂(hausdorffMeasure2 3)) := by
    rw [← integral_neg]
    apply setIntegral_congr_fun (hmeas a)
    intro x hx
    simpa only [show u x = a from hx.2, hab.ne, ↓reduceIte] using
      hflux x (hfront.symm ▸ Or.inl hx)
  have hbint : (∫ x in U ∩ u ⁻¹' {b}, inner ℝ (Y x) (ν x) ∂(hausdorffMeasure2 3)) =
      ∫ x in U ∩ u ⁻¹' {b}, inner ℝ (X x) (gradient u x) / gradNorm u x
        ∂(hausdorffMeasure2 3) := by
    apply setIntegral_congr_fun (hmeas b)
    intro x hx
    simpa only [show u x = b from hx.2, ↓reduceIte] using
      hflux x (hfront.symm ▸ Or.inr hx)
  rw [haint, hbint]
  simp only [hausdorffMeasure2]
  ring

end LiquidDrop.CapacitaryK

import NoCompromise.DeGiorgi.SmoothGraph
import Mathlib.Analysis.Calculus.InverseFunctionTheorem.ContDiff
import Mathlib.Analysis.Calculus.Deriv.MeanValue

/-!
# Normal coordinates at a graph boundary

The height describes a subgraph. The last chart coordinate points into that
subgraph, along the negative of the unnormalized upward graph normal.
-/

noncomputable section

open Set Filter Metric InnerProductSpace
open scoped Topology Gradient

namespace LiquidDrop

/-- The unnormalized upward graph normal. -/
def boundaryGraphNormal (ψ : EuclideanSpace ℝ (Fin 2) → ℝ)
    (x : EuclideanSpace ℝ (Fin 2)) : EuclideanSpace ℝ (Fin 3) :=
  graphAppendN (-gradient ψ x) 1

/-- Normal graph coordinates, with positive last coordinate on the subgraph side. -/
def boundaryNormalChart (ψ : EuclideanSpace ℝ (Fin 2) → ℝ)
    (y : EuclideanSpace ℝ (Fin 3)) : EuclideanSpace ℝ (Fin 3) :=
  graphAppendN (graphProjectionN 2 y) (ψ (graphProjectionN 2 y)) -
    y (Fin.last 2) • boundaryGraphNormal ψ (graphProjectionN 2 y)

@[simp] lemma boundaryNormalChart_face (ψ : EuclideanSpace ℝ (Fin 2) → ℝ)
    (x : EuclideanSpace ℝ (Fin 2)) :
    boundaryNormalChart ψ (graphAppendN x 0) = graphMapN ψ x := by
  simp only [boundaryNormalChart, graphProjectionN_append, graphAppendN_last, zero_smul,
    sub_zero]
  rfl

@[simp] lemma boundaryNormalChart_projection (ψ : EuclideanSpace ℝ (Fin 2) → ℝ)
    (x : EuclideanSpace ℝ (Fin 2)) (t : ℝ) :
    graphProjectionN 2 (boundaryNormalChart ψ (graphAppendN x t)) =
      x + t • gradient ψ x := by
  simp only [boundaryNormalChart, graphProjectionN_append, graphAppendN_last,
    boundaryGraphNormal, map_sub, map_smul, smul_neg, sub_neg_eq_add]

@[simp] lemma boundaryNormalChart_last (ψ : EuclideanSpace ℝ (Fin 2) → ℝ)
    (x : EuclideanSpace ℝ (Fin 2)) (t : ℝ) :
    boundaryNormalChart ψ (graphAppendN x t) (Fin.last 2) = ψ x - t := by
  simp only [boundaryNormalChart, graphProjectionN_append, graphAppendN_last,
    boundaryGraphNormal, PiLp.sub_apply, PiLp.smul_apply, smul_eq_mul, mul_one]

/-- One derivative is used to construct the normal field. -/
theorem contDiff_boundaryGraphNormal {ψ : EuclideanSpace ℝ (Fin 2) → ℝ}
    {r : WithTop ℕ∞} (hψ : ContDiff ℝ (r + 1) ψ) :
    ContDiff ℝ r (boundaryGraphNormal ψ) := by
  have hg : ContDiff ℝ r (gradient ψ) :=
    (toDual ℝ (EuclideanSpace ℝ (Fin 2))).symm.contDiff.comp (hψ.fderiv_right le_rfl)
  change ContDiff ℝ r (fun x => graphBaseN 2 (-gradient ψ x) +
    (1 : ℝ) • EuclideanSpace.single (Fin.last 2) 1)
  exact ((graphBaseN 2).contDiff.comp hg.neg).add contDiff_const

/-- Normal coordinates lose one derivative relative to the height. -/
theorem contDiff_boundaryNormalChart {ψ : EuclideanSpace ℝ (Fin 2) → ℝ}
    {r : WithTop ℕ∞} (hψ : ContDiff ℝ (r + 1) ψ) :
    ContDiff ℝ r (boundaryNormalChart ψ) := by
  have hh : ContDiff ℝ r ψ := hψ.of_le (le_add_of_nonneg_right zero_le_one)
  exact (((graphBaseN 2).contDiff.comp (graphProjectionN 2).contDiff).add
    ((hh.comp (graphProjectionN 2).contDiff).smul contDiff_const)).sub
    ((EuclideanSpace.proj (Fin.last 2)).contDiff.smul
      ((contDiff_boundaryGraphNormal hψ).comp (graphProjectionN 2).contDiff))

theorem smooth_boundaryNormalChart {ψ : EuclideanSpace ℝ (Fin 2) → ℝ}
    (hψ : ContDiff ℝ (⊤ : ℕ∞) ψ) :
    ContDiff ℝ (⊤ : ℕ∞) (boundaryNormalChart ψ) :=
  contDiff_boundaryNormalChart (by simpa using hψ)

/-- The face derivative for a graph with slope `p`. -/
def boundaryNormalLinear (p : EuclideanSpace ℝ (Fin 2)) :
    EuclideanSpace ℝ (Fin 3) →L[ℝ] EuclideanSpace ℝ (Fin 3) :=
  (graphTangentN p).comp (graphProjectionN 2) -
    (EuclideanSpace.proj (Fin.last 2)).smulRight (graphAppendN (-p) 1)

lemma boundaryNormalLinear_apply (p : EuclideanSpace ℝ (Fin 2))
    (v : EuclideanSpace ℝ (Fin 3)) :
    boundaryNormalLinear p v = graphAppendN
      (graphProjectionN 2 v + v (Fin.last 2) • p)
      (inner ℝ p (graphProjectionN 2 v) - v (Fin.last 2)) := by
  apply PiLp.ext
  intro i
  refine Fin.lastCases ?_ (fun j => ?_) i <;>
    simp only [boundaryNormalLinear, sub_apply,
      ContinuousLinearMap.comp_apply, ContinuousLinearMap.smulRight_apply,
      EuclideanSpace.coe_proj, PiLp.sub_apply, PiLp.smul_apply,
      graphTangentN_last, graphTangentN_castSucc, graphAppendN_last,
      graphAppendN_castSucc, PiLp.neg_apply, PiLp.add_apply, graphProjectionN_apply,
      smul_eq_mul, mul_one, mul_neg, sub_neg_eq_add]

/-- On the face, the derivative has tangential columns and the negative normal column. -/
theorem hasFDerivAt_boundaryNormalChart_face
    {ψ : EuclideanSpace ℝ (Fin 2) → ℝ} (hψ : ContDiff ℝ 2 ψ)
    (x : EuclideanSpace ℝ (Fin 2)) :
    HasFDerivAt (boundaryNormalChart ψ) (boundaryNormalLinear (gradient ψ x))
      (graphAppendN x 0) := by
  have hg := (hasFDerivAt_graphMapN (hψ.differentiable (by norm_num)
    (graphProjectionN 2 (graphAppendN x 0)))).comp
    (graphAppendN x 0) (graphProjectionN 2).hasFDerivAt
  simp only [graphProjectionN_append] at hg
  have hn : Differentiable ℝ (boundaryGraphNormal ψ) :=
    (contDiff_boundaryGraphNormal (r := 1) hψ).differentiable one_ne_zero
  have hp := (EuclideanSpace.proj (Fin.last 2)).hasFDerivAt.smul
    ((hn (graphProjectionN 2 (graphAppendN x 0))).hasFDerivAt.comp
      (graphAppendN x 0) (graphProjectionN 2).hasFDerivAt)
  simp only [EuclideanSpace.coe_proj, graphAppendN_last, zero_smul, zero_add,
    graphProjectionN_append, Function.comp_def] at hp
  exact hg.sub hp

theorem fderiv_boundaryNormalChart_face
    {ψ : EuclideanSpace ℝ (Fin 2) → ℝ} (hψ : ContDiff ℝ 2 ψ)
    (x : EuclideanSpace ℝ (Fin 2)) :
    fderiv ℝ (boundaryNormalChart ψ) (graphAppendN x 0) =
      boundaryNormalLinear (gradient ψ x) :=
  (hasFDerivAt_boundaryNormalChart_face hψ x).fderiv

/-- Uniformly near any base point, the two signs of the normal coordinate give
the subgraph and supergraph sides, respectively. Only a C¹ height is needed. -/
theorem boundaryNormalChart_sides
    {ψ : EuclideanSpace ℝ (Fin 2) → ℝ} (hψ : ContDiff ℝ 1 ψ)
    (a : EuclideanSpace ℝ (Fin 2)) :
    ∃ δ > 0, ∃ ε > 0, ∀ x ∈ ball a δ, ∀ t ∈ Ioo (-ε) ε,
      (boundaryNormalChart ψ (graphAppendN x t) ∈ smoothSubgraph ψ ↔ 0 < t) ∧
      (ψ (graphProjectionN 2 (boundaryNormalChart ψ (graphAppendN x t))) <
        boundaryNormalChart ψ (graphAppendN x t) (Fin.last 2) ↔ t < 0) := by
  let q : EuclideanSpace ℝ (Fin 2) × ℝ → ℝ := fun z =>
    inner ℝ (gradient ψ (z.1 + z.2 • gradient ψ z.1)) (gradient ψ z.1) + 1
  have hg := continuous_gradient_of_contDiff hψ
  have hq : Continuous q := by
    exact ((hg.comp (continuous_fst.add (continuous_snd.smul
      (hg.comp continuous_fst)))).inner (hg.comp continuous_fst)).add continuous_const
  have hq0 : 0 < q (a, 0) := by
    simp only [q, zero_smul, add_zero]
    exact add_pos_of_nonneg_of_pos real_inner_self_nonneg zero_lt_one
  have hnear : {z | 0 < q z} ∈ 𝓝 (a, 0) :=
    hq.continuousAt.preimage_mem_nhds (Ioi_mem_nhds hq0)
  obtain ⟨U, hU, V, hV, hUV⟩ := mem_nhds_prod_iff.mp hnear
  obtain ⟨δ, hδ, hδU⟩ := Metric.mem_nhds_iff.mp hU
  obtain ⟨ε, hε, hεV⟩ := Metric.mem_nhds_iff.mp hV
  refine ⟨δ, hδ, ε, hε, ?_⟩
  intro x hx t ht
  let g : ℝ → ℝ := fun s => ψ (x + s • gradient ψ x) - ψ x + s
  have hd (s : ℝ) : HasDerivAt g (q (x, s)) s := by
    have hl : HasDerivAt (fun s : ℝ => x + s • gradient ψ x) (gradient ψ x) s := by
      simpa using ((hasDerivAt_id s).smul_const (gradient ψ x)).const_add x
    convert!
      (((hψ.differentiable one_ne_zero _).hasFDerivAt.comp_hasDerivAt s hl).sub_const
        (ψ x)).add (hasDerivAt_id s) using 1
    simp only [q, inner_gradient_left]
  have hm : StrictMonoOn g (Ioo (-ε) ε) := by
    apply strictMonoOn_of_deriv_pos (convex_Ioo _ _)
      (fun s _ => (hd s).continuousAt.continuousWithinAt)
    intro s hs
    rw [(hd s).deriv]
    have hs' : s ∈ Ioo (-ε) ε := interior_subset hs
    have hsV : s ∈ V := hεV (by
      simpa only [mem_ball, Real.dist_eq, sub_zero, abs_lt, mem_Ioo] using hs')
    exact hUV (show (x, s) ∈ U ×ˢ V from ⟨hδU hx, hsV⟩)
  have hz : (0 : ℝ) ∈ Ioo (-ε) ε := ⟨neg_neg_of_pos hε, hε⟩
  have hg0 : g 0 = 0 := by simp [g]
  have hpos : 0 < g t ↔ 0 < t := by
    simpa only [hg0] using hm.lt_iff_lt hz ht
  have hneg : g t < 0 ↔ t < 0 := by
    simpa only [hg0] using hm.lt_iff_lt ht hz
  simp only [smoothSubgraph, mem_ofPred_eq, boundaryNormalChart_projection,
    boundaryNormalChart_last]
  constructor
  · exact (show ψ x - t < ψ (x + t • gradient ψ x) ↔ 0 < g t by
      dsimp [g]; constructor <;> intro h <;> linarith).trans hpos
  · exact (show ψ (x + t • gradient ψ x) < ψ x - t ↔ g t < 0 by
      dsimp [g]; constructor <;> intro h <;> linarith).trans hneg

end LiquidDrop

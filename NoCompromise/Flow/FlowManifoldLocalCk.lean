import NoCompromise.Flow.FlowMaximal
import Mathlib.Geometry.Manifold.IntegralCurve.ExistUnique

/-!
# Local `C^k` flows on a smooth manifold without boundary

The local manifold assertion of `cor:flow-manifold` is obtained by transporting
the Euclidean maximal flow through an extended chart.
-/

open Function Manifold Set Filter
open scoped Topology ContDiff

namespace LiquidDrop

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] {H : Type*} [TopologicalSpace H]
  {I : ModelWithCorners ℝ E H} {M : Type*} [TopologicalSpace M]
  [ChartedSpace H M] [IsManifold I ∞ M] [T2Space M]
  [BoundarylessManifold I M]
  {v : (x : M) → TangentSpace I x} {k : ℕ∞}

set_option backward.isDefEq.respectTransparency false in
omit [FiniteDimensional ℝ E] [T2Space M] [BoundarylessManifold I M] in
/-- The coordinate representative of a `C^k` vector field is `C^k` on the
interior of the extended chart's target. -/
lemma local_contDiffOn_chartVectorField
    (hv : CMDiff k (fun x ↦ (⟨x, v x⟩ : TangentBundle I M))) (x₀ : M) :
    ContDiffOn ℝ k
      (fun y ↦ tangentCoordChange I ((extChartAt I x₀).symm y) x₀
        ((extChartAt I x₀).symm y) (v ((extChartAt I x₀).symm y)))
      (interior (extChartAt I x₀).target) := by
  intro y hy
  have hys : (extChartAt I x₀).symm y ∈ (chartAt H x₀).source :=
    by simpa only [extChartAt_source] using
      (extChartAt I x₀).map_target (interior_subset hy)
  have hsymm : ContMDiffAt 𝓘(ℝ, E) I k (extChartAt I x₀).symm y :=
    ((contMDiffOn_extChartAt_symm x₀).mono interior_subset y hy).contMDiffAt
      (isOpen_interior.mem_nhds hy)
  have hsrc : (⟨(extChartAt I x₀).symm y, v ((extChartAt I x₀).symm y)⟩ :
      TangentBundle I M) ∈
      (chartAt (ModelProd H E) (⟨x₀, v x₀⟩ : TangentBundle I M)).source := by
    simpa only [mfld_simps] using hys
  have hchart := (contMDiffAt_extChartAt' (I := I.prod 𝓘(ℝ, E))
    (n := (k : WithTop ℕ∞)) hsrc).comp y (hv.contMDiffAt.comp y hsymm)
  exact hchart.contDiffAt.snd.contDiffWithinAt

set_option backward.isDefEq.respectTransparency false in
omit [FiniteDimensional ℝ E] [T2Space M] [BoundarylessManifold I M] in
/-- Transfer an integral curve in the interior of a chart target back to the manifold. -/
lemma local_isMIntegralCurveOn_chartSymm (x₀ : M) {f : ℝ → E} {s : Set ℝ}
    (hf : ∀ t ∈ s, f t ∈ interior (extChartAt I x₀).target ∧
      HasDerivAt f
        (tangentCoordChange I ((extChartAt I x₀).symm (f t)) x₀
          ((extChartAt I x₀).symm (f t)) (v ((extChartAt I x₀).symm (f t)))) t) :
    IsMIntegralCurveOn ((extChartAt I x₀).symm ∘ f) v s := by
  intro t ht
  let xₜ : M := (extChartAt I x₀).symm (f t)
  have h := (hf t ht).2
  have hf3 := (hf t ht).1
  have hf3' := interior_subset hf3
  have hft1 : xₜ ∈ (extChartAt I x₀).source := (extChartAt I x₀).map_target hf3'
  have hft2 := mem_extChartAt_source (I := I) xₜ
  apply HasMFDerivAt.hasMFDerivWithinAt
  refine ⟨(continuousAt_extChartAt_symm'' hf3').comp h.continuousAt,
    HasDerivWithinAt.hasFDerivWithinAt ?_⟩
  simp only [mfld_simps, hasDerivWithinAt_univ]
  change HasDerivAt ((extChartAt I xₜ ∘ (extChartAt I x₀).symm) ∘ f) (v xₜ) t
  rw [← tangentCoordChange_self (I := I) (x := xₜ) (z := xₜ) (v := v xₜ) hft2,
    ← tangentCoordChange_comp (x := x₀) ⟨⟨hft2, hft1⟩, hft2⟩]
  apply HasFDerivAt.comp_hasDerivAt _ _ h
  apply HasFDerivWithinAt.hasFDerivAt (s := range I) _ <|
    mem_nhds_iff.mpr ⟨interior (extChartAt I x₀).target,
      subset_trans interior_subset (extChartAt_target_subset_range ..),
      isOpen_interior, hf3⟩
  rw [← (extChartAt I x₀).right_inv hf3']
  exact hasFDerivWithinAt_tangentCoordChange ⟨hft1, hft2⟩

omit [T2Space M] in
/-- `cor:flow-manifold` on an abstract boundaryless manifold, local flow: a `C^k` vector field,
`1 ≤ k ≤ ∞`, has a local flow with joint `C^k` dependence on time and the initial point near
every point of the manifold. -/
theorem exists_local_contMDiff_flow (hk : 1 ≤ k)
    (hv : CMDiff k (fun x ↦ (⟨x, v x⟩ : TangentBundle I M))) (x₀ : M) :
    ∃ ε > 0, ∃ N ∈ 𝓝 x₀, ∃ F : ℝ → M → M,
      ContMDiffOn (𝓘(ℝ, ℝ).prod I) I k (fun q : ℝ × M => F q.1 q.2)
        (Ioo (-ε) ε ×ˢ N) ∧
      ∀ x ∈ N, F 0 x = x ∧ IsMIntegralCurveOn (fun t => F t x) v (Ioo (-ε) ε) := by
  let φ := extChartAt I x₀
  let U := interior φ.target
  let X : E → E := fun y ↦ tangentCoordChange I (φ.symm y) x₀ (φ.symm y) (v (φ.symm y))
  have hU : IsOpen U := isOpen_interior
  have hx₀ : φ x₀ ∈ U := I.isInteriorPoint_iff.mp BoundarylessManifold.isInteriorPoint
  have hXk : ContDiffOn ℝ k X U := local_contDiffOn_chartVectorField hv x₀
  have hk' : (1 : WithTop ℕ∞) ≤ (k : WithTop ℕ∞) := by exact_mod_cast hk
  have hX : ContDiffOn ℝ 1 X U := hXk.of_le hk'
  obtain ⟨hDo, hDF⟩ := isOpen_maxFlowDomain_and_contDiffOn hU hk hXk
  have hD₀ : (0, φ x₀) ∈ maxFlowDomain X U :=
    ⟨hx₀, (isFlowCurveOn_maxFlow hU hX hx₀).2.2.1⟩
  obtain ⟨A, hA, W, hW, hAW⟩ := mem_nhds_prod_iff.mp (hDo.mem_nhds hD₀)
  obtain ⟨ε, hε, hεA⟩ := Metric.mem_nhds_iff.mp hA
  have hεA' : Ioo (-ε) ε ⊆ A := by simpa only [Real.ball_eq_Ioo, zero_sub, zero_add] using hεA
  have h0 : (0 : ℝ) ∈ Ioo (-ε) ε := ⟨neg_lt_zero.mpr hε, hε⟩
  let N := φ ⁻¹' W ∩ φ.source
  have hN : N ∈ 𝓝 x₀ :=
    inter_mem ((continuousAt_extChartAt x₀).preimage_mem_nhds hW)
      (extChartAt_source_mem_nhds x₀)
  have hD : ∀ t ∈ Ioo (-ε) ε, ∀ x ∈ N, (t, φ x) ∈ maxFlowDomain X U :=
    fun t ht x hx => hAW ⟨hεA' ht, hx.1⟩
  have hγ : ∀ x ∈ N, IsFlowCurveOn X U (φ x) (maxFlowInterval X U (φ x))
      (fun t => maxFlow X U t (φ x)) :=
    fun x hx => isFlowCurveOn_maxFlow hU hX (hD 0 h0 x hx).1
  let F : ℝ → M → M := fun t x => φ.symm (maxFlow X U t (φ x))
  refine ⟨ε, hε, N, hN, F, ?_, ?_⟩
  · have hchart : ContMDiffOn (𝓘(ℝ, ℝ).prod I) 𝓘(ℝ, E) k
        (fun q : ℝ × M => φ q.2) (Ioo (-ε) ε ×ˢ N) :=
      contMDiffOn_extChartAt.comp contMDiffOn_snd (fun q hq => by
        simpa only [φ, extChartAt_source, mem_preimage] using hq.2.2)
    have hpair : ContMDiffOn (𝓘(ℝ, ℝ).prod I) 𝓘(ℝ, ℝ × E) k
        (fun q : ℝ × M => (q.1, φ q.2)) (Ioo (-ε) ε ×ˢ N) :=
      contMDiffOn_fst.prodMk_space hchart
    have hflow := hDF.contMDiffOn.comp hpair (fun q hq => hD q.1 hq.1 q.2 hq.2)
    exact (contMDiffOn_extChartAt_symm x₀).comp hflow (fun q hq => by
      change maxFlow X U q.1 (φ q.2) ∈ φ.target
      exact interior_subset ((hγ q.2 hq.2).2.2.2.2 q.1 (hD q.1 hq.1 q.2 hq.2).2).1)
  · intro x hx
    constructor
    · change φ.symm (maxFlow X U 0 (φ x)) = x
      have hinit : maxFlow X U 0 (φ x) = φ x := (hγ x hx).2.2.2.1
      rw [hinit, φ.left_inv hx.2]
    · exact local_isMIntegralCurveOn_chartSymm x₀ (fun t ht =>
        (hγ x hx).2.2.2.2 t (hD t ht x hx).2)

/-- The local `C^k` flow agrees on its whole time interval with every integral
curve on that interval having the same initial point. -/
theorem exists_local_contMDiff_flow_unique (hk : 1 ≤ k)
    (hv : CMDiff k (fun x ↦ (⟨x, v x⟩ : TangentBundle I M))) (x₀ : M) :
    ∃ ε > 0, ∃ N ∈ 𝓝 x₀, ∃ F : ℝ → M → M,
      ContMDiffOn (𝓘(ℝ, ℝ).prod I) I k (fun q : ℝ × M => F q.1 q.2)
        (Ioo (-ε) ε ×ˢ N) ∧
      ∀ x ∈ N, F 0 x = x ∧ IsMIntegralCurveOn (fun t => F t x) v (Ioo (-ε) ε) ∧
        ∀ γ : ℝ → M, γ 0 = x → IsMIntegralCurveOn γ v (Ioo (-ε) ε) →
          EqOn γ (fun t => F t x) (Ioo (-ε) ε) := by
  obtain ⟨ε, hε, N, hN, F, hF, hcurves⟩ := exists_local_contMDiff_flow hk hv x₀
  refine ⟨ε, hε, N, hN, F, hF, fun x hx => ?_⟩
  refine ⟨(hcurves x hx).1, (hcurves x hx).2, fun γ hγ0 hγ => ?_⟩
  have hk' : (1 : WithTop ℕ∞) ≤ (k : WithTop ℕ∞) := by exact_mod_cast hk
  exact isMIntegralCurveOn_Ioo_eqOn_of_contMDiff_boundaryless
    (show (0 : ℝ) ∈ Ioo (-ε) ε from ⟨neg_lt_zero.mpr hε, hε⟩)
    (hv.of_le hk') hγ (hcurves x hx).2 (hγ0.trans (hcurves x hx).1.symm)

end LiquidDrop

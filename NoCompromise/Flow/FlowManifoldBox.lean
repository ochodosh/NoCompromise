import NoCompromise.Flow.FlowManifoldAbstract
import NoCompromise.Flow.FlowManifoldLocalCk
import NoCompromise.Flow.FlowBoxCk

/-!
# Flow boxes on abstract manifolds

The flow-box clause of `cor:flow-manifold`: a nonvanishing `C^k` vector field,
with `1 ≤ k ≤ ∞`, admits a product coordinate neighborhood in which vertical
lines are its integral curves. These curves agree with the maximal flow.
-/

open Function Manifold Set Filter
open scoped Topology ContDiff

namespace LiquidDrop

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] {H : Type*} [TopologicalSpace H]
  {I : ModelWithCorners ℝ E H} {M : Type*} [TopologicalSpace M]
  [ChartedSpace H M] [IsManifold I (⊤ : ℕ∞) M] [T2Space M]
  [BoundarylessManifold I M]
  {v : (x : M) → TangentSpace I x} {k : ℕ∞}

set_option backward.isDefEq.respectTransparency false in
/-- A `C^k` flow box at a nonzero point of a vector field on a smooth,
finite-dimensional, Hausdorff manifold without boundary. The complement is
taken in the preferred tangent coordinates at `p`; the chart representative
of the field has value `v p` there. Both coordinate maps are `C^k`, vertical
lines are integral curves, and their values agree with the maximal flow. -/
theorem exists_contMDiff_flowBox (hk : 1 ≤ k)
    (hv : CMDiff k (fun x ↦ (⟨x, v x⟩ : TangentBundle I M)))
    (p : M) (hp : v p ≠ 0) (K : Submodule ℝ E) (hK : IsCompl K (ℝ ∙ v p)) :
    ∃ ε : ℝ, 0 < ε ∧ ∃ r : ℝ, 0 < r ∧
      ∃ Ψ : K × ℝ → M, ∃ W : Set M,
        IsOpen W ∧ p ∈ W ∧ Ψ (0, 0) = p ∧
        InjOn Ψ (Metric.ball (0 : K) r ×ˢ Ioo (-ε) ε) ∧
        Ψ '' (Metric.ball (0 : K) r ×ˢ Ioo (-ε) ε) = W ∧
        ContMDiffOn 𝓘(ℝ, K × ℝ) I k Ψ (Metric.ball (0 : K) r ×ˢ Ioo (-ε) ε) ∧
        ∃ Ψinv : M → K × ℝ,
          ContMDiffOn I 𝓘(ℝ, K × ℝ) k Ψinv W ∧
          InvOn Ψinv Ψ (Metric.ball (0 : K) r ×ˢ Ioo (-ε) ε) W ∧
          (∀ q ∈ Metric.ball (0 : K) r ×ˢ Ioo (-ε) ε,
            IsMIntegralCurveOn (fun s => Ψ (q.1, s)) v (Ioo (-ε) ε)) ∧
          (∀ q ∈ Metric.ball (0 : K) r ×ˢ Ioo (-ε) ε,
            Ψ q = mMaxFlow v q.2 (Ψ (q.1, 0))) := by
  let φ := extChartAt I p
  let U := interior φ.target
  let X : E → E := fun y ↦ tangentCoordChange I (φ.symm y) p (φ.symm y) (v (φ.symm y))
  have hpU : φ p ∈ U := I.isInteriorPoint_iff.mp BoundarylessManifold.isInteriorPoint
  have hXp : X (φ p) = v p := by
    dsimp [X]
    rw [φ.left_inv (mem_extChartAt_source p)]
    exact tangentCoordChange_self (mem_extChartAt_source p)
  have hXk : ContDiffOn ℝ k X U := local_contDiffOn_chartVectorField hv p
  obtain ⟨ε, hε, r, hr, e, hes, he0, heU, he, hei, hederiv, _⟩ :=
    exists_contDiff_flowBox_local hk isOpen_interior hXk (φ p) hpU
      (by simpa only [hXp] using hp) K (by simpa only [hXp] using hK)
  let Ψ : K × ℝ → M := φ.symm ∘ e
  let Ψinv : M → K × ℝ := e.symm ∘ φ
  let W : Set M := φ.source ∩ φ ⁻¹' e.target
  have h0 : (0 : ℝ) ∈ Ioo (-ε) ε := ⟨neg_lt_zero.mpr hε, hε⟩
  have h00 : ((0 : K), (0 : ℝ)) ∈ e.source := by
    rw [hes]
    exact ⟨Metric.mem_ball_self hr, h0⟩
  have heφ : e.target ⊆ φ.target := subset_trans heU interior_subset
  have hΨmaps : MapsTo Ψ e.source W := by
    intro q hq
    have hqφ := heφ (e.map_source hq)
    exact ⟨φ.map_target hqφ, by
      change φ (φ.symm (e q)) ∈ e.target
      rw [φ.right_inv hqφ]
      exact e.map_source hq⟩
  have hinv : InvOn Ψinv Ψ e.source W := by
    constructor
    · intro q hq
      change e.symm (φ (φ.symm (e q))) = q
      rw [φ.right_inv (heφ (e.map_source hq)), e.left_inv hq]
    · intro x hx
      change φ.symm (e (e.symm (φ x))) = x
      rw [e.right_inv hx.2, φ.left_inv hx.1]
  have hΨimage : Ψ '' e.source = W := by
    apply Subset.antisymm hΨmaps.image_subset
    intro x hx
    exact ⟨Ψinv x, e.map_target hx.2, hinv.2 hx⟩
  have hcurves : ∀ q ∈ e.source,
      IsMIntegralCurveOn (fun s => Ψ (q.1, s)) v (Ioo (-ε) ε) := by
    intro q hq
    apply local_isMIntegralCurveOn_chartSymm p
    intro t ht
    have hqt : (q.1, t) ∈ e.source := by
      rw [hes] at hq ⊢
      exact ⟨hq.1, ht⟩
    exact ⟨heU (e.map_source hqt), hederiv (q.1, t) hqt⟩
  refine ⟨ε, hε, r, hr, Ψ, W, isOpen_extChartAt_preimage' p e.open_target,
    ?_, ?_, ?_, ?_, ?_, Ψinv, ?_, ?_, ?_, ?_⟩
  · refine ⟨mem_extChartAt_source p, ?_⟩
    change φ p ∈ e.target
    rw [← he0]
    exact e.map_source h00
  · change φ.symm (e (0, 0)) = p
    rw [he0, φ.left_inv (mem_extChartAt_source p)]
  · rw [← hes]
    exact hinv.1.injOn
  · rwa [← hes]
  · rw [← hes]
    exact (contMDiffOn_extChartAt_symm p).comp he.contMDiffOn
      (fun q hq => heφ (e.map_source hq))
  · exact hei.contMDiffOn.comp
      (contMDiffOn_extChartAt.mono (fun x hx => by
        simpa only [φ, extChartAt_source] using hx.1)) (fun x hx => hx.2)
  · rwa [← hes]
  · rwa [← hes]
  · intro q hq
    have hk' : (1 : WithTop ℕ∞) ≤ (k : WithTop ℕ∞) := by exact_mod_cast hk
    exact (mMaxFlow_maximal (hv.of_le hk') h0 rfl
      (hcurves q (hes.symm ▸ hq))).2 hq.2

end LiquidDrop

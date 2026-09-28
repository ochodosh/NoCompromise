import NoCompromise.Flow.FlowBoxCk
import NoCompromise.Flow.FlowMaximal
import NoCompromise.Surface.TangentFlow

/-!
# `C^k` flows: flow boxes of the maximal flow, and flows on compact surfaces

`cor:flow-manifold`, remaining clauses at `C^k`, `1 ≤ k ≤ ∞`:

* the flow-box conclusion holds for the maximal local flow wherever `X ≠ 0`
  (`maxFlow_flowBox`): the `C^k` chart of `thm:flow-box` is `(y, t) ↦ Φ_t(p + y)`;
* on a compact smooth embedded surface a `C^k` tangent field (defined on an open neighbourhood)
  is complete, and its flow is the restriction of a jointly `C^k` ambient flow satisfying the
  group law (`exists_contDiff_flow_of_tangent`).
-/

open Set Filter
open scoped NNReal Topology

namespace LiquidDrop

section Euclidean

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]
  [FiniteDimensional ℝ E] {X : E → E} {U : Set E}

/-- `cor:flow-manifold`, flow-box clause: wherever `X ≠ 0`, the maximal local flow
`(y, t) ↦ Φ_t(p + y)` on a product `ball × (-ε, ε)` in `H × ℝ` (any complement `H` of `ℝ X(p)`)
is a `C^k` chart with `C^k` inverse in which `X` becomes `∂/∂t`. -/
theorem maxFlow_flowBox {k : ℕ∞} (hk : 1 ≤ k) (hU : IsOpen U) (hXk : ContDiffOn ℝ k X U)
    (p : E) (hpU : p ∈ U) (hp : X p ≠ 0) (H : Submodule ℝ E) (hH : IsCompl H (ℝ ∙ X p)) :
    ∃ ε : ℝ, 0 < ε ∧ ∃ r : ℝ, 0 < r ∧
      ∃ e : OpenPartialHomeomorph (H × ℝ) E,
        e.source = Metric.ball (0 : H) r ×ˢ Ioo (-ε) ε ∧
        e (0, 0) = p ∧ e.target ⊆ U ∧
        ContDiffOn ℝ k e e.source ∧ ContDiffOn ℝ k e.symm e.target ∧
        (∀ q ∈ e.source, HasDerivAt (fun s => e (q.1, s)) (X (e q)) q.2) ∧
        ∀ q ∈ e.source, q.2 ∈ maxFlowInterval X U (p + (q.1 : E)) ∧
          e q = maxFlow X U q.2 (p + (q.1 : E)) := by
  have hX : ContDiffOn ℝ 1 X U := hXk.of_le (by exact_mod_cast hk)
  obtain ⟨ε, hε, r, hr, e, hsrc, he0, htgt, hce, hci, hder, hcurve⟩ :=
    exists_contDiff_flowBox_local hk hU hXk p hpU hp H hH
  refine ⟨ε, hε, r, hr, e, hsrc, he0, htgt, hce, hci, hder, fun q hq => ?_⟩
  have hsrc' (s : ℝ) (hs : s ∈ Ioo (-ε) ε) : ((q.1, s) : H × ℝ) ∈ e.source := by
    rw [hsrc] at hq ⊢
    exact ⟨hq.1, hs⟩
  have hzero : e (q.1, 0) = p + (q.1 : E) := by
    obtain ⟨γ, hγ0, hγq, -⟩ := hcurve (q.1, 0) (hsrc' 0 ⟨by linarith, hε⟩)
    exact hγq.symm.trans hγ0
  have hflow : IsFlowCurveOn X U (p + (q.1 : E)) (Ioo (-ε) ε) (fun s => e (q.1, s)) := by
    refine ⟨isOpen_Ioo, ordConnected_Ioo, ⟨by linarith, hε⟩, hzero, fun s hs => ?_⟩
    exact ⟨htgt (e.map_source (hsrc' s hs)), hder (q.1, s) (hsrc' s hs)⟩
  have hq2 : q.2 ∈ Ioo (-ε) ε := by
    rw [hsrc] at hq
    exact hq.2
  exact ⟨subset_maxFlowInterval hflow hq2,
    (maxFlow_eq_of_isFlowCurveOn hU hX hflow hq2).symm⟩

end Euclidean

/-- `cor:flow-manifold` on a compact smooth embedded surface: a `C^k` field (`1 ≤ k ≤ ∞`) on an
open neighbourhood of the surface and tangent to it is complete on the surface, and its flow is
the restriction of a jointly `C^k` ambient flow with the group law. Every integral curve of `X`
through a point of `S` on an order-connected time set around `0` is a piece of this flow. -/
theorem exists_contDiff_flow_of_tangent {S : Set E₃} (hS : IsSmoothEmbeddedSurface S)
    (hSc : IsCompact S) {U : Set E₃} (hU : IsOpen U) (hSU : S ⊆ U) {X : E₃ → E₃} {k : ℕ∞}
    (hk : 1 ≤ k) (hXk : ContDiffOn ℝ k X U) (htan : ∀ p ∈ S, X p ∈ tangentPlane S p) :
    ∃ Φ : ℝ → E₃ → E₃, ContDiff ℝ k (fun q : ℝ × E₃ => Φ q.1 q.2) ∧
      (∀ x, Φ 0 x = x) ∧ (∀ s t x, Φ (s + t) x = Φ s (Φ t x)) ∧
      (∀ x ∈ S, ∀ t, Φ t x ∈ S ∧ HasDerivAt (fun s => Φ s x) (X (Φ t x)) t) ∧
      ∀ x ∈ S, ∀ {I : Set ℝ} {γ : ℝ → E₃}, I.OrdConnected → (0 : ℝ) ∈ I → γ 0 = x →
        (∀ t ∈ I, γ t ∈ U ∧ HasDerivAt γ (X (γ t)) t) → EqOn γ (fun t => Φ t x) I := by
  have hk' : (1 : WithTop ℕ∞) ≤ (k : WithTop ℕ∞) := by exact_mod_cast hk
  have hX : ContDiffOn ℝ 1 X U := hXk.of_le hk'
  obtain ⟨Y, hY, hYc, V, _, hSV, _, hYX⟩ := exists_compactSupport_eq_near_contDiff hU hXk hSc hSU
  have hY1 : ContDiff ℝ 1 Y := hY.of_le hk'
  obtain ⟨L, M, hL, hM⟩ := lipschitz_bounded_of_hasCompactSupport hY1 hYc
  have hmem : ∀ x ∈ S, ∀ t, globalFlow Y hL hM t x ∈ S := by
    intro x hx t
    exact integralCurve_mem_of_tangent hS hSc.isClosed isOpen_univ hY1.contDiffOn
      (fun p hp => (hYX (hSV hp.1)).symm ▸ htan p hp.1) ordConnected_univ (mem_univ 0)
      (fun t _ => ⟨mem_univ _, hasDerivAt_globalFlow hL hM x t⟩)
      (by simpa only [globalFlow_zero] using hx) t (mem_univ t)
  have hcurve : ∀ x ∈ S, ∀ t, globalFlow Y hL hM t x ∈ S ∧
      HasDerivAt (fun s => globalFlow Y hL hM s x) (X (globalFlow Y hL hM t x)) t := by
    intro x hx t
    refine ⟨hmem x hx t, ?_⟩
    rw [← hYX (hSV (hmem x hx t))]
    exact hasDerivAt_globalFlow hL hM x t
  refine ⟨globalFlow Y hL hM, contDiff_globalFlow_uncurry hL hM hk hY,
    globalFlow_zero hL hM, fun s t x => globalFlow_add hL hM s t x, hcurve, ?_⟩
  intro x hx I γ hI h0 hγ0 hγ
  exact integralCurve_unique_of_contDiffOn hU hX hI h0 hγ
    (fun t _ => ⟨hSU (hcurve x hx t).1, (hcurve x hx t).2⟩)
    (by rw [hγ0, globalFlow_zero])

end LiquidDrop

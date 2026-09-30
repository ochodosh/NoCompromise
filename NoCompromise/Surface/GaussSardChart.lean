module

public import NoCompromise.Surface.MorseChart
public import NoCompromise.Surface.RegularValue
public import NoCompromise.Surface.Shape
public import NoCompromise.Area.RankDeficient
public import NoCompromise.Area.Linear

@[expose] public section

/-!
# Sard for the Gauss map in one chart (`cor:sard-charts`)

For a chart `e` of an embedded surface `S` with `C¹` inverse and a closed ball
`closedBall c r ⊆ e.target`, the Gauss-map images of the critical points of `n` (points where
`d_pn` does not map `T_pS` onto `T_{n p}S²`) lying over the open ball are
`hausdorffMeasure2 3`-null. The proof extends `n ∘ e.symm` from the closed ball to a globally
Lipschitz map of the plane and applies `lem:rank-deficient`
(`hausdorffMeasure2_image_jacobian2_eq_zero`).
-/

noncomputable section

open Set Filter Function
open scoped Topology NNReal

namespace LiquidDrop

local notation "E2" => EuclideanSpace ℝ (Fin 2)

/-- A `C¹` map on an open set containing a closed ball agrees on that ball with a globally
Lipschitz map of the plane. -/
theorem exists_lipschitzWith_eqOn_closedBall {m : ℕ} {G : E2 → EuclideanSpace ℝ (Fin m)}
    {s : Set E2} (hG : ContDiffOn ℝ 1 G s) {c : E2} {r : ℝ}
    (hB : Metric.closedBall c r ⊆ s) :
    ∃ (K : ℝ≥0) (Ĝ : E2 → EuclideanSpace ℝ (Fin m)), LipschitzWith K Ĝ ∧
      EqOn G Ĝ (Metric.closedBall c r) := by
  obtain ⟨K, hK⟩ := (hG.mono hB).exists_lipschitzOnWith one_ne_zero (convex_closedBall c r)
    (isCompact_closedBall c r)
  let L := EuclideanSpace.equiv (Fin m) ℝ
  have hLG : LipschitzOnWith (‖(L : EuclideanSpace ℝ (Fin m) →L[ℝ] (Fin m → ℝ))‖₊ * K)
      (fun x => L (G x)) (Metric.closedBall c r) :=
    (ContinuousLinearMap.lipschitzWith
      (L : EuclideanSpace ℝ (Fin m) →L[ℝ] (Fin m → ℝ))).comp_lipschitzOnWith hK
  obtain ⟨g, hg, hgeq⟩ := hLG.extend_pi
  refine ⟨_, fun x => L.symm (g x), (ContinuousLinearMap.lipschitzWith
    (L.symm : (Fin m → ℝ) →L[ℝ] EuclideanSpace ℝ (Fin m))).comp hg, fun x hx => ?_⟩
  simp only
  rw [← hgeq hx]
  simp

/-- `cor:sard-charts` for the Gauss map over one closed ball of a chart with `C¹` inverse
(no projection form of the chart is needed). -/
theorem hausdorffMeasure2_gaussMap_critical_of_chart {S : Set E₃} {n : E₃ → E₃}
    (hS : IsSmoothEmbeddedSurface S) (hn : IsUnitNormalField S n)
    (e : OpenPartialHomeomorph S E2)
    (hψ : ContDiffOn ℝ 1 (fun y => (e.symm y : E₃)) e.target)
    {c : E2} {r : ℝ} (hB : Metric.closedBall c r ⊆ e.target) :
    hausdorffMeasure2 3 (n '' {p | ∃ u ∈ Metric.ball c r, (e.symm u : E₃) = p ∧
      (tangentPlane S p).map (fderiv ℝ n p : E₃ →ₗ[ℝ] E₃) ≠
        tangentPlane (Metric.sphere (0 : E₃) 1) (n p)}) = 0 := by
  set ψ : E2 → E₃ := fun y => (e.symm y : E₃) with hψdef
  have hψS : ∀ u, ψ u ∈ S := fun u => (e.symm u).2
  have hψd : ∀ u ∈ e.target, DifferentiableAt ℝ ψ u := fun u hu =>
    (hψ.contDiffAt (e.open_target.mem_nhds hu)).differentiableAt one_ne_zero
  have hnd : ∀ u, DifferentiableAt ℝ n (ψ u) := fun u =>
    (hn.contDiffAt (hψS u)).differentiableAt (by simp)
  have hGC : ContDiffOn ℝ 1 (n ∘ ψ) e.target := fun u hu =>
    (((hn.contDiffAt (hψS u)).of_le (by simp)).comp u
      (hψ.contDiffAt (e.open_target.mem_nhds hu))).contDiffWithinAt
  obtain ⟨K, Ĝ, hĜ, hĜeq⟩ := exists_lipschitzWith_eqOn_closedBall hGC hB
  refine MeasureTheory.measure_mono_null ?_ (hausdorffMeasure2_image_jacobian2_eq_zero hĜ)
  rintro _ ⟨p, ⟨u, hu, rfl, hcrit⟩, rfl⟩
  have hub : u ∈ Metric.closedBall c r := Metric.ball_subset_closedBall hu
  refine ⟨u, ?_, (hĜeq hub).symm⟩
  change jacobian2 Ĝ u = 0
  have hloc : Ĝ =ᶠ[𝓝 u] n ∘ ψ := by
    filter_upwards [Metric.isOpen_ball.mem_nhds hu] with x hx
    exact (hĜeq (Metric.ball_subset_closedBall hx)).symm
  have hfd : fderiv ℝ Ĝ u = (fderiv ℝ n (ψ u)).comp (fderiv ℝ ψ u) := by
    rw [hloc.fderiv_eq]
    exact fderiv_comp u (hnd u) (hψd u (hB hub))
  by_contra hne
  have hpos : 0 < jacobian2 Ĝ u := lt_of_le_of_ne (jacobian2Linear_nonneg _) (Ne.symm hne)
  unfold jacobian2 at hpos
  rw [hfd, jacobian2Linear_pos_iff_injective] at hpos
  apply hcrit
  set L := (fderiv ℝ n (ψ u)).comp (fderiv ℝ ψ u)
  have hle : (tangentPlane S (ψ u)).map (fderiv ℝ n (ψ u) : E₃ →ₗ[ℝ] E₃) ≤
      tangentPlane (Metric.sphere (0 : E₃) 1) (n (ψ u)) := by
    rintro _ ⟨X, hX, rfl⟩
    exact fderiv_normal_mem_tangentPlane_sphere hS hn (hψS u) hX
  have hrange : LinearMap.range (L : E2 →ₗ[ℝ] E₃) ≤
      (tangentPlane S (ψ u)).map (fderiv ℝ n (ψ u) : E₃ →ₗ[ℝ] E₃) := by
    rintro _ ⟨v, rfl⟩
    exact ⟨fderiv ℝ ψ u v, chart_fderiv_mem_tangentPlane le_rfl hψ (hB hub) v, rfl⟩
  have hfr : Module.finrank ℝ (LinearMap.range (L : E2 →ₗ[ℝ] E₃)) = 2 := by
    rw [LinearMap.finrank_range_of_inj hpos]
    simp
  have hsph : Module.finrank ℝ (tangentPlane (Metric.sphere (0 : E₃) 1) (n (ψ u))) = 2 := by
    rw [tangentPlane_sphere_normal_eq hS hn (hψS u)]
    exact hS.finrank_tangentPlane (hψS u)
  refine Submodule.eq_of_le_of_finrank_le hle ?_
  rw [hsph]
  exact hfr.symm.le.trans (Submodule.finrank_mono hrange)

/-- `cor:sard-charts` for the Gauss map, one projection chart. -/
theorem hausdorffMeasure2_gaussMap_critical_chart {S : Set E₃} {n : E₃ → E₃}
    (hS : IsSmoothEmbeddedSurface S) (hn : IsUnitNormalField S n)
    (e : OpenPartialHomeomorph S E2) (P : E₃ →L[ℝ] E2) (q : E₃)
    (_he : ∀ x : S, e x = P ((x : E₃) - q))
    (hψ : ContDiffOn ℝ 1 (fun y => (e.symm y : E₃)) e.target)
    {c : E2} {r : ℝ} (hB : Metric.closedBall c r ⊆ e.target) :
    hausdorffMeasure2 3 (n '' {p | ∃ u ∈ Metric.ball c r, (e.symm u : E₃) = p ∧
      (tangentPlane S p).map (fderiv ℝ n p : E₃ →ₗ[ℝ] E₃) ≠
        tangentPlane (Metric.sphere (0 : E₃) 1) (n p)}) = 0 :=
  hausdorffMeasure2_gaussMap_critical_of_chart hS hn e hψ hB

end LiquidDrop

module

public import NoCompromise.Stationary.BootstrapC3Chart
public import NoCompromise.Stationary.BootstrapC3

@[expose] public section

/-!
# `prop:bootstrap-C3` at every boundary point

Blueprint `prop:bootstrap-C3` and `cor:minimizer-stationary`. The unit-disk regularity step
(a `C^{2,a}` weak solution of the prescribed-mean-curvature equation with `C^{1,a}` forcing is
`C³` on the half disk) is isolated as the proposition `MCGraphC3UnitStatement`, proved by
`mc_graph_C3_unit` (`mcGraphC3UnitStatement_holds`); localisation in a boundary chart, the
`C^{1,a}` forcing, rescaling, and gluing the charts are proved here.
-/

noncomputable section
open Set Filter Metric MeasureTheory InnerProductSpace
open scoped Topology Gradient RealInnerProductSpace
namespace LiquidDrop

/-- Blueprint `prop:bootstrap-C3` (unit-disk core): a `C^{2,a}` weak solution of the
prescribed-mean-curvature equation on the unit disk with `C^{1,a}` forcing is `C³` on the
half disk. -/
def MCGraphC3UnitStatement : Prop :=
  ∀ a : ℝ, 0 < a → a < 1 → ∀ f G : EuclideanSpace ℝ (Fin 2) → ℝ,
    HasC2HolderOn a f (ball 0 1) → HasC1HolderOn a G (ball 0 1) →
    (∀ φ : EuclideanSpace ℝ (Fin 2) → ℝ,
      ContDiff ℝ (⊤ : ℕ∞) φ → HasCompactSupport φ → tsupport φ ⊆ ball 0 1 →
      (∫ y, inner ℝ (gradient f y) (gradient φ y) /
        Real.sqrt (1 + ‖gradient f y‖ ^ 2)) = ∫ y, G y * φ y) →
    ContDiffOn ℝ 3 f (ball 0 (1 / 2))

/-- Blueprint `prop:bootstrap-C3`: the unit-disk core transfers to every disk. -/
theorem mc_graph_C3_ball (hU : MCGraphC3UnitStatement) {a : ℝ} (ha : 0 < a) (ha1 : a < 1)
    {f G : EuclideanSpace ℝ (Fin 2) → ℝ}
    (y0 : EuclideanSpace ℝ (Fin 2)) {ρ : ℝ} (hρ : 0 < ρ)
    (hf : HasC2HolderOn a f (ball y0 ρ))
    (hG : HasC1HolderOn a G (ball y0 ρ))
    (he : ∀ φ : EuclideanSpace ℝ (Fin 2) → ℝ,
      ContDiff ℝ (⊤ : ℕ∞) φ → HasCompactSupport φ → tsupport φ ⊆ ball y0 ρ →
      (∫ y, inner ℝ (gradient f y) (gradient φ y) /
        Real.sqrt (1 + ‖gradient f y‖ ^ 2)) = ∫ y, G y * φ y) :
    ContDiffOn ℝ 3 f (ball y0 (ρ / 2)) := by
  have hm : MapsTo (fun x => y0 + ρ • x) (ball (0 : EuclideanSpace ℝ (Fin 2)) 1)
      (ball y0 ρ) := quasilinear_ballScaling_maps_unit y0 hρ
  have hfρ : HasC2HolderOn a (fun z => ρ⁻¹ • f (y0 + ρ • z)) (ball 0 1) :=
    bootstrap_c2Holder_affine ha.le ha1.le isOpen_ball isOpen_ball hf y0 ρ ρ⁻¹ hm
  have hGρ : HasC1HolderOn a (fun z => ρ * G (y0 + ρ • z)) (ball 0 1) :=
    bootstrap_c1Holder_affine ha.le ha1.le isOpen_ball hG y0 ρ ρ hm
  have h3 := hU a ha ha1 _ _ hfρ hGρ
    (mc_weak_rescale y0 hρ (hf.contDiff.of_le (by norm_num)) he)
  have hmback : MapsTo (fun x => ρ⁻¹ • (x - y0))
      (ball y0 (ρ / 2)) (ball (0 : EuclideanSpace ℝ (Fin 2)) (1 / 2)) := by
    intro x hx
    rw [mem_ball, dist_zero_right, norm_smul, Real.norm_eq_abs, abs_inv, abs_of_pos hρ,
      ← dist_eq_norm]
    rw [mem_ball] at hx
    rw [inv_mul_lt_iff₀ hρ]
    linarith
  have hback : ContDiffOn ℝ 3
      (fun x => ρ • (fun z => ρ⁻¹ • f (y0 + ρ • z)) (ρ⁻¹ • (x - y0)))
      (ball y0 (ρ / 2)) :=
    (h3.comp ((contDiff_id.sub contDiff_const).const_smul ρ⁻¹).contDiffOn hmback).const_smul ρ
  apply hback.congr
  intro x _
  simp only [smul_smul, mul_inv_cancel₀ hρ.ne', one_smul, smul_eq_mul, add_sub_cancel]
  field_simp

set_option maxHeartbeats 800000 in
-- The chart/slab construction needs extra elaboration for the composed coordinate maps.
/-- Blueprint `prop:bootstrap-C3`: at a boundary point of a minimiser, a chart height that is
`C^{2,a}` near the base point is `C³` on a smaller disk. -/
theorem MinimizerRep.height_C3_near (hU : MCGraphC3UnitStatement) {V : ℝ}
    {Ω : Set AmbientSpace}
    (h : MinimizerRep V Ω) {c : C1BoundaryChart} (hc : c.IsChartFor Ω)
    {p : AmbientSpace} (hp : p ∈ frontier Ω) (hpc : p ∈ c.region)
    {a : ℝ} (ha : 0 < a) (ha1 : a < 1)
    (hf : ∃ ρ₀ > 0, HasC2HolderOn a c.height
      (ball (graphProjectionN 2 (c.placement.symm p)) ρ₀)) :
    ∃ ρ > 0, ContDiffOn ℝ 3 c.height
      (ball (graphProjectionN 2 (c.placement.symm p)) ρ) := by
  let y1 := graphProjectionN 2 (c.placement.symm p)
  have hy1 : c.placement (graphMapN c.height y1) = p := by
    have hmem : p ∈ c.graphSurface ∩ c.region := by
      rw [← hc.frontier_inter_eq]
      exact ⟨hp, hpc⟩
    obtain ⟨⟨w, ⟨y, hy⟩, hw⟩, _⟩ := hmem
    have hpy : c.placement (graphMapN c.height y) = p := by rw [hy]; exact hw
    have hy0 : y1 = y := by
      dsimp [y1]
      rw [← hpy, c.placement.symm_apply_apply]
      exact graphProjectionN_append y (c.height y)
    rwa [hy0]
  obtain ⟨ρ₀, hρ₀, hf⟩ := hf
  let Φ : (EuclideanSpace ℝ (Fin 2)) × ℝ → AmbientSpace := fun q =>
    c.placement (graphBaseN 2 q.1 + q.2 • EuclideanSpace.single (Fin.last 2) (1 : ℝ))
  have hΦ : Continuous Φ :=
    c.placement.continuous.comp (((graphBaseN 2).continuous.comp continuous_fst).add
      (continuous_snd.smul continuous_const))
  have hΦp : Φ (y1, c.height y1) = p := hy1
  obtain ⟨ε, hε, hball⟩ := Metric.isOpen_iff.mp (c.isOpen_region.preimage hΦ)
    (y1, c.height y1)
    (by change Φ (y1, c.height y1) ∈ c.region; rw [hΦp]; exact hpc)
  obtain ⟨r, hr, hfr⟩ := Metric.continuousAt_iff.mp
    (c.height_contDiff.continuous.continuousAt (x := y1)) (ε / 2) (half_pos hε)
  let R := min (ρ₀ / 2) (min r ε)
  have hR : 0 < R := lt_min (half_pos hρ₀) (lt_min hr hε)
  have hRr : R ≤ r := (min_le_right _ _).trans (min_le_left _ _)
  have hRε : R ≤ ε := (min_le_right _ _).trans (min_le_right _ _)
  have hRρ : R ≤ ρ₀ / 2 := min_le_left _ _
  have hslab : ∀ ζ : EuclideanSpace ℝ (Fin 2) → ℝ,
      tsupport ζ ⊆ ball y1 R → ∀ y ∈ tsupport ζ, ∀ t : ℝ,
      |t - c.height y| ≤ ε / 2 →
      c.placement (graphBaseN 2 y + t • EuclideanSpace.single (Fin.last 2) 1) ∈ c.region := by
    intro ζ hζ y hy t ht
    have hyr : dist y y1 < r := lt_of_lt_of_le (hζ hy) hRr
    have hyε : dist y y1 < ε := lt_of_lt_of_le (hζ hy) hRε
    have hfy := hfr hyr
    rw [Real.dist_eq] at hfy
    have htε : dist t (c.height y1) < ε := by
      rw [Real.dist_eq]
      calc
        |t - c.height y1| ≤ |t - c.height y| + |c.height y - c.height y1| := abs_sub_le _ _ _
        _ < ε / 2 + ε / 2 := by linarith
        _ = ε := by ring
    have hmem : (y, t) ∈ ball (y1, c.height y1) ε := by
      rw [mem_ball, Prod.dist_eq]
      exact max_lt hyε htε
    have hΦmem : Φ (y, t) ∈ c.region := hball hmem
    exact hΦmem
  have hG := (chart_forcing_c1Holder h.bounded (minimizerMultiplier V Ω) c hρ₀
    hf.contDiff ha ha1).mono (ball_subset_ball hRρ) |>.1
  refine ⟨R / 2, half_pos hR, ?_⟩
  apply mc_graph_C3_ball hU ha ha1 y1 hR
    ((hf.nondiv_mono (ball_subset_ball (hRρ.trans (by linarith)))).1) hG
  intro ζ hζ hcζ hsζ
  exact h.graph_prescribed_mean_curvature c hc hζ hcζ (half_pos hε) (hslab ζ hsζ)

/-- Blueprint `prop:bootstrap-C3`: a minimiser with `C^{1,a}` boundary has `C³` boundary,
given the unit-disk core `MCGraphC3UnitStatement`. -/
theorem MinimizerRep.hasCkBoundary_three (hU : MCGraphC3UnitStatement) {V : ℝ}
    {Ω : Set AmbientSpace} (h : MinimizerRep V Ω) {a : ℝ}
    (ha : 0 < a) (ha1 : a < 1) (hC : HasC1HolderBoundary a Ω) :
    HasCkBoundary 3 Ω := by
  apply hasCkBoundary_of_local
  intro p hp
  obtain ⟨c, hc, hpc, hβ⟩ := h.exists_c2Holder_chart ha ha1 hC hp
  obtain ⟨ρ, hρ, h3⟩ := h.height_C3_near hU hc hp hpc (a := 1 / 2) (by norm_num) (by norm_num)
    (hβ (1 / 2) (by norm_num) (by norm_num))
  exact ⟨c, hc, hpc, ρ, hρ, h3⟩

/-- Blueprint `cor:minimizer-stationary`: a minimiser with `C^{1,a}` boundary is a
stationary domain with multiplier `λ`, and the scaling identity holds, given the unit-disk
core `MCGraphC3UnitStatement` of `prop:bootstrap-C3`. -/
theorem MinimizerRep.stationary_of_c1Holder (hU : MCGraphC3UnitStatement) {V : ℝ}
    {Ω : Set AmbientSpace} (h : MinimizerRep V Ω) {a : ℝ}
    (ha : 0 < a) (ha1 : a < 1) (hC : HasC1HolderBoundary a Ω) :
    IsStationaryDomain V (minimizerMultiplier V Ω) Ω ∧
      3 * V * minimizerMultiplier V Ω =
        2 * (perimeter Ω).toReal + 5 * (coulombEnergy Ω).toReal ∧
      3 * V * minimizerMultiplier V Ω =
        5 * (energy Ω).toReal - 3 * (perimeter Ω).toReal :=
  h.stationary_and_scaling_of_hasCkBoundary (h.hasCkBoundary_three hU ha ha1 hC)

/-- Blueprint `prop:bootstrap-C3` (unit-disk core): discharged by `mc_graph_C3_unit`. -/
theorem mcGraphC3UnitStatement_holds : MCGraphC3UnitStatement :=
  fun _ ha ha1 _ _ hf hG he => (mc_graph_C3_unit ha ha1 hf hG he).1

/-- Blueprint `prop:bootstrap-C3`: a minimiser with `C^{1,a}` boundary (`0 < a < 1`) has
`C³` boundary. -/
theorem MinimizerRep.hasCkBoundary_three_of_c1Holder {V : ℝ} {Ω : Set AmbientSpace}
    (h : MinimizerRep V Ω) {a : ℝ} (ha : 0 < a) (ha1 : a < 1)
    (hC : HasC1HolderBoundary a Ω) : HasCkBoundary 3 Ω :=
  h.hasCkBoundary_three mcGraphC3UnitStatement_holds ha ha1 hC

/-- Blueprint `cor:minimizer-stationary`: a minimiser with `C^{1,a}` boundary (the boundary
regularity of `not:minimizer-rep`) is a stationary domain with multiplier `λ`, and the
scaling identity holds. -/
theorem MinimizerRep.isStationaryDomain_of_c1Holder {V : ℝ} {Ω : Set AmbientSpace}
    (h : MinimizerRep V Ω) {a : ℝ} (ha : 0 < a) (ha1 : a < 1)
    (hC : HasC1HolderBoundary a Ω) :
    IsStationaryDomain V (minimizerMultiplier V Ω) Ω ∧
      3 * V * minimizerMultiplier V Ω =
        2 * (perimeter Ω).toReal + 5 * (coulombEnergy Ω).toReal ∧
      3 * V * minimizerMultiplier V Ω =
        5 * (energy Ω).toReal - 3 * (perimeter Ω).toReal :=
  h.stationary_of_c1Holder mcGraphC3UnitStatement_holds ha ha1 hC

end LiquidDrop

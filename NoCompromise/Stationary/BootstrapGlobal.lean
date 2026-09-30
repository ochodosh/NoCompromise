module

public import NoCompromise.Stationary.BootstrapC2Chart
public import NoCompromise.Stationary.ChartLocalize
public import NoCompromise.Stationary.PointwiseEL
public import NoCompromise.Elliptic.NondivSchauderLocalization

@[expose] public section

/-!
# The smooth bootstrap at every boundary point

Blueprint `prop:bootstrap-C2` and `cor:EL-pointwise`, globalised over the boundary.
The input is the `C^{1,a}` boundary of `not:minimizer-rep` (the blueprint fixes `a = 1/2`,
produced by `thm:eps-regularity` through `prop:no-singular-points`); it is recorded as the
explicit hypothesis `HasC1HolderBoundary a Ω`, for any exponent `0 < a < 1`.
-/

noncomputable section
open Set Metric
namespace LiquidDrop

variable {V : ℝ} {Ω : Set AmbientSpace}

/-- Blueprint `prop:bootstrap-C2`: `C^{2,α}` regularity on an open set passes to any
function agreeing with the given one there. -/
lemma HasC2HolderOn.congr_of_isOpen {n : ℕ} {α : ℝ}
    {f g : EuclideanSpace ℝ (Fin n) → ℝ} {U : Set (EuclideanSpace ℝ (Fin n))}
    (hU : IsOpen U) (hf : HasC2HolderOn α f U) (he : EqOn g f U) :
    HasC2HolderOn α g U := by
  have h1 : EqOn (fderiv ℝ g) (fderiv ℝ f) U := fun x hx =>
    (he.eventuallyEq_of_mem (hU.mem_nhds hx)).fderiv_eq
  have h2 : EqOn (fderiv ℝ (fderiv ℝ g)) (fderiv ℝ (fderiv ℝ f)) U := fun x hx =>
    (h1.eventuallyEq_of_mem (hU.mem_nhds hx)).fderiv_eq
  exact ⟨hf.contDiff.congr he, (nondiv_holder_congr he).1.mpr hf.function_holder,
    (nondiv_holder_congr h1).1.mpr hf.derivative_holder,
    (nondiv_holder_congr h2).1.mpr hf.hessian_holder⟩

/-- Blueprint `prop:bootstrap-C2`: if the boundary of the minimiser is `C^{1,a}`, then at
every boundary point there is a chart whose height is `C^{2,β}` near the base point, for
every `0 < β < 1`. -/
theorem MinimizerRep.exists_c2Holder_chart (h : MinimizerRep V Ω) {a : ℝ}
    (ha : 0 < a) (ha1 : a < 1) (hC : HasC1HolderBoundary a Ω)
    {p : AmbientSpace} (hp : p ∈ frontier Ω) :
    ∃ c : C1BoundaryChart, c.IsChartFor Ω ∧ p ∈ c.region ∧
      ∀ β : ℝ, 0 < β → β < 1 → ∃ ρ > 0, HasC2HolderOn β c.height
        (ball (graphProjectionN 2 (c.placement.symm p)) ρ) := by
  obtain ⟨c, hc, hpc, hf⟩ := hC p hp
  exact ⟨c, hc, hpc, h.height_C2_holder_all hc hp hpc ha ha1 hf⟩

/-- Blueprint `prop:bootstrap-C2`: a `C^{1,a}` boundary of the minimiser is `C²`. -/
theorem MinimizerRep.hasCkBoundary_two (h : MinimizerRep V Ω) {a : ℝ}
    (ha : 0 < a) (ha1 : a < 1) (hC : HasC1HolderBoundary a Ω) :
    HasCkBoundary 2 Ω := by
  apply hasCkBoundary_of_local
  intro p hp
  obtain ⟨c, hc, hpc, hβ⟩ := h.exists_c2Holder_chart ha ha1 hC hp
  obtain ⟨ρ, hρ, hC2⟩ := hβ (1 / 2) (by norm_num) (by norm_num)
  exact ⟨c, hc, hpc, ρ, hρ, hC2.contDiff⟩

/-- Blueprint `prop:bootstrap-C2`: every boundary point of a minimiser with `C^{1,a}`
boundary lies in a chart whose height is globally `C²` and `C^{2,β}` near the base point,
for every `0 < β < 1`. -/
theorem MinimizerRep.exists_c2_chart (h : MinimizerRep V Ω) {a : ℝ}
    (ha : 0 < a) (ha1 : a < 1) (hC : HasC1HolderBoundary a Ω)
    {p : AmbientSpace} (hp : p ∈ frontier Ω) :
    ∃ c : C1BoundaryChart, c.IsChartFor Ω ∧ p ∈ c.region ∧ ContDiff ℝ 2 c.height ∧
      ∀ β : ℝ, 0 < β → β < 1 → ∃ ρ > 0, HasC2HolderOn β c.height
        (ball (graphProjectionN 2 (c.placement.symm p)) ρ) := by
  obtain ⟨c, hc, hpc, hall⟩ := h.exists_c2Holder_chart ha ha1 hC hp
  obtain ⟨ρ, hρ, hC2⟩ := hall (1 / 2) (by norm_num) (by norm_num)
  obtain ⟨c', hc', hpc', hk', hpl, _, heq⟩ :=
    C1BoundaryChart.exists_localized (k := 2) hc hpc hρ hC2.contDiff
  refine ⟨c', hc', hpc', hk', ?_⟩
  intro β hβ hβ1
  obtain ⟨r, hr, hr2⟩ := hall β hβ hβ1
  have hmin : 0 < min r (ρ / 2) := lt_min hr (half_pos hρ)
  refine ⟨min r (ρ / 2), hmin, ?_⟩
  have hsub : ball (graphProjectionN 2 (c'.placement.symm p)) (min r (ρ / 2)) ⊆
      ball (graphProjectionN 2 (c.placement.symm p)) (ρ / 2) := by
    rw [hpl]; exact ball_subset_ball (min_le_right _ _)
  have hsub' : ball (graphProjectionN 2 (c'.placement.symm p)) (min r (ρ / 2)) ⊆
      ball (graphProjectionN 2 (c.placement.symm p)) r := by
    rw [hpl]; exact ball_subset_ball (min_le_left _ _)
  have hEq : EqOn c'.height c.height
      (ball (graphProjectionN 2 (c'.placement.symm p)) (min r (ρ / 2))) :=
    heq.mono hsub
  exact ((hr2.nondiv_mono hsub').1).congr_of_isOpen isOpen_ball hEq

/-- Blueprint `cor:EL-pointwise`: if the boundary of the minimiser is `C^{1,a}`, then it is
`C²` and at every boundary point `H + v_Ω = λ` holds in a chart with globally `C²` height
(and in every such chart, by `MinimizerRep.eulerLagrange_pointwise`). -/
theorem MinimizerRep.eulerLagrange_everywhere (h : MinimizerRep V Ω) {a : ℝ}
    (ha : 0 < a) (ha1 : a < 1) (hC : HasC1HolderBoundary a Ω) :
    HasCkBoundary 2 Ω ∧ ∀ p ∈ frontier Ω, ∃ c : C1BoundaryChart, c.IsChartFor Ω ∧
      p ∈ c.region ∧ ContDiff ℝ 2 c.height ∧
      meanCurvature (frontier Ω) c.outwardNormal p + (coulombPotential Ω p).toReal =
        minimizerMultiplier V Ω := by
  refine ⟨h.hasCkBoundary_two ha ha1 hC, ?_⟩
  intro p hp
  obtain ⟨c, hc, hpc, hk, _⟩ := h.exists_c2_chart ha ha1 hC hp
  exact ⟨c, hc, hpc, hk, h.eulerLagrange_pointwise hc hk hp hpc⟩

end LiquidDrop

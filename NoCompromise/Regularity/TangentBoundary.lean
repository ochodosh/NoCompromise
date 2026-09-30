module

public import NoCompromise.Regularity.Monotonicity

@[expose] public section

/-!
# Nontriviality of a minimizing tangent limit

For a quasiminimizer, a point outside the essential boundary has a neighborhood
with zero perimeter. Thus positive ball perimeters place the point on the
boundary of the canonical density-one representative.
-/

noncomputable section
open MeasureTheory Set Filter Metric
open scoped Topology ENNReal
namespace LiquidDrop

lemma IsLocallyPerimeterMinimizing.isOmegaMinimal {F : Set AmbientSpace}
    (hF : IsLocallyPerimeterMinimizing F) : IsOmegaMinimal F 0 := by
  change IsOmegaMinimalAtScales F 0 1
  simpa only [ENNReal.ofReal_one] using hF 1 (by norm_num)

lemma IsOmegaMinimal.mem_frontier_densityOne_of_perimeter_pos
    {F : Set AmbientSpace} {ω : ℝ} (hF : IsOmegaMinimal F ω) {x : AmbientSpace}
    (hp : ∀ R : ℝ, 0 < R → 0 < (perimeterIn F (ball x R)).toReal) :
    x ∈ frontier (densityOne F) := by
  rw [hF.frontier_densityOne]
  by_contra hx
  obtain ⟨R, hR, hsub⟩ := Metric.isOpen_iff.mp hF.isClosed_essentialBoundary.isOpen_compl x hx
  have hd : Disjoint (ball x R) (essentialBoundary F) :=
    disjoint_left.mpr fun y hy hb => hsub hy hb
  have hz := perimeterIn_eq_zero_of_disjoint_essentialBoundary hF.locallyFinite
    hF.nullMeasurable isOpen_ball hd
  have hh := hp R hR
  rw [hz, ENNReal.toReal_zero] at hh
  exact lt_irrefl _ hh

/-- A positive constant density ratio prevents a minimizing tangent from losing
either phase at the origin, expressed through the canonical open representative. -/
lemma IsLocallyPerimeterMinimizing.zero_mem_frontier_of_density
    {F : Set AmbientSpace} (hF : IsLocallyPerimeterMinimizing F)
    {θ : ℝ} (hθ : 0 < θ)
    (hd : ∀ R : ℝ, 0 < R → (perimeterIn F (ball 0 R)).toReal = θ * R ^ 2) :
    (0 : AmbientSpace) ∈ frontier (densityOne F) := by
  apply hF.isOmegaMinimal.mem_frontier_densityOne_of_perimeter_pos
  intro R hR
  rw [hd R hR]
  positivity

end LiquidDrop

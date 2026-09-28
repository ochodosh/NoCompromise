import NoCompromise.Regularity.DeformationCompression
import NoCompromise.Regularity.DeformationStrip

/-! # Actual finite-perimeter competitors for the cylindrical deformation -/

noncomputable section
open Set MeasureTheory
namespace LiquidDrop

lemma compressionBeta_eq_one {σ τ ε : ℝ} (hst : σ < τ)
    {p : EuclideanSpace ℝ (Fin 2)} (hp : τ ≤ ‖p‖) : compressionBeta σ τ ε p = 1 := by
  have he : compressionProfile σ τ p = 1 := compressionRadialProfile_one hst hp
  simp only [compressionBeta, he, mul_one]
  ring

lemma verticalCompression_eq_self {β : EuclideanSpace ℝ (Fin 2) → ℝ} {c : ℝ}
    {x : AmbientSpace} (hb : β (graphProjectionN 2 x) = 1) :
    verticalCompression β c x = x := by
  rw [verticalCompression, hb, one_mul, add_sub_cancel]
  exact graphAppendN_projection x

lemma compression_image_mem_outside {σ τ ε c : ℝ} (hst : σ < τ)
    {E : Set AmbientSpace} {x : AmbientSpace} (hx : τ ≤ ‖graphProjectionN 2 x‖) :
    x ∈ verticalCompression (compressionBeta σ τ ε) c '' E ↔ x ∈ E := by
  constructor
  · rintro ⟨y, hy, he⟩
    have hp : graphProjectionN 2 y = graphProjectionN 2 x := by
      simpa only [verticalCompression_projection] using congrArg (graphProjectionN 2) he
    have heq : verticalCompression (compressionBeta σ τ ε) c y = y :=
      verticalCompression_eq_self (compressionBeta_eq_one hst (by simpa only [hp] using hx))
    rw [heq] at he
    exact he ▸ hy
  · intro hE
    exact ⟨x, hE, verticalCompression_eq_self (compressionBeta_eq_one hst hx)⟩

/-- Compress the globally BV slice extension and put the original set back
outside the vertical strip. The core also shrinks and will flatten in the limit. -/
def compressionCompetitor (E : Set AmbientSpace) (r σ τ ε c : ℝ) : Set AmbientSpace :=
  replaceVerticalStrip E
    (verticalCompression (compressionBeta σ τ ε) c '' verticalPhaseExtension E r) r

theorem compressionCompetitor_locallyFinitePerimeter {E : Set AmbientSpace}
    (hE : HasLocallyFinitePerimeter E) (hmE : NullMeasurableSet E volume)
    {r σ τ ε : ℝ} (hr : 0 ≤ r) (hσ : 0 < σ) (hst : σ < τ)
    (hε : 0 < ε) (hε1 : ε ≤ 1) (c : ℝ) :
    HasLocallyFinitePerimeter (compressionCompetitor E r σ τ ε c) ∧
      NullMeasurableSet (compressionCompetitor E r σ τ ε c) volume := by
  have hExt := hasLocallyFinitePerimeter_verticalPhaseExtension hE hmE hr
  have hmExt := nullMeasurableSet_verticalPhaseExtension hmE r
  have hG := hasLocallyFinitePerimeter_verticalCompression hσ hst hε hε1 c
    _ hExt hmExt
  have hmG := nullMeasurableSet_image_of_differentiable
    ((contDiff_verticalCompression (contDiff_compressionBeta hσ hst ε) c).differentiable
      one_ne_zero)
    (verticalCompressionHomeomorph (compressionBeta σ τ ε)
      (contDiff_compressionBeta hσ hst ε) (compressionBeta_ne_zero hε hε1) c).injective hmExt
  exact ⟨hasLocallyFinitePerimeter_replaceVerticalStrip hE hmE hG hmG hr,
    nullMeasurableSet_replaceVerticalStrip hmE hmG r⟩

lemma compressionCompetitor_mem_outside_base {E : Set AmbientSpace}
    {r σ τ ε c : ℝ} (hst : σ < τ) {x : AmbientSpace}
    (hx : τ ≤ ‖graphProjectionN 2 x‖) :
    x ∈ compressionCompetitor E r σ τ ε c ↔ x ∈ E := by
  by_cases hh : -r ≤ x 2 ∧ x 2 < r
  · rw [compressionCompetitor, replaceVerticalStrip_mem_between hh,
      compression_image_mem_outside hst hx, verticalPhaseExtension_mem_between hh]
  · exact replaceVerticalStrip_mem_outside hh

lemma compressionCompetitor_mem_outside_height {E : Set AmbientSpace}
    {r σ τ ε c : ℝ} {x : AmbientSpace} (hx : ¬ (-r ≤ x 2 ∧ x 2 < r)) :
    x ∈ compressionCompetitor E r σ τ ε c ↔ x ∈ E :=
  replaceVerticalStrip_mem_outside hx

end LiquidDrop

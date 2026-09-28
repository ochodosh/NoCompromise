import NoCompromise.Regularity.DeformationLocality
import NoCompromise.Regularity.OmegaMinimal

/-! # Quasiminimality localized by genuine boundary-null cancellation -/

noncomputable section
open Set MeasureTheory Filter Metric
open scoped ENNReal Topology symmDiff
namespace LiquidDrop
set_option maxSynthPendingDepth 8

/-- Exterior perimeter cancels on any bounded open comparison region whose
boundary is null for the competitor perimeter. No global finite perimeter is
assumed, and the original set's boundary mass need not vanish. -/
theorem IsOmegaMinimal.perimeterIn_le_of_null_frontier
    {E F U : Set AmbientSpace} {ω : ℝ} (hE : IsOmegaMinimal E ω)
    (hF : HasLocallyFinitePerimeter F) (hmF : NullMeasurableSet F volume)
    (hU : IsOpen U) (hbU : Bornology.IsBounded U)
    (hUB : closure U ⊆ ball (0 : AmbientSpace) 1)
    (hext : ∀ x ∉ U, x ∈ F ↔ x ∈ E)
    (hfront : canonicalPerimeterMeasure F hF hmF (frontier U) = 0) :
    perimeterIn E U ≤ perimeterIn F U + ENNReal.ofReal ω * volume U := by
  have hdiff : F ∆ E ⊆ U := by
    intro x hx
    by_contra hu
    have he := hext x hu
    simp only [mem_symmDiff] at hx
    tauto
  have hc : IsCompact (closure (F ∆ E)) :=
    hbU.isCompact_closure.of_isClosed_subset isClosed_closure (closure_mono hdiff)
  have hs : closure (F ∆ E) ⊆ ball (0 : AmbientSpace) 1 := (closure_mono hdiff).trans hUB
  have hcomp := hE.comparison 0 1 (by norm_num) (by simp) F hmF hF hc hs
  have herr : volume (E ∆ F) ≤ volume U := by
    rw [symmDiff_comm]
    exact measure_mono hdiff
  let W := ball (0 : AmbientSpace) 1 ∩ (closure U)ᶜ
  have hW : IsOpen W := isOpen_ball.inter isClosed_closure.isOpen_compl
  have hEUW : Disjoint U W := disjoint_left.mpr fun x hx hw => hw.2 (subset_closure hx)
  have hWU : W ⊆ Uᶜ := fun x hx hu => hx.2 (subset_closure hu)
  have heq : (canonicalPerimeterMeasure E hE.locallyFinite hE.nullMeasurable).restrict W =
      (canonicalPerimeterMeasure F hF hmF).restrict W := by
    apply canonicalPerimeterMeasure_restrict_eq_of_indicator_ae hE.locallyFinite
      hE.nullMeasurable hF hmF hW
    apply (ae_restrict_iff' hW.measurableSet).mpr
    exact Eventually.of_forall fun x hx => by
      have he := hext x (hWU hx)
      by_cases hxE : x ∈ E <;> simp [he, hxE]
  have hextmass : perimeterIn F W = perimeterIn E W := by
    have he := congrArg (fun μ : Measure AmbientSpace => μ univ) heq
    simpa only [Measure.restrict_apply_univ,
      canonicalPerimeterMeasure_open E hE.locallyFinite hE.nullMeasurable hW,
      canonicalPerimeterMeasure_open F hF hmF hW] using he.symm
  have hcover : ball (0 : AmbientSpace) 1 ⊆ U ∪ W ∪ frontier U := by
    intro x hx
    by_cases hxU : x ∈ U
    · exact Or.inl (Or.inl hxU)
    by_cases hxcl : x ∈ closure U
    · exact Or.inr (by rw [hU.frontier_eq]; exact ⟨hxcl, hxU⟩)
    · exact Or.inl (Or.inr ⟨hx, hxcl⟩)
  have hFball : perimeterIn F (ball (0 : AmbientSpace) 1) ≤
      perimeterIn F U + perimeterIn E W := by
    rw [← canonicalPerimeterMeasure_open F hF hmF isOpen_ball,
      ← canonicalPerimeterMeasure_open F hF hmF hU, ← hextmass,
      ← canonicalPerimeterMeasure_open F hF hmF hW]
    apply (measure_mono hcover).trans
    have hh := (measure_union_le (μ := canonicalPerimeterMeasure F hF hmF)
      (U ∪ W) (frontier U)).trans (add_le_add (measure_union_le U W) le_rfl)
    simpa only [hfront, add_zero] using hh
  have hEball : perimeterIn E U + perimeterIn E W ≤
      perimeterIn E (ball (0 : AmbientSpace) 1) := by
    rw [← canonicalPerimeterMeasure_open E hE.locallyFinite hE.nullMeasurable hU,
      ← canonicalPerimeterMeasure_open E hE.locallyFinite hE.nullMeasurable hW,
      ← canonicalPerimeterMeasure_open E hE.locallyFinite hE.nullMeasurable isOpen_ball,
      ← measure_union hEUW hW.measurableSet]
    exact measure_mono (union_subset (subset_closure.trans hUB) inter_subset_left)
  have hfin : perimeterIn E W < ∞ :=
    (variation_mono measurableSet_ball inter_subset_left).trans_lt
      (hE.locallyFinite _ isOpen_ball isBounded_ball.isCompact_closure)
  apply ENNReal.le_of_add_le_add_left hfin.ne
  have hh := hEball.trans (hcomp.trans (add_le_add hFball (mul_le_mul' le_rfl herr)))
  simpa only [add_assoc, add_comm, add_left_comm] using hh

end LiquidDrop

module

public import NoCompromise.Regularity.PerimeterConvergenceLocal

@[expose] public section

/-!
# The comparison inequality for actual good-radius glued competitors

Quasiminimality is used at a larger admissible radius. The unchanged exterior
perimeter is finite there and cancels, leaving the interior target perimeter,
the genuine spherical mismatch, and the volume penalty.
-/

noncomputable section
open MeasureTheory Set Filter Metric
open scoped ENNReal Topology symmDiff
namespace LiquidDrop
set_option maxSynthPendingDepth 8

/-- The actual gluing comparison works at every admissible scale and does not
require finite global perimeter of either set. -/
theorem IsOmegaMinimalAtScales.perimeterIn_goodRadius_gluing_le
    {E F : Set AmbientSpace} {ω : ℝ} {s : ℝ≥0∞} (hE : IsOmegaMinimalAtScales E ω s)
    {hF : HasLocallyFinitePerimeter F} {hmF : NullMeasurableSet F volume}
    {x : AmbientSpace} {r R : ℝ}
    (hgE : IsGoodRadius E hE.locallyFinite hE.nullMeasurable x r)
    (hgF : IsGoodRadius F hF hmF x r) (hrR : r < R) (hscale : ENNReal.ofReal R ≤ s) :
    perimeterIn E (ball x r) ≤ perimeterIn F (ball x r) +
      hausdorffMeasure2 3 ((densityOne F ∆ densityOne E) ∩ sphere x r) +
        ENNReal.ofReal ω * volume ((E ∆ F) ∩ ball x r) := by
  let G := (F ∩ ball x r) ∪ (E \ ball x r)
  have hmG : NullMeasurableSet G volume :=
    (hmF.inter measurableSet_ball.nullMeasurableSet).union
      (hE.nullMeasurable.diff measurableSet_ball.nullMeasurableSet)
  have hG : HasLocallyFinitePerimeter G := hgE.hasLocallyFinitePerimeter_gluing hgF
  have hdiff : G ∆ E = (E ∆ F) ∩ ball x r := by
    ext y
    simp only [G, mem_symmDiff, mem_union, mem_inter_iff, Set.mem_sdiff]
    tauto
  have hcl : closure (G ∆ E) ⊆ closedBall x r := by
    rw [hdiff]
    exact closure_minimal (inter_subset_right.trans ball_subset_closedBall) isClosed_closedBall
  have hc : IsCompact (closure (G ∆ E)) :=
    (isCompact_closedBall x r).of_isClosed_subset isClosed_closure hcl
  have hs : closure (G ∆ E) ⊆ ball x R := hcl.trans (closedBall_subset_ball hrR)
  have hcomp := hE.comparison x R (hgE.1.trans hrR) hscale G hmG hG hc hs
  have herr : E ∆ G = (E ∆ F) ∩ ball x r := (symmDiff_comm E G).trans hdiff
  rw [herr] at hcomp
  have hglue := hgE.gluing_perimeterIn_le hgF isOpen_ball (closedBall_subset_ball hrR)
  have hupper := hcomp.trans (add_le_add hglue le_rfl)
  let A := ball x R \ closedBall x r
  have hA : IsOpen A := isOpen_ball.sdiff isClosed_closedBall
  have hAF : perimeterIn E A < ∞ :=
    (variation_mono measurableSet_ball sdiff_subset).trans_lt
      (hE.locallyFinite _ isOpen_ball isBounded_ball.isCompact_closure)
  have hp := canonicalPerimeterPolar E hE.locallyFinite hE.nullMeasurable
  have hdis : Disjoint (ball x r) A := Set.disjoint_left.mpr fun _ hz hw =>
    hw.2 (ball_subset_closedBall hz)
  have hsub : ball x r ∪ A ⊆ ball x R :=
    union_subset (ball_subset_ball hrR.le) sdiff_subset
  have hsum : perimeterIn E (ball x r) + perimeterIn E A ≤ perimeterIn E (ball x R) := by
    rw [← hp.open_eq _ isOpen_ball, ← hp.open_eq _ hA, ← hp.open_eq _ isOpen_ball]
    rw [← measure_union hdis hA.measurableSet]
    exact measure_mono hsub
  apply ENNReal.le_of_add_le_add_left hAF.ne
  simpa only [A, add_assoc, add_comm, add_left_comm] using hsum.trans hupper

end LiquidDrop

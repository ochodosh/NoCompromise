import NoCompromise.BV.GraphTraces

/-!
# Reflection of genuine BV traces

Negation exchanges essential left and right approach filters. Consequently the
canonical one-sided traces, including their default values when no limit exists,
are exchanged exactly. Reflection of graph coordinates gives the corresponding
pointwise identification of lower and upper graph traces.
-/

noncomputable section
open MeasureTheory Set Filter Metric
open scoped ENNReal Topology
namespace LiquidDrop
set_option maxSynthPendingDepth 8

lemma tendsto_neg_bvTraceLeftFilter (a : ℝ) :
    Tendsto Neg.neg (bvTraceLeftFilter a) (bvTraceRightFilter (-a)) :=
  tendsto_neg_nhdsLT.inf
    (Measure.measurePreserving_neg (volume : Measure ℝ)).quasiMeasurePreserving.tendsto_ae

lemma tendsto_neg_bvTraceRightFilter (a : ℝ) :
    Tendsto Neg.neg (bvTraceRightFilter a) (bvTraceLeftFilter (-a)) :=
  tendsto_neg_nhdsGT.inf
    (Measure.measurePreserving_neg (volume : Measure ℝ)).quasiMeasurePreserving.tendsto_ae

lemma HasBVRightTrace.comp_neg {f : ℝ → ℝ} {a L : ℝ} (h : HasBVRightTrace f a L) :
    HasBVLeftTrace (fun t => f (-t)) (-a) L := by
  apply h.comp
  simpa only [neg_neg] using tendsto_neg_bvTraceLeftFilter (-a)

lemma HasBVLeftTrace.comp_neg {f : ℝ → ℝ} {a L : ℝ} (h : HasBVLeftTrace f a L) :
    HasBVRightTrace (fun t => f (-t)) (-a) L := by
  apply h.comp
  simpa only [neg_neg] using tendsto_neg_bvTraceRightFilter (-a)

lemma bvLeftTrace_comp_neg (f : ℝ → ℝ) (a : ℝ) :
    bvLeftTrace (fun t => f (-t)) (-a) = bvRightTrace f a := by
  classical
  by_cases h : ∃ L, HasBVRightTrace f a L
  · obtain ⟨L, hL⟩ := h
    exact hL.comp_neg.eq_bvLeftTrace.trans hL.eq_bvRightTrace.symm
  · have hn : ¬∃ L, HasBVLeftTrace (fun t => f (-t)) (-a) L := by
      rintro ⟨L, hL⟩
      apply h
      refine ⟨L, ?_⟩
      simpa only [neg_neg] using hL.comp_neg
    simp only [bvLeftTrace, bvRightTrace, dite_eq_right hn, dite_eq_right h]

lemma bvRightTrace_comp_neg (f : ℝ → ℝ) (a : ℝ) :
    bvRightTrace (fun t => f (-t)) (-a) = bvLeftTrace f a := by
  simpa only [neg_neg] using (bvLeftTrace_comp_neg (fun t => f (-t)) (-a)).symm

lemma coordinateReflection_last_graphAppendN {n : ℕ}
    (x : EuclideanSpace ℝ (Fin n)) (t : ℝ) :
    coordinateReflection (Fin.last n) (graphAppendN x t) = graphAppendN x (-t) := by
  apply PiLp.ext
  intro i
  by_cases hi : i = Fin.last n
  · subst i
    simp [coordinateReflection_apply]
  · simp [coordinateReflection_apply, graphAppendN, hi]

lemma graphProjectionN_coordinateReflection_last {n : ℕ}
    (z : EuclideanSpace ℝ (Fin (n + 1))) :
    graphProjectionN n (coordinateReflection (Fin.last n) z) = graphProjectionN n z := by
  apply PiLp.ext
  intro i
  simp only [graphProjectionN_apply, coordinateReflection_apply, Fin.castSucc_ne_last,
    ↓reduceIte]

/-- Reflection exchanges the two constructed graph traces pointwise. -/
lemma graphBVLowerTrace_reflect {n : ℕ}
    (f : EuclideanSpace ℝ (Fin (n + 1)) → ℝ) (g : EuclideanSpace ℝ (Fin n) → ℝ)
    (z : EuclideanSpace ℝ (Fin (n + 1))) :
    graphBVLowerTrace (f ∘ coordinateReflection (Fin.last n)) (fun x => -g x)
      (coordinateReflection (Fin.last n) z) = graphBVUpperTrace f g z := by
  simp only [graphBVLowerTrace, graphBVUpperTrace, graphProjectionN_coordinateReflection_last,
    Function.comp_def, coordinateReflection_last_graphAppendN, neg_add, neg_neg]
  simpa only [neg_zero] using
    bvLeftTrace_comp_neg (fun t => f (graphAppendN (graphProjectionN n z)
      (t + g (graphProjectionN n z)))) 0

lemma graphBVUpperTrace_reflect {n : ℕ}
    (f : EuclideanSpace ℝ (Fin (n + 1)) → ℝ) (g : EuclideanSpace ℝ (Fin n) → ℝ)
    (z : EuclideanSpace ℝ (Fin (n + 1))) :
    graphBVUpperTrace (f ∘ coordinateReflection (Fin.last n)) (fun x => -g x)
      (coordinateReflection (Fin.last n) z) = graphBVLowerTrace f g z := by
  simp only [graphBVLowerTrace, graphBVUpperTrace, graphProjectionN_coordinateReflection_last,
    Function.comp_def, coordinateReflection_last_graphAppendN, neg_add, neg_neg]
  simpa only [neg_zero] using
    bvRightTrace_comp_neg (fun t => f (graphAppendN (graphProjectionN n z)
      (t + g (graphProjectionN n z)))) 0

end LiquidDrop

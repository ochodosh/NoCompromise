import NoCompromise.BV.FlatCut
import NoCompromise.BV.ScalarC1Transport
import NoCompromise.DeGiorgi.SmoothGraph

/-!
# Actual locally integrable BV traces on C¹ graphs

A volume-preserving C¹ shear reduces a graph to a coordinate hyperplane. The
traces below are the already constructed essential one-sided limits, and are
locally integrable for the genuine Hausdorff surface measure of the graph.
-/

noncomputable section
open MeasureTheory Filter Set Metric
open scoped ENNReal Topology
namespace LiquidDrop
set_option maxSynthPendingDepth 8

/-- The ambient Euclidean realization of the graph shear. -/
def c1GraphShear {n : ℕ} {g : EuclideanSpace ℝ (Fin n) → ℝ} (hg : Continuous g) :
    EuclideanSpace ℝ (Fin (n + 1)) ≃ₜ EuclideanSpace ℝ (Fin (n + 1)) :=
  (realLineCoordinates n).symm.trans (smoothGraphCoordinates hg)

@[simp] lemma c1GraphShear_apply {n : ℕ} {g : EuclideanSpace ℝ (Fin n) → ℝ}
    (hg : Continuous g) (z : EuclideanSpace ℝ (Fin (n + 1))) :
    c1GraphShear hg z = graphAppendN (graphProjectionN n z)
      (z (Fin.last n) + g (graphProjectionN n z)) := rfl

@[simp] lemma c1GraphShear_symm_apply {n : ℕ} {g : EuclideanSpace ℝ (Fin n) → ℝ}
    (hg : Continuous g) (z : EuclideanSpace ℝ (Fin (n + 1))) :
    (c1GraphShear hg).symm z = graphAppendN (graphProjectionN n z)
      (z (Fin.last n) - g (graphProjectionN n z)) := rfl

lemma contDiff_c1GraphShear {n : ℕ} {g : EuclideanSpace ℝ (Fin n) → ℝ}
    (hg : ContDiff ℝ 1 g) : ContDiff ℝ 1 (c1GraphShear hg.continuous) := by
  change ContDiff ℝ 1 (fun z : EuclideanSpace ℝ (Fin (n + 1)) =>
    graphBaseN n (graphProjectionN n z) +
      (z (Fin.last n) + g (graphProjectionN n z)) • EuclideanSpace.single (Fin.last n) 1)
  have hp : ContDiff ℝ 1 (fun z : EuclideanSpace ℝ (Fin (n + 1)) => z (Fin.last n)) :=
    (EuclideanSpace.proj (𝕜 := ℝ) (Fin.last n)).contDiff
  fun_prop

lemma contDiff_c1GraphShear_symm {n : ℕ} {g : EuclideanSpace ℝ (Fin n) → ℝ}
    (hg : ContDiff ℝ 1 g) : ContDiff ℝ 1 (c1GraphShear hg.continuous).symm := by
  change ContDiff ℝ 1 (fun z : EuclideanSpace ℝ (Fin (n + 1)) =>
    graphBaseN n (graphProjectionN n z) +
      (z (Fin.last n) - g (graphProjectionN n z)) • EuclideanSpace.single (Fin.last n) 1)
  have hp : ContDiff ℝ 1 (fun z : EuclideanSpace ℝ (Fin (n + 1)) => z (Fin.last n)) :=
    (EuclideanSpace.proj (𝕜 := ℝ) (Fin.last n)).contDiff
  fun_prop

lemma c1GraphShear_measurePreserving {n : ℕ} {g : EuclideanSpace ℝ (Fin n) → ℝ}
    (hg : Continuous g) : MeasurePreserving (c1GraphShear hg) volume volume :=
  (smoothGraphCoordinates_measurePreserving hg).comp
    ((realLineCoordinates_measurePreserving n).symm (realLineCoordinates n).toMeasurableEquiv)

lemma c1GraphShear_preimage_subgraph {n : ℕ} {g : EuclideanSpace ℝ (Fin n) → ℝ}
    (hg : Continuous g) :
    c1GraphShear hg ⁻¹' smoothSubgraph g = {z | z (Fin.last n) < 0} := by
  ext z
  simp [smoothSubgraph]

lemma IsLocallyBVOn.comp_c1GraphShear {n : ℕ}
    {f : EuclideanSpace ℝ (Fin (n + 1)) → ℝ} (hf : IsLocallyBVOn f univ)
    {g : EuclideanSpace ℝ (Fin n) → ℝ} (hg : ContDiff ℝ 1 g) :
    IsLocallyBVOn (f ∘ c1GraphShear hg.continuous) univ :=
  hf.comp_C1_diffeomorphism _ (contDiff_c1GraphShear hg) (contDiff_c1GraphShear_symm hg)

/-- The interior, lower-side trace on a graph, extended vertically off the graph. -/
def graphBVLowerTrace {n : ℕ} (f : EuclideanSpace ℝ (Fin (n + 1)) → ℝ)
    (g : EuclideanSpace ℝ (Fin n) → ℝ) (z : EuclideanSpace ℝ (Fin (n + 1))) : ℝ :=
  bvLeftTrace (fun t => f (graphAppendN (graphProjectionN n z)
    (t + g (graphProjectionN n z)))) 0

/-- The exterior, upper-side trace on a graph, extended vertically off the graph. -/
def graphBVUpperTrace {n : ℕ} (f : EuclideanSpace ℝ (Fin (n + 1)) → ℝ)
    (g : EuclideanSpace ℝ (Fin n) → ℝ) (z : EuclideanSpace ℝ (Fin (n + 1))) : ℝ :=
  bvRightTrace (fun t => f (graphAppendN (graphProjectionN n z)
    (t + g (graphProjectionN n z)))) 0

lemma graphBVLowerTrace_graphMap {n : ℕ}
    (f : EuclideanSpace ℝ (Fin (n + 1)) → ℝ)
    {g : EuclideanSpace ℝ (Fin n) → ℝ} (hg : Continuous g) (x : EuclideanSpace ℝ (Fin n)) :
    graphBVLowerTrace f g (graphMapN g x) =
      flatBVLeftTrace (f ∘ c1GraphShear hg) 0 x := by
  simp [graphBVLowerTrace, flatBVLeftTrace,
    show graphMapN g x = graphAppendN x (g x) from rfl]

lemma graphBVUpperTrace_graphMap {n : ℕ}
    (f : EuclideanSpace ℝ (Fin (n + 1)) → ℝ)
    {g : EuclideanSpace ℝ (Fin n) → ℝ} (hg : Continuous g) (x : EuclideanSpace ℝ (Fin n)) :
    graphBVUpperTrace f g (graphMapN g x) =
      flatBVRightTrace (f ∘ c1GraphShear hg) 0 x := by
  simp [graphBVUpperTrace, flatBVRightTrace,
    show graphMapN g x = graphAppendN x (g x) from rfl]

lemma IsLocallyBVOn.ae_graph_oneSided_traces {n : ℕ}
    {f : EuclideanSpace ℝ (Fin (n + 1)) → ℝ} (hf : IsLocallyBVOn f univ)
    {g : EuclideanSpace ℝ (Fin n) → ℝ} (hg : ContDiff ℝ 1 g) :
    ∀ᵐ x ∂volume,
      HasBVLeftTrace (fun t => f (graphAppendN x (t + g x))) 0
        (graphBVLowerTrace f g (graphMapN g x)) ∧
      HasBVRightTrace (fun t => f (graphAppendN x (t + g x))) 0
        (graphBVUpperTrace f g (graphMapN g x)) := by
  filter_upwards [(hf.comp_c1GraphShear hg).ae_line_oneSided_traces] with x hx
  simpa only [graphBVLowerTrace_graphMap f hg.continuous,
    graphBVUpperTrace_graphMap f hg.continuous, flatBVLeftTrace, flatBVRightTrace,
    Function.comp_def,
    c1GraphShear_apply, graphProjectionN_append, graphAppendN_last] using hx 0

/-- Local integrability on the base transfers to Hausdorff graph area. -/
lemma locallyIntegrable_smoothGraphArea_of_comp {n : ℕ}
    {g : EuclideanSpace ℝ (Fin n) → ℝ} (hg : ContDiff ℝ 1 g)
    {T : EuclideanSpace ℝ (Fin (n + 1)) → ℝ}
    (hT : LocallyIntegrable (T ∘ graphMapN g) volume) :
    LocallyIntegrable T (smoothGraphArea g) := by
  apply locallyIntegrable_iff.mpr
  intro K hK
  have he := isClosedEmbedding_smoothGraphMap hg.continuous
  have hpre : IsCompact (graphMapN g ⁻¹' K) := he.isProperMap.isCompact_preimage hK
  have hc : Continuous (fun x => Real.sqrt (1 + ‖gradient g x‖ ^ 2)) :=
    Real.continuous_sqrt.comp
      (continuous_const.add ((continuous_gradient_of_contDiff hg).norm.pow 2))
  rw [smoothGraphArea_eq_map hg, he.measurableEmbedding.integrableOn_map_iff]
  rw [IntegrableOn, restrict_withDensity hpre.measurableSet,
    integrable_withDensity_iff hc.measurable.ennreal_ofReal
      (Eventually.of_forall fun _ => ENNReal.ofReal_lt_top)]
  simpa only [ENNReal.toReal_ofReal (Real.sqrt_nonneg _)] using!
    (hT.integrableOn_isCompact hpre).mul_continuousOn hc.continuousOn hpre

/-- Graph traces are locally L¹ for actual surface area, with no global slope bound. -/
theorem IsLocallyBVOn.locallyIntegrable_graphBVTraces {n : ℕ}
    {f : EuclideanSpace ℝ (Fin (n + 1)) → ℝ} (hf : IsLocallyBVOn f univ)
    {g : EuclideanSpace ℝ (Fin n) → ℝ} (hg : ContDiff ℝ 1 g) :
    LocallyIntegrable (graphBVLowerTrace f g) (smoothGraphArea g) ∧
      LocallyIntegrable (graphBVUpperTrace f g) (smoothGraphArea g) := by
  constructor
  · apply locallyIntegrable_smoothGraphArea_of_comp hg
    simpa only [Function.comp_def, graphBVLowerTrace_graphMap f hg.continuous] using
      (hf.comp_c1GraphShear hg).locallyIntegrable_flatBVLeftTrace 0
  · apply locallyIntegrable_smoothGraphArea_of_comp hg
    simpa only [Function.comp_def, graphBVUpperTrace_graphMap f hg.continuous] using
      (hf.comp_c1GraphShear hg).locallyIntegrable_flatBVRightTrace 0

lemma ae_smoothGraphArea_of_ae_base {n : ℕ}
    {g : EuclideanSpace ℝ (Fin n) → ℝ} (hg : ContDiff ℝ 1 g)
    {P : EuclideanSpace ℝ (Fin (n + 1)) → Prop}
    (hP : ∀ᵐ x ∂volume, P (graphMapN g x)) : ∀ᵐ z ∂smoothGraphArea g, P z := by
  rw [smoothGraphArea_eq_map hg,
    (isClosedEmbedding_smoothGraphMap hg.continuous).measurableEmbedding.ae_map_iff]
  exact (withDensity_absolutelyContinuous _ _).ae_le hP

/-- The surface traces are genuine essential limits along transverse vertical lines. -/
theorem IsLocallyBVOn.ae_surface_graph_oneSided_traces {n : ℕ}
    {f : EuclideanSpace ℝ (Fin (n + 1)) → ℝ} (hf : IsLocallyBVOn f univ)
    {g : EuclideanSpace ℝ (Fin n) → ℝ} (hg : ContDiff ℝ 1 g) :
    ∀ᵐ z ∂smoothGraphArea g,
      HasBVLeftTrace (fun t => f (graphAppendN (graphProjectionN n z)
        (t + g (graphProjectionN n z)))) 0 (graphBVLowerTrace f g z) ∧
      HasBVRightTrace (fun t => f (graphAppendN (graphProjectionN n z)
        (t + g (graphProjectionN n z)))) 0 (graphBVUpperTrace f g z) := by
  apply ae_smoothGraphArea_of_ae_base hg
  simpa only [show ∀ x, graphProjectionN n (graphMapN g x) = x from
    fun x => graphProjectionN_append x (g x)] using hf.ae_graph_oneSided_traces hg

end LiquidDrop

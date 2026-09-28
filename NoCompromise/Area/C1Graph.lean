import NoCompromise.Area.C1GraphLocal
import Mathlib.MeasureTheory.Integral.Lebesgue.Map
import Mathlib.Topology.Compactness.SigmaCompact

/-!
# Area and weighted area of C¹ graphs on open domains

Compact exhaustion extends the elementary compact-patch area theorem. The
resulting pushforward and integral identities use normalized Hausdorff measure.
-/

noncomputable section
open MeasureTheory Set Module Filter Function Metric
open scoped ENNReal NNReal Topology Gradient
namespace LiquidDrop
set_option maxSynthPendingDepth 8

/-- The area identity on arbitrary Borel subsets of an open C¹ graph domain. -/
theorem c1_graph_image_measure_eq_lintegral {k : ℕ}
    {U A : Set (EuclideanSpace ℝ (Fin k))} (hU : IsOpen U)
    {f : EuclideanSpace ℝ (Fin k) → ℝ} (hf : ContDiffOn ℝ 1 f U)
    (hA : MeasurableSet A) (hAU : A ⊆ U) :
    Measure.euclideanHausdorffMeasure k (graphMapN f '' A) =
      ∫⁻ y in A, ENNReal.ofReal (graphJacobianN f y) := by
  let : LocallyCompactSpace U := hU.locallyCompactSpace
  let K := CompactExhaustion.choice U
  let C : ℕ → Set (EuclideanSpace ℝ (Fin k)) := fun j => Subtype.val '' K j
  have hCc (j : ℕ) : IsCompact (C j) := (K.isCompact j).image continuous_subtype_val
  have hCU (j : ℕ) : C j ⊆ U := by rintro _ ⟨x, _, rfl⟩; exact x.property
  have hCm : Monotone C := fun i j hij => image_mono (K.subset hij)
  let B (j : ℕ) := A ∩ C j
  have hBm : Monotone B := fun i j hij => inter_subset_inter_right A (hCm hij)
  have hBmeas (j : ℕ) : MeasurableSet (B j) := hA.inter (hCc j).measurableSet
  have hBA : (⋃ j, B j) = A := by
    apply Subset.antisymm (iUnion_subset fun _ => inter_subset_left)
    intro x hx
    obtain ⟨j, hj⟩ := K.exists_mem ⟨x, hAU hx⟩
    exact mem_iUnion.mpr ⟨j, hx, ⟨⟨x, hAU hx⟩, hj, rfl⟩⟩
  let μ := volume.withDensity (fun x => ENNReal.ofReal (graphJacobianN f x))
  have hμ (j : ℕ) : μ (B j) =
      Measure.euclideanHausdorffMeasure k (graphMapN f '' B j) := by
    rw [show μ (B j) = ∫⁻ x in B j, ENNReal.ofReal (graphJacobianN f x) from
      withDensity_apply _ (hBmeas j)]
    exact (graph_image_measure_eq_lintegral_of_compact hU (hCc j) (hCU j) hf
      (hBmeas j) inter_subset_right).symm
  rw [show (∫⁻ y in A, ENNReal.ofReal (graphJacobianN f y)) = μ A from
    (withDensity_apply _ hA).symm]
  rw [← hBA, image_iUnion, (show Monotone (fun j => graphMapN f '' B j) from
    fun i j hij => image_mono (hBm hij)).measure_iUnion, hBm.measure_iUnion]
  exact iSup_congr fun j => (hμ j).symm

/-- Normalized Hausdorff area has the usual square-root graph density in every dimension. -/
theorem c1_graph_area {k : ℕ} {U A : Set (EuclideanSpace ℝ (Fin k))}
    (hU : IsOpen U) {f : EuclideanSpace ℝ (Fin k) → ℝ} (hf : ContDiffOn ℝ 1 f U)
    (hA : MeasurableSet A) (hAU : A ⊆ U) :
    Measure.euclideanHausdorffMeasure k (graphMapN f '' A) =
      ∫⁻ x in A, ENNReal.ofReal (Real.sqrt (1 + ‖gradient f x‖ ^ 2)) := by
  rw [c1_graph_image_measure_eq_lintegral hU hf hA hAU]
  apply setLIntegral_congr_fun hA
  intro x hx
  dsimp only
  rw [graphJacobianN_eq
    ((hf.differentiableOn (by norm_num) x (hAU hx)).differentiableAt (hU.mem_nhds (hAU hx)))]

/-- The graph Jacobian-weighted volume pushes forward to normalized Hausdorff measure. -/
theorem c1_graph_map_withDensity {k : ℕ} {U A : Set (EuclideanSpace ℝ (Fin k))}
    (hU : IsOpen U) {f : EuclideanSpace ℝ (Fin k) → ℝ} (hf : ContDiffOn ℝ 1 f U)
    (hA : MeasurableSet A) (hAU : A ⊆ U) :
    Measure.map (graphMapN f)
      ((volume.restrict A).withDensity (fun x => ENNReal.ofReal (graphJacobianN f x))) =
        (Measure.euclideanHausdorffMeasure k).restrict (graphMapN f '' A) := by
  classical
  let F := A.piecewise (graphMapN f) (fun _ => 0)
  have hFm : Measurable F :=
    ((continuousOn_graphMapN hf.continuousOn).mono hAU).measurable_piecewise
      continuousOn_const hA
  have hFeq (x) (hx : x ∈ A) : F x = graphMapN f x := piecewise_eq_of_mem A _ _ hx
  have hae : F =ᵐ[(volume.restrict A).withDensity
      (fun x => ENNReal.ofReal (graphJacobianN f x))] graphMapN f :=
    (withDensity_absolutelyContinuous _ _).ae_eq
      (by filter_upwards [ae_restrict_mem hA] with x hx; exact hFeq x hx)
  rw [← Measure.map_congr hae]
  ext T hT
  rw [Measure.map_apply hFm hT, withDensity_apply _ (hFm hT),
    Measure.restrict_apply hT, Measure.restrict_restrict (hFm hT)]
  rw [← c1_graph_image_measure_eq_lintegral hU hf ((hFm hT).inter hA)
    (inter_subset_right.trans hAU)]
  congr 1
  ext y
  constructor
  · rintro ⟨x, ⟨hxT, hxA⟩, rfl⟩
    exact ⟨by simpa only [mem_preimage, hFeq x hxA] using hxT, ⟨x, hxA, rfl⟩⟩
  · rintro ⟨hyT, x, hxA, rfl⟩
    exact ⟨x, ⟨by simpa only [mem_preimage, hFeq x hxA] using hyT, hxA⟩, rfl⟩

/-- Weighted graph area for every nonnegative Borel weight on the ambient space. -/
theorem c1_graph_lintegral {k : ℕ} {U A : Set (EuclideanSpace ℝ (Fin k))}
    (hU : IsOpen U) {f : EuclideanSpace ℝ (Fin k) → ℝ} (hf : ContDiffOn ℝ 1 f U)
    (hA : MeasurableSet A) (hAU : A ⊆ U)
    {q : EuclideanSpace ℝ (Fin (k + 1)) → ℝ≥0∞} (hq : Measurable q) :
    (∫⁻ y in graphMapN f '' A, q y ∂Measure.euclideanHausdorffMeasure k) =
      ∫⁻ x in A, q (graphMapN f x) * ENNReal.ofReal
        (Real.sqrt (1 + ‖gradient f x‖ ^ 2)) := by
  have hm : AEMeasurable (graphMapN f) (volume.restrict A) :=
    ((continuousOn_graphMapN hf.continuousOn).mono hAU).aemeasurable hA
  rw [← c1_graph_map_withDensity hU hf hA hAU,
    lintegral_map' hq.aemeasurable (hm.mono_ac (withDensity_absolutelyContinuous _ _))]
  have hw := lintegral_withDensity_eq_lintegral_mul₀
    (measurable_graphJacobianN f).ennreal_ofReal.aemeasurable (hq.comp_aemeasurable hm)
  simp only [Function.comp_apply, Pi.mul_apply] at hw
  rw [hw]
  apply setLIntegral_congr_fun hA
  intro x hx
  dsimp only
  rw [graphJacobianN_eq
    ((hf.differentiableOn (by norm_num) x (hAU hx)).differentiableAt (hU.mem_nhds (hAU hx))),
    mul_comm]

/-- Borel graph patches are Borel in the ambient Euclidean space. -/
lemma c1_graph_image_measurableSet {k : ℕ} {U A : Set (EuclideanSpace ℝ (Fin k))}
    {f : EuclideanSpace ℝ (Fin k) → ℝ} (hf : ContDiffOn ℝ 1 f U)
    (hA : MeasurableSet A) (hAU : A ⊆ U) : MeasurableSet (graphMapN f '' A) :=
  hA.image_of_continuousOn_injOn ((continuousOn_graphMapN hf.continuousOn).mono hAU)
    (graphMapN_injective f).injOn

/-- Pushforward form with the explicit square-root density. -/
theorem c1_graph_map_withDensity_sqrt {k : ℕ} {U A : Set (EuclideanSpace ℝ (Fin k))}
    (hU : IsOpen U) {f : EuclideanSpace ℝ (Fin k) → ℝ} (hf : ContDiffOn ℝ 1 f U)
    (hA : MeasurableSet A) (hAU : A ⊆ U) :
    Measure.map (graphMapN f) ((volume.restrict A).withDensity
      (fun x => ENNReal.ofReal (Real.sqrt (1 + ‖gradient f x‖ ^ 2)))) =
        (Measure.euclideanHausdorffMeasure k).restrict (graphMapN f '' A) := by
  rw [← c1_graph_map_withDensity hU hf hA hAU]
  congr 1
  apply withDensity_congr_ae
  filter_upwards [ae_restrict_mem hA] with x hx
  rw [graphJacobianN_eq
    ((hf.differentiableOn (by norm_num) x (hAU hx)).differentiableAt (hU.mem_nhds (hAU hx)))]

end LiquidDrop

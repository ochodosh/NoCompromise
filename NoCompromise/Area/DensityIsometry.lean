module

public import NoCompromise.Area.Graph
public import NoCompromise.DeGiorgi.LipschitzPieces

@[expose] public section

/-!
# Transport of graph-piece densities under orthogonal changes of frame

Normalized Hausdorff area, restricted graph measures, and centered ball densities
are preserved by orthogonal maps. The general last-coordinate graph convention
agrees with the planar graph convention used in the area formula.
-/

noncomputable section
open MeasureTheory Set Filter Metric
open scoped Topology ENNReal NNReal
namespace LiquidDrop

lemma graphMapN_two_eq_graphMap (f : EuclideanSpace ℝ (Fin 2) → ℝ) :
    graphMapN f = graphMap f := by
  funext p
  ext i
  fin_cases i <;> simp [graphMapN, graphMap, graphBaseN, graphBaseEmbedding]

lemma hausdorffMeasure2_restrict_isometry_image
    (e : AmbientSpace ≃ₗᵢ[ℝ] AmbientSpace) (S : Set AmbientSpace) :
    (hausdorffMeasure2 3).restrict (e '' S) =
      Measure.map e ((hausdorffMeasure2 3).restrict S) := by
  ext B hB
  rw [Measure.restrict_apply hB, Measure.map_apply e.continuous.measurable hB,
    Measure.restrict_apply (hB.preimage e.continuous.measurable)]
  have heq : B ∩ e '' S = e '' (e ⁻¹' B ∩ S) := (Set.image_preimage_inter _ _ _).symm
  rw [heq]
  exact e.isometry.euclideanHausdorffMeasure_image _

lemma hausdorffMeasure2_real_ball_inter_isometry_image
    (e : AmbientSpace ≃ₗᵢ[ℝ] AmbientSpace) (S : Set AmbientSpace) (x : AmbientSpace) (r : ℝ) :
    (hausdorffMeasure2 3).real (ball (e x) r ∩ e '' S) =
      (hausdorffMeasure2 3).real (ball x r ∩ S) := by
  have heq : ball (e x) r ∩ e '' S = e '' (ball x r ∩ S) := by
    rw [Set.image_inter e.injective, e.image_ball]
  rw [heq, Measure.real, Measure.real]
  exact congrArg ENNReal.toReal (e.isometry.euclideanHausdorffMeasure_image _)

/-- A quadratic area density statement on a set transports to its orthogonal image. -/
theorem ae_area_density_isometry_image
    (e : AmbientSpace ≃ₗᵢ[ℝ] AmbientSpace) (S : Set AmbientSpace) {d : ℝ}
    (hS : ∀ᵐ x ∂(hausdorffMeasure2 3).restrict S,
      Tendsto (fun r : ℝ => (hausdorffMeasure2 3).real (ball x r ∩ S) /
        (Real.pi * r ^ 2)) (𝓝[>] 0) (𝓝 d)) :
    ∀ᵐ x ∂(hausdorffMeasure2 3).restrict (e '' S),
      Tendsto (fun r : ℝ => (hausdorffMeasure2 3).real (ball x r ∩ e '' S) /
        (Real.pi * r ^ 2)) (𝓝[>] 0) (𝓝 d) := by
  have he : MeasurableEmbedding (fun x : AmbientSpace => e x) :=
    e.toHomeomorph.measurableEmbedding
  rw [hausdorffMeasure2_restrict_isometry_image, he.ae_map_iff]
  simpa only [hausdorffMeasure2_real_ball_inter_isometry_image] using hS

/-- Every orthogonal image of a Lipschitz graph is closed. -/
lemma isClosed_rotated_graphMapN (e : AmbientSpace ≃ₗᵢ[ℝ] AmbientSpace)
    {f : EuclideanSpace ℝ (Fin 2) → ℝ} {K : ℝ≥0} (hf : LipschitzWith K f) :
    IsClosed (range (fun p => e (graphMapN f p))) := by
  rw [graphMapN_two_eq_graphMap]
  have heq : range (fun p => e (graphMap f p)) = e '' range (graphMap f) := by
    exact Set.range_comp e (graphMap f)
  rw [heq]
  exact e.toHomeomorph.isClosedMap _ (isClosedEmbedding_graphMap hf).isClosed_range

end LiquidDrop

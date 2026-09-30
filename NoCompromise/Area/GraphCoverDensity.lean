module

public import NoCompromise.Area.DensityIsometry
public import NoCompromise.Measure.DensityIdentification
public import NoCompromise.Area.GraphDensity

@[expose] public section

/-!
# Area density on countable Lipschitz graph covers

Borel pieces inherit unit area density from their graph parameters.
Differentiation of restrictions then gives unit density on the full locally
finite area measure carried by countably many rotated graphs.
-/

noncomputable section
open MeasureTheory Set Filter Metric
open scoped Topology ENNReal NNReal
namespace LiquidDrop

/-- A Borel subset of a rotated graph is the image of its parameter preimage. -/
lemma rotated_graph_piece_eq_image
    (e : AmbientSpace ≃ₗᵢ[ℝ] AmbientSpace)
    (f : EuclideanSpace ℝ (Fin 2) → ℝ) (S : Set AmbientSpace) :
    range (fun p => e (graphMapN f p)) ∩ S =
      e '' (graphMap f '' ((fun p => e (graphMap f p)) ⁻¹' S)) := by
  rw [graphMapN_two_eq_graphMap]
  ext y
  constructor
  · rintro ⟨⟨p, rfl⟩, hp⟩
    exact ⟨graphMap f p, ⟨p, hp, rfl⟩, rfl⟩
  · rintro ⟨_, ⟨p, hp, rfl⟩, rfl⟩
    exact ⟨⟨p, rfl⟩, hp⟩

/-- A locally finite area measure carried by countably many rotated Lipschitz
graphs has unit normalized quadratic density almost everywhere. -/
theorem ae_area_density_of_graph_cover
    (S : Set AmbientSpace) (hS : MeasurableSet S)
    [IsLocallyFiniteMeasure ((hausdorffMeasure2 3).restrict S)]
    (e : ℕ → AmbientSpace ≃ₗᵢ[ℝ] AmbientSpace)
    (f : ℕ → EuclideanSpace ℝ (Fin 2) → ℝ)
    (K : ℕ → ℝ≥0) (hf : ∀ j, LipschitzWith (K j) (f j))
    (hcover : (hausdorffMeasure2 3).restrict S
      (⋃ j, range (fun p => e j (graphMapN (f j) p)))ᶜ = 0) :
    ∀ᵐ x ∂(hausdorffMeasure2 3).restrict S,
      Tendsto (fun r : ℝ => ((hausdorffMeasure2 3).restrict S).real (ball x r) /
        (Real.pi * r ^ 2)) (𝓝[>] 0) (𝓝 1) := by
  let H (j : ℕ) := range (fun p => e j (graphMapN (f j) p))
  have hH (j : ℕ) : MeasurableSet (H j) := (isClosed_rotated_graphMapN (e j) (hf j)).measurableSet
  apply ae_tendsto_measureReal_ball_quotient_of_countable_cover
    ((hausdorffMeasure2 3).restrict S) H hH hcover (fun r => Real.pi * r ^ 2) (fun _ => 1)
  intro j
  let G := (fun p => e j (graphMap (f j) p)) ⁻¹' S
  have hG : MeasurableSet G := hS.preimage
    ((e j).continuous.comp (lipschitzWith_graphMap (hf j)).continuous).measurable
  have hd := ae_area_density_isometry_image (e j) (graphMap (f j) '' G)
    (ae_graph_piece_density (hf j) hG)
  have hset : H j ∩ S = e j '' (graphMap (f j) '' G) :=
    rotated_graph_piece_eq_image (e j) (f j) S
  rw [Measure.restrict_restrict (hH j), hset]
  simpa only [Measure.real, Measure.restrict_apply isOpen_ball.measurableSet] using hd

end LiquidDrop

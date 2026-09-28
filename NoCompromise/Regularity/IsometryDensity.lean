import NoCompromise.Regularity.IsometryMinimal
import NoCompromise.Regularity.DensitySimilarity

/-! # Exact canonical phase representatives in rigid coordinates -/

noncomputable section
open Set MeasureTheory Filter Metric
open scoped ENNReal Topology
namespace LiquidDrop

lemma densityRatio_preimage_affineIsometry (E : Set AmbientSpace)
    (a : AmbientSpace ≃ᵃⁱ[ℝ] AmbientSpace) (x : AmbientSpace) (r : ℝ) :
    densityRatio (a ⁻¹' E) x r = densityRatio E (a x) r := by
  have hball : a '' ball x r = ball (a x) r := a.toIsometryEquiv.image_ball x r
  have hv : volume (ball x r) = volume (ball (a x) r) := by
    rw [← hball, volume_image_affineIsometry]
  unfold densityRatio
  rw [← volume_image_affineIsometry a ((a ⁻¹' E) ∩ ball x r),
    image_inter a.injective, image_preimage_eq _ a.surjective, hball, hv]

lemma densityOne_preimage_affineIsometry (E : Set AmbientSpace)
    (a : AmbientSpace ≃ᵃⁱ[ℝ] AmbientSpace) :
    densityOne (a ⁻¹' E) = a ⁻¹' densityOne E := by
  ext x
  change Tendsto (densityRatio (a ⁻¹' E) x) (𝓝[>] (0 : ℝ)) (𝓝 1) ↔
    Tendsto (densityRatio E (a x)) (𝓝[>] (0 : ℝ)) (𝓝 1)
  rw [show densityRatio (a ⁻¹' E) x = densityRatio E (a x) from
    funext (densityRatio_preimage_affineIsometry E a x)]

lemma densityZero_preimage_affineIsometry (E : Set AmbientSpace)
    (a : AmbientSpace ≃ᵃⁱ[ℝ] AmbientSpace) :
    densityZero (a ⁻¹' E) = a ⁻¹' densityZero E := by
  ext x
  change Tendsto (densityRatio (a ⁻¹' E) x) (𝓝[>] (0 : ℝ)) (𝓝 0) ↔
    Tendsto (densityRatio E (a x)) (𝓝[>] (0 : ℝ)) (𝓝 0)
  rw [show densityRatio (a ⁻¹' E) x = densityRatio E (a x) from
    funext (densityRatio_preimage_affineIsometry E a x)]

lemma frontier_densityOne_preimage_affineIsometry (E : Set AmbientSpace)
    (a : AmbientSpace ≃ᵃⁱ[ℝ] AmbientSpace) :
    frontier (densityOne (a ⁻¹' E)) = a ⁻¹' frontier (densityOne E) := by
  rw [densityOne_preimage_affineIsometry]
  exact (a.toHomeomorph.preimage_frontier (densityOne E)).symm

end LiquidDrop

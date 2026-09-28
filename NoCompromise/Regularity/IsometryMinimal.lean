import NoCompromise.Regularity.OmegaMinimal
import NoCompromise.DeGiorgi.SmoothBoundary

/-! # Genuine quasiminimality under rigid changes of coordinates -/

noncomputable section
open Set MeasureTheory Filter Metric
open scoped ENNReal Topology symmDiff
namespace LiquidDrop

lemma HasLocallyFinitePerimeter.preimage_affineIsometry {n : ℕ}
    {E : Set (EuclideanSpace ℝ (Fin n))} (hE : HasLocallyFinitePerimeter E)
    (hmE : NullMeasurableSet E volume)
    (a : EuclideanSpace ℝ (Fin n) ≃ᵃⁱ[ℝ] EuclideanSpace ℝ (Fin n)) :
    HasLocallyFinitePerimeter (a ⁻¹' E) := by
  intro D hD hcD
  rw [perimeterIn_preimage_affineIsometry_eq hD
    ((measure_mono subset_closure).trans_lt hcD.measure_lt_top).ne a hmE]
  apply hE (a '' D) (a.toHomeomorph.isOpenMap D hD)
  have hcl : a '' closure D = closure (a '' D) := a.toHomeomorph.image_closure D
  rw [← hcl]
  exact hcD.image a.continuous

lemma nullMeasurableSet_image_affineIsometry {n : ℕ}
    {E : Set (EuclideanSpace ℝ (Fin n))} (hmE : NullMeasurableSet E volume)
    (a : EuclideanSpace ℝ (Fin n) ≃ᵃⁱ[ℝ] EuclideanSpace ℝ (Fin n)) :
    NullMeasurableSet (a '' E) volume := by
  have he : a '' E = a.symm ⁻¹' E := by
    ext x
    constructor
    · rintro ⟨y, hy, rfl⟩
      simpa only [mem_preimage, a.symm_apply_apply] using hy
    · intro hx
      exact ⟨a.symm x, hx, a.apply_symm_apply x⟩
  rw [he]
  exact hmE.preimage (measurePreserving_affineIsometry a.symm).quasiMeasurePreserving

lemma HasLocallyFinitePerimeter.image_affineIsometry {n : ℕ}
    {E : Set (EuclideanSpace ℝ (Fin n))} (hE : HasLocallyFinitePerimeter E)
    (hmE : NullMeasurableSet E volume)
    (a : EuclideanSpace ℝ (Fin n) ≃ᵃⁱ[ℝ] EuclideanSpace ℝ (Fin n)) :
    HasLocallyFinitePerimeter (a '' E) := by
  have he : a '' E = a.symm ⁻¹' E := by
    ext x
    constructor
    · rintro ⟨y, hy, rfl⟩
      simpa only [mem_preimage, a.symm_apply_apply] using hy
    · intro hx
      exact ⟨a.symm x, hx, a.apply_symm_apply x⟩
  rw [he]
  exact hE.preimage_affineIsometry hmE a.symm

/-- Rigid transport preserves the exact coefficient and every admissible radius. -/
theorem IsOmegaMinimalAtScales.preimage_affineIsometry {n : ℕ}
    {E : Set (EuclideanSpace ℝ (Fin n))} {ω : ℝ} {s : ℝ≥0∞}
    (hE : IsOmegaMinimalAtScales E ω s)
    (a : EuclideanSpace ℝ (Fin n) ≃ᵃⁱ[ℝ] EuclideanSpace ℝ (Fin n)) :
    IsOmegaMinimalAtScales (a ⁻¹' E) ω s := by
  refine ⟨hE.nonneg, hE.scale_pos,
    hE.nullMeasurable.preimage (measurePreserving_affineIsometry a).quasiMeasurePreserving,
    hE.locallyFinite.preimage_affineIsometry hE.nullMeasurable a, ?_⟩
  intro x r hr hrs F hmF hpF hc hs
  have hmG := nullMeasurableSet_image_affineIsometry hmF a
  have hpG := hpF.image_affineIsometry hmF a
  have heE : a '' (a ⁻¹' E) = E := image_preimage_eq _ a.surjective
  have hsd : (a '' F) ∆ E = a '' (F ∆ (a ⁻¹' E)) := by
    rw [image_symmDiff a.injective, heE]
  have hcl (S : Set (EuclideanSpace ℝ (Fin n))) :
      a '' closure S = closure (a '' S) := a.toHomeomorph.image_closure S
  have hball : a '' ball x r = ball (a x) r := a.toIsometryEquiv.image_ball x r
  have hcG : IsCompact (closure ((a '' F) ∆ E)) := by
    rw [hsd, ← hcl]
    exact hc.image a.continuous
  have hsG : closure ((a '' F) ∆ E) ⊆ ball (a x) r := by
    rw [hsd, ← hcl, ← hball]
    exact image_mono hs
  have hcomp := hE.comparison (a x) r hr hrs (a '' F) hmG hpG hcG hsG
  have heq (B : Set (EuclideanSpace ℝ (Fin n))) (hmB : NullMeasurableSet B volume) :
      perimeterIn (a ⁻¹' B) (ball x r) = perimeterIn B (ball (a x) r) := by
    rw [perimeterIn_preimage_affineIsometry_eq isOpen_ball
      isBounded_ball.measure_lt_top.ne a hmB, hball]
  have hF : a ⁻¹' (a '' F) = F := preimage_image_eq _ a.injective
  have hv : volume (E ∆ (a '' F)) = volume ((a ⁻¹' E) ∆ F) := by
    have he : a '' ((a ⁻¹' E) ∆ F) = E ∆ (a '' F) := by
      rw [image_symmDiff a.injective, heE]
    rw [← he, volume_image_affineIsometry]
  rw [← heq E hE.nullMeasurable, ← heq (a '' F) hmG, hF, hv] at hcomp
  exact hcomp

theorem IsOmegaMinimal.preimage_affineIsometry {n : ℕ}
    {E : Set (EuclideanSpace ℝ (Fin n))} {ω : ℝ} (hE : IsOmegaMinimal E ω)
    (a : EuclideanSpace ℝ (Fin n) ≃ᵃⁱ[ℝ] EuclideanSpace ℝ (Fin n)) :
    IsOmegaMinimal (a ⁻¹' E) ω := IsOmegaMinimalAtScales.preimage_affineIsometry hE a

end LiquidDrop

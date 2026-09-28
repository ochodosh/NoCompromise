import NoCompromise.BV.Density
import NoCompromise.Area.Linear
import Mathlib.Analysis.InnerProductSpace.Projection.Reflection

/-!
# Planar slicing in three dimensions

The coordinate split preserves ordinary volume, while its planar sections are
isometries and hence preserve normalized Hausdorff area. Tonelli proves the
coordinate identity; a reflection supplies every unit normal. Applying this to
the Borel density-one representative gives the blueprint's planar slicing
identity for every Lebesgue-measurable set, with infinite values allowed and
without a finite-perimeter hypothesis.
-/

noncomputable section
open MeasureTheory Set Metric Filter
open scoped ENNReal Topology
namespace LiquidDrop

/-- Split off the first Euclidean coordinate, preserving volume. -/
def slicingCoordinates : AmbientSpace ≃ᵐ (ℝ × EuclideanSpace ℝ (Fin 2)) :=
  (MeasurableEquiv.toLp 2 (Fin 3 → ℝ)).symm.trans
    ((MeasurableEquiv.piFinSuccAbove (fun _ : Fin 3 => ℝ) 0).trans
      (MeasurableEquiv.prodCongr (MeasurableEquiv.refl ℝ)
        (MeasurableEquiv.toLp 2 (Fin 2 → ℝ))))

lemma measurePreserving_slicingCoordinates : MeasurePreserving slicingCoordinates := by
  exact ((MeasurePreserving.id volume).prod (PiLp.volume_preserving_toLp (Fin 2))).comp
    ((volume_preserving_piFinSuccAbove (fun _ : Fin 3 => ℝ) 0).comp
      (PiLp.volume_preserving_ofLp (Fin 3)))

@[simp] lemma slicingCoordinates_fst (x : AmbientSpace) : (slicingCoordinates x).1 = x 0 := rfl

/-- The standard parametrization of a plane normal to the first coordinate axis. -/
def coordinatePlaneParam (t : ℝ) (p : EuclideanSpace ℝ (Fin 2)) : AmbientSpace :=
  slicingCoordinates.symm (t, p)

@[simp] lemma coordinatePlaneParam_zero (t : ℝ) (p : EuclideanSpace ℝ (Fin 2)) :
    coordinatePlaneParam t p 0 = t := rfl

@[simp] lemma coordinatePlaneParam_succ (t : ℝ) (p : EuclideanSpace ℝ (Fin 2)) (i : Fin 2) :
    coordinatePlaneParam t p i.succ = p i := by
  fin_cases i <;> rfl

lemma isometry_coordinatePlaneParam (t : ℝ) : Isometry (coordinatePlaneParam t) := by
  apply Isometry.of_dist_eq
  intro x y
  rw [dist_eq_norm, dist_eq_norm]
  apply (sq_eq_sq₀ (norm_nonneg _) (norm_nonneg _)).mp
  simp only [EuclideanSpace.real_norm_sq_eq, Fin.sum_univ_three, Fin.sum_univ_two,
    PiLp.sub_apply, coordinatePlaneParam_zero, sub_self,
    zero_pow (by norm_num : (2 : ℕ) ≠ 0), zero_add]
  rfl

lemma hausdorffMeasure2_coordinate_slice (A : Set AmbientSpace) (t : ℝ) :
    hausdorffMeasure2 3 (A ∩ {x | x 0 = t}) = volume (coordinatePlaneParam t ⁻¹' A) := by
  have heq : A ∩ {x | x 0 = t} = coordinatePlaneParam t '' (coordinatePlaneParam t ⁻¹' A) := by
    ext x
    constructor
    · intro hx
      refine ⟨(slicingCoordinates x).2, ?_, ?_⟩
      · change coordinatePlaneParam t (slicingCoordinates x).2 ∈ A
        have : coordinatePlaneParam t (slicingCoordinates x).2 = x := by
          unfold coordinatePlaneParam
          rw [← hx.2, ← slicingCoordinates_fst x, Prod.mk.eta, slicingCoordinates.symm_apply_apply]
        rw [this]
        exact hx.1
      · unfold coordinatePlaneParam
        rw [← hx.2, ← slicingCoordinates_fst x, Prod.mk.eta, slicingCoordinates.symm_apply_apply]
    · rintro ⟨p, hp, rfl⟩
      exact ⟨hp, coordinatePlaneParam_zero t p⟩
  rw [heq]
  exact ((isometry_coordinatePlaneParam t).euclideanHausdorffMeasure_image
    (coordinatePlaneParam t ⁻¹' A)).trans
    (congrArg (fun μ : Measure (EuclideanSpace ℝ (Fin 2)) =>
      μ (coordinatePlaneParam t ⁻¹' A)) hausdorffMeasure2_plane)

lemma coordinate_plane_slicing {A : Set AmbientSpace} (hA : MeasurableSet A) (a b : ℝ) :
    ∫⁻ t in Ioo a b, hausdorffMeasure2 3 (A ∩ {x | x 0 = t}) =
      volume (A ∩ {x | a < x 0 ∧ x 0 < b}) := by
  let S : Set (ℝ × EuclideanSpace ℝ (Fin 2)) :=
    slicingCoordinates.symm ⁻¹' A ∩ Prod.fst ⁻¹' Ioo a b
  have hS : MeasurableSet S := (hA.preimage slicingCoordinates.symm.measurable).inter
    (measurableSet_Ioo.preimage measurable_fst)
  have heq : slicingCoordinates ⁻¹' S = A ∩ {x | a < x 0 ∧ x 0 < b} := by
    ext x
    simp [S]
  rw [← heq, measurePreserving_slicingCoordinates.measure_preimage hS.nullMeasurableSet]
  change _ = (volume.prod volume) S
  rw [Measure.prod_apply hS, ← lintegral_indicator measurableSet_Ioo]
  apply lintegral_congr
  intro t
  by_cases ht : t ∈ Ioo a b
  · rw [Set.indicator_of_mem ht, hausdorffMeasure2_coordinate_slice]
    congr 1
    ext p
    simp [S, coordinatePlaneParam, ht]
  · rw [Set.indicator_of_notMem ht]
    have : Prod.mk t ⁻¹' S = ∅ := by
      ext p
      simp [S, ht]
    rw [this, measure_empty]

lemma measurable_coordinate_plane_sections {A : Set AmbientSpace} (hA : MeasurableSet A) :
    Measurable (fun t => hausdorffMeasure2 3 (A ∩ {x | x 0 = t})) := by
  simp_rw [hausdorffMeasure2_coordinate_slice]
  exact measurable_measure_prodMk_left (hA.preimage slicingCoordinates.symm.measurable)

/-- Reflection aligns a coordinate axis with any unit normal. -/
lemma exists_slicing_isometry {ν : AmbientSpace} (hν : ‖ν‖ = 1) :
    ∃ e : AmbientSpace ≃ₗᵢ[ℝ] AmbientSpace,
      ∀ x, inner ℝ (e x) ν = x 0 := by
  let u : AmbientSpace := EuclideanSpace.single 0 1
  let e := (ℝ ∙ (u - ν))ᗮ.reflection
  have he : e u = ν := Submodule.reflection_sub (by simpa [u] using hν.symm)
  refine ⟨e, fun x => ?_⟩
  rw [← he, e.inner_map_map]
  simp [u, EuclideanSpace.inner_single_right]

lemma hausdorffMeasure2_plane_slice_isometry {ν : AmbientSpace}
    (e : AmbientSpace ≃ₗᵢ[ℝ] AmbientSpace) (he : ∀ x, inner ℝ (e x) ν = x 0)
    (A : Set AmbientSpace) (t : ℝ) :
    hausdorffMeasure2 3 (A ∩ {x | inner ℝ x ν = t}) =
      hausdorffMeasure2 3 ((e ⁻¹' A) ∩ {x | x 0 = t}) := by
  have hset : A ∩ {x | inner ℝ x ν = t} = e '' ((e ⁻¹' A) ∩ {x | x 0 = t}) := by
    apply e.surjective.preimage_injective
    rw [preimage_image_eq _ e.injective]
    ext x
    simp [he]
  rw [hset]
  exact e.isometry.euclideanHausdorffMeasure_image _

/-- Planar slicing of a Borel set, with extended nonnegative values. -/
theorem planar_slicing_measurable {A : Set AmbientSpace} (hA : MeasurableSet A)
    {ν : AmbientSpace} (hν : ‖ν‖ = 1) (a b : ℝ) :
    ∫⁻ t in Ioo a b, hausdorffMeasure2 3 (A ∩ {x | inner ℝ x ν = t}) =
      volume (A ∩ {x | a < inner ℝ x ν ∧ inner ℝ x ν < b}) := by
  obtain ⟨e, he⟩ := exists_slicing_isometry hν
  simp_rw [hausdorffMeasure2_plane_slice_isometry e he]
  rw [coordinate_plane_slicing (hA.preimage e.continuous.measurable)]
  have hset : (e ⁻¹' A) ∩ {x | a < x 0 ∧ x 0 < b} =
      e ⁻¹' (A ∩ {x | a < inner ℝ x ν ∧ inner ℝ x ν < b}) := by
    ext x
    simp [he]
  rw [hset]
  apply e.measurePreserving.measure_preimage
  exact (hA.inter (measurableSet_Ioo.preimage (by fun_prop))).nullMeasurableSet

lemma measurable_plane_sections {A : Set AmbientSpace} (hA : MeasurableSet A)
    {ν : AmbientSpace} (hν : ‖ν‖ = 1) :
    Measurable (fun t => hausdorffMeasure2 3 (A ∩ {x | inner ℝ x ν = t})) := by
  obtain ⟨e, he⟩ := exists_slicing_isometry hν
  simp_rw [hausdorffMeasure2_plane_slice_isometry e he]
  exact measurable_coordinate_plane_sections (hA.preimage e.continuous.measurable)

/-- Planar slicing uses the Borel density-one representative on the planes and
ordinary volume of the original Lebesgue-measurable set in the slab. -/
theorem planar_slicing {E : Set AmbientSpace} (hE : NullMeasurableSet E volume)
    {ν : AmbientSpace} (hν : ‖ν‖ = 1) (a b : ℝ) :
    ∫⁻ t in Ioo a b, hausdorffMeasure2 3 (densityOne E ∩ {x | inner ℝ x ν = t}) =
      volume (E ∩ {x | a < inner ℝ x ν ∧ inner ℝ x ν < b}) := by
  rw [planar_slicing_measurable (measurableSet_densityOne hE) hν]
  exact measure_congr ((densityOne_ae_eq (by norm_num : 0 < 3) hE).inter EventuallyEq.rfl)

end LiquidDrop

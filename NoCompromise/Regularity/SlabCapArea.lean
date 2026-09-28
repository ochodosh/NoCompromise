import NoCompromise.Regularity.SlabCap
import NoCompromise.DeGiorgi.HalfspacePairing

/-! # Cap area and genuine phase points on the caps -/

noncomputable section
open Set MeasureTheory Metric
open scoped ENNReal
namespace LiquidDrop

lemma isometry_graphAppendN (n : ℕ) (s : ℝ) :
    Isometry (fun p : EuclideanSpace ℝ (Fin n) => graphAppendN p s) := by
  apply Isometry.of_dist_eq
  intro x y
  simpa only [graphAppendN, dist_eq_norm, add_sub_add_right_eq_sub] using
    (isometry_graphBaseN n).dist_eq x y

lemma hausdorffMeasure2_cylindricalCap (r s : ℝ) :
    hausdorffMeasure2 3 (cylindricalCap r s) = volume (ball (0 : EuclideanSpace ℝ (Fin 2)) r) :=
  ((isometry_graphAppendN 2 s).euclideanHausdorffMeasure_image _).trans
    (congrArg (fun μ : Measure (EuclideanSpace ℝ (Fin 2)) => μ (ball 0 r))
      hausdorffMeasure2_plane)

lemma cylindricalCap_pos {r : ℝ} (hr : 0 < r) (s : ℝ) :
    0 < hausdorffMeasure2 3 (cylindricalCap r s) := by
  rw [hausdorffMeasure2_cylindricalCap]
  exact measure_ball_pos volume 0 hr

lemma exists_cap_mem_of_ae_phase {r s : ℝ} (hr : 0 < r) {F : Set AmbientSpace}
    (hF : hausdorffMeasure2 3 (cylindricalCap r s \ F) = 0) :
    ∃ p : EuclideanSpace ℝ (Fin 2), ‖p‖ < r ∧ graphAppendN p s ∈ F := by
  by_contra hno
  push Not at hno
  have he : cylindricalCap r s \ F = cylindricalCap r s := by
    apply sdiff_eq_left.mpr
    apply disjoint_left.mpr
    rintro x ⟨p, hp, rfl⟩ hx
    exact hno p (by simpa only [mem_ball, dist_zero_right] using hp) hx
  rw [he] at hF
  exact (cylindricalCap_pos hr s).ne' hF

lemma IsSlabCapConfiguration.exists_cap_phase_points
    {E : Set AmbientSpace} {hE : HasLocallyFinitePerimeter E}
    {hmE : NullMeasurableSet E volume} {r c η : ℝ}
    (h : IsSlabCapConfiguration E hE hmE r c η) :
    (∃ p : EuclideanSpace ℝ (Fin 2), ‖p‖ < r ∧ graphAppendN p (-r) ∈ densityOne E) ∧
      ∃ p : EuclideanSpace ℝ (Fin 2), ‖p‖ < r ∧ graphAppendN p r ∈ densityZero E :=
  ⟨exists_cap_mem_of_ae_phase h.1.1 h.2.1, exists_cap_mem_of_ae_phase h.1.1 h.2.2⟩

end LiquidDrop

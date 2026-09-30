module

public import Mathlib.MeasureTheory.Integral.Bochner.Set
public import Mathlib.Analysis.InnerProductSpace.PiL2
public import Mathlib.Analysis.Normed.Lp.MeasurableSpace

@[expose] public section

/-!
# Finite measurable partitions subordinate to small neighborhoods

Compactness gives finitely many small closed balls; successive differences
produce disjoint Borel parts with the same union and explicit diameter bounds.
-/

noncomputable section
open MeasureTheory Set Metric Function
namespace LiquidDrop
set_option maxSynthPendingDepth 8

/-- A Borel subset of a compact Euclidean set has a finite Borel partition into
small-diameter sets, with a center in the compact carrier for each part. -/
theorem exists_finite_measurable_partition_of_compact_subset {n : ℕ}
    {K A : Set (EuclideanSpace ℝ (Fin n))} (hK : IsCompact K)
    (hA : MeasurableSet A) (hAK : A ⊆ K) {r : ℝ} (hr : 0 < r) :
    ∃ (k : ℕ) (B : Fin k → Set (EuclideanSpace ℝ (Fin n))) (c : Fin k → K),
      (∀ i, MeasurableSet (B i)) ∧ Pairwise (Disjoint on B) ∧ (⋃ i, B i) = A ∧
      (∀ i, B i ⊆ A) ∧ (∀ i, ∀ x ∈ B i, ‖x - (c i : EuclideanSpace ℝ (Fin n))‖ ≤ r) ∧
      (∀ i, ∀ x ∈ B i, ∀ y ∈ B i, ‖x - y‖ ≤ r) := by
  classical
  obtain ⟨t, ht⟩ := hK.elim_finite_subcover
    (fun c : K => ball (c : EuclideanSpace ℝ (Fin n)) (r / 2))
    (fun _ => isOpen_ball) (by
      intro x hx
      exact mem_iUnion.mpr ⟨⟨x, hx⟩, mem_ball_self (by positivity)⟩)
  let k := Fintype.card ↥t
  let c (i : Fin k) : K := ((Fintype.equivFin ↥t).symm i).val
  let V (i : Fin k) := closedBall (c i : EuclideanSpace ℝ (Fin n)) (r / 2)
  let B (i : Fin k) := A ∩ disjointed V i
  have hm (i : Fin k) : MeasurableSet (V i) := isClosed_closedBall.measurableSet
  have hmd (i : Fin k) : MeasurableSet (disjointed V i) := by
    rw [disjointed_eq_inter_compl]
    exact (hm i).inter (MeasurableSet.iInter fun j =>
      MeasurableSet.iInter fun _ => (hm j).compl)
  have hAV : A ⊆ ⋃ i, V i := by
    intro x hx
    obtain ⟨z, hz, hxz⟩ := mem_iUnion₂.mp (ht (hAK hx))
    refine mem_iUnion.mpr ⟨(Fintype.equivFin ↥t) ⟨z, hz⟩, ?_⟩
    simpa only [V, c, Equiv.symm_apply_apply] using (ball_subset_closedBall hxz)
  have hb (i : Fin k) : B i ⊆ V i := inter_subset_right.trans (disjointed_subset V i)
  refine ⟨k, B, c, fun i => hA.inter (hmd i),
    (disjoint_disjointed V).mono (fun _ _ h => h.mono inter_subset_right inter_subset_right),
    ?_, fun _ => inter_subset_left, ?_, ?_⟩
  · change (⋃ i, A ∩ disjointed V i) = A
    rw [← inter_iUnion, iUnion_disjointed, inter_eq_left.mpr hAV]
  · intro i x hx
    have h := mem_closedBall.mp (hb i hx)
    rw [dist_eq_norm] at h
    linarith
  · intro i x hx y hy
    have h := dist_triangle x (c i) y
    have hx' := mem_closedBall.mp (hb i hx)
    have hy' := mem_closedBall.mp (hb i hy)
    rw [dist_comm (c i : EuclideanSpace ℝ (Fin n)) y] at h
    simp only [dist_eq_norm] at h hx' hy'
    linarith

end LiquidDrop

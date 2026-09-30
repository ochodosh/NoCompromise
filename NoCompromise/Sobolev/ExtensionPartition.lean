module

public import NoCompromise.BV.StrictApprox
public import Mathlib.Geometry.Manifold.PartitionOfUnity

@[expose] public section

/-!
# Finite smooth partitions for BV extension

A finite bounded open cover of a compact Euclidean set admits a smooth partition
with compact supports subordinate to the cover and uniform bounds on each gradient.
The cover may be indexed by a finite subtype, as in a finite boundary-chart cover.
-/

open Set Metric InnerProductSpace
open scoped Topology Gradient Manifold

namespace LiquidDrop

set_option maxSynthPendingDepth 8

/-- A smooth compactly supported scalar function has a finite nonnegative uniform
bound on its Hilbert gradient. -/
lemma exists_nonneg_bound_gradient_of_contDiff {n : ℕ}
    {ζ : EuclideanSpace ℝ (Fin n) → ℝ} (hζ : ContDiff ℝ 1 ζ)
    (hcζ : HasCompactSupport ζ) :
    ∃ B : ℝ, 0 ≤ B ∧ ∀ x, ‖gradient ζ x‖ ≤ B := by
  have hcg : HasCompactSupport (gradient ζ) :=
    hcζ.of_isClosed_subset (isClosed_tsupport _) (tsupport_gradient_subset ζ)
  obtain ⟨B, hB⟩ := hcg.exists_bound_of_continuous (continuous_gradient_of_contDiff hζ)
  exact ⟨max B 0, le_max_right _ _, fun x => (hB x).trans (le_max_left _ _)⟩

/-- Finite smooth partition of unity on a compact set, with compact supports inside the
prescribed bounded open cover and a separate finite gradient bound for each piece. -/
theorem exists_finite_smooth_partition_of_bounded_open_cover {n : ℕ} {ι : Type*}
    [Fintype ι] {K : Set (EuclideanSpace ℝ (Fin n))} (hK : IsCompact K)
    (U : ι → Set (EuclideanSpace ℝ (Fin n))) (hU : ∀ i, IsOpen (U i))
    (hbU : ∀ i, Bornology.IsBounded (U i)) (hcover : K ⊆ ⋃ i, U i) :
    ∃ ζ : ι → EuclideanSpace ℝ (Fin n) → ℝ, ∃ B : ι → ℝ,
      (∀ i, ContDiff ℝ (⊤ : ℕ∞) (ζ i) ∧ HasCompactSupport (ζ i) ∧
        tsupport (ζ i) ⊆ U i ∧ (∀ x, 0 ≤ ζ i x ∧ ζ i x ≤ 1) ∧
        0 ≤ B i ∧ ∀ x, ‖gradient (ζ i) x‖ ≤ B i) ∧
      (∀ x ∈ K, ∑ i, ζ i x = 1) ∧ (∀ x, ∑ i, ζ i x ≤ 1) := by
  classical
  obtain ⟨ρ, hρ⟩ := SmoothPartitionOfUnity.exists_isSubordinate
    (I := 𝓘(ℝ, EuclideanSpace ℝ (Fin n))) hK.isClosed U hU hcover
  have hc (i : ι) : HasCompactSupport (ρ i) :=
    isCompact_of_isClosed_isBounded (isClosed_tsupport _) ((hbU i).subset (hρ i))
  have hd (i : ι) : ContDiff ℝ (⊤ : ℕ∞) (ρ i) := (ρ i).contMDiff.contDiff
  choose B hB hbound using fun i =>
    exists_nonneg_bound_gradient_of_contDiff ((hd i).of_le (by simp)) (hc i)
  refine ⟨fun i => ρ i, B, fun i => ⟨hd i, hc i, hρ i,
    fun x => ⟨ρ.nonneg i x, ρ.le_one i x⟩, hB i, hbound i⟩, ?_, ?_⟩
  · intro x hx
    simpa only [finsum_eq_sum_of_fintype] using ρ.sum_eq_one hx
  · intro x
    simpa only [finsum_eq_sum_of_fintype] using ρ.sum_le_one x

end LiquidDrop

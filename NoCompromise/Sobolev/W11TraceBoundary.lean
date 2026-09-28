import NoCompromise.Sobolev.W11TraceChart
import NoCompromise.Sobolev.W11Extension
import NoCompromise.Sobolev.H1TraceBoundaryGeometry

/-!
# Boundary L¹ restriction on a bounded Lipschitz domain

A finite boundary-plane cover transfers the chart estimates to normalized
Hausdorff measure. A continuity-preserving W¹,¹ extension gives a bound using
only the function and gradient norms inside the original domain.
-/

noncomputable section
open MeasureTheory Set Filter
open scoped ENNReal NNReal Topology
namespace LiquidDrop
set_option maxSynthPendingDepth 8

lemma memLp_one_of_finite_measure_cover {n : ℕ} {ι : Type*} [Fintype ι]
    {μ : Measure (EuclideanSpace ℝ (Fin n))}
    (ν : ι → Measure (EuclideanSpace ℝ (Fin n)))
    (hle : μ ≤ ∑ i, ν i) {f : EuclideanSpace ℝ (Fin n) → ℝ}
    (hf : ∀ i, MemLp f 1 (ν i)) :
    MemLp f 1 μ ∧ lpNorm f 1 μ ≤ ∑ i, lpNorm f 1 (ν i) := by
  have hi (i) := memLp_one_iff_integrable.mp (hf i)
  have hisum : Integrable f (∑ i, ν i) :=
    integrable_finsetSum_measure.mpr (fun i _ => hi i)
  have hmem := memLp_one_iff_integrable.mpr (hisum.mono_measure hle)
  refine ⟨hmem, ?_⟩
  rw [lpNorm_one_eq_integral_norm hmem.aestronglyMeasurable]
  calc
    _ ≤ ∫ x, ‖f x‖ ∂(∑ i, ν i) :=
      integral_mono_measure hle (Eventually.of_forall fun _ => norm_nonneg _) hisum.norm
    _ = ∑ i, ∫ x, ‖f x‖ ∂ν i := integral_finsetSum_measure (fun i _ => (hi i).norm)
    _ = _ := Finset.sum_congr rfl fun i _ => (lpNorm_one_eq_integral_norm (hf i).aestronglyMeasurable).symm

theorem exists_global_w11_boundary_restriction_bound {k : ℕ}
    {D : Set (EuclideanSpace ℝ (Fin (k + 1)))} (hD : IsOpen D)
    (hbD : Bornology.IsBounded D) (hL : HasLipschitzBoundary D) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ f G, HasW11GradientOn f G univ → Continuous f →
      MemLp f 1 ((Measure.euclideanHausdorffMeasure k).restrict (frontier D)) ∧
        lpNorm f 1 ((Measure.euclideanHausdorffMeasure k).restrict (frontier D)) ≤
          C * (lpNorm f 1 volume + lpNorm G 1 volume) := by
  classical
  obtain ⟨s, hs⟩ := exists_finite_boundary_plane_cover hD hbD hL
  let S (i : ↥s) := range (fun x => i.val.val.boundaryPlaneChart (graphAppendN x 0))
  let ν (i : ↥s) := (Measure.euclideanHausdorffMeasure k).restrict (S i)
  let A (i : ↥s) :=
    (((1 + i.val.val.lip : ℝ≥0) : ℝ) ^ k) *
      (max 1 ((1 + i.val.val.lip : ℝ≥0) : ℝ) *
        ((1 + i.val.val.lip : ℝ≥0) : ℝ) ^ (k + 1))
  have hA (i : ↥s) : 0 ≤ A i := by dsimp [A]; positivity
  refine ⟨∑ i : ↥s, A i, Finset.sum_nonneg (fun i _ => hA i), fun f G hf hc => ?_⟩
  have hp (i : ↥s) := memLp_chart_surface_of_continuous_w11 i.val.val.boundaryPlaneChart
    i.val.val.lipschitz_boundaryPlaneChart i.val.val.lipschitz_boundaryPlaneChart_symm hf hc
  have hcover : frontier D ⊆ ⋃ i : ↥s, S i := by
    simpa only [S, iUnion_subtype] using hs
  have hle : (Measure.euclideanHausdorffMeasure k).restrict (frontier D) ≤ ∑ i : ↥s, ν i :=
    ((Measure.restrict_mono_set _ hcover).trans Measure.restrict_iUnion_le).trans_eq
      (Measure.sum_fintype ν)
  obtain ⟨hm, hb⟩ := memLp_one_of_finite_measure_cover ν hle (fun i => (hp i).1)
  refine ⟨hm, hb.trans ?_⟩
  calc
    _ ≤ ∑ i : ↥s, A i * (lpNorm f 1 volume + lpNorm G 1 volume) := by
      apply Finset.sum_le_sum
      intro i _
      simpa only [ν, S, A, mul_assoc] using (hp i).2
    _ = _ := (Finset.sum_mul _ _ _).symm

/-- The actual boundary restriction estimate uses only the W¹,¹ norm on the domain.
The boundary measure is normalized Hausdorff measure, and no trace operator or
boundary estimate is among the hypotheses. -/
theorem exists_w11_boundary_restriction_bound {k : ℕ}
    {D : Set (EuclideanSpace ℝ (Fin (k + 1)))} (hD : IsOpen D)
    (hbD : Bornology.IsBounded D) (hL : HasLipschitzBoundary D) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ f G, HasW11GradientOn f G D → Continuous f →
      MemLp f 1 ((Measure.euclideanHausdorffMeasure k).restrict (frontier D)) ∧
        lpNorm f 1 ((Measure.euclideanHausdorffMeasure k).restrict (frontier D)) ≤
          C * (lpNorm f 1 (volume.restrict D) + lpNorm G 1 (volume.restrict D)) := by
  obtain ⟨Ce, hCe, hExt⟩ := exists_continuous_w11_extension_bound hD hbD hL
  obtain ⟨Cb, hCb, hTr⟩ := exists_global_w11_boundary_restriction_bound hD hbD hL
  refine ⟨Cb * Ce, mul_nonneg hCb hCe, fun f G hf hc => ?_⟩
  obtain ⟨F, H, hcF, hFH, heq, hb⟩ := hExt f G hf hc
  obtain ⟨hmF, hbF⟩ := hTr F H hFH hcF
  have heqAE : F =ᵐ[(Measure.euclideanHausdorffMeasure k).restrict (frontier D)] f :=
    ae_restrict_of_forall_mem isClosed_frontier.measurableSet
      (fun _ hx => heq (frontier_subset_closure hx))
  have hmf := hmF.ae_eq heqAE
  refine ⟨hmf, ?_⟩
  rw [← toReal_eLpNorm, ← eLpNorm_congr_ae heqAE, toReal_eLpNorm]
  calc
    _ ≤ Cb * (lpNorm F 1 volume + lpNorm H 1 volume) := hbF
    _ ≤ Cb * (Ce * (lpNorm f 1 (volume.restrict D) + lpNorm G 1 (volume.restrict D))) :=
      mul_le_mul_of_nonneg_left hb hCb
    _ = _ := (mul_assoc _ _ _).symm

end LiquidDrop

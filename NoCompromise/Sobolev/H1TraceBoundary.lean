module

public import NoCompromise.Sobolev.H1TraceBoundaryGeometry
public import NoCompromise.Sobolev.H1ContinuousExtension

@[expose] public section

/-!
# The boundary L² estimate on bounded Lipschitz domains

Finite chart-plane estimates give the Hausdorff L² bound for continuous global
H¹ functions. The continuity-preserving H¹ extension then makes this bound depend
only on the H¹ norm inside the domain, with equality on the actual boundary.
-/

noncomputable section
open MeasureTheory Set Filter InnerProductSpace
open scoped ENNReal NNReal Topology Gradient
namespace LiquidDrop
set_option maxSynthPendingDepth 8

/-- An upper measure cover transfers finitely many L² estimates to the covered measure. -/
lemma memLp_two_of_finite_measure_cover {n : ℕ} {ι : Type*} [Fintype ι]
    {μ : Measure (EuclideanSpace ℝ (Fin n))}
    (ν : ι → Measure (EuclideanSpace ℝ (Fin n)))
    (hle : μ ≤ ∑ i, ν i) {f : EuclideanSpace ℝ (Fin n) → ℝ}
    (hc : Continuous f) (hf : ∀ i, MemLp f 2 (ν i)) :
    MemLp f 2 μ ∧ lpNorm f 2 μ ^ 2 ≤ ∑ i, lpNorm f 2 (ν i) ^ 2 := by
  have hi (i) := (memLp_two_iff_integrable_sq_norm (hf i).aestronglyMeasurable).mp (hf i)
  have hisum : Integrable (fun x => ‖f x‖ ^ 2) (∑ i, ν i) :=
    integrable_finsetSum_measure.mpr (fun i _ => hi i)
  have hmem := (memLp_two_iff_integrable_sq_norm hc.aestronglyMeasurable).mpr
    (hisum.mono_measure hle)
  refine ⟨hmem, ?_⟩
  rw [lpNorm_two_sq_eq_integral_norm_sq hmem]
  calc
    _ ≤ ∫ x, ‖f x‖ ^ 2 ∂(∑ i, ν i) :=
      integral_mono_measure hle (Eventually.of_forall fun _ => sq_nonneg _) hisum
    _ = ∑ i, ∫ x, ‖f x‖ ^ 2 ∂ν i := integral_finsetSum_measure (fun i _ => hi i)
    _ = _ := Finset.sum_congr rfl fun i _ => (lpNorm_two_sq_eq_integral_norm_sq (hf i)).symm

/-- A finite chart cover bounds boundary restriction by the global H¹ norm. -/
theorem exists_global_h1_boundary_restriction_bound {k : ℕ}
    {D : Set (EuclideanSpace ℝ (Fin (k + 1)))} (hD : IsOpen D)
    (hbD : Bornology.IsBounded D) (hL : HasLipschitzBoundary D) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ f G, HasH1GradientOn f G univ → Continuous f →
      MemLp f 2 ((Measure.euclideanHausdorffMeasure k).restrict (frontier D)) ∧
        lpNorm f 2 ((Measure.euclideanHausdorffMeasure k).restrict (frontier D)) ≤
          C * (lpNorm f 2 volume + lpNorm G 2 volume) := by
  classical
  obtain ⟨s, hs⟩ := exists_finite_boundary_plane_cover hD hbD hL
  let S (i : ↥s) := range (fun x => i.val.val.boundaryPlaneChart (graphAppendN x 0))
  let ν (i : ↥s) := (Measure.euclideanHausdorffMeasure k).restrict (S i)
  let A (i : ↥s) :=
    (((1 + i.val.val.lip : ℝ≥0) : ℝ) ^ k) *
      (max 1 ((1 + i.val.val.lip : ℝ≥0) : ℝ) *
        ((1 + i.val.val.lip : ℝ≥0) : ℝ) ^ (((k + 1 : ℕ) : ℝ) / 2)) ^ 2
  have hA (i : ↥s) : 0 ≤ A i := by dsimp [A]; positivity
  have hsum : 0 ≤ ∑ i : ↥s, A i := Finset.sum_nonneg fun i _ => hA i
  refine ⟨Real.sqrt (∑ i : ↥s, A i), Real.sqrt_nonneg _, fun f G hf hc => ?_⟩
  have hp (i : ↥s) := memLp_chart_surface_of_continuous_h1 i.val.val.boundaryPlaneChart
    i.val.val.lipschitz_boundaryPlaneChart i.val.val.lipschitz_boundaryPlaneChart_symm hf hc
  have hcover : frontier D ⊆ ⋃ i : ↥s, S i := by
    simpa only [S, iUnion_subtype] using hs
  have hle : (Measure.euclideanHausdorffMeasure k).restrict (frontier D) ≤ ∑ i : ↥s, ν i :=
    ((Measure.restrict_mono_set _ hcover).trans Measure.restrict_iUnion_le).trans_eq
      (Measure.sum_fintype ν)
  obtain ⟨hm, hb⟩ := memLp_two_of_finite_measure_cover ν hle hc (fun i => (hp i).1)
  refine ⟨hm, ?_⟩
  apply le_of_sq_le_sq _ (mul_nonneg (Real.sqrt_nonneg _)
    (add_nonneg lpNorm_nonneg lpNorm_nonneg))
  rw [mul_pow, Real.sq_sqrt hsum]
  apply hb.trans
  calc
    _ ≤ ∑ i : ↥s, A i * (lpNorm f 2 volume + lpNorm G 2 volume) ^ 2 := by
      apply Finset.sum_le_sum
      intro i _
      simpa only [ν, S, A, mul_pow, mul_assoc] using (hp i).2
    _ = _ := (Finset.sum_mul _ _ _).symm

/-- The actual boundary restriction estimate uses only the H¹ norm on the domain.
The boundary measure is normalized Hausdorff measure, and no trace operator or
boundary estimate is among the hypotheses. -/
theorem exists_h1_boundary_restriction_bound {k : ℕ}
    {D : Set (EuclideanSpace ℝ (Fin (k + 1)))} (hD : IsOpen D)
    (hbD : Bornology.IsBounded D) (hL : HasLipschitzBoundary D) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ f G, HasH1GradientOn f G D → Continuous f →
      MemLp f 2 ((Measure.euclideanHausdorffMeasure k).restrict (frontier D)) ∧
        lpNorm f 2 ((Measure.euclideanHausdorffMeasure k).restrict (frontier D)) ≤
          C * (lpNorm f 2 (volume.restrict D) + lpNorm G 2 (volume.restrict D)) := by
  obtain ⟨Ce, hCe, hExt⟩ := exists_continuous_h1_extension_bound hD hbD hL
  obtain ⟨Cb, hCb, hTr⟩ := exists_global_h1_boundary_restriction_bound hD hbD hL
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
    _ ≤ Cb * (lpNorm F 2 volume + lpNorm H 2 volume) := hbF
    _ ≤ Cb * (Ce * (lpNorm f 2 (volume.restrict D) + lpNorm G 2 (volume.restrict D))) :=
      mul_le_mul_of_nonneg_left hb hCb
    _ = _ := (mul_assoc _ _ _).symm

end LiquidDrop

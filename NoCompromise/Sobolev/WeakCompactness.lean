module

public import NoCompromise.Sobolev.Hilbert
public import Mathlib.Analysis.Normed.Module.WeakDual

@[expose] public section

/-!
# Weak sequential compactness of H¹

Sequential Banach–Alaoglu and Hilbert-space Riesz representation give weak
subsequence extraction. Restricting to the closed span of the sequence avoids any
separability assumption on the ambient Hilbert space. No compact embedding or
Rellich theorem is used.
-/

noncomputable section

open MeasureTheory Filter Set InnerProductSpace TopologicalSpace
open scoped ENNReal Topology

namespace LiquidDrop

set_option maxSynthPendingDepth 8

/-- A bounded sequence in a separable real Hilbert space has a weakly convergent
subsequence, and the limit retains the norm bound. -/
theorem exists_subseq_weakly_tendsto_of_separable_hilbert_bound
    {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]
    [SeparableSpace E] (u : ℕ → E) {C : ℝ} (hu : ∀ j, ‖u j‖ ≤ C) :
    ∃ v : E, ∃ σ : ℕ → ℕ, StrictMono σ ∧ ‖v‖ ≤ C ∧
      ∀ ℓ : E →L[ℝ] ℝ, Tendsto (fun j => ℓ (u (σ j))) atTop (𝓝 (ℓ v)) := by
  let F (j : ℕ) : WeakDual ℝ E := StrongDual.toWeakDual (toDual ℝ E (u j))
  have hF (j : ℕ) : F j ∈ WeakDual.toStrongDual ⁻¹' Metric.closedBall (0 : E →L[ℝ] ℝ) C := by
    change dist (toDual ℝ E (u j)) 0 ≤ C
    simpa only [dist_zero_right, (toDual ℝ E).norm_map] using hu j
  obtain ⟨φ, hφ, σ, hσ, ht⟩ :=
    WeakDual.isSeqCompact_closedBall ℝ E (0 : E →L[ℝ] ℝ) C hF
  let v : E := (toDual ℝ E).symm (WeakDual.toStrongDual φ)
  refine ⟨v, σ, hσ, ?_, ?_⟩
  · change ‖(toDual ℝ E).symm (WeakDual.toStrongDual φ)‖ ≤ C
    rw [(toDual ℝ E).symm.norm_map]
    simpa only [mem_preimage, Metric.mem_closedBall, dist_zero_right] using hφ
  · intro ℓ
    have h := (WeakDual.eval_continuous ((toDual ℝ E).symm ℓ)).continuousAt.tendsto.comp ht
    have hseq (j : ℕ) : F (σ j) ((toDual ℝ E).symm ℓ) = ℓ (u (σ j)) := by
      change inner ℝ (u (σ j)) ((toDual ℝ E).symm ℓ) = _
      rw [real_inner_comm, toDual_symm_apply]
    have hlim : φ ((toDual ℝ E).symm ℓ) = ℓ v := by
      change (WeakDual.toStrongDual φ) ((toDual ℝ E).symm ℓ) = _
      rw [← toDual_symm_apply, real_inner_comm, toDual_symm_apply]
    simpa only [Function.comp_def, hseq, hlim] using h

/-- Every bounded sequence in a real Hilbert space has a weakly convergent
subsequence. Separability is needed only for the closed span of that sequence. -/
theorem exists_subseq_weakly_tendsto_of_hilbert_bound
    {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]
    (u : ℕ → E) {C : ℝ} (hu : ∀ j, ‖u j‖ ≤ C) :
    ∃ v : E, ∃ σ : ℕ → ℕ, StrictMono σ ∧ ‖v‖ ≤ C ∧
      ∀ ℓ : E →L[ℝ] ℝ, Tendsto (fun j => ℓ (u (σ j))) atTop (𝓝 (ℓ v)) := by
  let V : Submodule ℝ E := (Submodule.span ℝ (range u)).topologicalClosure
  have hsep : IsSeparable (V : Set E) := (countable_range u).isSeparable.span.closure
  let : SeparableSpace V := hsep.separableSpace
  let w (j : ℕ) : V := ⟨u j, Submodule.le_topologicalClosure _
    (Submodule.subset_span (mem_range_self j))⟩
  obtain ⟨v, σ, hσ, hv, ht⟩ :=
    exists_subseq_weakly_tendsto_of_separable_hilbert_bound w hu
  refine ⟨v.val, σ, hσ, hv, fun ℓ => ?_⟩
  exact ht (ℓ.comp V.subtypeL)

/-- A uniformly bounded sequence of H¹ classes has a weakly convergent subsequence
in H¹ itself, with the same norm bound on the limit. -/
theorem exists_subseq_weakly_tendsto_h1 {n : ℕ}
    {U : Set (EuclideanSpace ℝ (Fin n))} (u : ℕ → H1Space U)
    {C : ℝ} (hu : ∀ j, ‖u j‖ ≤ C) :
    ∃ v : H1Space U, ∃ σ : ℕ → ℕ, StrictMono σ ∧ ‖v‖ ≤ C ∧
      ∀ ℓ : H1Space U →L[ℝ] ℝ,
        Tendsto (fun j => ℓ (u (σ j))) atTop (𝓝 (ℓ v)) :=
  exists_subseq_weakly_tendsto_of_hilbert_bound u hu

/-- The same subsequence converges weakly in the scalar and gradient L² components,
since both projections from H¹ are continuous linear maps. -/
theorem exists_subseq_weakly_tendsto_h1_components {n : ℕ}
    {U : Set (EuclideanSpace ℝ (Fin n))} (u : ℕ → H1Space U)
    {C : ℝ} (hu : ∀ j, ‖u j‖ ≤ C) :
    ∃ v : H1Space U, ∃ σ : ℕ → ℕ, StrictMono σ ∧ ‖v‖ ≤ C ∧
      (∀ ℓ : H1Space U →L[ℝ] ℝ,
        Tendsto (fun j => ℓ (u (σ j))) atTop (𝓝 (ℓ v))) ∧
      (∀ ℓ : Lp ℝ 2 (volume.restrict U) →L[ℝ] ℝ,
        Tendsto (fun j => ℓ (u (σ j)).toLp) atTop (𝓝 (ℓ v.toLp))) ∧
      (∀ ℓ : Lp (EuclideanSpace ℝ (Fin n)) 2 (volume.restrict U) →L[ℝ] ℝ,
        Tendsto (fun j => ℓ (u (σ j)).gradientLp) atTop (𝓝 (ℓ v.gradientLp))) := by
  obtain ⟨v, σ, hσ, hv, ht⟩ := exists_subseq_weakly_tendsto_h1 u hu
  exact ⟨v, σ, hσ, hv, ht, fun ℓ => ht (ℓ.comp H1Space.toLpCLM),
    fun ℓ => ht (ℓ.comp H1Space.gradientCLM)⟩

end LiquidDrop

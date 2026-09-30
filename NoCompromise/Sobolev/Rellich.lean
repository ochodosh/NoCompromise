module

public import NoCompromise.Sobolev.PlanarDomain
public import NoCompromise.Sobolev.WeakCompactness
public import NoCompromise.Sobolev.Poincare

@[expose] public section

/-!
# Simultaneous weak H¹ and strong L² convergence

On bounded Lipschitz domains, the constructed BV extension and compactness give
L¹ compactness. The planar H¹ to L⁴ estimate and interpolation give strong L²
convergence, and continuous linear functionals identify the strong and weak limits.
This proves the blueprint's Rellich theorem on every positive-radius planar disk.
-/

open MeasureTheory Filter Set
open scoped ENNReal Topology
namespace LiquidDrop
set_option maxSynthPendingDepth 8

/-- On a bounded Lipschitz domain, a bounded H¹ sequence with a uniform L⁴ bound
has one subsequence converging weakly in H¹ and strongly in L² to the same H¹ limit.
The separate planar theorem below supplies the L⁴ bound from H¹ alone. -/
theorem exists_subseq_weak_h1_strong_l2_of_l4_bound {n : ℕ}
    {D : Set (EuclideanSpace ℝ (Fin n))} (hD : IsOpen D)
    (hbD : Bornology.IsBounded D) (hL : HasLipschitzBoundary D)
    (u : ℕ → H1Space D) {C : ℝ} (hu : ∀ j, ‖u j‖ ≤ C)
    {A : ℝ≥0∞} (hA : A < ∞)
    (h4 : ∀ j, eLpNorm (u j) 4 (volume.restrict D) ≤ A) :
    ∃ v : H1Space D, ∃ σ : ℕ → ℕ, StrictMono σ ∧ ‖v‖ ≤ C ∧
      (∀ ℓ : H1Space D →L[ℝ] ℝ,
        Tendsto (fun j => ℓ (u (σ j))) atTop (𝓝 (ℓ v))) ∧
      Tendsto (fun j => (u (σ j)).toLp) atTop (𝓝 v.toLp) := by
  have hC : 0 ≤ C := (norm_nonneg (u 0)).trans (hu 0)
  have hvol : volume D < ∞ := hbD.measure_lt_top
  have hBV (j) : IsBVOn (u j) D := (u j).hasH1GradientOn.isBVOn hvol
  have hb (j) : (∫ x in D, |u j x|) + (variation (u j) D).toReal ≤
      (volume D).toReal ^ (1 / 2 : ℝ) * (2 * C) := by
    have h := (u j).hasH1GradientOn.bv_bound_real hvol
    rw [← (u j).norm_toLp_eq_lpNorm, ← (u j).norm_gradientLp_eq_lpNorm] at h
    simp only [Real.norm_eq_abs] at h
    apply h.trans
    apply mul_le_mul_of_nonneg_left _ (by positivity)
    exact (u j).sum_norm_le.trans (mul_le_mul_of_nonneg_left (hu j) (by norm_num))
  obtain ⟨v, σ, hσ, hv, hweak⟩ := exists_subseq_weakly_tendsto_h1 u hu
  obtain ⟨g, τ, hτ, hg, ht⟩ := hasBVCompactness_of_lipschitzBoundary hD hbD hL
    (fun j => u (σ j)) (fun j => hBV (σ j))
    ((volume D).toReal ^ (1 / 2 : ℝ) * (2 * C)) (by positivity) (fun j => hb (σ j))
  have htnorm : Tendsto (fun j => ∫ x in D, ‖u (σ (τ j)) x - g x‖) atTop (𝓝 0) := by
    simpa only [Real.norm_eq_abs] using ht
  obtain ⟨hf2, hg2, ht2⟩ := l2_convergence_of_l1_and_l4_bound
    (fun j => (hBV (σ (τ j))).1) hg htnorm hA (fun j => h4 (σ (τ j)))
  have htoLp (j) : (hf2 j).toLp (u (σ (τ j))) = (u (σ (τ j))).toLp := by
    apply Lp.ext
    exact MemLp.coeFn_toLp (hf2 j)
  simp only [htoLp] at ht2
  have heq : hg2.toLp g = v.toLp := by
    apply (SeparatingDual.eq_iff_forall_dual_eq (R := ℝ)).mpr
    intro ℓ
    have hstrong := ℓ.continuous.continuousAt.tendsto.comp ht2
    have hweak' := (hweak (ℓ.comp H1Space.toLpCLM)).comp hτ.tendsto_atTop
    exact tendsto_nhds_unique hstrong hweak'
  refine ⟨v, σ ∘ τ, hσ.comp hτ, hv, ?_, ?_⟩
  · intro ℓ
    exact (hweak ℓ).comp hτ.tendsto_atTop
  · simpa only [Function.comp_def, heq] using ht2

/-- On any bounded open planar domain with Lipschitz boundary, every H¹-bounded
sequence has a subsequence converging weakly in H¹ and strongly in L². -/
theorem exists_subseq_weak_h1_strong_l2_planar
    {D : Set (EuclideanSpace ℝ (Fin 2))} (hD : IsOpen D)
    (hbD : Bornology.IsBounded D) (hL : HasLipschitzBoundary D)
    (u : ℕ → H1Space D) {C : ℝ} (hu : ∀ j, ‖u j‖ ≤ C) :
    ∃ v : H1Space D, ∃ σ : ℕ → ℕ, StrictMono σ ∧ ‖v‖ ≤ C ∧
      (∀ ℓ : H1Space D →L[ℝ] ℝ,
        Tendsto (fun j => ℓ (u (σ j))) atTop (𝓝 (ℓ v))) ∧
      Tendsto (fun j => (u (σ j)).toLp) atTop (𝓝 v.toLp) := by
  obtain ⟨K, hK, hGN⟩ := planar_gn_lipschitzDomain hD hbD hL
  apply exists_subseq_weak_h1_strong_l2_of_l4_bound hD hbD hL u hu
    (A := ENNReal.ofReal (K * (2 * C))) ENNReal.ofReal_lt_top
  intro j
  obtain ⟨hm, hb⟩ := hGN (u j) (u j).gradientLp (u j).hasH1GradientOn
  rw [← ofReal_lpNorm hm]
  apply ENNReal.ofReal_le_ofReal
  apply hb.trans
  rw [← (u j).norm_toLp_eq_lpNorm, ← (u j).norm_gradientLp_eq_lpNorm]
  exact mul_le_mul_of_nonneg_left
    ((u j).sum_norm_le.trans (mul_le_mul_of_nonneg_left (hu j) (by norm_num))) hK.le


/-- Blueprint `thm:rellich`: simultaneous weak H¹ and strong L² compactness
on a positive-radius planar disk, with the same H¹ limit and norm bound. -/
theorem rellich_disk (z : EuclideanSpace ℝ (Fin 2)) {r : ℝ} (hr : 0 < r)
    (u : ℕ → H1Space (Metric.ball z r)) {C : ℝ} (hu : ∀ j, ‖u j‖ ≤ C) :
    ∃ v : H1Space (Metric.ball z r), ∃ σ : ℕ → ℕ, StrictMono σ ∧ ‖v‖ ≤ C ∧
      (∀ ℓ : H1Space (Metric.ball z r) →L[ℝ] ℝ,
        Tendsto (fun j => ℓ (u (σ j))) atTop (𝓝 (ℓ v))) ∧
      Tendsto (fun j => (u (σ j)).toLp) atTop (𝓝 v.toLp) :=
  exists_subseq_weak_h1_strong_l2_planar Metric.isOpen_ball Metric.isBounded_ball
    (hasLipschitzBoundary_ball z hr) u hu

end LiquidDrop

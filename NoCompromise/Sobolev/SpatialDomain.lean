import NoCompromise.Sobolev.SpatialGN
import NoCompromise.Sobolev.Rellich

/-!
# Spatial H¹ embeddings and compactness on bounded Lipschitz domains

The constructed extension gives the domain L⁶ estimate. Finite volume gives L⁴,
and BV compactness with interpolation gives simultaneous weak H¹ and strong L² convergence.
-/

noncomputable section
open MeasureTheory Filter Metric Set
open scoped ENNReal NNReal Topology
namespace LiquidDrop
set_option maxSynthPendingDepth 8

/-- A bounded open spatial Lipschitz domain has a uniform H¹ to L⁶ estimate. -/
theorem spatial_gn_lipschitzDomain {D : Set (EuclideanSpace ℝ (Fin 3))}
    (hD : IsOpen D) (hbD : Bornology.IsBounded D) (hL : HasLipschitzBoundary D) :
    ∃ C : ℝ, 0 < C ∧ ∀ f G, HasH1GradientOn f G D →
      MemLp f 6 (volume.restrict D) ∧
        lpNorm f 6 (volume.restrict D) ≤
          C * (lpNorm f 2 (volume.restrict D) + lpNorm G 2 (volume.restrict D)) := by
  obtain ⟨T, W, C, _, _, _, hC, hT⟩ :=
    exists_h1_extension_in_bounded_neighborhood hD hbD hL
  refine ⟨4 * C + 1, by positivity, fun f G hf => ?_⟩
  obtain ⟨H, hH, heq, _, hb⟩ := hT f G hf
  have hae : T f =ᵐ[volume.restrict D] f :=
    ae_restrict_of_forall_mem hD.measurableSet heq
  have hm := hH.memLp_six.mono_measure (Measure.restrict_le_self (s := D))
  have hmf := hm.ae_eq hae
  refine ⟨hmf, ?_⟩
  have hr : lpNorm f 6 (volume.restrict D) ≤ lpNorm (T f) 6 volume := by
    rw [← toReal_eLpNorm, ← toReal_eLpNorm,
      ← eLpNorm_congr_ae hae]
    exact ENNReal.toReal_mono hH.memLp_six.eLpNorm_ne_top
      (eLpNorm_mono_measure (T f) Measure.restrict_le_self)
  apply hr.trans (hH.lpNorm_six_le.trans ?_)
  have hsum : 0 ≤ lpNorm f 2 (volume.restrict D) + lpNorm G 2 (volume.restrict D) :=
    add_nonneg lpNorm_nonneg lpNorm_nonneg
  have hHle : lpNorm H 2 volume ≤
      C * (lpNorm f 2 (volume.restrict D) + lpNorm G 2 (volume.restrict D)) :=
    (le_add_of_nonneg_left lpNorm_nonneg).trans hb
  nlinarith

/-- Finite-volume Hölder interpolation from L⁶ to L⁴. -/
lemma lpNorm_four_le_lpNorm_six_mul_measure {α : Type*} [MeasurableSpace α]
    {μ : Measure α} [IsFiniteMeasure μ] {f : α → ℝ} (hf : MemLp f 6 μ) :
    MemLp f 4 μ ∧ lpNorm f 4 μ ≤ lpNorm f 6 μ * (μ univ).toReal ^ (1 / 12 : ℝ) := by
  have hm := hf.mono_exponent (by norm_num : (4 : ℝ≥0∞) ≤ 6)
  refine ⟨hm, ?_⟩
  have h := eLpNorm_le_eLpNorm_mul_rpow_measure_univ (by norm_num : (4 : ℝ≥0∞) ≤ 6) hf.aestronglyMeasurable
  norm_num only [ENNReal.toReal_ofNat, show (1 / (4 : ℝ) - 1 / 6) = 1 / 12 by norm_num] at h
  have hr := ENNReal.toReal_mono (by finiteness) h
  simpa only [ENNReal.toReal_mul, ← ENNReal.toReal_rpow,
    toReal_eLpNorm, toReal_eLpNorm] using hr

/-- Bounded spatial Lipschitz domains have a uniform H¹ to L⁴ estimate. -/
theorem spatial_h1_l4_lipschitzDomain {D : Set (EuclideanSpace ℝ (Fin 3))}
    (hD : IsOpen D) (hbD : Bornology.IsBounded D) (hL : HasLipschitzBoundary D) :
    ∃ C : ℝ, 0 < C ∧ ∀ f G, HasH1GradientOn f G D →
      MemLp f 4 (volume.restrict D) ∧
        lpNorm f 4 (volume.restrict D) ≤
          C * (lpNorm f 2 (volume.restrict D) + lpNorm G 2 (volume.restrict D)) := by
  let : IsFiniteMeasure (volume.restrict D) := ⟨by simpa using hbD.measure_lt_top⟩
  obtain ⟨C, hC, h6⟩ := spatial_gn_lipschitzDomain hD hbD hL
  refine ⟨C * (volume D).toReal ^ (1 / 12 : ℝ) + 1, by positivity, fun f G hf => ?_⟩
  obtain ⟨hm, hb⟩ := h6 f G hf
  obtain ⟨hm4, hb4⟩ := lpNorm_four_le_lpNorm_six_mul_measure hm
  simp only [Measure.restrict_apply_univ] at hb4
  refine ⟨hm4, hb4.trans ?_⟩
  have hq : 0 ≤ (volume D).toReal ^ (1 / 12 : ℝ) := by positivity
  have hs : 0 ≤ lpNorm f 2 (volume.restrict D) + lpNorm G 2 (volume.restrict D) :=
    add_nonneg lpNorm_nonneg lpNorm_nonneg
  nlinarith [mul_le_mul_of_nonneg_right hb hq]

/-- Bounded H¹ sequences on spatial Lipschitz domains have simultaneous weak H¹
and strong L² convergence along a subsequence, with the same limit. -/
theorem exists_subseq_weak_h1_strong_l2_spatial
    {D : Set (EuclideanSpace ℝ (Fin 3))} (hD : IsOpen D)
    (hbD : Bornology.IsBounded D) (hL : HasLipschitzBoundary D)
    (u : ℕ → H1Space D) {C : ℝ} (hu : ∀ j, ‖u j‖ ≤ C) :
    ∃ v : H1Space D, ∃ σ : ℕ → ℕ, StrictMono σ ∧ ‖v‖ ≤ C ∧
      (∀ ℓ : H1Space D →L[ℝ] ℝ,
        Tendsto (fun j => ℓ (u (σ j))) atTop (𝓝 (ℓ v))) ∧
      Tendsto (fun j => (u (σ j)).toLp) atTop (𝓝 v.toLp) := by
  obtain ⟨K, hK, hGN⟩ := spatial_h1_l4_lipschitzDomain hD hbD hL
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

end LiquidDrop

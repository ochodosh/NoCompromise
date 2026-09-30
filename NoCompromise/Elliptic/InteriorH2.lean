module

public import NoCompromise.Elliptic.InteriorH2Localization

@[expose] public section

/-!
# Interior H² regularity for distributional Poisson equations

The input function and source are only L² on the larger ball. The first and
second weak derivatives are constructed, and the estimate has a constant
chosen before the data. The argument works in every finite dimension.
-/

noncomputable section

open MeasureTheory Filter Metric Set InnerProductSpace
open scoped NNReal ENNReal Topology Gradient Convolution

namespace LiquidDrop

set_option maxSynthPendingDepth 8

/-- Distributional Poisson equations restrict to arbitrary subsets. -/
theorem HasDistributionalLaplacianOn.mono {n : ℕ}
    {U V : Set (EuclideanSpace ℝ (Fin n))} {u f : EuclideanSpace ℝ (Fin n) → ℝ}
    (h : HasDistributionalLaplacianOn u f U) (hVU : V ⊆ U) :
    HasDistributionalLaplacianOn u f V := by
  refine ⟨h.locallyIntegrable_function.mono_set hVU,
    h.locallyIntegrable_source.mono_set hVU, ?_⟩
  intro φ hφ hcφ hsφ
  have hleft (W : Set (EuclideanSpace ℝ (Fin n))) (hs : tsupport φ ⊆ W) :
      (∫ x in W, u x * laplacianN φ x) = ∫ x, u x * laplacianN φ x :=
    setIntegral_eq_integral_of_forall_compl_eq_zero fun x hx => by
      rw [image_eq_zero_of_notMem_tsupport
        (fun ht => hx (hs ((tsupport_laplacianN_subset φ) ht))), mul_zero]
  have hright (W : Set (EuclideanSpace ℝ (Fin n))) (hs : tsupport φ ⊆ W) :
      (∫ x in W, f x * φ x) = ∫ x, f x * φ x :=
    setIntegral_eq_integral_of_forall_compl_eq_zero fun x hx => by
      rw [image_eq_zero_of_notMem_tsupport (fun ht => hx (hs ht)), mul_zero]
  have heq := h.test_eq φ hφ hcφ (hsφ.trans hVU)
  rw [hleft U (hsφ.trans hVU), hright U (hsφ.trans hVU)] at heq
  rw [hleft V hsφ, hright V hsφ]
  exact heq

lemma poisson_lpNorm_mono_measure {α F : Type*} [MeasurableSpace α]
    [NormedAddCommGroup F] {μ ν : Measure α} {f : α → F}
    (hf : MemLp f 2 ν) (hμν : μ ≤ ν) : lpNorm f 2 μ ≤ lpNorm f 2 ν := by
  rw [← toReal_eLpNorm, ← toReal_eLpNorm]
  exact ENNReal.toReal_mono hf.eLpNorm_ne_top (eLpNorm_mono_measure _ hμν)

/-- Interior H² regularity and estimate for L² distributional Poisson data.
The displayed sum of L² norms includes the genuine gradient and all Hessian rows. -/
theorem interior_h2 {n : ℕ} (z : EuclideanSpace ℝ (Fin n)) {r R : ℝ} (hrR : r < R) :
    ∃ C : ℝ, 0 < C ∧ ∀ u f : EuclideanSpace ℝ (Fin n) → ℝ,
      HasDistributionalLaplacianOn u f (ball z R) →
      MemLp u 2 (volume.restrict (ball z R)) → MemLp f 2 (volume.restrict (ball z R)) →
      ∃ G : EuclideanSpace ℝ (Fin n) → EuclideanSpace ℝ (Fin n),
      ∃ H : Fin n → EuclideanSpace ℝ (Fin n) → EuclideanSpace ℝ (Fin n),
        HasH2DerivativesOn u G H (ball z r) ∧
        lpNorm u 2 (volume.restrict (ball z r)) + lpNorm G 2 (volume.restrict (ball z r)) +
          ∑ i, lpNorm (H i) 2 (volume.restrict (ball z r)) ≤
            C * (lpNorm u 2 (volume.restrict (ball z R)) +
              lpNorm f 2 (volume.restrict (ball z R))) := by
  classical
  let s := (r + R) / 2
  have hrs : r < s := by dsimp [s]; linarith
  have hsR : s < R := by dsimp [s]; linarith
  obtain ⟨C₁, hC₁, hH1⟩ := exists_poisson_interior_h1_bound z hsR
  obtain ⟨η, hη, hcη, hsη, hone, hbη⟩ := exists_smooth_cutoff_one_near_compact
    (isCompact_closedBall z r) isOpen_ball (closedBall_subset_ball hrs)
  have hη1 : ContDiff ℝ 1 η := hη.of_le (by simp)
  have hη2 : ContDiff ℝ 2 η := hη.of_le (by simp)
  have hbηnorm (x) : ‖η x‖ ≤ 1 := by
    rw [Real.norm_eq_abs, abs_of_nonneg (hbη x).1]
    exact (hbη x).2
  obtain ⟨B, hB, hbgrad⟩ := exists_nonneg_bound_gradient_of_contDiff hη1 hcη
  have hclap : HasCompactSupport (laplacianN η) :=
    hcη.of_isClosed_subset (isClosed_tsupport _) (tsupport_laplacianN_subset η)
  obtain ⟨C₀, hbC₀⟩ := hclap.exists_bound_of_continuous (continuous_laplacianN hη2)
  let C₂ := max C₀ 0
  have hC₂ : 0 ≤ C₂ := le_max_right _ _
  have hblap (x) : ‖laplacianN η x‖ ≤ C₂ := (hbC₀ x).trans (le_max_left _ _)
  refine ⟨1 + (1 + B) * C₁ + (n : ℝ) * (1 + (C₂ + 2 * B) * C₁), by positivity, ?_⟩
  intro u f h hu hf
  obtain ⟨G, hG, hGb⟩ := hH1 u f h hu hf
  have hsmall : ball z s ⊆ ball z R := ball_subset_ball hsR.le
  have hfsmall := hf.mono_measure (Measure.restrict_mono hsmall le_rfl)
  let W (x : EuclideanSpace ℝ (Fin n)) := η x • G x + u x • gradient η x
  let q (x : EuclideanSpace ℝ (Fin n)) := η x * f x + laplacianN η x * u x +
    2 * inner ℝ (gradient η x) (G x)
  have hcut := hG.mul_compact_cutoff measurableSet_ball hη1 hcη hsη hbηnorm hbgrad
  have hq := poisson_cutoff_source_memLp_and_bound measurableSet_ball hG.memLp_function
    hfsmall hG.memLp_gradient hη hsη zero_le_one hB hC₂ hbηnorm hbgrad hblap
  have hqeq := (h.mono hsmall).mul_compact_cutoff hG.toHasWeakGradientOn hη hcη hsη
  obtain ⟨H, hH, hHb⟩ := hqeq.hasH2DerivativesOn_of_compact hcut.1 hcut.2.1 hq.1
  have hmW : MemLp W 2 volume := by
    simpa only [Measure.restrict_univ] using hcut.1.memLp_gradient
  have huEq : (fun x => η x * u x) =ᵐ[volume.restrict (ball z r)] u := by
    filter_upwards [ae_restrict_mem measurableSet_ball] with x hx
    rw [hone.self_of_nhdsSet x (ball_subset_closedBall hx), one_mul]
  have hHsmall : HasH2DerivativesOn u W H (ball z r) :=
    ⟨(hH.hasH1GradientOn.mono (subset_univ _)).congr_ae huEq EventuallyEq.rfl,
      fun i => (hH.coordinate_hasH1GradientOn i).mono (subset_univ _)⟩
  have hmulfin : ENNReal.ofReal B * eLpNorm u 2 (volume.restrict (ball z s)) ≠ ∞ :=
    ENNReal.mul_ne_top ENNReal.ofReal_ne_top hG.memLp_function.eLpNorm_ne_top
  have hbW : lpNorm W 2 volume ≤ lpNorm G 2 (volume.restrict (ball z s)) +
      B * lpNorm u 2 (volume.restrict (ball z s)) := by
    have hb := hcut.2.2.2
    simp only [ENNReal.ofReal_one, one_mul] at hb
    have ht := ENNReal.toReal_mono
      (ENNReal.add_ne_top.mpr ⟨hG.memLp_gradient.eLpNorm_ne_top, hmulfin⟩) hb
    change (eLpNorm W 2 volume).toReal ≤ _ at ht
    simpa only [ENNReal.toReal_add hG.memLp_gradient.eLpNorm_ne_top hmulfin, ENNReal.toReal_mul,
      ENNReal.toReal_ofReal hB, toReal_eLpNorm,
      toReal_eLpNorm, toReal_eLpNorm] using ht
  let D := lpNorm u 2 (volume.restrict (ball z R)) + lpNorm f 2 (volume.restrict (ball z R))
  have hD : 0 ≤ D := add_nonneg lpNorm_nonneg lpNorm_nonneg
  have hu0 : 0 ≤ lpNorm u 2 (volume.restrict (ball z s)) := lpNorm_nonneg
  have hG0 : 0 ≤ lpNorm G 2 (volume.restrict (ball z s)) := lpNorm_nonneg
  have hqbound : lpNorm q 2 volume ≤ (1 + (C₂ + 2 * B) * C₁) * D := by
    have hfb := poisson_lpNorm_mono_measure hf (Measure.restrict_mono hsmall le_rfl)
    have hsource : lpNorm q 2 volume ≤ lpNorm f 2 (volume.restrict (ball z s)) +
        C₂ * lpNorm u 2 (volume.restrict (ball z s)) +
          2 * B * lpNorm G 2 (volume.restrict (ball z s)) := by
      simpa only [one_mul] using hq.2
    calc
      _ ≤ D + (C₂ + 2 * B) *
          (lpNorm u 2 (volume.restrict (ball z s)) +
            lpNorm G 2 (volume.restrict (ball z s))) := by
        dsimp [D]
        nlinarith [mul_nonneg hB hu0, mul_nonneg hC₂ hG0,
          show 0 ≤ lpNorm u 2 (volume.restrict (ball z R)) from lpNorm_nonneg]
      _ ≤ D + (C₂ + 2 * B) * (C₁ * D) :=
        add_le_add le_rfl (mul_le_mul_of_nonneg_left hGb (by positivity))
      _ = _ := by ring
  have hWbound : lpNorm W 2 (volume.restrict (ball z r)) ≤ (1 + B) * C₁ * D := by
    calc
      _ ≤ lpNorm W 2 volume := poisson_lpNorm_mono_measure hmW Measure.restrict_le_self
      _ ≤ (1 + B) * (lpNorm u 2 (volume.restrict (ball z s)) +
          lpNorm G 2 (volume.restrict (ball z s))) := by
        nlinarith [mul_nonneg hB hG0]
      _ ≤ (1 + B) * (C₁ * D) := mul_le_mul_of_nonneg_left hGb (by positivity)
      _ = _ := by ring
  have hHbound (i : Fin n) : lpNorm (H i) 2 (volume.restrict (ball z r)) ≤
      (1 + (C₂ + 2 * B) * C₁) * D := by
    have hmH : MemLp (H i) 2 volume := by
      simpa only [Measure.restrict_univ] using (hH.coordinate_hasH1GradientOn i).memLp_gradient
    exact (poisson_lpNorm_mono_measure hmH Measure.restrict_le_self).trans
      ((hHb i).trans hqbound)
  have hHsum : (∑ i, lpNorm (H i) 2 (volume.restrict (ball z r))) ≤
      (n : ℝ) * ((1 + (C₂ + 2 * B) * C₁) * D) := by
    simpa only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul] using
      Finset.sum_le_sum (s := Finset.univ) (fun i _ => hHbound i)
  have hub : lpNorm u 2 (volume.restrict (ball z r)) ≤ D := by
    have hb := poisson_lpNorm_mono_measure hu
      (Measure.restrict_mono (ball_subset_ball hrR.le) le_rfl)
    exact hb.trans (le_add_of_nonneg_right lpNorm_nonneg)
  refine ⟨W, H, hHsmall, ?_⟩
  change _ ≤ (1 + (1 + B) * C₁ + (n : ℝ) * (1 + (C₂ + 2 * B) * C₁)) * D
  nlinarith only [hub, hWbound, hHsum]

end LiquidDrop

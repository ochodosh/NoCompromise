import NoCompromise.Elliptic.SobolevChainSchwartz

/-!
# Continuous representatives from the H² estimate

Smooth compact approximants with strongly convergent functions and Laplacians
converge uniformly in dimensions below four. Applying this to mollifications
constructs a continuous representative of a weak Poisson solution.
-/

noncomputable section

open MeasureTheory Filter Metric Set InnerProductSpace
open scoped NNReal ENNReal Topology Gradient Convolution

namespace LiquidDrop

/-- Strong L² convergence of functions and Laplacians produces a uniform limit. -/
theorem sobolevChain_exists_continuous_limit {n : ℕ} (hn : n < 4)
    {v : ℕ → EuclideanSpace ℝ (Fin n) → ℝ}
    (hv : ∀ j, ContDiff ℝ (⊤ : ℕ∞) (v j)) (hcv : ∀ j, HasCompactSupport (v j))
    {u f : EuclideanSpace ℝ (Fin n) → ℝ} (hu : MemLp u 2 volume) (hf : MemLp f 2 volume)
    (htu : Tendsto (fun j => lpNorm (v j - u) 2 volume) atTop (𝓝 0))
    (htf : Tendsto (fun j => lpNorm (laplacianN (v j) - f) 2 volume) atTop (𝓝 0)) :
    ∃ w : EuclideanSpace ℝ (Fin n) → ℝ,
      Continuous w ∧ w =ᵐ[volume] u ∧ TendstoUniformly v w atTop := by
  have hmv j : MemLp (v j) 2 volume := (hv j).continuous.memLp_of_hasCompactSupport (hcv j)
  have hmΔ j : MemLp (laplacianN (v j)) 2 volume :=
    (continuous_laplacianN ((hv j).of_le (by simp))).memLp_of_hasCompactSupport
      ((hcv j).of_isClosed_subset (isClosed_tsupport _) (tsupport_laplacianN_subset _))
  let C := 2 * lpNorm (fun y : EuclideanSpace ℝ (Fin n) =>
    (1 + ‖y‖) ^ (-2 : ℝ)) 2 volume
  have hC : 0 ≤ C := mul_nonneg (by norm_num) lpNorm_nonneg
  let a (j : ℕ) := lpNorm (v j - u) 2 volume + lpNorm (laplacianN (v j) - f) 2 volume
  have ha : Tendsto (fun j => C * a j) atTop (𝓝 0) := by
    simpa only [a, add_zero, mul_zero] using (htu.add htf).const_mul C
  have hCau : UniformCauchySeqOn v atTop univ := by
    apply Metric.uniformCauchySeqOn_iff.mpr
    intro ε hε
    obtain ⟨N, hN⟩ := eventually_atTop.mp (ha.eventually (Iio_mem_nhds (half_pos hε)))
    refine ⟨N, fun j hj k hk x _ => ?_⟩
    have hju := lpNorm_sub_le_lpNorm_sub_add_lpNorm_sub (hmv j) hu
      (h := v k) (by norm_num : (1 : ℝ≥0∞) ≤ 2)
    have hjf := lpNorm_sub_le_lpNorm_sub_add_lpNorm_sub (hmΔ j) hf
      (h := laplacianN (v k)) (by norm_num : (1 : ℝ≥0∞) ≤ 2)
    rw [lpNorm_sub_comm u (v k)] at hju
    rw [lpNorm_sub_comm f (laplacianN (v k))] at hjf
    have hb := sobolevChain_smooth_uniform_bound hn ((hv j).sub (hv k))
      ((hcv j).sub (hcv k)) x
    change ‖v j x - v k x‖ ≤ C *
      (lpNorm (v j - v k) 2 volume + lpNorm (laplacianN (v j - v k)) 2 volume) at hb
    rw [sobolevChain_laplacianN_sub ((hv j).of_le (by simp))
      ((hv k).of_le (by simp))] at hb
    have hab : lpNorm (v j - v k) 2 volume +
        lpNorm (laplacianN (v j) - laplacianN (v k)) 2 volume ≤ a j + a k := by
      dsimp only [a]
      linarith only [hju, hjf]
    rw [dist_eq_norm]
    apply (hb.trans (mul_le_mul_of_nonneg_left hab hC)).trans_lt
    have hj' := hN j hj
    have hk' := hN k hk
    change C * a j < ε / 2 at hj'
    change C * a k < ε / 2 at hk'
    nlinarith
  choose w hw using fun x => cauchySeq_tendsto_of_complete (hCau.cauchySeq (mem_univ x))
  have htw : TendstoUniformly v w atTop :=
    tendstoUniformlyOn_univ.mp (hCau.tendstoUniformlyOn_of_tendsto (fun x _ => hw x))
  refine ⟨w, htw.continuous (Eventually.of_forall
    fun j => (hv j).continuous).frequently, ?_, htw⟩
  have hel : Tendsto (fun j => eLpNorm (v j - u) 2 volume) atTop (𝓝 0) := by
    have h := (ENNReal.continuous_ofReal.tendsto 0).comp htu
    simpa only [Function.comp_def, ENNReal.ofReal_zero, ofReal_lpNorm ((hmv _).sub hu)] using h
  obtain ⟨σ, hσ, hae⟩ := (tendstoInMeasure_of_tendsto_eLpNorm
    (by norm_num : (2 : ℝ≥0∞) ≠ 0) hel).exists_seq_tendsto_ae
  filter_upwards [hae] with x hx
  exact tendsto_nhds_unique ((hw x).comp hσ.tendsto_atTop) hx

/-- A compactly supported weak Poisson solution has a constructed continuous
representative, with a uniform estimate from the actual L² data. -/
theorem HasDistributionalLaplacianOn.exists_continuous_of_compact {n : ℕ} (hn : n < 4)
    {u f : EuclideanSpace ℝ (Fin n) → ℝ} (h : HasDistributionalLaplacianOn u f univ)
    (hu : MemLp u 2 volume) (hf : MemLp f 2 volume) (hcu : HasCompactSupport u) :
    ∃ w : EuclideanSpace ℝ (Fin n) → ℝ, Continuous w ∧ w =ᵐ[volume] u ∧
      ∀ x, ‖w x‖ ≤ 2 * lpNorm (fun y : EuclideanSpace ℝ (Fin n) =>
        (1 + ‖y‖) ^ (-2 : ℝ)) 2 volume * (lpNorm u 2 volume + lpNorm f 2 volume) := by
  let φ (j : ℕ) : ContDiffBump (0 : EuclideanSpace ℝ (Fin n)) :=
    ⟨(1 / ((j : ℝ) + 1)) / 2, 1 / ((j : ℝ) + 1), by positivity,
      half_lt_self (by positivity)⟩
  have hφ : Tendsto (fun j => (φ j).rOut) atTop (𝓝 0) :=
    tendsto_one_div_add_atTop_nhds_zero_nat (𝕜 := ℝ)
  let v (j : ℕ) := (φ j).normed volume ⋆[ContinuousLinearMap.lsmul ℝ ℝ] u
  have hv (j) : ContDiff ℝ (⊤ : ℕ∞) (v j) :=
    (φ j).hasCompactSupport_normed.contDiff_convolution_left _ (φ j).contDiff_normed
      (hu.locallyIntegrable (by norm_num))
  have hcv (j) : HasCompactSupport (v j) :=
    (φ j).hasCompactSupport_normed.convolution _ hcu
  have hlap (j) : laplacianN (v j) =
      (φ j).normed volume ⋆[ContinuousLinearMap.lsmul ℝ ℝ] f := by
    funext x
    simpa only [Set.indicator_univ] using h.laplacianN_convolution_indicator
      isOpen_univ (by simpa only [Measure.restrict_univ] using hu)
      (by simpa only [Measure.restrict_univ] using hf)
      (φ j).contDiff_normed (φ j).hasCompactSupport_normed x (subset_univ _)
  have htu : Tendsto (fun j => lpNorm (v j - u) 2 volume) atTop (𝓝 0) :=
    tendsto_lpNorm_bump_convolution_sub hu hφ
  have htf : Tendsto (fun j => lpNorm (laplacianN (v j) - f) 2 volume) atTop (𝓝 0) := by
    simp only [hlap]
    exact tendsto_lpNorm_bump_convolution_sub hf hφ
  obtain ⟨w, hw, hae, htw⟩ := sobolevChain_exists_continuous_limit hn hv hcv hu hf htu htf
  refine ⟨w, hw, hae, fun x => ?_⟩
  apply le_of_tendsto (htw.tendsto_at x).norm
  apply Eventually.of_forall
  intro j
  have hvb := memLp_two_convolution_probability_kernel (φ j).continuous_normed
    (φ j).hasCompactSupport_normed (φ j).nonneg_normed (φ j).integral_normed hu
  have hfb := memLp_two_convolution_probability_kernel (φ j).continuous_normed
    (φ j).hasCompactSupport_normed (φ j).nonneg_normed (φ j).integral_normed hf
  have hvN : lpNorm (v j) 2 volume ≤ lpNorm u 2 volume := by
    simpa only [one_mul] using poisson_lpNorm_le_of_eLpNorm_le hvb.1 hu zero_le_one
      (by simpa only [ENNReal.ofReal_one, one_mul] using hvb.2.1)
  have hfN : lpNorm (laplacianN (v j)) 2 volume ≤ lpNorm f 2 volume := by
    rw [hlap]
    simpa only [one_mul] using poisson_lpNorm_le_of_eLpNorm_le hfb.1 hf zero_le_one
      (by simpa only [ENNReal.ofReal_one, one_mul] using hfb.2.1)
  apply (sobolevChain_smooth_uniform_bound hn (hv j) (hcv j) x).trans
  exact mul_le_mul_of_nonneg_left (add_le_add hvN hfN)
    (mul_nonneg (by norm_num) lpNorm_nonneg)

/-- Interior continuity and the uniform estimate for L² distributional Poisson
solutions in dimensions below four. The representative is constructed, not assumed. -/
theorem interior_poisson_continuous {n : ℕ} (hn : n < 4)
    (z : EuclideanSpace ℝ (Fin n)) {r R : ℝ} (hrR : r < R) :
    ∃ C : ℝ, 0 < C ∧ ∀ u f : EuclideanSpace ℝ (Fin n) → ℝ,
      HasDistributionalLaplacianOn u f (ball z R) →
      MemLp u 2 (volume.restrict (ball z R)) → MemLp f 2 (volume.restrict (ball z R)) →
      ∃ w : EuclideanSpace ℝ (Fin n) → ℝ, Continuous w ∧
        w =ᵐ[volume.restrict (ball z r)] u ∧ ∀ x, ‖w x‖ ≤
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
  let T := 2 * lpNorm (fun y : EuclideanSpace ℝ (Fin n) =>
    (1 + ‖y‖) ^ (-2 : ℝ)) 2 volume
  have hT : 0 ≤ T := mul_nonneg (by norm_num) lpNorm_nonneg
  refine ⟨1 + T * (C₁ + 1 + (C₂ + 2 * B) * C₁), by positivity, ?_⟩
  intro u f h hu hf
  obtain ⟨G, hG, hGb⟩ := hH1 u f h hu hf
  have hsmall : ball z s ⊆ ball z R := ball_subset_ball hsR.le
  have hfsmall := hf.mono_measure (Measure.restrict_mono hsmall le_rfl)
  let q (x : EuclideanSpace ℝ (Fin n)) := η x * f x + laplacianN η x * u x +
    2 * inner ℝ (gradient η x) (G x)
  have hcut := hG.mul_compact_cutoff measurableSet_ball hη1 hcη hsη hbηnorm hbgrad
  have hq := poisson_cutoff_source_memLp_and_bound measurableSet_ball hG.memLp_function
    hfsmall hG.memLp_gradient hη hsη zero_le_one hB hC₂ hbηnorm hbgrad hblap
  have hqeq := (h.mono hsmall).mul_compact_cutoff hG.toHasWeakGradientOn hη hcη hsη
  have hmu : MemLp (fun x => η x * u x) 2 volume := by
    simpa only [Measure.restrict_univ] using hcut.1.memLp_function
  obtain ⟨w, hw, hae, hwb⟩ := hqeq.exists_continuous_of_compact hn hmu hq.1 hcut.2.1
  have huEq : (fun x => η x * u x) =ᵐ[volume.restrict (ball z r)] u := by
    filter_upwards [ae_restrict_mem measurableSet_ball] with x hx
    rw [hone.self_of_nhdsSet x (ball_subset_closedBall hx), one_mul]
  have hwEq : w =ᵐ[volume.restrict (ball z r)] (fun x => η x * u x) :=
    ae_restrict_of_ae hae
  refine ⟨w, hw, hwEq.trans huEq, fun x => ?_⟩
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
  have hubound : lpNorm (fun y => η y * u y) 2 volume ≤ C₁ * D := by
    have ht := poisson_lpNorm_le_of_eLpNorm_le hmu hG.memLp_function zero_le_one hcut.2.2.1
    simp only [one_mul] at ht
    linarith only [ht, hGb, hG0]
  calc
    ‖w x‖ ≤ T * (lpNorm (fun y => η y * u y) 2 volume + lpNorm q 2 volume) := hwb x
    _ ≤ T * ((C₁ + 1 + (C₂ + 2 * B) * C₁) * D) := by
      apply mul_le_mul_of_nonneg_left _ hT
      nlinarith only [hubound, hqbound]
    _ ≤ (1 + T * (C₁ + 1 + (C₂ + 2 * B) * C₁)) * D := by
      nlinarith only [hD]

end LiquidDrop

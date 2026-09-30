module

public import NoCompromise.Elliptic.InteriorH2Energy
public import NoCompromise.Sobolev.H1FlatExtension
public import NoCompromise.Sobolev.ExtensionPartition

@[expose] public section

/-!
# Recovering local H¹ regularity from distributional L² Poisson data

Smooth interior convolutions have uniformly bounded gradients by the cutoff
energy estimate. Weak Hilbert-space compactness then produces the original
solution's first weak derivatives.
-/

noncomputable section

open MeasureTheory Filter Metric Set InnerProductSpace
open scoped NNReal ENNReal Topology Gradient Convolution

namespace LiquidDrop

set_option maxSynthPendingDepth 8

lemma poisson_lpNorm_le_mul_of_norm_le {α E F : Type*} [MeasurableSpace α]
    [NormedAddCommGroup E] [NormedAddCommGroup F] {μ : Measure α} {p : ℝ≥0∞}
    {f : α → E} {g : α → F} (hf : MemLp f p μ) {C : ℝ} (hC : 0 ≤ C)
    (hbound : ∀ x, ‖g x‖ ≤ C * ‖f x‖) : lpNorm g p μ ≤ C * lpNorm f p μ := by
  have h := lpNorm_mono_real (hf.norm.const_mul C) hbound
  change lpNorm g p μ ≤ lpNorm (C • fun x => ‖f x‖) p μ at h
  simpa only [lpNorm_const_smul, coe_nnnorm, Real.norm_eq_abs, abs_of_nonneg hC,
    lpNorm_norm hf.aestronglyMeasurable] using h

/-- A smooth Poisson solution has a quantitative local H¹ bound wherever the
compact cutoff equals one. Only the function and forcing need global L² bounds. -/
theorem smooth_poisson_hasH1_on_cutoff {n : ℕ}
    {u q η : EuclideanSpace ℝ (Fin n) → ℝ} {V : Set (EuclideanSpace ℝ (Fin n))}
    (hV : MeasurableSet V) (hu : ContDiff ℝ 2 u)
    (hmu : MemLp u 2 volume) (hmq : MemLp q 2 volume)
    (hη : ContDiff ℝ 1 η) (hcη : HasCompactSupport η)
    (hbη : ∀ x, ‖η x‖ ≤ 1) {B : ℝ} (hB : 0 ≤ B)
    (hbgrad : ∀ x, ‖gradient η x‖ ≤ B) (hone : ∀ x ∈ V, η x = 1)
    (hEq : EqOn (laplacianN u) q (tsupport η)) :
    HasH1GradientOn u (gradient u) V ∧
      lpNorm (gradient u) 2 (volume.restrict V) ≤
        (1 + 2 * B) * lpNorm u 2 volume + lpNorm q 2 volume := by
  let v (x : EuclideanSpace ℝ (Fin n)) : EuclideanSpace ℝ (Fin n) := η x • gradient u x
  have hu1 := hu.of_le (by norm_num : (1 : WithTop ℕ∞) ≤ 2)
  have hv : MemLp v 2 volume :=
    (hη.continuous.smul (continuous_gradient_of_contDiff hu1)).memLp_of_hasCompactSupport
      (hcη.smul_right (f' := gradient u))
  have heV : gradient u =ᵐ[volume.restrict V] v := by
    filter_upwards [ae_restrict_mem hV] with x hx
    simp only [v, hone x hx, one_smul]
  have hmgrad := (hv.mono_measure Measure.restrict_le_self).ae_eq heV.symm
  have hgradnorm : lpNorm (gradient u) 2 (volume.restrict V) ≤ lpNorm v 2 volume := by
    rw [← toReal_eLpNorm, ← toReal_eLpNorm, eLpNorm_congr_ae heV]
    exact ENNReal.toReal_mono hv.eLpNorm_ne_top (eLpNorm_mono_measure _ Measure.restrict_le_self)
  have hA : lpNorm (fun x => η x * u x) 2 volume ≤ lpNorm u 2 volume := by
    have h := poisson_lpNorm_le_mul_of_norm_le hmu (C := 1) zero_le_one
      (g := fun x => η x * u x) (fun x => by
        rw [norm_mul]
        exact mul_le_mul_of_nonneg_right (hbη x) (norm_nonneg _))
    simpa only [one_mul] using h
  have hQ : lpNorm (fun x => η x * laplacianN u x) 2 volume ≤ lpNorm q 2 volume := by
    have heq : (fun x => η x * laplacianN u x) = fun x => η x * q x := by
      funext x
      by_cases hx : x ∈ tsupport η
      · rw [hEq hx]
      · rw [image_eq_zero_of_notMem_tsupport hx, zero_mul, zero_mul]
    rw [heq]
    have h := poisson_lpNorm_le_mul_of_norm_le hmq (C := 1) zero_le_one
      (g := fun x => η x * q x) (fun x => by
        rw [norm_mul]
        exact mul_le_mul_of_nonneg_right (hbη x) (norm_nonneg _))
    simpa only [one_mul] using h
  have hW : lpNorm (fun x => u x • gradient η x) 2 volume ≤ B * lpNorm u 2 volume :=
    poisson_lpNorm_le_mul_of_norm_le hmu hB (fun x => by
      rw [norm_smul, mul_comm B]
      exact mul_le_mul_of_nonneg_left (hbgrad x) (norm_nonneg _))
  refine ⟨⟨(hasWeakGradientOn_of_contDiffOn isOpen_univ hu1.contDiffOn).mono (subset_univ _),
    hmu.mono_measure Measure.restrict_le_self, hmgrad⟩, ?_⟩
  have he := smooth_poisson_cutoff_lpNorm hu hη hcη
  change lpNorm v 2 volume ≤ _ at he
  linarith only [hgradnorm, he, hA, hQ, hW]

/-- L² distributional Poisson data have an actual weak L² gradient on every set
where a compact interior cutoff equals one. The estimate uses no original H¹ data. -/
theorem HasDistributionalLaplacianOn.hasH1GradientOn_cutoff {n : ℕ}
    {U V : Set (EuclideanSpace ℝ (Fin n))} (hU : IsOpen U) (hV : MeasurableSet V)
    {u f η : EuclideanSpace ℝ (Fin n) → ℝ}
    (h : HasDistributionalLaplacianOn u f U)
    (hu : MemLp u 2 (volume.restrict U)) (hf : MemLp f 2 (volume.restrict U))
    (hη : ContDiff ℝ 1 η) (hcη : HasCompactSupport η) (hsη : tsupport η ⊆ U)
    (hbη : ∀ x, ‖η x‖ ≤ 1) {B : ℝ} (hB : 0 ≤ B)
    (hbgrad : ∀ x, ‖gradient η x‖ ≤ B) (hone : ∀ x ∈ V, η x = 1) :
    ∃ G : EuclideanSpace ℝ (Fin n) → EuclideanSpace ℝ (Fin n),
      HasH1GradientOn u G V ∧ lpNorm G 2 (volume.restrict V) ≤
        (1 + 2 * B) * lpNorm u 2 (volume.restrict U) + lpNorm f 2 (volume.restrict U) := by
  have hVK : V ⊆ tsupport η := by
    intro x hx
    apply subset_tsupport η
    rw [Function.mem_support, hone x hx]
    exact one_ne_zero
  have hVU := hVK.trans hsη
  obtain ⟨δ, hδ, hδU⟩ := hcη.exists_cthickening_subset_open hU hsη
  let φ (j : ℕ) : ContDiffBump (0 : EuclideanSpace ℝ (Fin n)) :=
    ⟨(δ / ((j : ℝ) + 1)) / 2, δ / ((j : ℝ) + 1), by positivity,
      half_lt_self (by positivity)⟩
  have hφδ (j) : (φ j).rOut ≤ δ :=
    div_le_self hδ.le (by linarith [Nat.cast_nonneg (α := ℝ) j])
  have hφlim : Tendsto (fun j => (φ j).rOut) atTop (𝓝 0) := by
    simpa only [mul_one_div, mul_zero] using
      (tendsto_one_div_add_atTop_nhds_zero_nat (𝕜 := ℝ)).const_mul δ
  have hs (j : ℕ) (x : EuclideanSpace ℝ (Fin n)) (hx : x ∈ tsupport η) :
      tsupport (fun y => (φ j).normed volume (x - y)) ⊆ U := by
    intro y hy
    have hy' := tsupport_comp_subset_preimage
      ((φ j).normed volume) (continuous_const.sub continuous_id) hy
    have hdist : dist y x ≤ δ := by
      have hy'' : ‖x - y‖ ≤ (φ j).rOut := by
        simpa only [ContDiffBump.tsupport_normed_eq, mem_preimage, mem_closedBall,
          dist_zero_right, Pi.sub_apply, id_eq] using hy'
      rw [dist_comm, dist_eq_norm]
      exact hy''.trans (hφδ j)
    exact hδU (mem_cthickening_of_dist_le y x δ (tsupport η) hx hdist)
  let u0 := U.indicator u
  let f0 := U.indicator f
  have hu0 : MemLp u0 2 volume := (memLp_indicator_iff_restrict hU.measurableSet).mpr hu
  have hf0 : MemLp f0 2 volume := (memLp_indicator_iff_restrict hU.measurableSet).mpr hf
  let v (j : ℕ) := (φ j).normed volume ⋆[ContinuousLinearMap.lsmul ℝ ℝ] u0
  let q (j : ℕ) := (φ j).normed volume ⋆[ContinuousLinearMap.lsmul ℝ ℝ] f0
  have hv (j) := memLp_two_convolution_probability_kernel (φ j).continuous_normed
    (φ j).hasCompactSupport_normed (φ j).nonneg_normed (φ j).integral_normed hu0
  have hq (j) := memLp_two_convolution_probability_kernel (φ j).continuous_normed
    (φ j).hasCompactSupport_normed (φ j).nonneg_normed (φ j).integral_normed hf0
  have hvs (j) : ContDiff ℝ (⊤ : ℕ∞) (v j) :=
    (φ j).hasCompactSupport_normed.contDiff_convolution_left _ (φ j).contDiff_normed
      (hu0.locallyIntegrable (by norm_num))
  have hEq (j) : EqOn (laplacianN (v j)) (q j) (tsupport η) :=
    fun x hx => h.laplacianN_convolution_indicator hU hu hf (φ j).contDiff_normed
      (φ j).hasCompactSupport_normed x (hs j x hx)
  have hvH1 (j) := smooth_poisson_hasH1_on_cutoff hV ((hvs j).of_le (by simp))
    (hv j).1 (hq j).1 hη hcη hbη hB hbgrad hone (hEq j)
  have hvnorm (j) : lpNorm (v j) 2 volume ≤ lpNorm u 2 (volume.restrict U) := by
    rw [← toReal_eLpNorm, ← toReal_eLpNorm]
    apply ENNReal.toReal_mono hu.eLpNorm_ne_top
    simpa only [u0, eLpNorm_indicator_eq_eLpNorm_restrict hU.measurableSet] using (hv j).2.1
  have hqnorm (j) : lpNorm (q j) 2 volume ≤ lpNorm f 2 (volume.restrict U) := by
    rw [← toReal_eLpNorm, ← toReal_eLpNorm]
    apply ENNReal.toReal_mono hf.eLpNorm_ne_top
    simpa only [f0, eLpNorm_indicator_eq_eLpNorm_restrict hU.measurableSet] using (hq j).2.1
  let C := (1 + 2 * B) * lpNorm u 2 (volume.restrict U) + lpNorm f 2 (volume.restrict U)
  have hC : 0 ≤ C :=
    add_nonneg (mul_nonneg (by positivity) lpNorm_nonneg) lpNorm_nonneg
  have hbound (j) : lpNorm (gradient (v j)) 2 (volume.restrict V) ≤ C :=
    (hvH1 j).2.trans (add_le_add
      (mul_le_mul_of_nonneg_left (hvnorm j) (by positivity)) (hqnorm j))
  have ht := (h.tendsto_bump_convolution_indicator hU hV hVU hu hf φ hφlim
    (fun j x hx => hs j x (hVK hx))).1
  obtain ⟨G, hG, _, hbG⟩ := exists_hasH1GradientOn_of_l2_limit_of_uniform_bounds
    (fun j => (hvH1 j).1) (hu.mono_measure (Measure.restrict_mono hVU le_rfl)) ht
    hu.eLpNorm_lt_top (ENNReal.ofReal_lt_top (r := C))
    (fun j => (eLpNorm_mono_measure _ Measure.restrict_le_self).trans
      (by simpa only [u0, eLpNorm_indicator_eq_eLpNorm_restrict hU.measurableSet]
        using (hv j).2.1))
    (fun j => by
      rw [← ofReal_lpNorm (hvH1 j).1.memLp_gradient]
      exact ENNReal.ofReal_le_ofReal (hbound j))
  refine ⟨G, hG, ?_⟩
  rw [← toReal_eLpNorm]
  exact (ENNReal.toReal_mono (by finiteness) hbG).trans_eq (ENNReal.toReal_ofReal hC)

/-- A quantitative interior H¹ estimate starting solely from L² distributional
Poisson data. The constant is chosen from the two balls before the data are given. -/
theorem exists_poisson_interior_h1_bound {n : ℕ} (z : EuclideanSpace ℝ (Fin n))
    {r R : ℝ} (hrR : r < R) :
    ∃ C : ℝ, 0 < C ∧ ∀ u f : EuclideanSpace ℝ (Fin n) → ℝ,
      HasDistributionalLaplacianOn u f (ball z R) →
      MemLp u 2 (volume.restrict (ball z R)) → MemLp f 2 (volume.restrict (ball z R)) →
      ∃ G : EuclideanSpace ℝ (Fin n) → EuclideanSpace ℝ (Fin n),
        HasH1GradientOn u G (ball z r) ∧
        lpNorm u 2 (volume.restrict (ball z r)) + lpNorm G 2 (volume.restrict (ball z r)) ≤
          C * (lpNorm u 2 (volume.restrict (ball z R)) +
            lpNorm f 2 (volume.restrict (ball z R))) := by
  obtain ⟨η, hη, hcη, hsη, hone, hbη⟩ := exists_smooth_cutoff_one_near_compact
    (isCompact_closedBall z r) isOpen_ball (closedBall_subset_ball hrR)
  have hη1 : ContDiff ℝ 1 η := hη.of_le (by simp)
  obtain ⟨B, hB, hbgrad⟩ := exists_nonneg_bound_gradient_of_contDiff hη1 hcη
  refine ⟨2 + 2 * B, by positivity, ?_⟩
  intro u f h hu hf
  obtain ⟨G, hG, hGb⟩ := h.hasH1GradientOn_cutoff isOpen_ball measurableSet_ball hu hf
    hη1 hcη hsη (fun x => by rw [Real.norm_eq_abs, abs_of_nonneg (hbη x).1]; exact (hbη x).2)
    hB hbgrad (fun x hx => hone.self_of_nhdsSet x (ball_subset_closedBall hx))
  have hub : lpNorm u 2 (volume.restrict (ball z r)) ≤
      lpNorm u 2 (volume.restrict (ball z R)) := by
    have hm := hu.mono_measure (Measure.restrict_mono (ball_subset_ball hrR.le) le_rfl)
    rw [← toReal_eLpNorm, ← toReal_eLpNorm]
    exact ENNReal.toReal_mono hu.eLpNorm_ne_top
      (eLpNorm_mono_measure _ (Measure.restrict_mono (ball_subset_ball hrR.le) le_rfl))
  refine ⟨G, hG, ?_⟩
  have hf0 : 0 ≤ lpNorm f 2 (volume.restrict (ball z R)) := lpNorm_nonneg
  nlinarith [mul_nonneg hB hf0]

end LiquidDrop

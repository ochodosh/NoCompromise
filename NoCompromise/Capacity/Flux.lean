module

public import NoCompromise.Capacity.Potential
public import NoCompromise.Elliptic.HarmonicDerivativeTranslation
public import NoCompromise.Elliptic.KelvinRemovableCutoff

@[expose] public section

/-!
# Decay of capacitary potentials

Exterior comparison gives the reciprocal-distance bound. A scale-invariant
interior harmonic gradient estimate then gives quadratic gradient decay.
-/

noncomputable section
open Set Filter Metric MeasureTheory InnerProductSpace
open scoped Topology ENNReal NNReal Gradient
namespace LiquidDrop

/-- Nonnegative boundary values and limit zero at infinity imply nonnegativity
throughout the exterior. -/
theorem nonneg_of_exterior_harmonic
    {K : Set (EuclideanSpace ℝ (Fin 3))} (hK : IsCompact K)
    {u : EuclideanSpace ℝ (Fin 3) → ℝ} (hu : Continuous u)
    (hh : HasDistributionalLaplacianOn u (fun _ => 0) Kᶜ)
    (hb : ∀ x ∈ K, 0 ≤ u x)
    (hinf : Tendsto u (cocompact (EuclideanSpace ℝ (Fin 3))) (𝓝 0)) :
    ∀ x ∈ Kᶜ, 0 ≤ u x := by
  have h := exterior_maximum_principle (v := fun x => -u x) hK hu.neg
    (by simpa only [neg_one_mul, neg_zero] using hh.const_mul (-1))
    (fun x hx => neg_nonpos.mpr (hb x (hK.isClosed.frontier_subset
      (by simpa only [frontier_compl] using hx))))
    (by simpa only [neg_zero] using hinf.neg)
  exact fun x hx => neg_nonpos.mp (h x hx)

/-- The absolute-value reciprocal-distance estimate for a capacitary solution. -/
theorem abs_le_div_norm_of_capacitary_potential
    {K : Set (EuclideanSpace ℝ (Fin 3))} (hK : IsCompact K)
    {R₀ : ℝ} (hR₀ : 0 < R₀) (hKR : K ⊆ closedBall 0 R₀)
    (hzero : (0 : EuclideanSpace ℝ (Fin 3)) ∈ interior K)
    {u : EuclideanSpace ℝ (Fin 3) → ℝ} (hu : Continuous u)
    (hh : HasDistributionalLaplacianOn u (fun _ => 0) Kᶜ)
    (hb : ∀ x ∈ K, u x = 1)
    (hinf : Tendsto u (cocompact (EuclideanSpace ℝ (Fin 3))) (𝓝 0)) :
    ∀ x ∈ Kᶜ, |u x| ≤ R₀ / ‖x‖ := by
  have hn := nonneg_of_exterior_harmonic hK hu hh
    (fun x hx => by rw [hb x hx]; norm_num) hinf
  have he := le_div_norm_of_exterior_harmonic hK hR₀ hKR hzero hu hh
    (fun x hx => (hb x hx).le) hinf
  exact fun x hx => by rw [abs_of_nonneg (hn x hx)]; exact he x hx

/-- A universal interior gradient estimate, with the radius dependence explicit.
Only continuity on the harmonicity ball is needed. -/
theorem harmonic_gradient_bound_scaled :
    ∃ C₀ : ℝ, 0 ≤ C₀ ∧ ∀ (z : EuclideanSpace ℝ (Fin 3)) (r M : ℝ)
      (u : EuclideanSpace ℝ (Fin 3) → ℝ), 0 < r →
      ContinuousOn u (ball z r) →
      HasDistributionalLaplacianOn u (fun _ => 0) (ball z r) →
      (∀ y ∈ ball z r, |u y| ≤ M) → ‖gradient u z‖ ≤ C₀ * M / r := by
  obtain ⟨C, hC, hbound⟩ := harmonic_derivative_l2_bound
    (n := 3) (k := 1) (by decide) (r := 1 / 2) (R := 1) (by norm_num)
  let μ := volume.restrict (ball (0 : EuclideanSpace ℝ (Fin 3)) 1)
  let B := lpNorm (fun _ : EuclideanSpace ℝ (Fin 3) => (1 : ℝ)) 2 μ
  have hB : 0 ≤ B := lpNorm_nonneg
  refine ⟨2 * C * B, by positivity, ?_⟩
  intro z r M u hr hu hh hM
  have hM0 : 0 ≤ M := (abs_nonneg (u z)).trans (hM z (mem_ball_self hr))
  have hs := hh.contDiffOn_of_continuous (by decide) isOpen_ball hu
  obtain ⟨v, hv, he⟩ := exists_global_contDiff_eq_near_compact isOpen_ball
    (isCompact_closedBall z (r / 2)) (closedBall_subset_ball (half_lt_self hr)) hs
  have hae : v =ᵐ[volume.restrict (ball z (r / 2))] u := by
    filter_upwards [ae_restrict_mem measurableSet_ball] with y hy
    exact (he y (ball_subset_closedBall hy)).self_of_nhds
  have hvH := (hh.mono (ball_subset_ball (half_le_self hr.le))).congr_ae
    hae.symm EventuallyEq.rfl
  have hvLap := hvH.laplacianN_eq_zero isOpen_ball (hv.of_le (by simp))
  have hvt : ContDiff ℝ (⊤ : ℕ∞) (fun s => v (z + s)) :=
    hv.comp (contDiff_const.add contDiff_id)
  let w := fun y => v (z + (r / 2) • y)
  have hw : ContDiff ℝ (⊤ : ℕ∞) w :=
    hv.comp (contDiff_const.add (contDiff_id.const_smul (r / 2)))
  have hmap : ∀ y ∈ ball (0 : EuclideanSpace ℝ (Fin 3)) 1,
      z + (r / 2) • y ∈ ball z (r / 2) := by
    intro y hy
    have hy' : ‖y‖ < 1 := by simpa only [mem_ball, dist_zero_right] using hy
    simpa only [mem_ball, dist_eq_norm, add_sub_cancel_left, norm_smul,
      Real.norm_of_nonneg (half_pos hr).le, mul_one] using
      mul_lt_mul_of_pos_left hy' (half_pos hr)
  have hwH : HasDistributionalLaplacianOn w (fun _ => 0) (ball 0 1) := by
    apply hasDistributionalLaplacianOn_zero_of_contDiff hw isOpen_ball
    intro y hy
    change laplacianN (fun t => (fun s => v (z + s)) ((r / 2) • t)) y = 0
    rw [kelvin_laplacianN_comp_smul (hvt.of_le (by simp)),
      laplacianN_comp_add_left, hvLap (hmap y hy), mul_zero]
  have hwM : ∀ y ∈ ball (0 : EuclideanSpace ℝ (Fin 3)) 1, ‖w y‖ ≤ M := by
    intro y hy
    change |v (z + (r / 2) • y)| ≤ M
    rw [(he _ (ball_subset_closedBall (hmap y hy))).self_of_nhds]
    exact hM _ (ball_subset_ball (half_le_self hr.le) (hmap y hy))
  let : IsFiniteMeasure μ :=
    ⟨by dsimp [μ]; rw [Measure.restrict_apply_univ]; exact isBounded_ball.measure_lt_top⟩
  have hwae : ∀ᵐ y ∂μ, ‖w y‖ ≤ M := by
    filter_upwards [ae_restrict_mem measurableSet_ball] with y hy
    exact hwM y hy
  have hwL : MemLp w 2 μ := MemLp.of_bound hw.continuous.aestronglyMeasurable M hwae
  have hconst : MemLp (fun _ : EuclideanSpace ℝ (Fin 3) => M) 2 μ := memLp_const M
  have hL : lpNorm w 2 μ ≤ M * B := by
    have hb : lpNorm w 2 μ ≤ lpNorm (fun _ : EuclideanSpace ℝ (Fin 3) => M) 2 μ := by
      rw [← toReal_eLpNorm, ← toReal_eLpNorm]
      apply ENNReal.toReal_mono hconst.eLpNorm_ne_top
      apply eLpNorm_mono_ae hw.continuous.aestronglyMeasurable
      filter_upwards [hwae] with y hy
      simpa only [Real.norm_of_nonneg hM0] using hy
    convert hb using 1
    simp only [B, lpNorm_const' (by norm_num : (2 : ℝ≥0∞) ≠ 0)
      (by norm_num : (2 : ℝ≥0∞) ≠ ∞), Real.norm_of_nonneg hM0, norm_one, one_mul]
  have hder := hbound 0 w hwH hwL hw.contDiffOn 1 le_rfl
    0 (mem_ball_self (by norm_num : (0 : ℝ) < 1 / 2))
  have hgrad : gradient w 0 = (r / 2) • gradient u z := by
    change gradient (fun t => (fun s => v (z + s)) ((r / 2) • t)) 0 = _
    rw [gradient_comp_const_smul (hvt.of_le (by simp)), smul_zero]
    have ht : gradient (fun s => v (z + s)) 0 = gradient v z := by
      apply PiLp.ext
      intro i
      simp only [gradient_apply_eq_fderiv_single, fderiv_comp_add_left, add_zero]
    rw [ht, (he z (mem_closedBall_self (half_pos hr).le)).gradient_eq]
  have hnorm : ‖gradient w 0‖ = ‖iteratedFDeriv ℝ 1 w 0‖ := by
    rw [norm_iteratedFDeriv_one]
    exact (toDual ℝ (EuclideanSpace ℝ (Fin 3))).symm.norm_map _
  have hfinal : (r / 2) * ‖gradient u z‖ ≤ C * (M * B) := by
    calc
      (r / 2) * ‖gradient u z‖ = ‖gradient w 0‖ := by
        rw [hgrad, norm_smul, Real.norm_of_nonneg (half_pos hr).le]
      _ ≤ C * (M * B) := hnorm ▸ hder.trans (mul_le_mul_of_nonneg_left hL hC.le)
  apply (le_div_iff₀ hr).mpr
  nlinarith

/-- Capacitary potentials decay like reciprocal distance, and their genuine
gradients decay quadratically outside twice the enclosing radius. -/
theorem potential_decay
    {K : Set (EuclideanSpace ℝ (Fin 3))} (hK : IsCompact K)
    {R₀ : ℝ} (hR₀ : 0 < R₀) (hKR : K ⊆ closedBall 0 R₀)
    (hzero : (0 : EuclideanSpace ℝ (Fin 3)) ∈ interior K)
    {u : EuclideanSpace ℝ (Fin 3) → ℝ} (hu : Continuous u)
    (hh : HasDistributionalLaplacianOn u (fun _ => 0) Kᶜ)
    (hb : ∀ x ∈ K, u x = 1)
    (hinf : Tendsto u (cocompact (EuclideanSpace ℝ (Fin 3))) (𝓝 0)) :
    ∃ C : ℝ, (∀ x ∈ Kᶜ, |u x| ≤ R₀ / ‖x‖) ∧
      ∀ x, 2 * R₀ ≤ ‖x‖ → ‖gradient u x‖ ≤ C / ‖x‖ ^ 2 := by
  have habs := abs_le_div_norm_of_capacitary_potential hK hR₀ hKR hzero hu hh hb hinf
  obtain ⟨C₀, hC₀, hgrad⟩ := harmonic_gradient_bound_scaled
  refine ⟨4 * C₀ * R₀, habs, ?_⟩
  intro x hx
  have hxpos : 0 < ‖x‖ := by linarith
  have hnorm : ∀ y ∈ ball x (‖x‖ / 2), ‖x‖ / 2 < ‖y‖ := by
    intro y hy
    have hd : ‖x - y‖ < ‖x‖ / 2 := by
      simpa only [mem_ball, dist_eq_norm, norm_sub_rev] using hy
    have ht := norm_add_le (x - y) y
    rw [sub_add_cancel] at ht
    linarith
  have hsub : ball x (‖x‖ / 2) ⊆ Kᶜ := by
    intro y hy hyK
    have hyR : ‖y‖ ≤ R₀ := by
      simpa only [mem_closedBall, dist_zero_right] using hKR hyK
    have := hnorm y hy
    linarith
  have hM : ∀ y ∈ ball x (‖x‖ / 2), |u y| ≤ 2 * R₀ / ‖x‖ := by
    intro y hy
    have hypos : 0 < ‖y‖ := (half_pos hxpos).trans (hnorm y hy)
    apply (habs y (hsub hy)).trans
    apply (div_le_div_iff₀ hypos hxpos).mpr
    nlinarith [hnorm y hy]
  have hg := hgrad x (‖x‖ / 2) (2 * R₀ / ‖x‖) u (half_pos hxpos)
    hu.continuousOn (hh.mono hsub) hM
  convert hg using 1
  field_simp
  ring

end LiquidDrop

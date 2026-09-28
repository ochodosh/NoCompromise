import NoCompromise.Elliptic.BoundaryHolderLimits
import NoCompromise.Elliptic.CampanatoGrowthStep

/-! Supercritical normal-excess decay bounds all half-ball means, and hence
upgrades the actual gradient energy to cubic growth. -/

noncomputable section
open MeasureTheory Filter Metric Set InnerProductSpace
open scoped ENNReal NNReal Topology Gradient RealInnerProductSpace
namespace LiquidDrop
set_option maxSynthPendingDepth 8

lemma boundary_power_oscillation_normalization {K r γ : ℝ} (hK : 0 ≤ K) (hr : 0 < r) :
    K * r ^ (3 + 2 * γ) =
      (Real.sqrt (K / volume.real (boundaryHalfBall 1)) * r ^ γ) ^ 2 *
        volume.real (boundaryHalfBall r) := by
  have hV : 0 < volume.real (boundaryHalfBall 1) :=
    ENNReal.toReal_pos (boundaryHalfBall_volume_pos zero_lt_one).ne'
      (boundaryHalfBall_volume_lt_top 1).ne
  rw [boundaryHalfBall_real_volume hr, mul_pow, Real.sq_sqrt (div_nonneg hK hV.le),
    campanato_square_rpow hr.le γ, Real.rpow_add hr, Real.rpow_ofNat]
  field_simp

/-- Positive excess decay above the volume exponent produces a uniform cubic
energy bound. No bounded-gradient or boundary-value premise is used. -/
theorem boundary_energy_cubic_of_normal_decay {K γ R M : ℝ}
    (hK : 0 ≤ K) (hγ : 0 < γ) (hR : 0 < R) (hM : 0 ≤ M) :
    ∃ P : ℝ, 0 ≤ P ∧ ∀ F : EuclideanSpace ℝ (Fin 3) → EuclideanSpace ℝ (Fin 3),
      MemLp F 2 (volume.restrict (boundaryHalfBall R)) →
      (∫ x in boundaryHalfBall R, ‖F x‖ ^ 2) ≤ M →
      (∀ r ∈ Ioc 0 R,
        boundaryNormalExcess (EuclideanSpace.single (Fin.last 2) 1) F
          (volume.restrict (boundaryHalfBall r)) ≤ K * r ^ (3 + 2 * γ)) →
      ∀ r ∈ Ioc 0 R, (∫ x in boundaryHalfBall r, ‖F x‖ ^ 2) ≤ P * r ^ (3 : ℝ) := by
  let B := Real.sqrt (K / volume.real (boundaryHalfBall 1))
  obtain ⟨C, hC, hlimit⟩ := boundary_average_limit_constant (Real.sqrt_nonneg _) hγ
    (B := B)
  let Q := Real.sqrt (M / volume.real (boundaryHalfBall R)) + 2 * C * R ^ γ
  let P := 2 * K * R ^ (2 * γ) + 2 * Q ^ 2 * volume.real (boundaryHalfBall 1)
  have hQ : 0 ≤ Q := by dsimp [Q]; positivity
  have hP : 0 ≤ P := by dsimp [P]; positivity
  refine ⟨P, hP, ?_⟩
  intro F hF hE hosc
  obtain ⟨v, _, hv⟩ := hlimit F R hR hF (fun r hr =>
    (hosc r hr).trans_eq (boundary_power_oscillation_normalization hK hr.1))
  let : IsFiniteMeasure (volume.restrict (boundaryHalfBall R)) :=
    ⟨by simpa using boundaryHalfBall_volume_lt_top R⟩
  have hVR : 0 < volume.real (boundaryHalfBall R) :=
    ENNReal.toReal_pos (boundaryHalfBall_volume_pos hR).ne' (boundaryHalfBall_volume_lt_top R).ne
  have hmean : ‖⨍ x in boundaryHalfBall R, F x‖ ≤
      Real.sqrt (M / volume.real (boundaryHalfBall R)) := by
    apply (sq_le_sq₀ (norm_nonneg _) (Real.sqrt_nonneg _)).mp
    rw [Real.sq_sqrt (div_nonneg hM hVR.le)]
    have hh := campanato_norm_average_sq_le
      (by simpa using (boundaryHalfBall_volume_pos hR).ne') hF
    simp only [Measure.real, Measure.restrict_apply_univ] at hh
    change ‖⨍ x in boundaryHalfBall R, F x‖ ^ 2 ≤
      (volume.real (boundaryHalfBall R))⁻¹ * ∫ x in boundaryHalfBall R, ‖F x‖ ^ 2 at hh
    apply hh.trans
    rw [div_eq_mul_inv, mul_comm M]
    exact mul_le_mul_of_nonneg_left hE (inv_nonneg.mpr hVR.le)
  have hvbound : ‖v‖ ≤ Real.sqrt (M / volume.real (boundaryHalfBall R)) + C * R ^ γ := by
    have hh := hv R ⟨hR, le_rfl⟩
    have hn := norm_le_insert' v (⨍ x in boundaryHalfBall R, F x)
    rw [norm_sub_rev] at hh
    linarith
  intro r hr
  have hrpos : 0 < r := hr.1
  let μ := volume.restrict (boundaryHalfBall r)
  let : IsFiniteMeasure μ := ⟨by simpa [μ] using boundaryHalfBall_volume_lt_top r⟩
  have hFr := hF.mono_measure (Measure.restrict_mono (boundaryHalfBall_mono hr.2) le_rfl)
  let m := ⨍ x in boundaryHalfBall r, F x
  have hmr : ‖m‖ ≤ Q := by
    have hh := hv r hr
    have hn := norm_le_insert' m v
    have hp := mul_le_mul_of_nonneg_left
      (Real.rpow_le_rpow hr.1.le hr.2 hγ.le) hC
    dsimp [Q]
    linarith
  have he := campanato_integral_norm_sq_le_twice hFr (memLp_const m)
  have hvar := (boundary_variance_le_normal_excess hFr
    (EuclideanSpace.single (Fin.last 2) 1)).trans (hosc r hr)
  have hi : (∫ _x in boundaryHalfBall r, ‖m‖ ^ 2) =
      volume.real (boundaryHalfBall r) * ‖m‖ ^ 2 := by
    simp only [integral_const, smul_eq_mul, Measure.real, Measure.restrict_apply_univ]
  rw [hi, boundaryHalfBall_real_volume hr.1] at he
  have hmsq : ‖m‖ ^ 2 ≤ Q ^ 2 := (sq_le_sq₀ (norm_nonneg _) hQ).mpr hmr
  have hpow : K * r ^ (3 + 2 * γ) ≤ K * R ^ (2 * γ) * r ^ (3 : ℕ) := by
    rw [Real.rpow_add hr.1, Real.rpow_ofNat]
    have hp := Real.rpow_le_rpow hr.1.le hr.2 (show 0 ≤ 2 * γ by positivity)
    nlinarith [mul_le_mul_of_nonneg_left hp (show 0 ≤ K * r ^ (3 : ℕ) by positivity)]
  have hnorm := mul_le_mul_of_nonneg_left hmsq
    (show 0 ≤ r ^ (3 : ℕ) * volume.real (boundaryHalfBall 1) by positivity)
  rw [Real.rpow_ofNat]
  dsimp [P]
  nlinarith only [he, hvar, hpow, hnorm]

end LiquidDrop

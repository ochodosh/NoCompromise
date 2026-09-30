module

public import NoCompromise.CapacitaryK.QuadrupoleMean
public import NoCompromise.Elliptic.HarmonicDerivativeTranslation
public import NoCompromise.CapacitaryK.HarmonicSmooth

@[expose] public section

/-!
# Differentiated translated capacitary remainders

Scaled interior estimates for the differentiated remainder in Chapter 31,
`lem:K-normalization`.
-/

noncomputable section

open Set Filter Metric InnerProductSpace MeasureTheory
open scoped Topology Gradient RealInnerProductSpace ENNReal NNReal

namespace LiquidDrop.CapacitaryK

local notation "E₃" => EuclideanSpace ℝ (Fin 3)

/-- Interior harmonic derivative estimates, with the radius dependence explicit. -/
theorem harmonic_scaled_iteratedFDeriv_bound (k : ℕ) :
    ∃ c : ℝ, 0 < c ∧ ∀ (W : E₃ → ℝ) (x : E₃) (ρ ε : ℝ), 0 < ρ →
      ContDiffOn ℝ (⊤ : ℕ∞) W (ball x ρ) → (∀ y ∈ ball x ρ, laplacianN W y = 0) →
      (∀ y ∈ ball x ρ, |W y| ≤ ε) → ‖iteratedFDeriv ℝ k W x‖ ≤ c * ε / ρ ^ k := by
  obtain ⟨C, hC, hbound⟩ := harmonic_derivative_l2_bound
    (n := 3) (k := k) (by decide) (r := 1 / 2) (R := 1) (by norm_num)
  let μ := volume.restrict (ball (0 : E₃) 1)
  let B := lpNorm (fun _ : E₃ => (1 : ℝ)) 2 μ
  have hB : 0 ≤ B := lpNorm_nonneg
  refine ⟨2 ^ k * C * (B + 1), by positivity, ?_⟩
  intro W x ρ ε hρ hW hΔ hε
  have hε0 : 0 ≤ ε := (abs_nonneg (W x)).trans (hε x (mem_ball_self hρ))
  obtain ⟨v, hv, he⟩ := exists_global_contDiff_eq_near_compact isOpen_ball
    (isCompact_closedBall x (ρ / 2)) (closedBall_subset_ball (half_lt_self hρ)) hW
  have hvLap : ∀ y ∈ ball x (ρ / 2), laplacianN v y = 0 := by
    intro y hy
    rw [laplacianN_congr_nhds (he y (ball_subset_closedBall hy))]
    exact hΔ y (ball_subset_ball (half_le_self hρ.le) hy)
  have hvt : ContDiff ℝ (⊤ : ℕ∞) (fun s => v (x + s)) :=
    hv.comp (contDiff_const.add contDiff_id)
  let w := fun y => v (x + (ρ / 2) • y)
  have hw : ContDiff ℝ (⊤ : ℕ∞) w :=
    hv.comp (contDiff_const.add (contDiff_id.const_smul (ρ / 2)))
  have hmap : ∀ y ∈ ball (0 : E₃) 1, x + (ρ / 2) • y ∈ ball x (ρ / 2) := by
    intro y hy
    have hy' : ‖y‖ < 1 := by simpa only [mem_ball, dist_zero_right] using hy
    simpa only [mem_ball, dist_eq_norm, add_sub_cancel_left, norm_smul,
      Real.norm_of_nonneg (half_pos hρ).le, mul_one] using
      mul_lt_mul_of_pos_left hy' (half_pos hρ)
  have hwH : HasDistributionalLaplacianOn w (fun _ => 0) (ball 0 1) := by
    apply hasDistributionalLaplacianOn_zero_of_contDiff hw isOpen_ball
    intro y hy
    change laplacianN (fun t => (fun s => v (x + s)) ((ρ / 2) • t)) y = 0
    rw [kelvin_laplacianN_comp_smul (hvt.of_le (by simp)),
      laplacianN_comp_add_left, hvLap _ (hmap y hy), mul_zero]
  have hwM : ∀ y ∈ ball (0 : E₃) 1, ‖w y‖ ≤ ε := by
    intro y hy
    change |v (x + (ρ / 2) • y)| ≤ ε
    rw [(he _ (ball_subset_closedBall (hmap y hy))).self_of_nhds]
    exact hε _ (ball_subset_ball (half_le_self hρ.le) (hmap y hy))
  let : IsFiniteMeasure μ :=
    ⟨by dsimp [μ]; rw [Measure.restrict_apply_univ]; exact isBounded_ball.measure_lt_top⟩
  have hwae : ∀ᵐ y ∂μ, ‖w y‖ ≤ ε := by
    filter_upwards [ae_restrict_mem measurableSet_ball] with y hy
    exact hwM y hy
  have hwL : MemLp w 2 μ := MemLp.of_bound hw.continuous.aestronglyMeasurable ε hwae
  have hL : lpNorm w 2 μ ≤ ε * B := by
    have hconst : MemLp (fun _ : E₃ => ε) 2 μ := memLp_const ε
    have hb : lpNorm w 2 μ ≤ lpNorm (fun _ : E₃ => ε) 2 μ := by
      rw [← toReal_eLpNorm, ← toReal_eLpNorm]
      apply ENNReal.toReal_mono hconst.eLpNorm_ne_top
      apply eLpNorm_mono_ae hw.continuous.aestronglyMeasurable
      filter_upwards [hwae] with y hy
      simpa only [Real.norm_of_nonneg hε0] using hy
    simpa only [B, lpNorm_const' (by norm_num : (2 : ℝ≥0∞) ≠ 0)
      (by norm_num : (2 : ℝ≥0∞) ≠ ∞), Real.norm_of_nonneg hε0, norm_one, one_mul] using hb
  have hder := hbound 0 w hwH hwL hw.contDiffOn k le_rfl
    0 (mem_ball_self (by norm_num : (0 : ℝ) < 1 / 2))
  have hder' : ‖iteratedFDeriv ℝ k w 0‖ ≤ C * (ε * (B + 1)) :=
    hder.trans (mul_le_mul_of_nonneg_left
      (hL.trans (mul_le_mul_of_nonneg_left (by linarith : B ≤ B + 1) hε0)) hC.le)
  let A : E₃ →L[ℝ] E₃ := (ρ / 2)⁻¹ • ContinuousLinearMap.id ℝ E₃
  have hcomp : w ∘ A = fun y => v (x + y) := by
    funext y
    change v (x + (ρ / 2) • ((ρ / 2)⁻¹ • y)) = _
    rw [smul_smul, mul_inv_cancel₀ (ne_of_gt (half_pos hρ)), one_smul]
  have hd : iteratedFDeriv ℝ k W x =
      (iteratedFDeriv ℝ k w 0).compContinuousLinearMap (fun _ => A) := by
    have ht := A.iteratedFDeriv_comp_right hw 0 (i := k) (by simp)
    rw [hcomp, iteratedFDeriv_comp_add_left, add_zero] at ht
    simpa only [map_zero] using
      ((he x (mem_closedBall_self (half_pos hρ).le)).iteratedFDeriv ℝ k).self_of_nhds.symm.trans ht
  have hA : ‖A‖ = (ρ / 2)⁻¹ := by
    simp [A, norm_smul, abs_of_pos hρ]
  calc
    ‖iteratedFDeriv ℝ k W x‖ ≤ ‖iteratedFDeriv ℝ k w 0‖ * ((ρ / 2)⁻¹) ^ k := by
      rw [hd]
      simpa only [hA, Finset.prod_const, Finset.card_univ, Fintype.card_fin] using
        (iteratedFDeriv ℝ k w 0).norm_compContinuousLinearMap_le (fun _ => A)
    _ ≤ (C * (ε * (B + 1))) * ((ρ / 2)⁻¹) ^ k :=
      mul_le_mul_of_nonneg_right hder' (by positivity)
    _ = (2 ^ k * C * (B + 1)) * ε / ρ ^ k := by
      rw [inv_div, div_pow]
      ring

/-- The remainder after translating by the normalized dipole center. -/
def kelvinTranslatedRemainder (u v : E₃ → ℝ) (x : E₃) : ℝ :=
  u (x + (v 0)⁻¹ • gradient v 0) - v 0 / ‖x‖ - kelvinTranslatedQuadrupole v x / ‖x‖ ^ 5

theorem translated_quadrupole_contDiff (v : E₃ → ℝ) :
    ContDiff ℝ (⊤ : ℕ∞) (kelvinTranslatedQuadrupole v) := by
  have hi : ContDiff ℝ (⊤ : ℕ∞) (fun x : E₃ => ⟪gradient v 0, x⟫) :=
    contDiff_const.inner ℝ contDiff_id
  have hB : ContDiff ℝ (⊤ : ℕ∞) (fun x : E₃ => fderiv ℝ (fderiv ℝ v) 0 x x) :=
    (fderiv ℝ (fderiv ℝ v) 0).contDiff.clm_apply contDiff_id
  exact (((contDiff_const.mul (hi.pow 2)).sub
    (contDiff_const.mul (contDiff_norm_sq ℝ))).neg.div_const _).add (contDiff_const.mul hB)

private theorem translated_model_eq_kelvin (v : E₃ → ℝ) (x : E₃) :
    v 0 / ‖x‖ + kelvinTranslatedQuadrupole v x / ‖x‖ ^ 5 =
      kelvinTransform (fun y => v 0 + kelvinTranslatedQuadrupole v y) x := by
  simp only [kelvinTransform, kelvinInversion, kelvinTranslatedQuadrupole_smul,
    div_eq_mul_inv, inv_pow]
  ring

private theorem translated_remainder_smooth_harmonic
    {K : Set E₃} (hK : IsCompact K) {R₀ : ℝ} (hR₀ : 0 < R₀)
    (hKR : K ⊆ closedBall 0 R₀) {u v : E₃ → ℝ} (hu : Continuous u)
    (hh : HasDistributionalLaplacianOn u (fun _ => 0) Kᶜ)
    (hQ : ∀ x : E₃, laplacianN (kelvinTranslatedQuadrupole v) x = 0) :
    ContDiffOn ℝ (⊤ : ℕ∞) (kelvinTranslatedRemainder u v)
      {x | R₀ + ‖(v 0)⁻¹ • gradient v 0‖ < ‖x‖} ∧
    (∀ x, R₀ + ‖(v 0)⁻¹ • gradient v 0‖ < ‖x‖ →
      laplacianN (kelvinTranslatedRemainder u v) x = 0) := by
  let z := (v 0)⁻¹ • gradient v 0
  let U : Set E₃ := {x | R₀ + ‖z‖ < ‖x‖}
  have hU : IsOpen U := isOpen_lt continuous_const continuous_norm
  have hmap : ∀ x ∈ U, z + x ∈ Kᶜ := by
    intro x hx hxK
    have hxR : ‖z + x‖ ≤ R₀ := by
      simpa only [mem_closedBall, dist_zero_right] using hKR hxK
    have ht : ‖x‖ ≤ ‖z + x‖ + ‖z‖ := by
      simpa only [add_sub_cancel_left] using norm_sub_le (z + x) z
    have ht' : ‖x‖ ≤ R₀ + ‖z‖ := by linarith
    exact (not_lt_of_ge ht') hx
  have hx0 : ∀ x ∈ U, x ≠ 0 := by
    intro x hx he
    subst x
    have hz := norm_nonneg z
    change R₀ + ‖z‖ < ‖(0 : E₃)‖ at hx
    rw [norm_zero] at hx
    linarith
  have hsu := capacitary_potential_contDiffOn hK hu hh
  have hΔu := kelvin_laplacianN_eq_zero_of_distributional hK.isClosed.isOpen_compl
    hu.continuousOn hh
  have htu : ContDiffOn ℝ (⊤ : ℕ∞) (fun x => u (z + x)) U :=
    hsu.comp (contDiff_const.add contDiff_id).contDiffOn hmap
  have hhu : HasDistributionalLaplacianOn (fun x => u (z + x)) (fun _ => 0) U := by
    apply hasDistributionalLaplacianOn_zero_of_contDiffOn hU (htu.of_le (by simp))
    intro x hx
    rw [laplacianN_comp_add_left]
    exact hΔu _ (hmap x hx)
  let p : E₃ → ℝ := fun y => v 0 + kelvinTranslatedQuadrupole v y
  have hp : ContDiff ℝ (⊤ : ℕ∞) p := contDiff_const.add (translated_quadrupole_contDiff v)
  have hΔp : ∀ x, laplacianN p x = 0 := by
    have hd (i : Fin 3) : poissonCoordinateDerivative i p =
        poissonCoordinateDerivative i (kelvinTranslatedQuadrupole v) := by
      funext y
      simp only [p, poissonCoordinateDerivative, fderiv_const_add]
    intro x
    simpa only [laplacianN, hd] using hQ x
  have hsm : ContDiffOn ℝ (⊤ : ℕ∞) (kelvinTransform p) U := by
    apply hU.contDiffOn_iff.mpr
    intro x hx
    exact ((contDiffAt_id.norm ℝ (hx0 x hx)).inv (norm_ne_zero_iff.mpr (hx0 x hx))).mul
      (hp.contDiffAt.comp x (contDiffAt_kelvinInversion (hx0 x hx)))
  have hhm : HasDistributionalLaplacianOn (kelvinTransform p) (fun _ => 0) U := by
    apply hasDistributionalLaplacianOn_zero_of_contDiffOn hU (hsm.of_le (by simp))
    intro x hx
    rw [laplacianN_kelvinTransform (hx0 x hx) (hp.contDiffAt.of_le (by simp)), hΔp,
      mul_zero]
  have he : kelvinTranslatedRemainder u v = fun x => u (z + x) - kelvinTransform p x := by
    funext x
    rw [← translated_model_eq_kelvin]
    simp only [kelvinTranslatedRemainder, z, add_comm, sub_sub]
  have hs : ContDiffOn ℝ (⊤ : ℕ∞) (kelvinTranslatedRemainder u v) U := by
    rw [he]
    exact htu.sub hsm
  refine ⟨hs, ?_⟩
  apply kelvin_laplacianN_eq_zero_of_distributional hU hs.continuousOn
  rw [he]
  simpa only [sub_self] using hhu.sub hhm

private theorem harmonic_exterior_derivative_decay {W : E₃ → ℝ} {R M : ℝ}
    (hR : 0 < R) (hM : 0 ≤ M)
    (hs : ContDiffOn ℝ (⊤ : ℕ∞) W {x | R < ‖x‖})
    (hΔ : ∀ x, R < ‖x‖ → laplacianN W x = 0)
    (hb : ∀ x, R ≤ ‖x‖ → |W x| ≤ M / ‖x‖ ^ 4) :
    ∃ M' : ℝ, ∀ x : E₃, 2 * R ≤ ‖x‖ →
      |W x| ≤ M' / ‖x‖ ^ 4 ∧
      ‖fderiv ℝ W x‖ ≤ M' / ‖x‖ ^ 5 ∧
      ‖fderiv ℝ (fderiv ℝ W) x‖ ≤ M' / ‖x‖ ^ 6 := by
  obtain ⟨c₁, hc₁, hb₁⟩ := harmonic_scaled_iteratedFDeriv_bound 1
  obtain ⟨c₂, hc₂, hb₂⟩ := harmonic_scaled_iteratedFDeriv_bound 2
  let M' := M + 32 * c₁ * M + 64 * c₂ * M
  have hM₀ : M ≤ M' := by
    dsimp [M']
    nlinarith [mul_nonneg hc₁.le hM, mul_nonneg hc₂.le hM]
  have hM₁ : 32 * c₁ * M ≤ M' := by dsimp [M']; nlinarith [mul_nonneg hc₂.le hM]
  have hM₂ : 64 * c₂ * M ≤ M' := by dsimp [M']; nlinarith [mul_nonneg hc₁.le hM]
  refine ⟨M', fun x hx => ?_⟩
  have hxpos : 0 < ‖x‖ := by linarith
  have hhalf : R ≤ ‖x‖ / 2 := by linarith
  have hball : ∀ y ∈ ball x (‖x‖ / 2), ‖x‖ / 2 < ‖y‖ := by
    intro y hy
    have ht := norm_sub_norm_le x y
    rw [mem_ball, dist_eq_norm, norm_sub_rev] at hy
    linarith
  have hsub : ball x (‖x‖ / 2) ⊆ {y | R < ‖y‖} := by
    intro y hy
    exact hhalf.trans_lt (hball y hy)
  have hlocal : ∀ y ∈ ball x (‖x‖ / 2), |W y| ≤ 16 * M / ‖x‖ ^ 4 := by
    intro y hy
    have hny : ‖x‖ / 2 ≤ ‖y‖ := (hball y hy).le
    calc
      |W y| ≤ M / ‖y‖ ^ 4 := hb y (hhalf.trans hny)
      _ ≤ M / (‖x‖ / 2) ^ 4 := div_le_div_of_nonneg_left hM (by positivity)
        (pow_le_pow_left₀ (by positivity) hny 4)
      _ = 16 * M / ‖x‖ ^ 4 := by ring
  have hd₁ := hb₁ W x (‖x‖ / 2) (16 * M / ‖x‖ ^ 4) (half_pos hxpos)
    (hs.mono hsub) (fun y hy => hΔ y (hsub hy)) hlocal
  have hd₂ := hb₂ W x (‖x‖ / 2) (16 * M / ‖x‖ ^ 4) (half_pos hxpos)
    (hs.mono hsub) (fun y hy => hΔ y (hsub hy)) hlocal
  have he₁ : c₁ * (16 * M / ‖x‖ ^ 4) / (‖x‖ / 2) ^ 1 =
      (32 * c₁ * M) / ‖x‖ ^ 5 := by ring
  have he₂ : c₂ * (16 * M / ‖x‖ ^ 4) / (‖x‖ / 2) ^ 2 =
      (64 * c₂ * M) / ‖x‖ ^ 6 := by ring
  rw [norm_iteratedFDeriv_one, he₁] at hd₁
  have hn₂ : ‖iteratedFDeriv ℝ 2 W x‖ = ‖fderiv ℝ (fderiv ℝ W) x‖ := by
    rw [← norm_iteratedFDeriv_one (fderiv ℝ W), norm_iteratedFDeriv_fderiv]
  rw [hn₂, he₂] at hd₂
  exact ⟨(hb x (by linarith)).trans (div_le_div_of_nonneg_right hM₀ (by positivity)),
    hd₁.trans (div_le_div_of_nonneg_right hM₁ (by positivity)),
    hd₂.trans (div_le_div_of_nonneg_right hM₂ (by positivity))⟩

/-- `lem:K-normalization`: the translated remainder and its first two derivatives
decay with orders four, five, and six, respectively. -/
theorem capacitary_translated_remainder_derivatives
    {K : Set E₃} (hK : IsCompact K) {R₀ : ℝ} (hR₀ : 0 < R₀)
    (hKR : K ⊆ closedBall 0 R₀) (hzero : (0 : E₃) ∈ interior K)
    {u : E₃ → ℝ} (hu : Continuous u)
    (hh : HasDistributionalLaplacianOn u (fun _ => 0) Kᶜ)
    (hb : ∀ x ∈ K, u x = 1) (hinf : Tendsto u (cocompact E₃) (𝓝 0)) :
    ∃ (v : E₃ → ℝ) (r : ℝ), 0 < r ∧ ContDiffOn ℝ (⊤ : ℕ∞) v (ball 0 r) ∧
      EqOn v (kelvinTransform u) (ball 0 r \ {0}) ∧ (∀ y ∈ ball 0 r, laplacianN v y = 0) ∧
      0 < v 0 ∧
      Continuous (kelvinTranslatedQuadrupole v) ∧
      (∀ (c : ℝ) (x : E₃),
        kelvinTranslatedQuadrupole v (c • x) = c ^ 2 * kelvinTranslatedQuadrupole v x) ∧
      (∀ x : E₃, laplacianN (kelvinTranslatedQuadrupole v) x = 0) ∧
      (∫ θ, kelvinTranslatedQuadrupole v (θ : E₃) ∂(volume : Measure E₃).toSphere = 0) ∧
      ∃ R M : ℝ, 0 < R ∧
        ContDiffOn ℝ (⊤ : ℕ∞) (kelvinTranslatedRemainder u v) {x | R < ‖x‖} ∧
        ∀ x : E₃, R ≤ ‖x‖ →
          |kelvinTranslatedRemainder u v x| ≤ M / ‖x‖ ^ 4 ∧
          ‖fderiv ℝ (kelvinTranslatedRemainder u v) x‖ ≤ M / ‖x‖ ^ 5 ∧
          ‖fderiv ℝ (fderiv ℝ (kelvinTranslatedRemainder u v)) x‖ ≤ M / ‖x‖ ^ 6 := by
  obtain ⟨v, r, hr, hv, he, hΔv, hv0, hQc, hQs, hQΔ, hQmean, R, M, hR, hval⟩ :=
    capacitary_translated_expansion_normalized hK hR₀ hKR hzero hu hh hb hinf
  obtain ⟨hs, hΔ⟩ := translated_remainder_smooth_harmonic hK hR₀ hKR hu hh hQΔ
  let R₁ := max R (R₀ + ‖(v 0)⁻¹ • gradient v 0‖)
  have hR₁ : 0 < R₁ := hR.trans_le (le_max_left _ _)
  have hs₁ : ContDiffOn ℝ (⊤ : ℕ∞) (kelvinTranslatedRemainder u v) {x | R₁ < ‖x‖} := by
    apply hs.mono
    intro x hx
    change R₀ + ‖(v 0)⁻¹ • gradient v 0‖ < ‖x‖
    exact (le_max_right _ _).trans_lt hx
  obtain ⟨M', hder⟩ := harmonic_exterior_derivative_decay hR₁ (le_max_right M 0) hs₁
    (fun x hx => hΔ x ((le_max_right _ _).trans_lt hx)) (by
      intro x hx
      exact (hval x ((le_max_left _ _).trans hx)).trans
        (div_le_div_of_nonneg_right (le_max_left M 0) (by positivity)))
  refine ⟨v, r, hr, hv, he, hΔv, hv0, hQc, hQs, hQΔ, hQmean,
    2 * R₁, M', by positivity, ?_, hder⟩
  exact hs₁.mono (fun x hx => by change R₁ < ‖x‖; change 2 * R₁ < ‖x‖ at hx; linarith)

end LiquidDrop.CapacitaryK

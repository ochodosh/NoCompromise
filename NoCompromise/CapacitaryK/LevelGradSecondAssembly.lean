import NoCompromise.CapacitaryK.LevelGradSpatialDecay

/-!
# Second angular derivatives of the capacitary gradient-length expansion

The spatial remainder estimates and the radius expansion give the gradient-length
remainder uniformly through two ambient derivatives of its angular extension.
-/

noncomputable section

open Set Filter Metric InnerProductSpace
open scoped Topology Gradient RealInnerProductSpace

namespace LiquidDrop.CapacitaryK

set_option maxHeartbeats 600000 in
-- The assembly identifies three Kelvin extensions and combines their uniform constants.
/-- The gradient-length remainder on small capacitary levels is uniformly `O(t⁵)`
in value and in its first two ambient angular derivatives. -/
theorem capacitary_level_gradNorm_derivatives
    {K : Set E3} (hK : IsCompact K) {R₀ : ℝ} (hR₀ : 0 < R₀)
    (hKR : K ⊆ Metric.closedBall 0 R₀) (hzero : (0 : E3) ∈ interior K)
    {u : E3 → ℝ} (hu : Continuous u)
    (hh : HasDistributionalLaplacianOn u (fun _ => 0) Kᶜ)
    (hb : ∀ x ∈ K, u x = 1) (hinf : Tendsto u (cocompact E3) (𝓝 0)) :
    ∃ (v : E3 → ℝ) (r : ℝ), 0 < r ∧ ContDiffOn ℝ (⊤ : ℕ∞) v (Metric.ball 0 r) ∧
      EqOn v (kelvinTransform u) (Metric.ball 0 r \ {0}) ∧ 0 < v 0 ∧
      ∃ A : ℝ, 0 ≤ A ∧ ∀ᶠ t in 𝓝[>] (0 : ℝ), ∀ ρ : E3 → ℝ,
        (∀ y : E3, y ≠ 0 → ρ y = ρ (‖y‖⁻¹ • y)) →
        (∀ θ : E3, ‖θ‖ = 1 →
          0 < ρ θ ∧ u (ρ θ • θ + (v 0)⁻¹ • gradient v 0) = t) →
        ContDiffOn ℝ (⊤ : ℕ∞) ρ {y | y ≠ 0} ∧
        ∀ θ : E3, ‖θ‖ = 1 →
          |levelGradRemainder u v t ρ θ| ≤ A * t ^ 5 ∧
          ‖fderiv ℝ (levelGradRemainder u v t ρ) θ‖ ≤ A * t ^ 5 ∧
          ‖fderiv ℝ (fderiv ℝ (levelGradRemainder u v t ρ)) θ‖ ≤ A * t ^ 5 := by
  obtain ⟨v, r, hr, hv, he, hv0, R, M, hR, hM, hW, hWb⟩ :=
    levelGradDecay_capacitary_spatial_derivatives hK hR₀ hKR hzero hu hh hb hinf
  obtain ⟨vg, rg, hrg, hvg, heg, _, Ag, hAg, hevG⟩ :=
    capacitary_level_gradNorm_first_derivative hK hR₀ hKR hzero hu hh hb hinf
  obtain ⟨h0g, hgg, hQg⟩ := kelvin_extension_data_eq hrg hr hvg hv heg he
  have hremG (t : ℝ) (ρ : E3 → ℝ) :
      levelGradRemainder u vg t ρ = levelGradRemainder u v t ρ := by
    funext y
    simp only [levelGradRemainder, h0g, hgg, hQg]
  simp only [hremG, h0g, hgg] at hevG
  obtain ⟨vr, rr, hrr, hvr, her, _, Ar, hAr, hevR⟩ :=
    capacitary_level_radius_derivatives hK hR₀ hKR hzero hu hh hb hinf
  obtain ⟨h0r, hgr, hQr⟩ := kelvin_extension_data_eq hrr hr hvr hv her he
  have hremR (t : ℝ) (ρ : E3 → ℝ) :
      levelRadiusRemainder vr t ρ = levelRadiusRemainder v t ρ := by
    funext y
    simp only [levelRadiusRemainder, h0r, hQr]
  simp only [hremR, h0r, hgr] at hevR
  obtain ⟨B, hB, hBb⟩ := farQuadrupole_derivative_bounds
    (translated_quadrupole_contDiff v) (kelvinTranslatedQuadrupole_smul v)
  let L := Ar + B / (v 0) ^ 2
  let P := (Ar + 10 * B / (v 0) ^ 2) * v 0
  let A₂ := (16 * v 0 * (Ar * (v 0) ^ 2) + 59 * (2 * L) * (10 * B) +
    1152 * (10 * B) * P + (96 * v 0 + 960 * (10 * B)) * P ^ 2 +
    32 * M * ((P + 2) ^ 2 + (5 * P + 6))) / (v 0) ^ 5
  have hL : 0 ≤ L := by dsimp [L]; positivity
  have hP : 0 ≤ P := by dsimp [P]; positivity
  have hA₂ : 0 ≤ A₂ := by dsimp [A₂]; positivity
  refine ⟨v, r, hr, hv, he, hv0, max Ag A₂, hAg.trans (le_max_left _ _), ?_⟩
  have eC := level_eventually_lt_of_continuous (g := fun t => t / v 0)
    (continuous_id.div_const _) (by simp) one_pos
  have eL := level_eventually_lt_of_continuous (g := fun t => t * L)
    (continuous_id.mul continuous_const) (by simp) (by positivity : 0 < v 0 / 2)
  have eR := level_eventually_lt_of_continuous (g := fun t => t * (R + 1 + L))
    (continuous_id.mul continuous_const) (by simp) hv0
  filter_upwards [hevG, hevR, Ioo_mem_nhdsGT one_pos, eC, eL, eR]
    with t htG htR htr htC htL htFar
  have ht : 0 < t := htr.1
  have ht1 : t ≤ 1 := htr.2.le
  intro ρ hhom hroot
  obtain ⟨hsmooth, hρb⟩ := htR ρ hhom hroot
  obtain ⟨_, hGb⟩ := htG ρ hhom hroot
  refine ⟨hsmooth, fun θ hθ => ?_⟩
  obtain ⟨hGval, hGder⟩ := hGb θ hθ
  have hAg' := mul_le_mul_of_nonneg_right (le_max_left Ag A₂) (pow_nonneg ht.le 5)
  refine ⟨hGval.trans hAg', hGder.trans hAg', ?_⟩
  obtain ⟨hs, _⟩ := hroot θ hθ
  have hθ0 : θ ≠ 0 := by rintro rfl; simp at hθ
  obtain ⟨hρval, hρder, hρhess⟩ := hρb θ hθ
  have hqval : |kelvinTranslatedQuadrupole v θ| ≤ B := by
    simpa only [farQuadrupole, hθ, one_pow, div_one] using (hBb θ hθ0).1
  have hqder : ‖fderiv ℝ (farQuadrupole (kelvinTranslatedQuadrupole v)) θ‖ ≤ B := by
    simpa only [hθ, one_pow, div_one] using (hBb θ hθ0).2.1
  have hqhess : ‖fderiv ℝ (fderiv ℝ (farQuadrupole
      (kelvinTranslatedQuadrupole v))) θ‖ ≤ B := by
    simpa only [hθ, one_pow, div_one] using (hBb θ hθ0).2.2
  have hρval' : |ρ θ - (v 0 / t + t * kelvinTranslatedQuadrupole v θ / (v 0) ^ 2)| ≤
      Ar * t ^ 2 := by
    simpa only [levelRadiusRemainder, hθ, inv_one, one_smul] using hρval
  have hcoarse : |ρ θ - v 0 / t| ≤ L := by
    have hterm : |t * kelvinTranslatedQuadrupole v θ / (v 0) ^ 2| ≤ B / (v 0) ^ 2 := by
      rw [abs_div, abs_mul, abs_of_pos ht, abs_of_nonneg (sq_nonneg (v 0))]
      gcongr
      calc
        t * |kelvinTranslatedQuadrupole v θ| ≤ 1 * B :=
          mul_le_mul ht1 hqval (abs_nonneg _) (by norm_num)
        _ = B := one_mul B
    calc
      _ = |(ρ θ - (v 0 / t + t * kelvinTranslatedQuadrupole v θ / (v 0) ^ 2)) +
          t * kelvinTranslatedQuadrupole v θ / (v 0) ^ 2| := by congr 1; ring
      _ ≤ |ρ θ - (v 0 / t + t * kelvinTranslatedQuadrupole v θ / (v 0) ^ 2)| +
          |t * kelvinTranslatedQuadrupole v θ / (v 0) ^ 2| := abs_add_le _ _
      _ ≤ Ar * t ^ 2 + B / (v 0) ^ 2 := add_le_add hρval' hterm
      _ ≤ L := by
        dsimp [L]
        have ht2 : t ^ 2 ≤ 1 := by nlinarith
        nlinarith
  have hlower : v 0 / t - L ≤ ρ θ := by have := (abs_le.mp hcoarse).1; linarith
  have hhalf : v 0 / (2 * t) ≤ ρ θ := by
    have hLt : L ≤ v 0 / (2 * t) := by
      rw [le_div_iff₀ (by positivity)]
      nlinarith
    have heq : v 0 / t - v 0 / (2 * t) = v 0 / (2 * t) := by ring
    linarith
  have hinv2 : (ρ θ)⁻¹ ≤ 2 * (t / v 0) := by
    have h := (inv_le_inv₀ hs (by positivity : 0 < v 0 / (2 * t))).mpr hhalf
    exact h.trans_eq (by field_simp)
  have hsR : R < ρ θ := by
    have hrlt : R + 1 + L < v 0 / t := by
      rw [lt_div_iff₀ ht]
      nlinarith
    linarith
  have hs1 : 1 ≤ ρ θ := hR.trans hsR.le
  have hinv := levelGrad_inverse_radius_error hv0 ht hs hL hinv2 hcoarse
  have hρc : ContDiffAt ℝ 2 ρ θ :=
    (hsmooth.contDiffAt (isOpen_ne.mem_nhds hθ0)).of_le (by simp)
  obtain ⟨hDρ, hDDρ⟩ := levelArea_radius_derivative_bounds ht.le ht1 hAr hB.le
    hθ hρc hqder hqhess hρder hρhess
  have hDρ' : ‖fderiv ℝ ρ θ‖ ≤ P * (t / v 0) := by
    convert hDρ using 1
    dsimp [P]
    field_simp
  have hDDρ' : ‖fderiv ℝ (fderiv ℝ ρ) θ‖ ≤ P * (t / v 0) := by
    convert hDDρ using 1
    dsimp [P]
    field_simp
  have hq₁ : ‖fderiv ℝ (fun y => kelvinTranslatedQuadrupole v (‖y‖⁻¹ • y)) θ‖ ≤
      10 * B := by
    rw [← (toDual ℝ E3).symm.norm_map
      (fderiv ℝ (fun y => kelvinTranslatedQuadrupole v (‖y‖⁻¹ • y)) θ)]
    change ‖gradient (fun y => kelvinTranslatedQuadrupole v (‖y‖⁻¹ • y)) θ‖ ≤ _
    rw [(levelRadius_angular_gradient (translated_quadrupole_contDiff v)
      (kelvinTranslatedQuadrupole_smul v) hθ).2]
    have hgrad : ‖gradient (farQuadrupole (kelvinTranslatedQuadrupole v)) θ‖ ≤ B := by
      rwa [gradient, (toDual ℝ E3).symm.norm_map]
    exact (levelRadius_tangent_norm_le hθ).trans (by nlinarith)
  have hq₂ := levelRadius_angular_fderiv_two_bound
    (translated_quadrupole_contDiff v) hB.le hθ hqder hqhess
  have herr : ‖fderiv ℝ (fderiv ℝ (levelRadiusRemainder v t ρ)) θ‖ ≤
      (Ar * (v 0) ^ 2) * (t / v 0) ^ 2 := by
    convert hρhess using 1
    field_simp
  have hn : ‖ρ θ • θ‖ = ρ θ := by
    rw [norm_smul, Real.norm_of_nonneg hs.le, hθ, mul_one]
  have hSR : R < ‖ρ θ • θ‖ := by simpa only [hn] using hsR
  have hWc : ContDiffAt ℝ 2 (levelGradSecond_spatialRemainder u v) (ρ θ • θ) :=
    (hW.contDiffAt ((isOpen_lt continuous_const continuous_norm).mem_nhds hSR)).of_le
      (by simp)
  obtain ⟨hDW, hDDW⟩ := hWb (ρ θ • θ) hSR.le
  rw [hn] at hDW hDDW
  have hess : ‖fderiv ℝ (fderiv ℝ (levelGradRemainder u v t ρ)) θ‖ ≤ A₂ * t ^ 5 :=
    levelGradSecond_remainder_hessian_bound hv0 ht.le htC.le hθ hs1 hinv2
      (by positivity) (by positivity) (by positivity) hP hM hρc hWc hinv
      (hqval.trans (by linarith)) hq₁ hq₂ hDρ' hDDρ' herr hDW hDDW
  exact hess.trans
    (mul_le_mul_of_nonneg_right (le_max_right Ag A₂) (pow_nonneg ht.le 5))

end LiquidDrop.CapacitaryK

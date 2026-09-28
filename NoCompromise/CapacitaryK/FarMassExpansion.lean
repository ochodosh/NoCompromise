import NoCompromise.CapacitaryK.FarMassDensity
import NoCompromise.CapacitaryK.LevelSandwich
import NoCompromise.CapacitaryK.PolarMassExpansion
import NoCompromise.CapacitaryK.TranslatedDerivatives

/-!
# `eq:K-p-expansion`, `lem:K-far-field`, `thm:capacitary-inequalities` for the capacitary potential

Volume route: `p(t) = μ{0 < u ≤ t} = ∫_{0<u≤t} Δ|∇u|` (`FarMassDensity`); after translating by the
dipole centre `z = ∇v(0)/v(0)`, the sublevels are sandwiched between radial graphs
(`level_sandwich`), and `Δ|∇u|(y+z) = 2C/|y|⁴ + 18 Q(y)/|y|⁸ + O(|y|⁻⁷)` with `Q` harmonic,
2-homogeneous and of zero spherical mean, so the polar-coordinates computation
(`polar_far_mass_expansion`) gives `μ{0 < u ≤ t} = 8πt + O(t⁴)`.

* `capacitary_far_mass_expansion_of_translated`: the mass expansion from the translated value
  and `Δ|∇u|` expansions (no further hypotheses).
* `GradNormLaplacianFarExpansion`: the pointwise far-field expansion of `Δ|∇U|` for an exterior
  harmonic `U = C/r + Q/r⁵ + W`, `∇W = O(r⁻⁵)`, `D²W = O(r⁻⁶)`; kept as a named hypothesis.
* `capacitary_far_mass_expansion`, `capacitary_Kp_expansion` (`eq:K-p-expansion`),
  `capacitary_K_far_field` (`lem:K-far-field`), `capacitary_inequalities_of_potential_far`
  (`thm:capacitary-inequalities`), each modulo `GradNormLaplacianFarExpansion`.
-/

noncomputable section
open Real Set Filter MeasureTheory Topology Asymptotics Metric
open scoped Gradient ENNReal

namespace LiquidDrop.CapacitaryK

theorem capacitary_far_mass_expansion_of_translated
    {K : Set E3} (hK : IsCompact K) (hzero : (0 : E3) ∈ interior K)
    {u : E3 → ℝ} (hu : Continuous u)
    (hh : HasDistributionalLaplacianOn u (fun _ => 0) Kᶜ)
    (hb : ∀ x ∈ K, u x = 1) (hinf : Tendsto u (cocompact E3) (𝓝 0))
    {μ : Measure E3}
    (hμK : ∀ L : Set E3, IsCompact L → L ⊆ Kᶜ → μ L < ⊤)
    (hμ : ∀ φ : E3 → ℝ, ContDiff ℝ (⊤ : ℕ∞) φ → HasCompactSupport φ → tsupport φ ⊆ Kᶜ →
        ∫ x, gradNorm u x * laplacianN φ x = ∫ x, φ x ∂μ)
    {z : E3} {Q : E3 → ℝ} {C R M : ℝ} (hC : 0 < C) (hR : 0 < R)
    (hQc : Continuous Q) (hQh : ∀ (c : ℝ) (y : E3), Q (c • y) = c ^ 2 * Q y)
    (hQm : ∫ θ, Q (θ : E3) ∂(volume : Measure E3).toSphere = 0)
    (hval : ∀ y : E3, R ≤ ‖y‖ → |u (y + z) - C / ‖y‖ - Q y / ‖y‖ ^ 5| ≤ M / ‖y‖ ^ 4)
    (hRK : ∀ y : E3, R ≤ ‖y‖ → y + z ∉ K)
    (hG : ∀ y : E3, R ≤ ‖y‖ → 0 < gradNorm u (y + z) ∧
      |laplacianN (gradNorm u) (y + z) - 2 * C / ‖y‖ ^ 4 - 18 * Q y / ‖y‖ ^ 8| ≤ M / ‖y‖ ^ 7) :
    (fun t => (μ (u ⁻¹' Ioc 0 t)).toReal - 8 * π * t) =O[𝓝[>] 0] (fun t => t ^ 4) := by
  have hpos := capacitary_pos_everywhere hK hzero hu hh hb hinf
  have hUc : Continuous (fun y => u (y + z)) := hu.comp (continuous_id.add continuous_const)
  obtain ⟨A, hA⟩ := level_sandwich hUc (fun y => hpos _) hQc hQh hC hR hval
  have hGm : Measurable (fun y => laplacianN (gradNorm u) (y + z)) :=
    (measurable_laplacianN _).comp (measurable_id.add_const z)
  have hSm : ∀ t, MeasurableSet {y | u (y + z) ≤ t} := fun t =>
    measurableSet_le hUc.measurable measurable_const
  have hPc : Continuous (fun y => 18 * Q y) := continuous_const.mul hQc
  have hPh : ∀ (c : ℝ) (y : E3), 18 * Q (c • y) = c ^ 2 * (18 * Q y) := by
    intro c y; rw [hQh]; ring
  have hPm : ∫ θ, 18 * Q (θ : E3) ∂(volume : Measure E3).toSphere = 0 := by
    rw [integral_const_mul, hQm, mul_zero]
  have hU : IsOpen Kᶜ := hK.isClosed.isOpen_compl
  have hu3 : ContDiffOn ℝ 3 u Kᶜ :=
    (capacitary_potential_contDiffOn hK hu hh).of_le (by norm_num)
  have hΔ := kelvin_laplacianN_eq_zero_of_distributional hU hu.continuousOn hh
  have hGnn : ∀ y : E3, R ≤ ‖y‖ → 0 ≤ laplacianN (gradNorm u) (y + z) := by
    intro y hy
    have hyK : y + z ∈ Kᶜ := hRK y hy
    apply laplacianN_gradNorm_nonneg_of_pos (hu3.contDiffAt (hU.mem_nhds hyK)) _ (hG y hy).1
    filter_upwards [hU.mem_nhds hyK] with w hw
    exact hΔ w hw
  obtain ⟨hint, hO⟩ := polar_far_mass_expansion hGm hQc hQh hPc hPh hQm hPm hC hR hGnn
    (fun y hy => (hG y hy).2) (fun t => {y | u (y + z) ≤ t}) hSm hA
  -- the translated sublevel lies in the far region for small `t`
  obtain ⟨B, hB0, hB⟩ := polar_homogeneous_bound hQc hQh
  set D : ℝ := R + B / C ^ 2 + |A| with hD
  have hDpos : 0 < D := by
    have : 0 ≤ B / C ^ 2 := div_nonneg hB0 (sq_nonneg _)
    have := abs_nonneg A
    linarith
  have hfar : ∀ᶠ t in 𝓝[>] (0 : ℝ), ∀ y : E3, u (y + z) ≤ t → R ≤ ‖y‖ := by
    filter_upwards [hA, Ioo_mem_nhdsGT (lt_min one_pos (div_pos hC hDpos))] with t hAt ht y hy
    obtain ⟨hy0, hyb⟩ := hAt.2 y hy
    have ht0 : 0 < t := ht.1
    have ht1 : t ≤ 1 := (ht.2.le.trans (min_le_left _ _))
    have htD : t ≤ C / D := ht.2.le.trans (min_le_right _ _)
    have hCt : D ≤ C / t := by
      rw [le_div_iff₀ ht0]
      rw [le_div_iff₀ hDpos] at htD
      linarith
    have hn : 0 < ‖y‖ := norm_pos_iff.mpr hy0
    have hq := hB y hy0
    have heq : t * Q y / (C ^ 2 * ‖y‖ ^ 2) = (t / C ^ 2) * (Q y / ‖y‖ ^ 2) := by
      field_simp
    have hlow : -(t / C ^ 2) * B ≤ t * Q y / (C ^ 2 * ‖y‖ ^ 2) := by
      rw [heq]
      have h1 := (abs_le.mp hq).1
      have h2 : 0 ≤ t / C ^ 2 := div_nonneg ht0.le (sq_nonneg _)
      nlinarith
    have htB : (t / C ^ 2) * B ≤ B / C ^ 2 := by
      rw [div_mul_eq_mul_div, div_le_div_iff_of_pos_right (by positivity)]
      nlinarith
    have hAt2 : A * t ^ 2 ≤ |A| := by
      have : t ^ 2 ≤ 1 := by nlinarith
      calc A * t ^ 2 ≤ |A| * t ^ 2 := by
            exact mul_le_mul_of_nonneg_right (le_abs_self A) (sq_nonneg t)
        _ ≤ |A| * 1 := mul_le_mul_of_nonneg_left this (abs_nonneg A)
        _ = |A| := mul_one _
    linarith
  have heq : (fun t => (∫ y in {y | u (y + z) ≤ t}, laplacianN (gradNorm u) (y + z)) - 8 * π * t)
      =ᶠ[𝓝[>] 0] (fun t => (μ (u ⁻¹' Ioc 0 t)).toReal - 8 * π * t) := by
    filter_upwards [hint, hfar, Ioo_mem_nhdsGT one_pos] with t hi hf ht
    rw [capacitary_far_mass_eq_translated_integral hK hzero hu hh hb hinf hμK hμ z ht.2
      (fun y hy => (hG y hy).1) hf hi]
  exact hO.congr' heq EventuallyEq.rfl

/-- The far-field expansion of `Δ|∇U|` for an exterior harmonic `U = C/r + Q/r⁵ + W` with
`∇W = O(r⁻⁵)`, `D²W = O(r⁻⁶)`: `Δ|∇U| = 2C/r⁴ + 18 Q/r⁸ + O(r⁻⁷)`. Used as a named hypothesis
(its proof is the algebra of the Bochner identity to second order). -/
def GradNormLaplacianFarExpansion : Prop :=
  ∀ (U Q : E3 → ℝ) (C R M : ℝ), 0 < C → 0 < R →
    ContDiffOn ℝ (⊤ : ℕ∞) U {x | R < ‖x‖} → (∀ x : E3, R < ‖x‖ → laplacianN U x = 0) →
    ContDiff ℝ (⊤ : ℕ∞) Q → (∀ (c : ℝ) (x : E3), Q (c • x) = c ^ 2 * Q x) →
    (∀ x : E3, laplacianN Q x = 0) →
    (∀ x : E3, R ≤ ‖x‖ →
      ‖fderiv ℝ (fun y => U y - C / ‖y‖ - Q y / ‖y‖ ^ 5) x‖ ≤ M / ‖x‖ ^ 5 ∧
      ‖fderiv ℝ (fderiv ℝ (fun y => U y - C / ‖y‖ - Q y / ‖y‖ ^ 5)) x‖ ≤ M / ‖x‖ ^ 6) →
    ∃ R' M' : ℝ, 0 < R' ∧ ∀ x : E3, R' ≤ ‖x‖ →
      0 < gradNorm U x ∧
      |laplacianN (gradNorm U) x - 2 * C / ‖x‖ ^ 4 - 18 * Q x / ‖x‖ ^ 8| ≤ M' / ‖x‖ ^ 7

theorem gradient_comp_add_right' (u : E3 → ℝ) (z x : E3) :
    gradient (fun y => u (y + z)) x = gradient u (x + z) := by
  simp only [gradient, fderiv_comp_add_right]

theorem gradNorm_comp_add_right (u : E3 → ℝ) (z : E3) :
    gradNorm (fun y => u (y + z)) = fun x => gradNorm u (x + z) := by
  funext x
  simp only [gradNorm, gradient_comp_add_right']

theorem laplacianN_comp_add_right' (f : E3 → ℝ) (z x : E3) :
    laplacianN (fun y => f (y + z)) x = laplacianN f (x + z) := by
  have h : (fun y => f (y + z)) = fun y => f (z + y) := by
    funext y; rw [add_comm]
  rw [h, laplacianN_comp_add_left, add_comm]

/-- `eq:K-p-expansion` (volume form) for the capacitary potential, modulo the named far-field
expansion of `Δ|∇U|`: `μ{0 < u ≤ t} = 8πt + O(t⁴)`. -/
theorem capacitary_far_mass_expansion
    (hGexp : GradNormLaplacianFarExpansion)
    {K : Set E3} (hK : IsCompact K) (hzero : (0 : E3) ∈ interior K)
    {u : E3 → ℝ} (hu : Continuous u)
    (hh : HasDistributionalLaplacianOn u (fun _ => 0) Kᶜ)
    (hb : ∀ x ∈ K, u x = 1) (hinf : Tendsto u (cocompact E3) (𝓝 0))
    {μ : Measure E3}
    (hμK : ∀ L : Set E3, IsCompact L → L ⊆ Kᶜ → μ L < ⊤)
    (hμ : ∀ φ : E3 → ℝ, ContDiff ℝ (⊤ : ℕ∞) φ → HasCompactSupport φ → tsupport φ ⊆ Kᶜ →
        ∫ x, gradNorm u x * laplacianN φ x = ∫ x, φ x ∂μ) :
    (fun t => (μ (u ⁻¹' Ioc 0 t)).toReal - 8 * π * t) =O[𝓝[>] 0] (fun t => t ^ 4) := by
  obtain ⟨R₀', hR₀'⟩ := hK.isBounded.subset_closedBall 0
  have hR₀ : (0 : ℝ) < max R₀' 1 := lt_of_lt_of_le one_pos (le_max_right _ _)
  have hKR : K ⊆ closedBall 0 (max R₀' 1) :=
    hR₀'.trans (closedBall_subset_closedBall (le_max_left _ _))
  set R₀ := max R₀' 1 with hR₀def
  obtain ⟨v, r, hr, hv, he, hΔv, hv0, hQc, hQs, hQΔ, hQm, R, M, hR, hsm, hbd⟩ :=
    capacitary_translated_remainder_derivatives hK hR₀ hKR hzero hu hh hb hinf
  set z : E3 := (v 0)⁻¹ • gradient v 0 with hz
  set Q := kelvinTranslatedQuadrupole v with hQ
  set R₁ := max R (R₀ + ‖z‖ + 1) with hR₁
  have hR₁0 : 0 < R₁ := hR.trans_le (le_max_left _ _)
  have hfarK : ∀ y : E3, R₀ + ‖z‖ + 1 ≤ ‖y‖ → R₀ < ‖y + z‖ := by
    intro y hy
    have := norm_sub_norm_le y (-z)
    rw [sub_neg_eq_add, norm_neg] at this
    linarith
  have huext := capacitary_potential_contDiffOn_exterior hK hKR hu hh
  have hΔ := kelvin_laplacianN_eq_zero_of_distributional hK.isClosed.isOpen_compl
    hu.continuousOn hh
  have hnotK : ∀ y : E3, R₀ < ‖y‖ → y ∉ K := by
    intro y hy hyK
    have := hKR hyK
    rw [mem_closedBall, dist_zero_right] at this
    linarith
  have hUs : ContDiffOn ℝ (⊤ : ℕ∞) (fun y => u (y + z)) {x | R₁ < ‖x‖} := by
    refine huext.comp (contDiffOn_id.add contDiffOn_const) ?_
    intro x hx
    exact hfarK x ((le_max_right _ _).trans hx.le)
  have hUh : ∀ x : E3, R₁ < ‖x‖ → laplacianN (fun y => u (y + z)) x = 0 := by
    intro x hx
    rw [laplacianN_comp_add_right']
    exact hΔ _ (hnotK _ (hfarK x ((le_max_right _ _).trans hx.le)))
  obtain ⟨R₂, M₂, hR₂, hG2⟩ := hGexp (fun y => u (y + z)) Q (v 0) R₁ M hv0 hR₁0 hUs hUh
    (translated_quadrupole_contDiff v) hQs hQΔ
    (fun x hx => ⟨(hbd x ((le_max_left _ _).trans hx)).2.1,
      (hbd x ((le_max_left _ _).trans hx)).2.2⟩)
  set R₃ := max R₁ R₂ with hR₃
  have hR₃0 : 0 < R₃ := hR₁0.trans_le (le_max_left _ _)
  set M₃ := max M M₂ with hM₃
  refine capacitary_far_mass_expansion_of_translated hK hzero hu hh hb hinf hμK hμ
    (z := z) (Q := Q) (C := v 0) (R := R₃) (M := M₃) hv0 hR₃0 hQc hQs hQm ?_ ?_ ?_
  · intro y hy
    have hyR : R ≤ ‖y‖ := (le_max_left _ _).trans ((le_max_left _ _).trans hy)
    have hn : 0 < ‖y‖ := hR.trans_le hyR
    exact (hbd y hyR).1.trans (div_le_div_of_nonneg_right (le_max_left _ _) (by positivity))
  · intro y hy
    exact hnotK _ (hfarK y ((le_max_right _ _).trans ((le_max_left _ _).trans hy)))
  · intro y hy
    have hyR : R₂ ≤ ‖y‖ := (le_max_right _ _).trans hy
    have hn : 0 < ‖y‖ := hR₂.trans_le hyR
    obtain ⟨h1, h2⟩ := hG2 y hyR
    rw [gradNorm_comp_add_right] at h1 h2
    rw [laplacianN_comp_add_right'] at h2
    exact ⟨h1, h2.trans (div_le_div_of_nonneg_right (le_max_right _ _) (by positivity))⟩

/-- `eq:K-p-expansion` for the canonical representative `p` of the capacitary potential,
modulo `GradNormLaplacianFarExpansion`: `p(t) = 8πt + O(t⁴)`. -/
theorem capacitary_Kp_expansion
    (hGexp : GradNormLaplacianFarExpansion)
    {K : Set E3} (hK : IsCompact K) (hzero : (0 : E3) ∈ interior K)
    {u : E3 → ℝ} (hu : Continuous u)
    (hh : HasDistributionalLaplacianOn u (fun _ => 0) Kᶜ)
    (hb : ∀ x ∈ K, u x = 1) (hinf : Tendsto u (cocompact E3) (𝓝 0))
    {μ : Measure E3} (hμU : μ Kᶜᶜ = 0)
    (hμK : ∀ L : Set E3, IsCompact L → L ⊆ Kᶜ → μ L < ⊤)
    (hμ : ∀ φ : E3 → ℝ, ContDiff ℝ (⊤ : ℕ∞) φ → HasCompactSupport φ → tsupport φ ⊆ Kᶜ →
        ∫ x, gradNorm u x * laplacianN φ x = ∫ x, φ x ∂μ)
    {t₀ : ℝ} (ht₀ : t₀ ∈ Ioo (0 : ℝ) 1)
    (ht₀R : ∀ x ∈ Kᶜ, u x = t₀ → gradient u x ≠ 0) :
    (fun t => Kp μ u t₀ (levelP Kᶜ u t₀) t - 8 * π * t) =O[𝓝[>] 0] (fun t => t ^ 4) := by
  have h0 := (capacitary_Kp_eq_far_mass hK hzero hu hh hb hinf hμU hμK hμ ht₀ ht₀R).1
  exact (Kp_expansion_iff_measure_expansion hu.measurable ht₀
    (K_slab_mass_finite hμU hμK (capacitary_slabs hu hb hinf)) h0).mpr
    (capacitary_far_mass_expansion hGexp hK hzero hu hh hb hinf hμK hμ)

/-- `lem:K-far-field` for the capacitary potential, modulo `GradNormLaplacianFarExpansion`:
`F(t) = 4πt² + O(t⁵)`, `p(t) = 8πt + O(t⁴)`, and `eq:K-far-field-limits`. -/
theorem capacitary_K_far_field
    (hGexp : GradNormLaplacianFarExpansion)
    {K : Set E3} (hK : IsCompact K) (hzero : (0 : E3) ∈ interior K)
    {u : E3 → ℝ} (hu : Continuous u)
    (hh : HasDistributionalLaplacianOn u (fun _ => 0) Kᶜ)
    (hb : ∀ x ∈ K, u x = 1) (hinf : Tendsto u (cocompact E3) (𝓝 0))
    {μ : Measure E3} (hμU : μ Kᶜᶜ = 0)
    (hμK : ∀ L : Set E3, IsCompact L → L ⊆ Kᶜ → μ L < ⊤)
    (hμ : ∀ φ : E3 → ℝ, ContDiff ℝ (⊤ : ℕ∞) φ → HasCompactSupport φ → tsupport φ ⊆ Kᶜ →
        ∫ x, gradNorm u x * laplacianN φ x = ∫ x, φ x ∂μ)
    {t₀ : ℝ} (ht₀ : t₀ ∈ Ioo (0 : ℝ) 1)
    (ht₀R : ∀ x ∈ Kᶜ, u x = t₀ → gradient u x ≠ 0) :
    (fun t => KFhat μ u t₀ (levelP Kᶜ u t₀) (levelF Kᶜ u t₀) t - 4 * π * t ^ 2)
        =O[𝓝[>] 0] (fun t => t ^ 5) ∧
      (fun t => Kp μ u t₀ (levelP Kᶜ u t₀) t - 8 * π * t) =O[𝓝[>] 0] (fun t => t ^ 4) ∧
      Tendsto (fun t => (KFhat μ u t₀ (levelP Kᶜ u t₀) (levelF Kᶜ u t₀) t - 4 * π * t ^ 2) /
        t ^ 4) (𝓝[>] 0) (𝓝 0) ∧
      Tendsto (levelH (KFhat μ u t₀ (levelP Kᶜ u t₀) (levelF Kᶜ u t₀))
        (Kp μ u t₀ (levelP Kᶜ u t₀))) (𝓝[>] 0) (𝓝 0) := by
  obtain ⟨R, hR⟩ := hK.isBounded.subset_closedBall 0
  have hR₀ : (0 : ℝ) < max R 1 := lt_of_lt_of_le one_pos (le_max_right _ _)
  have hKR : K ⊆ Metric.closedBall 0 (max R 1) :=
    hR.trans (Metric.closedBall_subset_closedBall (le_max_left _ _))
  obtain ⟨t₁, ht₁, M, hsmall⟩ := capacitary_small_level_decay hK hR₀ hKR hzero hu hh hb hinf
  have hU : IsOpen Kᶜ := hK.isClosed.isOpen_compl
  have hu3 : ContDiffOn ℝ 3 u Kᶜ := (capacitary_potential_contDiffOn hK hu hh).of_le (by norm_num)
  have hΔ := kelvin_laplacianN_eq_zero_of_distributional hU hu.continuousOn hh
  have hslabs := capacitary_slabs hu hb hinf
  have hlevels := capacitary_levels ⟨0, interior_subset hzero⟩ hu hb hinf
  have hF0 := KFhat_tendsto_zero_of_decay hU hu.measurable hu3 hΔ hμU hμK hμ hslabs hlevels
    ht₀ ht₀R t₁ ⟨ht₁.1, ht₁.2⟩ M hsmall
  have hp := capacitary_Kp_expansion hGexp hK hzero hu hh hb hinf hμU hμK hμ ht₀ ht₀R
  obtain ⟨_, _, hi, hF, _, _⟩ :=
    K_structure hu.measurable ht₀ (K_slab_mass_finite hμU hμK hslabs)
      (p₀ := levelP Kᶜ u t₀) (F₀ := levelF Kᶜ u t₀)
  have hFexp := F_expansion_of_p_expansion hi hF hF0 hp
  obtain ⟨hz, hh0⟩ := K_far_field_limits hFexp hp
  exact ⟨hFexp, hp, hz, hh0⟩

/-- `thm:capacitary-inequalities` for the capacitary potential with `eq:K-p-expansion`
discharged, modulo `GradNormLaplacianFarExpansion`; the remaining inputs are
`thm:total-curvature-bound` and the collar bounds near `∂K` (endpoint identification). -/
theorem capacitary_inequalities_of_potential_far
    (hGexp : GradNormLaplacianFarExpansion)
    {K : Set E3} (hK : IsCompact K) (hKconn : IsConnected K) (hcompl : IsPreconnected Kᶜ)
    (hzero : (0 : E3) ∈ interior K)
    {u : E3 → ℝ} (hu : Continuous u)
    (hh : HasDistributionalLaplacianOn u (fun _ => 0) Kᶜ)
    (hb : ∀ x ∈ K, u x = 1) (hinf : Tendsto u (cocompact E3) (𝓝 0))
    {μ : Measure E3} (hμU : μ Kᶜᶜ = 0)
    (hμK : ∀ L : Set E3, IsCompact L → L ⊆ Kᶜ → μ L < ⊤)
    (hμ : ∀ φ : E3 → ℝ, ContDiff ℝ (⊤ : ℕ∞) φ → HasCompactSupport φ → tsupport φ ⊆ Kᶜ →
        ∫ x, gradNorm u x * laplacianN φ x = ∫ x, φ x ∂μ)
    (h_of_total_curvature_bound : ∀ (S : Set E3) (n : E3 → E3), IsCompact S → IsConnected S →
      IsSmoothEmbeddedSurface S → IsUnitNormalField S n →
      ∫ x in S, gaussCurvature S n x ∂(Measure.euclideanHausdorffMeasure 2) ≤ 4 * Real.pi)
    {t₀ : ℝ} (ht₀ : t₀ ∈ Ioo (0 : ℝ) 1)
    (ht₀R : ∀ x ∈ Kᶜ, u x = t₀ → gradient u x ≠ 0)
    (hcollar : ∃ t₁ < 1, ∃ c > 0, ∃ M, ∀ x ∈ Kᶜ, t₁ < u x →
      c ≤ gradNorm u x ∧ |meanCurv u x * gradNorm u x| ≤ M) :
    4 * π ≤ levelF Kᶜ u t₀ + ∫ t in t₀..1, Kp μ u t₀ (levelP Kᶜ u t₀) t ∧
      4 * (levelF Kᶜ u t₀ + ∫ t in t₀..1, Kp μ u t₀ (levelP Kᶜ u t₀) t) - 8 * π ≤
        levelP Kᶜ u t₀ + (μ (u ⁻¹' Ioo t₀ 1)).toReal := by
  have hU : IsOpen Kᶜ := hK.isClosed.isOpen_compl
  have hu3 : ContDiffOn ℝ 3 u Kᶜ := (capacitary_potential_contDiffOn hK hu hh).of_le (by norm_num)
  have hΔ := kelvin_laplacianN_eq_zero_of_distributional hU hu.continuousOn hh
  exact capacitary_inequalities_of_potential_mass_expansion hK hKconn hcompl hzero hu hh hb hinf
    hμU hμK hμ h_of_total_curvature_bound ht₀ ht₀R
    (capacitary_far_mass_expansion hGexp hK hzero hu hh hb hinf hμK hμ)
    (collar_mass_ne_top hU hu.measurable hu3 hΔ hμU hμK hμ (capacitary_slabs hu hb hinf)
      ht₀ ht₀R hcollar)

end LiquidDrop.CapacitaryK

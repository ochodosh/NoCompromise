module

public import NoCompromise.CapacitaryK.FromPotential
public import NoCompromise.CapacitaryK.FarFieldZero
public import NoCompromise.CapacitaryK.Endpoint
public import NoCompromise.CapacitaryK.FarFieldMass
public import NoCompromise.CapacitaryK.CollarMass

@[expose] public section

/-!
# `thm:capacitary-inequalities` for the capacitary potential, with `F(0+) = 0` discharged

* `Kp_expansion_of_levelP_expansion`: all small levels are regular, so `eq:K-p-expansion` for the
  canonical representative `p` follows from `eq:K-p-expansion` for the geometric integral
  `levelP U u t = ∫_{u=t} H|∇u| dH²` (`lem:K-p-geometric`).
* `Kp_small_bounds`, `Kp_tendsto_zero_of_decay`: the partial far-field information on `p` that
  follows from `F(t) ≤ C t²` and monotonicity of `p` alone: `0 ≤ p(t) ≤ C t` for small `t`, so
  `p(0+) = 0`. (The full `eq:K-p-expansion`, `p(t) = 8πt + O(t⁴)`, needs `lem:K-normalization`
  and `lem:K-level-asymptotics` and is kept as a hypothesis.)
* `capacitary_inequalities_of_potential_expansion`: `thm:capacitary-inequalities` for the
  capacitary potential with `F(0+) = 0` discharged (`KFhat_tendsto_zero_of_decay`,
  `capacitary_small_level_decay`), `eq:K-p-expansion` in its geometric form, and the endpoint
  limits replaced by finiteness of the collar mass `μ{t₀ < u < 1}` (`Kp_KFhat_tendsto_one`), with
  the endpoint values `F(1) = F(t₀) + ∫_{t₀}^1 p` and `p(1) = p(t₀) + μ{t₀ < u < 1}` explicit.
  Their identification with `∫_{∂K} |∇u|²` and `∫_{∂K} H|∇u|` (regularity of `u` up to `∂K`) is
  not formalised here.
* `capacitary_Kp_eq_far_mass`, `capacitary_inequalities_of_potential_mass_expansion`: for the
  capacitary potential `p(t) = μ{0 < u ≤ t}`, so `eq:K-p-expansion` may equivalently be supplied
  as the far-region mass expansion `μ{0 < u ≤ t} = 8πt + O(t⁴)`.
* `capacitary_inequalities_of_potential_collar`: the finite collar mass is derived
  (`collar_mass_ne_top`) from the bounds `|∇u| ≥ c > 0` and `|H|∇u|| ≤ M` on `{u > t₁}`, which
  follow from `C²` regularity of `u` up to `∂K` and the Hopf sign (`thm:capacitary-potential`).
-/

noncomputable section
open Real Set Filter MeasureTheory Topology Asymptotics
open scoped Gradient ENNReal

namespace LiquidDrop.CapacitaryK

/-- `eq:K-p-expansion` for the canonical representative `p` from the expansion of the geometric
integral `∫_{u=t} H w dH²`, when all levels below `t₁` are regular. -/
theorem Kp_expansion_of_levelP_expansion {U : Set E3} (hU : IsOpen U) {u : E3 → ℝ}
    (humeas : Measurable u) (hu : ContDiffOn ℝ 3 u U) (hΔ : ∀ x ∈ U, laplacianN u x = 0)
    {μ : Measure E3} (hμU : μ Uᶜ = 0)
    (hμK : ∀ K : Set E3, IsCompact K → K ⊆ U → μ K < ⊤)
    (hμ : ∀ φ : E3 → ℝ, ContDiff ℝ (⊤ : ℕ∞) φ → HasCompactSupport φ → tsupport φ ⊆ U →
        ∫ x, gradNorm u x * laplacianN φ x = ∫ x, φ x ∂μ)
    (hslabs : ∀ a b, 0 < a → a < b → b < 1 →
      IsCompact (closure (U ∩ u ⁻¹' Ioo a b)) ∧ closure (U ∩ u ⁻¹' Ioo a b) ⊆ U)
    {t₀ : ℝ} (ht₀ : t₀ ∈ Ioo (0 : ℝ) 1) (ht₀R : ∀ x ∈ U, u x = t₀ → gradient u x ≠ 0)
    {t₁ : ℝ} (ht₁ : 0 < t₁) (hreg : ∀ x ∈ U, u x < t₁ → gradient u x ≠ 0)
    (hpexp : (fun t => levelP U u t - 8 * π * t) =O[𝓝[>] 0] (fun t => t ^ 4)) :
    (fun t => Kp μ u t₀ (levelP U u t₀) t - 8 * π * t) =O[𝓝[>] 0] (fun t => t ^ 4) := by
  refine hpexp.congr' ?_ EventuallyEq.rfl
  filter_upwards [Ioo_mem_nhdsGT (lt_min ht₁ one_pos)] with t ht
  have ht1 : t < t₁ := lt_of_lt_of_le ht.2 (min_le_left _ _)
  have ht2 : t < 1 := lt_of_lt_of_le ht.2 (min_le_right _ _)
  rw [K_p_geometric_of_harmonic hU humeas hu hΔ hμU hμK hμ hslabs ht₀ ht₀R t
    (fun x hx hxt => hreg x hx (hxt ▸ ht1)) ht.1 ht2]

/-- Partial `eq:K-p-expansion`: under quadratic small-level gradient decay, the canonical `p`
satisfies `0 ≤ p(t) ≤ C t` for small `t`. Only `F(t) ≤ C t²`, `F ≥ 0`, `F' = p` and monotonicity
of `p` are used: `(b - a) p(a) ≤ F(b) - F(a) ≤ (b - a) p(b)`. -/
theorem Kp_small_bounds {U : Set E3} (hU : IsOpen U) {u : E3 → ℝ}
    (humeas : Measurable u) (hu : ContDiffOn ℝ 3 u U) (hΔ : ∀ x ∈ U, laplacianN u x = 0)
    {μ : Measure E3} (hμU : μ Uᶜ = 0)
    (hμK : ∀ K : Set E3, IsCompact K → K ⊆ U → μ K < ⊤)
    (hμ : ∀ φ : E3 → ℝ, ContDiff ℝ (⊤ : ℕ∞) φ → HasCompactSupport φ → tsupport φ ⊆ U →
        ∫ x, gradNorm u x * laplacianN φ x = ∫ x, φ x ∂μ)
    (hslabs : ∀ a b, 0 < a → a < b → b < 1 →
      IsCompact (closure (U ∩ u ⁻¹' Ioo a b)) ∧ closure (U ∩ u ⁻¹' Ioo a b) ⊆ U)
    {t₀ : ℝ} (ht₀ : t₀ ∈ Ioo (0 : ℝ) 1) (ht₀R : ∀ x ∈ U, u x = t₀ → gradient u x ≠ 0)
    (t₁ : ℝ) (ht₁ : 0 < t₁ ∧ t₁ < 1) (M : ℝ)
    (hsmall : ∀ x ∈ U, u x < t₁ → gradient u x ≠ 0 ∧ gradNorm u x ≤ M * u x ^ 2) :
    ∃ C : ℝ, ∀ t, 0 < t → t < t₁ / 2 →
      0 ≤ Kp μ u t₀ (levelP U u t₀) t ∧ Kp μ u t₀ (levelP U u t₀) t ≤ C * t := by
  obtain ⟨C, hC⟩ := levelF_small_bound_of_decay hU hu hΔ hslabs t₁ ht₁ M hsmall
  have hfin := K_slab_mass_finite hμU hμK hslabs
  obtain ⟨hmono, -, hint, hF, -, -⟩ :=
    K_structure humeas ht₀ hfin (p₀ := levelP U u t₀) (F₀ := levelF U u t₀)
  set p := Kp μ u t₀ (levelP U u t₀) with hpdef
  set F := KFhat μ u t₀ (levelP U u t₀) (levelF U u t₀) with hFdef
  have hFeq : ∀ t, 0 < t → t < t₁ → F t = levelF U u t := fun t ht htt =>
    KFhat_eq_levelF hU humeas hu hΔ hμU hμK hμ hslabs ht₀ ht₀R t
      (fun x hx he => (hsmall x hx (he ▸ htt)).1) ht (htt.trans ht₁.2)
  have hsand : ∀ a b, 0 < a → a ≤ b → b < 1 →
      (b - a) * p a ≤ F b - F a ∧ F b - F a ≤ (b - a) * p b := by
    intro a b ha hab hb
    rw [hF a b ha hab hb]
    have hpm : ∀ s ∈ Icc a b, p a ≤ p s ∧ p s ≤ p b := fun s hs =>
      ⟨hmono ⟨ha, lt_of_le_of_lt hab hb⟩ ⟨lt_of_lt_of_le ha hs.1, lt_of_le_of_lt hs.2 hb⟩ hs.1,
        hmono ⟨lt_of_lt_of_le ha hs.1, lt_of_le_of_lt hs.2 hb⟩
          ⟨lt_of_lt_of_le ha hab, hb⟩ hs.2⟩
    constructor
    · have h := intervalIntegral.integral_mono_on hab intervalIntegrable_const
        (hint a b ha hab hb) (fun s hs => (hpm s hs).1)
      simpa [intervalIntegral.integral_const, smul_eq_mul] using h
    · have h := intervalIntegral.integral_mono_on hab (hint a b ha hab hb)
        intervalIntegrable_const (fun s hs => (hpm s hs).2)
      simpa [intervalIntegral.integral_const, smul_eq_mul] using h
  refine ⟨4 * C, fun t ht htt => ⟨?_, ?_⟩⟩
  · have hkey : ∀ s, 0 < s → s < t → -(C * s ^ 2) ≤ (t - s) * p t := by
      intro s hs hst
      have h1 := (hsand s t hs hst.le (by linarith)).2
      have h2 := (hC t ht (by linarith)).1
      have h3 := (hC s hs (by linarith)).2
      rw [hFeq t ht (by linarith), hFeq s hs (by linarith)] at h1
      linarith
    have hc : Continuous (fun s : ℝ => (t - s) * p t + C * s ^ 2) := by fun_prop
    have hlim : Tendsto (fun s : ℝ => (t - s) * p t + C * s ^ 2) (𝓝[>] 0)
        (𝓝 ((t - 0) * p t + C * 0 ^ 2)) := (hc.tendsto 0).mono_left nhdsWithin_le_nhds
    have hge : 0 ≤ (t - 0) * p t + C * 0 ^ 2 := by
      apply ge_of_tendsto hlim
      filter_upwards [Ioo_mem_nhdsGT ht] with s hs
      linarith [hkey s hs.1 hs.2]
    have htp : 0 ≤ t * p t := by simpa using hge
    rcases le_or_gt 0 (p t) with h | h
    · exact h
    · nlinarith
  · have h1 := (hsand t (2 * t) ht (by linarith) (by linarith)).1
    rw [hFeq (2 * t) (by linarith) (by linarith), hFeq t ht (by linarith)] at h1
    have h2 := (hC (2 * t) (by linarith) (by linarith)).2
    have h3 := (hC t ht (by linarith)).1
    have hmul : t * p t ≤ t * (4 * C * t) := by nlinarith
    exact le_of_mul_le_mul_left hmul ht

/-- Partial `eq:K-p-expansion`: `p(0+) = 0` under quadratic small-level gradient decay. -/
theorem Kp_tendsto_zero_of_decay {U : Set E3} (hU : IsOpen U) {u : E3 → ℝ}
    (humeas : Measurable u) (hu : ContDiffOn ℝ 3 u U) (hΔ : ∀ x ∈ U, laplacianN u x = 0)
    {μ : Measure E3} (hμU : μ Uᶜ = 0)
    (hμK : ∀ K : Set E3, IsCompact K → K ⊆ U → μ K < ⊤)
    (hμ : ∀ φ : E3 → ℝ, ContDiff ℝ (⊤ : ℕ∞) φ → HasCompactSupport φ → tsupport φ ⊆ U →
        ∫ x, gradNorm u x * laplacianN φ x = ∫ x, φ x ∂μ)
    (hslabs : ∀ a b, 0 < a → a < b → b < 1 →
      IsCompact (closure (U ∩ u ⁻¹' Ioo a b)) ∧ closure (U ∩ u ⁻¹' Ioo a b) ⊆ U)
    {t₀ : ℝ} (ht₀ : t₀ ∈ Ioo (0 : ℝ) 1) (ht₀R : ∀ x ∈ U, u x = t₀ → gradient u x ≠ 0)
    (t₁ : ℝ) (ht₁ : 0 < t₁ ∧ t₁ < 1) (M : ℝ)
    (hsmall : ∀ x ∈ U, u x < t₁ → gradient u x ≠ 0 ∧ gradNorm u x ≤ M * u x ^ 2) :
    Tendsto (Kp μ u t₀ (levelP U u t₀)) (𝓝[>] 0) (𝓝 0) := by
  obtain ⟨C, hC⟩ := Kp_small_bounds hU humeas hu hΔ hμU hμK hμ hslabs ht₀ ht₀R t₁ ht₁ M hsmall
  have hlim : Tendsto (fun t : ℝ => C * t) (𝓝[>] 0) (𝓝 0) := by
    simpa using (tendsto_const_nhds.mul tendsto_id).mono_left
      (show 𝓝[>] (0 : ℝ) ≤ 𝓝 0 from nhdsWithin_le_nhds)
  have hev : ∀ᶠ t : ℝ in 𝓝[>] 0, t ∈ Ioo 0 (t₁ / 2) := Ioo_mem_nhdsGT (by linarith [ht₁.1])
  apply tendsto_of_tendsto_of_tendsto_of_le_of_le' tendsto_const_nhds hlim
  · filter_upwards [hev] with t ht using (hC t ht.1 ht.2).1
  · filter_upwards [hev] with t ht using (hC t ht.1 ht.2).2

/-- `thm:capacitary-inequalities` for the capacitary potential, with `F(0+) = 0` discharged,
`eq:K-p-expansion` for the geometric `p(t) = ∫_{u=t} H|∇u| dH²` as a hypothesis, and the
endpoint limits replaced by finiteness of the collar mass `μ{t₀ < u < 1}`: the endpoint values
`F(1) = F(t₀) + ∫_{t₀}^1 p` and `p(1) = p(t₀) + μ{t₀ < u < 1}` satisfy
`4π ≤ F(1)` and `4F(1) - 8π ≤ p(1)`. -/
theorem capacitary_inequalities_of_potential_expansion
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
    (hpexp : (fun t => levelP Kᶜ u t - 8 * π * t) =O[𝓝[>] 0] (fun t => t ^ 4))
    (hcollar : μ (u ⁻¹' Ioo t₀ 1) ≠ ⊤) :
    4 * π ≤ levelF Kᶜ u t₀ + ∫ t in t₀..1, Kp μ u t₀ (levelP Kᶜ u t₀) t ∧
      4 * (levelF Kᶜ u t₀ + ∫ t in t₀..1, Kp μ u t₀ (levelP Kᶜ u t₀) t) - 8 * π ≤
        levelP Kᶜ u t₀ + (μ (u ⁻¹' Ioo t₀ 1)).toReal := by
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
  have hKp := Kp_expansion_of_levelP_expansion hU hu.measurable hu3 hΔ hμU hμK hμ hslabs
    ht₀ ht₀R ht₁.1 (fun x hx h => (hsmall x hx h).1) hpexp
  obtain ⟨hp1, hF1⟩ := Kp_KFhat_tendsto_one hu.measurable ht₀ hcollar
    (p₀ := levelP Kᶜ u t₀) (F₀ := levelF Kᶜ u t₀)
  exact capacitary_inequalities_of_potential hK hKconn hcompl hzero hu hh hb hinf hμU hμK hμ
    h_of_total_curvature_bound ht₀ ht₀R hF0 hKp hF1 hp1

/-- For the capacitary potential, the canonical `p` is the `μ`-mass of the far region:
`p(t) = μ{0 < u ≤ t}` for `t ∈ (0,1)` (from `p(0+) = 0`, `Kp_tendsto_zero_of_decay`). -/
theorem capacitary_Kp_eq_far_mass
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
    Tendsto (Kp μ u t₀ (levelP Kᶜ u t₀)) (𝓝[>] 0) (𝓝 0) ∧
      ∀ t, 0 < t → t < 1 →
        μ (u ⁻¹' Ioc 0 t) = ENNReal.ofReal (Kp μ u t₀ (levelP Kᶜ u t₀) t) ∧
          0 ≤ Kp μ u t₀ (levelP Kᶜ u t₀) t := by
  obtain ⟨R, hR⟩ := hK.isBounded.subset_closedBall 0
  have hR₀ : (0 : ℝ) < max R 1 := lt_of_lt_of_le one_pos (le_max_right _ _)
  have hKR : K ⊆ Metric.closedBall 0 (max R 1) :=
    hR.trans (Metric.closedBall_subset_closedBall (le_max_left _ _))
  obtain ⟨t₁, ht₁, M, hsmall⟩ := capacitary_small_level_decay hK hR₀ hKR hzero hu hh hb hinf
  have hU : IsOpen Kᶜ := hK.isClosed.isOpen_compl
  have hu3 : ContDiffOn ℝ 3 u Kᶜ := (capacitary_potential_contDiffOn hK hu hh).of_le (by norm_num)
  have hΔ := kelvin_laplacianN_eq_zero_of_distributional hU hu.continuousOn hh
  have hslabs := capacitary_slabs hu hb hinf
  have h0 := Kp_tendsto_zero_of_decay hU hu.measurable hu3 hΔ hμU hμK hμ hslabs ht₀ ht₀R t₁
    ⟨ht₁.1, ht₁.2⟩ M hsmall
  exact ⟨h0, fun t ht ht1 => Kp_eq_measure_of_tendsto_zero hu.measurable ht₀
    (K_slab_mass_finite hμU hμK hslabs) h0 ht ht1⟩

/-- `capacitary_inequalities_of_potential_expansion` with `eq:K-p-expansion` supplied as the
far-region mass expansion `μ{0 < u ≤ t} = 8πt + O(t⁴)` for `μ = Δ|∇u|`. -/
theorem capacitary_inequalities_of_potential_mass_expansion
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
    (hmexp : (fun t => (μ (u ⁻¹' Ioc 0 t)).toReal - 8 * π * t) =O[𝓝[>] 0] (fun t => t ^ 4))
    (hcollar : μ (u ⁻¹' Ioo t₀ 1) ≠ ⊤) :
    4 * π ≤ levelF Kᶜ u t₀ + ∫ t in t₀..1, Kp μ u t₀ (levelP Kᶜ u t₀) t ∧
      4 * (levelF Kᶜ u t₀ + ∫ t in t₀..1, Kp μ u t₀ (levelP Kᶜ u t₀) t) - 8 * π ≤
        levelP Kᶜ u t₀ + (μ (u ⁻¹' Ioo t₀ 1)).toReal := by
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
  have h0 := (capacitary_Kp_eq_far_mass hK hzero hu hh hb hinf hμU hμK hμ ht₀ ht₀R).1
  have hKp := (Kp_expansion_iff_measure_expansion hu.measurable ht₀
    (K_slab_mass_finite hμU hμK hslabs) h0).mpr hmexp
  obtain ⟨hp1, hF1⟩ := Kp_KFhat_tendsto_one hu.measurable ht₀ hcollar
    (p₀ := levelP Kᶜ u t₀) (F₀ := levelF Kᶜ u t₀)
  exact capacitary_inequalities_of_potential hK hKconn hcompl hzero hu hh hb hinf hμU hμK hμ
    h_of_total_curvature_bound ht₀ ht₀R hF0 hKp hF1 hp1

/-- `thm:capacitary-inequalities` for the capacitary potential, with the endpoint input stated
as collar bounds near `∂K`: `|∇u| ≥ c > 0` and `|H|∇u|| ≤ M` on `{u > t₁}` (consequences of
`C²` regularity up to `∂K` and the Hopf sign). The endpoint values are
`F(1) = F(t₀) + ∫_{t₀}^1 p` and `p(1) = p(t₀) + μ{t₀ < u < 1}`. -/
theorem capacitary_inequalities_of_potential_collar
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
    (hpexp : (fun t => levelP Kᶜ u t - 8 * π * t) =O[𝓝[>] 0] (fun t => t ^ 4))
    (hcollar : ∃ t₁ < 1, ∃ c > 0, ∃ M, ∀ x ∈ Kᶜ, t₁ < u x →
      c ≤ gradNorm u x ∧ |meanCurv u x * gradNorm u x| ≤ M) :
    4 * π ≤ levelF Kᶜ u t₀ + ∫ t in t₀..1, Kp μ u t₀ (levelP Kᶜ u t₀) t ∧
      4 * (levelF Kᶜ u t₀ + ∫ t in t₀..1, Kp μ u t₀ (levelP Kᶜ u t₀) t) - 8 * π ≤
        levelP Kᶜ u t₀ + (μ (u ⁻¹' Ioo t₀ 1)).toReal := by
  have hU : IsOpen Kᶜ := hK.isClosed.isOpen_compl
  have hu3 : ContDiffOn ℝ 3 u Kᶜ := (capacitary_potential_contDiffOn hK hu hh).of_le (by norm_num)
  have hΔ := kelvin_laplacianN_eq_zero_of_distributional hU hu.continuousOn hh
  exact capacitary_inequalities_of_potential_expansion hK hKconn hcompl hzero hu hh hb hinf
    hμU hμK hμ h_of_total_curvature_bound ht₀ ht₀R hpexp
    (collar_mass_ne_top hU hu.measurable hu3 hΔ hμU hμK hμ (capacitary_slabs hu hb hinf)
      ht₀ ht₀R hcollar)

end LiquidDrop.CapacitaryK

import NoCompromise.CapacitaryK.Representatives
import NoCompromise.CapacitaryK.Inequality
import NoCompromise.CapacitaryK.Asymptotics

/-!
# The measure differential inequality (chapter 31, `prop:K-measure-inequality`)

* `K_measure_ineq_level`: the pointwise chain `∫(|A|² + |∇_Σ log w|²) ≥ ∫H² - 8π ≥
  (∫Hw)²/∫w² - 8π` on one regular level, for an abstract surface measure `σ`, from
  `|A|² = H² - 2κ` (`conv:curvature`) and `∫κ ≤ 4π` (`lem:K-gauss-bonnet-input`).
* `K_measure_inequality`: the upgrade to `Dp ≥ (p²/F - 8π) dt` (increment form for the
  right-continuous `p`) together with local integrability of `p²/F`, from `Dp = u_#μ`, a lower
  density `d` of `u_#μ` (its singular part is nonnegative) and `d ≥ p²/F - 8π` a.e.
* `capacitary_inequalities_of_structure`: `thm:capacitary-inequalities` for the canonical
  `p = Kp`, `F = KFhat`, discharging the structural hypotheses of
  `CapacitaryK.capacitary_inequalities_core` by `K_structure` and `K_measure_inequality`.

The geometric inputs (lower density from `lem:K-pushforward-density`, `p`, `F` as level
integrals, the pointwise level inequality) are discharged in `FromLevels.lean`,
`PGeometric.lean`, `LevelInequality.lean` and `CapacitaryHarmonic.lean`.
-/

noncomputable section
open Real Set Filter MeasureTheory intervalIntegral Topology

namespace LiquidDrop.CapacitaryK

/-- `prop:K-measure-inequality`, pointwise chain on one regular level with surface measure `σ`:
`A2 = |A|²`, `g = |∇_Σ log w|² ≥ 0`, `κ` the Gauss curvature with
`|A|² = H² − 2κ` and `∫ κ ≤ 4π`. -/
theorem K_measure_ineq_level {Y : Type*} [MeasurableSpace Y] {σ : Measure Y}
    {A2 g H w κ : Y → ℝ}
    (hA : ∀ y, A2 y = H y ^ 2 - 2 * κ y) (hg : ∀ y, 0 ≤ g y)
    (hH2 : Integrable (fun y => H y ^ 2) σ) (hw2 : Integrable (fun y => w y ^ 2) σ)
    (hκi : Integrable κ σ) (hgi : Integrable g σ) (hκ : ∫ y, κ y ∂σ ≤ 4 * π)
    (hwpos : 0 < ∫ y, w y ^ 2 ∂σ) (hHw : AEStronglyMeasurable (fun y => H y * w y) σ) :
    ∫ y, H y ^ 2 ∂σ - 8 * π ≤ ∫ y, (A2 y + g y) ∂σ ∧
    (∫ y, H y * w y ∂σ) ^ 2 / (∫ y, w y ^ 2 ∂σ) - 8 * π ≤ ∫ y, H y ^ 2 ∂σ - 8 * π := by
  constructor
  · have hAi : Integrable (fun y => H y ^ 2 - 2 * κ y) σ := hH2.sub (hκi.const_mul 2)
    simp_rw [hA]
    rw [MeasureTheory.integral_add hAi hgi,
      MeasureTheory.integral_sub hH2 (hκi.const_mul 2), MeasureTheory.integral_const_mul]
    have hn : 0 ≤ ∫ y, g y ∂σ := MeasureTheory.integral_nonneg hg
    linarith
  · have hHwi : Integrable (fun y => H y * w y) σ := by
      refine (hH2.add hw2).mono' hHw (ae_of_all _ fun y => ?_)
      change ‖H y * w y‖ ≤ H y ^ 2 + w y ^ 2
      rw [Real.norm_eq_abs]
      apply abs_le.mpr
      constructor <;> nlinarith [sq_nonneg (H y + w y), sq_nonneg (H y - w y)]
    let c := (∫ y, H y * w y ∂σ) / (∫ y, w y ^ 2 ∂σ)
    have hsubi : Integrable (fun y => H y ^ 2 - (2 * c) * (H y * w y)) σ :=
      hH2.sub (hHwi.const_mul _)
    have he : (∫ y, (H y - c * w y) ^ 2 ∂σ) =
        (∫ y, H y ^ 2 ∂σ) - 2 * c * (∫ y, H y * w y ∂σ) +
          c ^ 2 * (∫ y, w y ^ 2 ∂σ) := by
      calc
        _ = ∫ y, (H y ^ 2 - (2 * c) * (H y * w y) + c ^ 2 * w y ^ 2) ∂σ := by
          apply MeasureTheory.integral_congr_ae
          exact ae_of_all _ fun y => by ring
        _ = _ := by
          rw [MeasureTheory.integral_add hsubi (hw2.const_mul _),
            MeasureTheory.integral_sub hH2 (hHwi.const_mul _), MeasureTheory.integral_const_mul,
            MeasureTheory.integral_const_mul]
    have hn : 0 ≤ (∫ y, H y ^ 2 ∂σ) - 2 * c * (∫ y, H y * w y ∂σ) +
        c ^ 2 * (∫ y, w y ^ 2 ∂σ) := by
      rw [← he]
      exact MeasureTheory.integral_nonneg (fun y => sq_nonneg _)
    have halg : (∫ y, H y ^ 2 ∂σ) - 2 * c * (∫ y, H y * w y ∂σ) +
        c ^ 2 * (∫ y, w y ^ 2 ∂σ) =
        (∫ y, H y ^ 2 ∂σ) - (∫ y, H y * w y ∂σ) ^ 2 / (∫ y, w y ^ 2 ∂σ) := by
      dsimp [c]
      field_simp [ne_of_gt hwpos]
      ring
    rw [halg] at hn
    linarith

/-- `prop:K-measure-inequality`, upgrade to `Dp ≥ (p²/F − 8π) dt`: `ν` is `u_#μ`,
`d` is a lower density of `ν` (the singular part is nonnegative),
and `d ≥ p²/F − 8π` a.e. on `(0,1)`. -/
theorem K_measure_inequality {ν : Measure ℝ} {p F d : ℝ → ℝ}
    (hpmono : MonotoneOn p (Ioo 0 1)) (hFcont : ContinuousOn F (Ioo 0 1))
    (hFpos : ∀ t, 0 < t → t < 1 → 0 < F t)
    (hDp : ∀ a b, 0 < a → a ≤ b → b < 1 → p b - p a = (ν (Ioc a b)).toReal)
    (hνfin : ∀ a b, 0 < a → a ≤ b → b < 1 → ν (Ioc a b) ≠ ⊤)
    (hdmeas : Measurable d)
    (hdens : ∀ a b, 0 < a → a ≤ b → b < 1 → ∫⁻ t in Ioc a b, ENNReal.ofReal (d t) ≤ ν (Ioc a b))
    (hd : ∀ᵐ t, t ∈ Ioo (0 : ℝ) 1 → p t ^ 2 / F t - 8 * π ≤ d t) :
    (∀ a b, 0 < a → a ≤ b → b < 1 → IntervalIntegrable (fun t => p t ^ 2 / F t) volume a b) ∧
    (∀ a b, 0 < a → a ≤ b → b < 1 → ∫ t in a..b, (p t ^ 2 / F t - 8 * π) ≤ p b - p a) := by
  have hlocal : ∀ a b, 0 < a → a ≤ b → b < 1 →
      IntervalIntegrable (fun t => p t ^ 2 / F t) volume a b ∧
      ∫ t in a..b, (p t ^ 2 / F t - 8 * π) ≤ p b - p a := by
    intro a b ha hab hb
    have hsub : Ioc a b ⊆ Ioo (0 : ℝ) 1 :=
      fun t ht => ⟨lt_trans ha ht.1, lt_of_le_of_lt ht.2 hb⟩
    have hpi : IntervalIntegrable p volume a b := by
      apply MonotoneOn.intervalIntegrable
      rw [uIcc_of_le hab]
      exact hpmono.mono (fun t ht => ⟨lt_of_lt_of_le ha ht.1, lt_of_le_of_lt ht.2 hb⟩)
    have hpm := ((intervalIntegrable_iff_integrableOn_Ioc_of_le hab).mp hpi).aestronglyMeasurable
    have hFm := (hFcont.mono hsub).aestronglyMeasurable (μ := volume) measurableSet_Ioc
    have hqm : AEStronglyMeasurable (fun t => p t ^ 2 / F t) (volume.restrict (Ioc a b)) :=
      (hpm.pow 2).div₀ hFm
    have hdm : AEMeasurable (fun t => ENNReal.ofReal (d t)) (volume.restrict (Ioc a b)) :=
      (ENNReal.measurable_ofReal.comp hdmeas).aemeasurable
    have hdi : Integrable (fun t => (ENNReal.ofReal (d t)).toReal) (volume.restrict (Ioc a b)) :=
      integrable_toReal_of_lintegral_ne_top hdm
        (ne_top_of_le_ne_top (hνfin a b ha hab hb) (hdens a b ha hab hb))
    have hbound : ∀ᵐ t ∂volume.restrict (Ioc a b),
        p t ^ 2 / F t - 8 * π ≤ (ENNReal.ofReal (d t)).toReal := by
      filter_upwards [ae_restrict_of_ae hd, ae_restrict_mem measurableSet_Ioc] with t hdt ht
      exact (hdt (hsub ht)).trans (by simp only [ENNReal.toReal_ofReal']; exact le_max_left _ _)
    have hqi : Integrable (fun t => p t ^ 2 / F t) (volume.restrict (Ioc a b)) := by
      refine (hdi.add (integrable_const (8 * π))).mono' hqm ?_
      filter_upwards [hbound, ae_restrict_mem measurableSet_Ioc] with t hdt ht
      have hn : 0 ≤ p t ^ 2 / F t := div_nonneg (sq_nonneg _) (hFpos t (hsub ht).1 (hsub ht).2).le
      rw [Real.norm_eq_abs, abs_of_nonneg hn]
      dsimp
      linarith
    refine ⟨(intervalIntegrable_iff_integrableOn_Ioc_of_le hab).mpr hqi, ?_⟩
    rw [integral_of_le hab, hDp a b ha hab hb]
    calc
      _ ≤ ∫ t in Ioc a b, (ENNReal.ofReal (d t)).toReal :=
        MeasureTheory.integral_mono_ae (hqi.sub (integrable_const _)) hdi hbound
      _ = (∫⁻ t in Ioc a b, ENNReal.ofReal (d t)).toReal :=
        integral_toReal hdm (ae_of_all _ fun t => ENNReal.ofReal_lt_top)
      _ ≤ (ν (Ioc a b)).toReal :=
        ENNReal.toReal_mono (hνfin a b ha hab hb) (hdens a b ha hab hb)
  exact ⟨fun a b ha hab hb => (hlocal a b ha hab hb).1,
    fun a b ha hab hb => (hlocal a b ha hab hb).2⟩

/-- `thm:capacitary-inequalities` from `prop:K-structure` and `prop:K-measure-inequality`.
The remaining inputs are positivity of `F`, the far-field limits (`lem:K-far-field`)
and the endpoint limits. -/
theorem capacitary_inequalities_of_structure {X : Type*} [MeasurableSpace X]
    {μ : Measure X} {u : X → ℝ}
    (hu : Measurable u) {t₀ p₀ F₀ F1 p1 : ℝ} {d : ℝ → ℝ} (ht₀ : t₀ ∈ Ioo (0 : ℝ) 1)
    (hfin : ∀ a b, 0 < a → a ≤ b → b < 1 → μ (u ⁻¹' Ioc a b) ≠ ⊤)
    (hFpos : ∀ t, 0 < t → t < 1 → 0 < KFhat μ u t₀ p₀ F₀ t)
    (hdmeas : Measurable d)
    (hdens : ∀ a b, 0 < a → a ≤ b → b < 1 →
      ∫⁻ t in Ioc a b, ENNReal.ofReal (d t) ≤ (μ.map u) (Ioc a b))
    (hd : ∀ᵐ t, t ∈ Ioo (0 : ℝ) 1 →
      Kp μ u t₀ p₀ t ^ 2 / KFhat μ u t₀ p₀ F₀ t - 8 * π ≤ d t)
    (hh0 : Tendsto (levelH (KFhat μ u t₀ p₀ F₀) (Kp μ u t₀ p₀)) (𝓝[>] 0) (𝓝 0))
    (hz0 : Tendsto (fun t => (KFhat μ u t₀ p₀ F₀ t - 4 * π * t ^ 2) / t ^ 4) (𝓝[>] 0) (𝓝 0))
    (hF1 : Tendsto (KFhat μ u t₀ p₀ F₀) (𝓝[<] 1) (𝓝 F1))
    (hp1 : Tendsto (Kp μ u t₀ p₀) (𝓝[<] 1) (𝓝 p1)) :
    4 * π ≤ F1 ∧ 4 * F1 - 8 * π ≤ p1 := by
  obtain ⟨hm, _, hi, hF, _, hDp⟩ := K_structure hu ht₀ hfin (p₀ := p₀) (F₀ := F₀)
  have hFc : ContinuousOn (KFhat μ u t₀ p₀ F₀) (Ioo 0 1) :=
    fun t ht => (continuousAt_of_primitive hi hF ht.1 ht.2).continuousWithinAt
  have hνfin : ∀ a b, 0 < a → a ≤ b → b < 1 → (μ.map u) (Ioc a b) ≠ ⊤ := by
    intro a b ha hab hb
    rw [Measure.map_apply hu measurableSet_Ioc]
    exact hfin a b ha hab hb
  obtain ⟨hq, hD⟩ := K_measure_inequality hm hFc hFpos hDp hνfin hdmeas hdens hd
  exact capacitary_inequalities_core hi hF hFpos hq hD hh0 hz0 hF1 hp1

/-- Positivity of `F` and `p` on `(0,1)` from the far-field expansions: if `p` is nondecreasing on
`(0,1)`, `F` is a primitive of `p` there, `F(t) = 4πt² + O(t⁵)` and `p(t) = 8πt + O(t⁴)` as
`t ↓ 0`, then `p > 0` and `F > 0` on `(0,1)`. -/
theorem pos_of_expansions {F p : ℝ → ℝ} (hpmono : MonotoneOn p (Ioo 0 1))
    (hpint : ∀ a b, 0 < a → a ≤ b → b < 1 → IntervalIntegrable p volume a b)
    (hF : ∀ a b, 0 < a → a ≤ b → b < 1 → F b - F a = ∫ t in a..b, p t)
    (hFexp : (fun t => F t - 4 * π * t ^ 2) =O[𝓝[>] 0] (fun t => t ^ 5))
    (hpexp : (fun t => p t - 8 * π * t) =O[𝓝[>] 0] (fun t => t ^ 4)) :
    ∀ t, 0 < t → t < 1 → 0 < p t ∧ 0 < F t := by
  have hid : Tendsto (fun t : ℝ => t) (𝓝[>] (0:ℝ)) (𝓝 0) := nhdsWithin_le_nhds
  -- `p(t)/t → 8π`, so `p > 0` near `0`.
  have hpq : (fun t => (p t - 8 * π * t) / t) =O[𝓝[>] 0] (fun t => t ^ 3) := by
    have h1 := hpexp.mul (Asymptotics.isBigO_refl (fun t : ℝ => t⁻¹) (𝓝[>] 0))
    refine h1.congr' (Eventually.of_forall fun t => by simp [div_eq_mul_inv]) ?_
    filter_upwards [self_mem_nhdsWithin] with t (ht : 0 < t)
    field_simp
  have h3 : Tendsto (fun t : ℝ => t ^ 3) (𝓝[>] (0:ℝ)) (𝓝 0) := by simpa using hid.pow 3
  have hpt : Tendsto (fun t => (p t - 8 * π * t) / t + 8 * π) (𝓝[>] (0:ℝ)) (𝓝 (0 + 8 * π)) :=
    (hpq.trans_tendsto h3).add tendsto_const_nhds
  rw [zero_add] at hpt
  have hev : ∀ᶠ t in 𝓝[>] (0:ℝ), 0 < (p t - 8 * π * t) / t + 8 * π :=
    hpt.eventually (eventually_gt_nhds (by positivity))
  have hppos_ev : ∀ᶠ t in 𝓝[>] (0:ℝ), 0 < p t := by
    filter_upwards [hev, self_mem_nhdsWithin] with t h (ht : 0 < t)
    have : (p t - 8 * π * t) / t + 8 * π = p t / t := by field_simp; ring
    rw [this] at h
    exact (div_pos_iff_of_pos_right ht).mp h
  have hppos : ∀ t, 0 < t → t < 1 → 0 < p t := by
    intro t ht0 ht1
    obtain ⟨s, hs, hst⟩ := ((hppos_ev.and (Ioo_mem_nhdsGT ht0)).exists)
    exact hs.trans_le (hpmono ⟨hst.1, hst.2.trans ht1⟩ ⟨ht0, ht1⟩ hst.2.le)
  -- `F → 0` at `0+`.
  have hF0 : Tendsto F (𝓝[>] (0:ℝ)) (𝓝 0) := by
    have h5 : Tendsto (fun t : ℝ => t ^ 5) (𝓝[>] (0:ℝ)) (𝓝 0) := by simpa using hid.pow 5
    have h2 : Tendsto (fun t : ℝ => 4 * π * t ^ 2) (𝓝[>] (0:ℝ)) (𝓝 0) := by
      simpa using (hid.pow 2).const_mul (4 * π)
    have := (hFexp.trans_tendsto h5).add h2
    simpa using this
  intro t ht0 ht1
  refine ⟨hppos t ht0 ht1, ?_⟩
  have hh0 : 0 < t / 2 := by linarith
  -- `F(t/2) ≥ 0` by monotonicity and the limit at `0+`.
  have hFhalf : 0 ≤ F (t / 2) := by
    apply le_of_tendsto hF0
    filter_upwards [Ioo_mem_nhdsGT hh0] with s hs
    have := hF s (t / 2) hs.1 hs.2.le (by linarith)
    have hnn : 0 ≤ ∫ r in s..t / 2, p r :=
      intervalIntegral.integral_nonneg hs.2.le fun r hr =>
        (hppos r (hs.1.trans_le hr.1) (by linarith [hr.2])).le
    linarith
  have hpos : 0 < ∫ r in t / 2..t, p r :=
    intervalIntegral.intervalIntegral_pos_of_pos_on (hpint _ _ hh0 (by linarith) ht1)
      (fun r hr => hppos r (hh0.trans hr.1) (hr.2.trans ht1)) (by linarith)
  have := hF (t / 2) t hh0 (by linarith) ht1
  linarith

/-- `thm:capacitary-inequalities` for the canonical `p = Kp`, `F = KFhat`, from
`prop:K-structure`, `prop:K-measure-inequality` (lower density `d` of `u_#μ` with
`d ≥ p²/F - 8π` a.e.) and the far-field expansions of `lem:K-far-field`. -/
theorem capacitary_inequalities_of_expansions {X : Type*} [MeasurableSpace X]
    {μ : Measure X} {u : X → ℝ}
    (hu : Measurable u) {t₀ p₀ F₀ F1 p1 : ℝ} {d : ℝ → ℝ} (ht₀ : t₀ ∈ Ioo (0 : ℝ) 1)
    (hfin : ∀ a b, 0 < a → a ≤ b → b < 1 → μ (u ⁻¹' Ioc a b) ≠ ⊤)
    (hdmeas : Measurable d)
    (hdens : ∀ a b, 0 < a → a ≤ b → b < 1 →
      ∫⁻ t in Ioc a b, ENNReal.ofReal (d t) ≤ (μ.map u) (Ioc a b))
    (hd : ∀ᵐ t, t ∈ Ioo (0 : ℝ) 1 →
      Kp μ u t₀ p₀ t ^ 2 / KFhat μ u t₀ p₀ F₀ t - 8 * π ≤ d t)
    (hFexp : (fun t => KFhat μ u t₀ p₀ F₀ t - 4 * π * t ^ 2) =O[𝓝[>] 0] (fun t => t ^ 5))
    (hpexp : (fun t => Kp μ u t₀ p₀ t - 8 * π * t) =O[𝓝[>] 0] (fun t => t ^ 4))
    (hF1 : Tendsto (KFhat μ u t₀ p₀ F₀) (𝓝[<] 1) (𝓝 F1))
    (hp1 : Tendsto (Kp μ u t₀ p₀) (𝓝[<] 1) (𝓝 p1)) :
    4 * π ≤ F1 ∧ 4 * F1 - 8 * π ≤ p1 := by
  obtain ⟨hm, _, hi, hF, _, _⟩ := K_structure hu ht₀ hfin (p₀ := p₀) (F₀ := F₀)
  have hpos := pos_of_expansions hm hi hF hFexp hpexp
  obtain ⟨hz0, hh0⟩ := K_far_field_limits hFexp hpexp
  exact capacitary_inequalities_of_structure hu ht₀ hfin (fun t h0 h1 => (hpos t h0 h1).2)
    hdmeas hdens hd hh0 hz0 hF1 hp1

end LiquidDrop.CapacitaryK

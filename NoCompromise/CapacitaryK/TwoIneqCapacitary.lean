import NoCompromise.CapacitaryK.GaussBonnetCapacitary

/-!
# `lem:K-h-monotone` and `prop:K-two-ineq` for the capacitary potential, unconditionally

`K_h_monotone_core` and `K_two_ineq_core` (CapacitaryK/Inequality.lean) are the
one-dimensional arguments, with the conclusions of `prop:K-structure`,
`prop:K-measure-inequality` and `lem:K-far-field` as hypotheses on abstract `F`, `p`. Here they
are instantiated for the capacitary potential `u` of `K`, with the canonical representatives of
`def:K-p` and `def:K-Fhat` based at a regular value `t₀ ∈ (0,1)`:

  `p = Kp μ u t₀ (levelP Kᶜ u t₀)`,   `F = KFhat μ u t₀ (levelP Kᶜ u t₀) (levelF Kᶜ u t₀)`,

where `μ = Δ|∇u|` is the measure of `prop:K-mu` (`K_mu`), given by its defining properties
`hμU`, `hμK`, `hμ`. Every hypothesis of the cores is discharged:

* `DF = p dt` and `Dp = u_#μ`: `K_structure` (`prop:K-structure`), with slab finiteness from
  `K_slab_mass_finite` and `capacitary_slabs`;
* `F > 0` on `(0,1)`: `pos_of_expansions` with the far-field expansions of
  `capacitary_K_far_field_unconditional` (`lem:K-far-field`);
* `Dp ≥ (p²/F − 8π) dt` and local integrability of `p²/F`: `K_measure_inequality`
  (`prop:K-measure-inequality`), from the lower density of `u_#μ`
  (`K_pushforward_lower_density`, `lem:K-pushforward-density`) and the pointwise level
  inequality `eq:K-measure-ineq-pointwise` at a.e. level (`capacitary_level_inequality_ae`,
  from `K_level_inequality_of_level_connected` with `capacitary_level_connected`, i.e.
  `lem:K-gauss-bonnet-input` with `lem:level-connected` and `thm:total-curvature-bound`);
* the far-field limits `eq:K-far-field-limits`: `capacitary_K_far_field_unconditional`.

The standing hypotheses on `K` and `u` are those of `capacitary_inequalities_of_potential`.
-/

noncomputable section
open Real Set Filter MeasureTheory Topology
open scoped Gradient ENNReal

namespace LiquidDrop.CapacitaryK

/-- `eq:K-measure-ineq-pointwise` for the capacitary potential at almost every level
`t ∈ (0,1)`, for the canonical `p`, `F`: `p(t)²/F(t) − 8π ≤ ∫_{u=t}(|A|² + |∇_Σ log w|²)`. -/
theorem capacitary_level_inequality_ae
    {K : Set E3} (hK : IsCompact K) (hKconn : IsConnected K) (hcompl : IsPreconnected Kᶜ)
    (hzero : (0 : E3) ∈ interior K)
    {u : E3 → ℝ} (hu : Continuous u)
    (hh : HasDistributionalLaplacianOn u (fun _ => 0) Kᶜ)
    (hb : ∀ x ∈ K, u x = 1) (hinf : Tendsto u (cocompact E3) (𝓝 0))
    {μ : Measure E3} (hμU : μ Kᶜᶜ = 0)
    (hμK : ∀ L : Set E3, IsCompact L → L ⊆ Kᶜ → μ L < ⊤)
    (hμ : ∀ φ : E3 → ℝ, ContDiff ℝ (⊤ : ℕ∞) φ → HasCompactSupport φ → tsupport φ ⊆ Kᶜ →
        ∫ x, gradNorm u x * laplacianN φ x = ∫ x, φ x ∂μ)
    {t₀ : ℝ} (ht₀ : t₀ ∈ Ioo (0 : ℝ) 1)
    (ht₀R : ∀ x ∈ Kᶜ, u x = t₀ → gradient u x ≠ 0) :
    ∀ᵐ t, t ∈ Ioo (0 : ℝ) 1 →
      Kp μ u t₀ (levelP Kᶜ u t₀) t ^ 2 / KFhat μ u t₀ (levelP Kᶜ u t₀) (levelF Kᶜ u t₀) t -
          8 * π ≤ levelDensity Kᶜ u t := by
  have hU : IsOpen Kᶜ := hK.isClosed.isOpen_compl
  have hu3 : ContDiffOn ℝ 3 u Kᶜ := (capacitary_potential_contDiffOn hK hu hh).of_le (by norm_num)
  have hΔ := kelvin_laplacianN_eq_zero_of_distributional hU hu.continuousOn hh
  have hslabs := capacitary_slabs hu hb hinf
  have hlevels := capacitary_levels ⟨0, interior_subset hzero⟩ hu hb hinf
  have hN := LiquidDrop.sard_three_dimensional_gradient hU hu3
  have hnot : ∀ᵐ s ∂volume, s ∉ u '' {x | x ∈ Kᶜ ∧ gradient u x = 0} :=
    measure_eq_zero_iff_ae_notMem.mp hN
  filter_upwards [hnot] with t ht h01
  have hR : ∀ x ∈ Kᶜ, u x = t → gradient u x ≠ 0 := fun x hx hxt h0 => ht ⟨x, ⟨hx, h0⟩, hxt⟩
  obtain ⟨hsub, hcpt, hne⟩ := hlevels t h01.1 h01.2
  have hreg' : ∀ x ∈ u ⁻¹' {t}, gradient u x ≠ 0 := fun x hx => hR x (hsub hx) hx
  have hset : Kᶜ ∩ u ⁻¹' {t} = u ⁻¹' {t} := inter_eq_right.mpr hsub
  obtain ⟨b, hb', hbR⟩ := exists_regular_value_mem hU hu3 h01.2
  obtain ⟨hKc, hcl⟩ := hslabs t b h01.1 hb'.1 hb'.2
  have hregab : ∀ x ∈ Kᶜ, (u x = t ∨ u x = b) → gradient u x ≠ 0 :=
    fun x hx h => h.elim (hR x hx) (hbR x hx)
  have hu1 : ContDiffOn ℝ 1 u Kᶜ := hu3.of_le (by norm_num)
  have hbdd := hKc.isBounded.subset subset_closure
  have hfin' := (slab_level_measure_lt_top hU hu1 hb'.1 hbdd hcl hregab).1
  have hfin : Measure.euclideanHausdorffMeasure 2 (u ⁻¹' {t}) < ⊤ := by rwa [hset] at hfin'
  have hFpos : 0 < levelF Kᶜ u t := by
    obtain ⟨x₀, hx₀⟩ := hne
    have hapos := level_measure_pos hU hu1 (hsub hx₀) hx₀ (hreg' x₀ hx₀)
    have hwc : ContinuousOn (fun x => gradNorm u x ^ 2) (Kᶜ ∩ u ⁻¹' {t}) :=
      ((continuousOn_gradNorm hU hu3).mono inter_subset_left).pow 2
    have hLc : IsCompact (Kᶜ ∩ u ⁻¹' {t}) := by rwa [hset]
    obtain ⟨y, hy, hymin⟩ := hLc.exists_isMinOn ⟨x₀, hsub hx₀, hx₀⟩ hwc
    have hm : 0 < gradNorm u y ^ 2 := by
      have : 0 < gradNorm u y := norm_pos_iff.mpr (hR y hy.1 hy.2)
      positivity
    have hLm : MeasurableSet (Kᶜ ∩ u ⁻¹' {t}) :=
      measurableSet_coarea_level_of_continuousOn hU.measurableSet hu3.continuousOn t
    have hint := slab_level_integrableOn hU hu1 hb'.1 hbdd hcl hregab (Or.inl rfl) hwc
    have hle : ∫ x in Kᶜ ∩ u ⁻¹' {t}, gradNorm u y ^ 2 ∂(Measure.euclideanHausdorffMeasure 2) ≤
        levelF Kᶜ u t := by
      apply setIntegral_mono_on _ hint hLm (fun x hx => hymin hx)
      exact integrableOn_const (hfin'.ne)
    refine lt_of_lt_of_le ?_ hle
    rw [setIntegral_const, smul_eq_mul]
    apply mul_pos _ hm
    exact ENNReal.toReal_pos hapos.ne' hfin'.ne
  rw [K_p_geometric_of_harmonic hU hu.measurable hu3 hΔ hμU hμK hμ hslabs ht₀ ht₀R t hR h01.1
      h01.2,
    KFhat_eq_levelF hU hu.measurable hu3 hΔ hμU hμK hμ hslabs ht₀ ht₀R t hR h01.1 h01.2]
  exact K_level_inequality_of_level_connected hU hu3 hΔ h01.1 h01.2 hsub hreg' hcpt hfin hFpos
    (capacitary_level_connected hK hKconn hcompl hzero hu hh hb hinf)

/-- The hypotheses of the one-dimensional cores `K_h_monotone_core` and `K_two_ineq_core`, all
proved for the capacitary potential with the canonical `p`, `F` based at a regular `t₀`:
local integrability of `p`, `DF = p dt`, `F > 0`, local integrability of `p²/F`,
`Dp ≥ (p²/F − 8π) dt`, and the far-field limits `h(t) → 0`, `(F(t) − 4πt²)/t⁴ → 0`. -/
theorem capacitary_K_level_structure
    {K : Set E3} (hK : IsCompact K) (hKconn : IsConnected K) (hcompl : IsPreconnected Kᶜ)
    (hzero : (0 : E3) ∈ interior K)
    {u : E3 → ℝ} (hu : Continuous u)
    (hh : HasDistributionalLaplacianOn u (fun _ => 0) Kᶜ)
    (hb : ∀ x ∈ K, u x = 1) (hinf : Tendsto u (cocompact E3) (𝓝 0))
    {μ : Measure E3} (hμU : μ Kᶜᶜ = 0)
    (hμK : ∀ L : Set E3, IsCompact L → L ⊆ Kᶜ → μ L < ⊤)
    (hμ : ∀ φ : E3 → ℝ, ContDiff ℝ (⊤ : ℕ∞) φ → HasCompactSupport φ → tsupport φ ⊆ Kᶜ →
        ∫ x, gradNorm u x * laplacianN φ x = ∫ x, φ x ∂μ)
    {t₀ : ℝ} (ht₀ : t₀ ∈ Ioo (0 : ℝ) 1)
    (ht₀R : ∀ x ∈ Kᶜ, u x = t₀ → gradient u x ≠ 0) :
    (∀ a b, 0 < a → a ≤ b → b < 1 →
      IntervalIntegrable (Kp μ u t₀ (levelP Kᶜ u t₀)) volume a b) ∧
    (∀ a b, 0 < a → a ≤ b → b < 1 →
      KFhat μ u t₀ (levelP Kᶜ u t₀) (levelF Kᶜ u t₀) b -
          KFhat μ u t₀ (levelP Kᶜ u t₀) (levelF Kᶜ u t₀) a =
        ∫ t in a..b, Kp μ u t₀ (levelP Kᶜ u t₀) t) ∧
    (∀ t, 0 < t → t < 1 → 0 < KFhat μ u t₀ (levelP Kᶜ u t₀) (levelF Kᶜ u t₀) t) ∧
    (∀ a b, 0 < a → a ≤ b → b < 1 →
      IntervalIntegrable (fun t => Kp μ u t₀ (levelP Kᶜ u t₀) t ^ 2 /
        KFhat μ u t₀ (levelP Kᶜ u t₀) (levelF Kᶜ u t₀) t) volume a b) ∧
    (∀ a b, 0 < a → a ≤ b → b < 1 →
      ∫ t in a..b, (Kp μ u t₀ (levelP Kᶜ u t₀) t ^ 2 /
          KFhat μ u t₀ (levelP Kᶜ u t₀) (levelF Kᶜ u t₀) t - 8 * π) ≤
        Kp μ u t₀ (levelP Kᶜ u t₀) b - Kp μ u t₀ (levelP Kᶜ u t₀) a) ∧
    Tendsto (levelH (KFhat μ u t₀ (levelP Kᶜ u t₀) (levelF Kᶜ u t₀))
      (Kp μ u t₀ (levelP Kᶜ u t₀))) (𝓝[>] 0) (𝓝 0) ∧
    Tendsto (fun t => (KFhat μ u t₀ (levelP Kᶜ u t₀) (levelF Kᶜ u t₀) t - 4 * π * t ^ 2) /
      t ^ 4) (𝓝[>] 0) (𝓝 0) := by
  have hU : IsOpen Kᶜ := hK.isClosed.isOpen_compl
  have hu3 : ContDiffOn ℝ 3 u Kᶜ := (capacitary_potential_contDiffOn hK hu hh).of_le (by norm_num)
  have hΔ := kelvin_laplacianN_eq_zero_of_distributional hU hu.continuousOn hh
  have hfin := K_slab_mass_finite hμU hμK (capacitary_slabs hu hb hinf)
  obtain ⟨d, hdm, hdeq, hdens⟩ :=
    K_pushforward_lower_density hU hu.measurable hu3 hΔ hμU hμK hμ hfin
  obtain ⟨hm, -, hi, hF, -, hDp⟩ :=
    K_structure hu.measurable ht₀ hfin (p₀ := levelP Kᶜ u t₀) (F₀ := levelF Kᶜ u t₀)
  obtain ⟨hFexp, hpexp, hz0, hh0⟩ :=
    capacitary_K_far_field_unconditional hK hzero hu hh hb hinf hμU hμK hμ ht₀ ht₀R
  have hFpos : ∀ t, 0 < t → t < 1 → 0 < KFhat μ u t₀ (levelP Kᶜ u t₀) (levelF Kᶜ u t₀) t :=
    fun t h0 h1 => (pos_of_expansions hm hi hF hFexp hpexp t h0 h1).2
  have hFc : ContinuousOn (KFhat μ u t₀ (levelP Kᶜ u t₀) (levelF Kᶜ u t₀)) (Ioo 0 1) :=
    fun t ht => (continuousAt_of_primitive hi hF ht.1 ht.2).continuousWithinAt
  have hνfin : ∀ a b, 0 < a → a ≤ b → b < 1 → (μ.map u) (Ioc a b) ≠ ⊤ := by
    intro a b ha hab hb1
    rw [Measure.map_apply hu.measurable measurableSet_Ioc]
    exact hfin a b ha hab hb1
  have hd : ∀ᵐ t, t ∈ Ioo (0 : ℝ) 1 →
      Kp μ u t₀ (levelP Kᶜ u t₀) t ^ 2 / KFhat μ u t₀ (levelP Kᶜ u t₀) (levelF Kᶜ u t₀) t -
        8 * π ≤ d t := by
    filter_upwards [capacitary_level_inequality_ae hK hKconn hcompl hzero hu hh hb hinf hμU hμK
      hμ ht₀ ht₀R, hdeq] with t h1 h2 ht
    rw [h2 ht]
    exact h1 ht
  obtain ⟨hq, hD⟩ := K_measure_inequality hm hFc hFpos hDp hνfin hdm hdens hd
  exact ⟨hi, hF, hFpos, hq, hD, hh0, hz0⟩

/-- **`lem:K-h-monotone`** (`eq:K-Dh`) for the capacitary potential, with no named hypothesis.
With `p`, `F` the canonical representatives based at a regular value `t₀ ∈ (0,1)` and
`h = p − 4F/t + 8πt` (`eq:K-h`, `levelH F p`): `Dh ≥ (p/√F − 2√F/t)² dt` on every
`[a,b] ⊆ (0,1)`, in the increment form
`∫_a^b (p/√F − 2√F/t)² ≤ h(b) − h(a)`, and `h` is nondecreasing on `(0,1)`. -/
theorem capacitary_K_h_monotone
    {K : Set E3} (hK : IsCompact K) (hKconn : IsConnected K) (hcompl : IsPreconnected Kᶜ)
    (hzero : (0 : E3) ∈ interior K)
    {u : E3 → ℝ} (hu : Continuous u)
    (hh : HasDistributionalLaplacianOn u (fun _ => 0) Kᶜ)
    (hb : ∀ x ∈ K, u x = 1) (hinf : Tendsto u (cocompact E3) (𝓝 0))
    {μ : Measure E3} (hμU : μ Kᶜᶜ = 0)
    (hμK : ∀ L : Set E3, IsCompact L → L ⊆ Kᶜ → μ L < ⊤)
    (hμ : ∀ φ : E3 → ℝ, ContDiff ℝ (⊤ : ℕ∞) φ → HasCompactSupport φ → tsupport φ ⊆ Kᶜ →
        ∫ x, gradNorm u x * laplacianN φ x = ∫ x, φ x ∂μ)
    {t₀ : ℝ} (ht₀ : t₀ ∈ Ioo (0 : ℝ) 1)
    (ht₀R : ∀ x ∈ Kᶜ, u x = t₀ → gradient u x ≠ 0) :
    (∀ a b, 0 < a → a ≤ b → b < 1 →
      ∫ t in a..b, (Kp μ u t₀ (levelP Kᶜ u t₀) t /
            √(KFhat μ u t₀ (levelP Kᶜ u t₀) (levelF Kᶜ u t₀) t) -
          2 * √(KFhat μ u t₀ (levelP Kᶜ u t₀) (levelF Kᶜ u t₀) t) / t) ^ 2 ≤
        levelH (KFhat μ u t₀ (levelP Kᶜ u t₀) (levelF Kᶜ u t₀)) (Kp μ u t₀ (levelP Kᶜ u t₀)) b -
          levelH (KFhat μ u t₀ (levelP Kᶜ u t₀) (levelF Kᶜ u t₀))
            (Kp μ u t₀ (levelP Kᶜ u t₀)) a) ∧
    MonotoneOn (levelH (KFhat μ u t₀ (levelP Kᶜ u t₀) (levelF Kᶜ u t₀))
      (Kp μ u t₀ (levelP Kᶜ u t₀))) (Ioo 0 1) := by
  obtain ⟨hi, hF, hFpos, hq, hD, -, -⟩ :=
    capacitary_K_level_structure hK hKconn hcompl hzero hu hh hb hinf hμU hμK hμ ht₀ ht₀R
  exact K_h_monotone_core hi hF hFpos hq hD

/-- **`prop:K-two-ineq`** (`eq:K-p-bound`, `eq:K-F-bound`) for the capacitary potential, with
no named hypothesis: with `p`, `F` the canonical representatives based at a regular value
`t₀ ∈ (0,1)`, for every `t ∈ (0,1)`, `p(t) ≥ 4F(t)/t − 8πt` and `F(t) ≥ 4πt²`. -/
theorem capacitary_K_two_ineq
    {K : Set E3} (hK : IsCompact K) (hKconn : IsConnected K) (hcompl : IsPreconnected Kᶜ)
    (hzero : (0 : E3) ∈ interior K)
    {u : E3 → ℝ} (hu : Continuous u)
    (hh : HasDistributionalLaplacianOn u (fun _ => 0) Kᶜ)
    (hb : ∀ x ∈ K, u x = 1) (hinf : Tendsto u (cocompact E3) (𝓝 0))
    {μ : Measure E3} (hμU : μ Kᶜᶜ = 0)
    (hμK : ∀ L : Set E3, IsCompact L → L ⊆ Kᶜ → μ L < ⊤)
    (hμ : ∀ φ : E3 → ℝ, ContDiff ℝ (⊤ : ℕ∞) φ → HasCompactSupport φ → tsupport φ ⊆ Kᶜ →
        ∫ x, gradNorm u x * laplacianN φ x = ∫ x, φ x ∂μ)
    {t₀ : ℝ} (ht₀ : t₀ ∈ Ioo (0 : ℝ) 1)
    (ht₀R : ∀ x ∈ Kᶜ, u x = t₀ → gradient u x ≠ 0) :
    ∀ t, 0 < t → t < 1 →
      4 * KFhat μ u t₀ (levelP Kᶜ u t₀) (levelF Kᶜ u t₀) t / t - 8 * π * t ≤
          Kp μ u t₀ (levelP Kᶜ u t₀) t ∧
        4 * π * t ^ 2 ≤ KFhat μ u t₀ (levelP Kᶜ u t₀) (levelF Kᶜ u t₀) t := by
  obtain ⟨hi, hF, hFpos, hq, hD, hh0, hz0⟩ :=
    capacitary_K_level_structure hK hKconn hcompl hzero hu hh hb hinf hμU hμK hμ ht₀ ht₀R
  exact K_two_ineq_core hi hF hFpos hq hD hh0 hz0

/-- `lem:K-h-monotone` and `prop:K-two-ineq` with the measure `μ = Δ|∇u|` of `prop:K-mu`
supplied by `K_mu`: there is a measure `μ` carried by `Kᶜ`, finite on compact subsets of `Kᶜ`,
with `∫ |∇u| Δφ = ∫ φ dμ` for smooth `φ` compactly supported in `Kᶜ`, such that for every
regular value `t₀ ∈ (0,1)` the canonical `p`, `F` based at `t₀` satisfy the conclusions of
`capacitary_K_h_monotone` and `capacitary_K_two_ineq`. -/
theorem exists_capacitary_K_mu_h_monotone_two_ineq
    {K : Set E3} (hK : IsCompact K) (hKconn : IsConnected K) (hcompl : IsPreconnected Kᶜ)
    (hzero : (0 : E3) ∈ interior K)
    {u : E3 → ℝ} (hu : Continuous u)
    (hh : HasDistributionalLaplacianOn u (fun _ => 0) Kᶜ)
    (hb : ∀ x ∈ K, u x = 1) (hinf : Tendsto u (cocompact E3) (𝓝 0)) :
    ∃ μ : Measure E3, μ Kᶜᶜ = 0 ∧ (∀ L : Set E3, IsCompact L → L ⊆ Kᶜ → μ L < ⊤) ∧
      (∀ φ : E3 → ℝ, ContDiff ℝ (⊤ : ℕ∞) φ → HasCompactSupport φ → tsupport φ ⊆ Kᶜ →
        ∫ x, gradNorm u x * laplacianN φ x = ∫ x, φ x ∂μ) ∧
      ∀ t₀ ∈ Ioo (0 : ℝ) 1, (∀ x ∈ Kᶜ, u x = t₀ → gradient u x ≠ 0) →
        ((∀ a b, 0 < a → a ≤ b → b < 1 →
          ∫ t in a..b, (Kp μ u t₀ (levelP Kᶜ u t₀) t /
                √(KFhat μ u t₀ (levelP Kᶜ u t₀) (levelF Kᶜ u t₀) t) -
              2 * √(KFhat μ u t₀ (levelP Kᶜ u t₀) (levelF Kᶜ u t₀) t) / t) ^ 2 ≤
            levelH (KFhat μ u t₀ (levelP Kᶜ u t₀) (levelF Kᶜ u t₀))
                (Kp μ u t₀ (levelP Kᶜ u t₀)) b -
              levelH (KFhat μ u t₀ (levelP Kᶜ u t₀) (levelF Kᶜ u t₀))
                (Kp μ u t₀ (levelP Kᶜ u t₀)) a) ∧
        MonotoneOn (levelH (KFhat μ u t₀ (levelP Kᶜ u t₀) (levelF Kᶜ u t₀))
          (Kp μ u t₀ (levelP Kᶜ u t₀))) (Ioo 0 1)) ∧
        ∀ t, 0 < t → t < 1 →
          4 * KFhat μ u t₀ (levelP Kᶜ u t₀) (levelF Kᶜ u t₀) t / t - 8 * π * t ≤
              Kp μ u t₀ (levelP Kᶜ u t₀) t ∧
            4 * π * t ^ 2 ≤ KFhat μ u t₀ (levelP Kᶜ u t₀) (levelF Kᶜ u t₀) t := by
  have hU : IsOpen Kᶜ := hK.isClosed.isOpen_compl
  have hu3 : ContDiffOn ℝ 3 u Kᶜ := (capacitary_potential_contDiffOn hK hu hh).of_le (by norm_num)
  have hΔ := kelvin_laplacianN_eq_zero_of_distributional hU hu.continuousOn hh
  obtain ⟨μ, hμU, hμK, hμ⟩ := K_mu hU hu3 hΔ
  exact ⟨μ, hμU, hμK, hμ, fun t₀ ht₀ ht₀R =>
    ⟨capacitary_K_h_monotone hK hKconn hcompl hzero hu hh hb hinf hμU hμK hμ ht₀ ht₀R,
      capacitary_K_two_ineq hK hKconn hcompl hzero hu hh hb hinf hμU hμK hμ ht₀ ht₀R⟩⟩

end LiquidDrop.CapacitaryK

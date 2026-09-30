module

public import NoCompromise.CapacitaryK.FarFieldZero
public import NoCompromise.CapacitaryK.Endpoint

@[expose] public section

/-!
# Finite collar mass (chapter 31, `thm:capacitary-inequalities`, endpoint step)

A positive lower bound for the gradient norm and a uniform bound for `H|∇u|`
near the boundary level give finite mass to `{t₀ < u < 1}`. Harmonic flux
conservation bounds the geometric representative `p` uniformly there; continuity
from below then bounds the collar mass. Consequently both canonical endpoint
limits exist. Identifying these limits with `∫_{∂K} H|∇u|` and
`∫_{∂K} |∇u|²` is not part of this result.
-/

noncomputable section

open Real Set Filter MeasureTheory Topology
open scoped Gradient ENNReal

namespace LiquidDrop.CapacitaryK

/-- A positive gradient lower bound converts a bound for `H|∇u|` into a
bound for the absolute geometric level integral by the flux. -/
lemma abs_levelP_le_mul_flux_of_collar {U : Set E3} (hU : IsOpen U) {u : E3 → ℝ}
    (hu : ContDiffOn ℝ 3 u U)
    (hslabs : ∀ a b, 0 < a → a < b → b < 1 →
      IsCompact (closure (U ∩ u ⁻¹' Ioo a b)) ∧ closure (U ∩ u ⁻¹' Ioo a b) ⊆ U)
    {t c M : ℝ} (ht : 0 < t) (ht1 : t < 1) (hc : 0 < c)
    (hbound : ∀ x ∈ U ∩ u ⁻¹' {t},
      c ≤ gradNorm u x ∧ |meanCurv u x * gradNorm u x| ≤ M) :
    |levelP U u t| ≤ (|M| / c) *
      ∫ x in U ∩ u ⁻¹' {t}, gradNorm u x ∂(Measure.euclideanHausdorffMeasure 2) := by
  have hreg : ∀ x ∈ U, u x = t → gradient u x ≠ 0 := by
    intro x hx he
    exact norm_pos_iff.mp (hc.trans_le (hbound x ⟨hx, he⟩).1)
  obtain ⟨b, hb, hbR⟩ := exists_regular_value_mem hU hu ht1
  obtain ⟨hK, hcl⟩ := hslabs t b ht hb.1 hb.2
  have hregab : ∀ x ∈ U, (u x = t ∨ u x = b) → gradient u x ≠ 0 :=
    fun x hx h => h.elim (hreg x hx) (hbR x hx)
  have hi := slab_level_integrableOn hU (hu.of_le (by norm_num)) hb.1
    (hK.isBounded.subset subset_closure) hcl hregab (Or.inl rfl)
    ((continuousOn_gradNorm hU hu).mono inter_subset_left)
  have hle := norm_integral_le_of_norm_le (hi.const_mul (|M| / c)) (f :=
    fun x => meanCurv u x * gradNorm u x) (by
      filter_upwards [ae_restrict_mem
        (measurableSet_coarea_level_of_continuousOn hU.measurableSet hu.continuousOn t)] with x hx
      rw [Real.norm_eq_abs]
      calc
        |meanCurv u x * gradNorm u x| ≤ |M| := (hbound x hx).2.trans (le_abs_self M)
        _ = (|M| / c) * c := by field_simp
        _ ≤ (|M| / c) * gradNorm u x :=
          mul_le_mul_of_nonneg_left (hbound x hx).1 (div_nonneg (abs_nonneg M) hc.le))
  simpa only [Real.norm_eq_abs, integral_const_mul, levelP] using hle

/-- `thm:capacitary-inequalities`, endpoint step: uniform collar bounds for
the gradient and `H|∇u|` imply finite mass of `{t₀ < u < 1}`. -/
theorem collar_mass_ne_top {U : Set E3} (hU : IsOpen U) {u : E3 → ℝ}
    (humeas : Measurable u) (hu : ContDiffOn ℝ 3 u U) (hΔ : ∀ x ∈ U, laplacianN u x = 0)
    {μ : Measure E3} (hμU : μ Uᶜ = 0)
    (hμK : ∀ K : Set E3, IsCompact K → K ⊆ U → μ K < ⊤)
    (hμ : ∀ φ : E3 → ℝ, ContDiff ℝ (⊤ : ℕ∞) φ → HasCompactSupport φ → tsupport φ ⊆ U →
        ∫ x, gradNorm u x * laplacianN φ x = ∫ x, φ x ∂μ)
    (hslabs : ∀ a b, 0 < a → a < b → b < 1 →
      IsCompact (closure (U ∩ u ⁻¹' Ioo a b)) ∧ closure (U ∩ u ⁻¹' Ioo a b) ⊆ U)
    {t₀ : ℝ} (ht₀ : t₀ ∈ Ioo (0 : ℝ) 1)
    (ht₀R : ∀ x ∈ U, u x = t₀ → gradient u x ≠ 0)
    (hcollar : ∃ t₁ < 1, ∃ c > 0, ∃ M, ∀ x ∈ U, t₁ < u x →
      c ≤ gradNorm u x ∧ |meanCurv u x * gradNorm u x| ≤ M) :
    μ (u ⁻¹' Ioo t₀ 1) ≠ ⊤ := by
  obtain ⟨t₁, ht₁, c, hc, M, hbound⟩ := hcollar
  have hmax : max t₀ t₁ < 1 := max_lt ht₀.2 ht₁
  obtain ⟨s, hs, _⟩ := exists_regular_value_mem hU hu hmax
  have hs0 : 0 < s := ht₀.1.trans ((le_max_left _ _).trans_lt hs.1)
  have hs1 : t₁ < s := (le_max_right _ _).trans_lt hs.1
  have hreg (t : ℝ) (ht : t₁ < t) : ∀ x ∈ U, u x = t → gradient u x ≠ 0 := by
    intro x hx he
    exact norm_pos_iff.mp (hc.trans_le (hbound x hx (he ▸ ht)).1)
  let Φ : ℝ → ℝ := fun t =>
    ∫ x in U ∩ u ⁻¹' {t}, gradNorm u x ∂(Measure.euclideanHausdorffMeasure 2)
  have hflux (a b : ℝ) (ha : 0 < a) (ha1 : t₁ < a) (hab : a < b) (hb : b < 1) :
      Φ a = Φ b := by
    obtain ⟨hK, hcl⟩ := hslabs a b ha hab hb
    exact level_flux_eq hU hu hΔ hab hK hcl
      (fun x hx he => he.elim (hreg a ha1 x hx) (hreg b (ha1.trans hab) x hx))
  let B := (|M| / c) * Φ s
  have hpbound (t : ℝ) (ht : t ∈ Ioo (max t₀ t₁) 1) :
      Kp μ u t₀ (levelP U u t₀) t ≤ B := by
    have ht0 : 0 < t := ht₀.1.trans ((le_max_left _ _).trans_lt ht.1)
    have ht1 : t₁ < t := (le_max_right _ _).trans_lt ht.1
    have he : Φ t = Φ s := by
      rcases lt_trichotomy t s with h | h | h
      · exact hflux t s ht0 ht1 h hs.2
      · rw [h]
      · exact (hflux s t hs0 hs1 h ht.2).symm
    rw [K_p_geometric_of_harmonic hU humeas hu hΔ hμU hμK hμ hslabs ht₀ ht₀R t
      (hreg t ht1) ht0 ht.2]
    have hb := abs_levelP_le_mul_flux_of_collar hU hu hslabs ht0 ht.2 hc
      (M := M) (fun x hx => hbound x hx.1 (hx.2 ▸ ht1))
    change |levelP U u t| ≤ (|M| / c) * Φ t at hb
    rw [he] at hb
    exact (le_abs_self _).trans hb
  have hfin := K_slab_mass_finite hμU hμK hslabs
  have hmass (t : ℝ) (ht : t ∈ Ioo (max t₀ t₁) 1) :
      μ (u ⁻¹' Ioc t₀ t) ≤ ENNReal.ofReal (B - levelP U u t₀) := by
    have ht0 : t₀ ≤ t := ((le_max_left _ _).trans_lt ht.1).le
    have hp := hpbound t ht
    simp only [Kp, ite_eq_left ht0] at hp
    rw [← ENNReal.ofReal_toReal (hfin t₀ t ht₀.1 ht0 ht.2)]
    exact ENNReal.ofReal_le_ofReal (by linarith)
  obtain ⟨r, hrmono, hrmem, hrlim⟩ := exists_seq_strictMono_tendsto' hmax
  have hsets : Monotone (fun n => u ⁻¹' Ioc t₀ (r n)) :=
    fun i j hij => preimage_mono (Ioc_subset_Ioc_right (hrmono.monotone hij))
  have hunion : u ⁻¹' Ioo t₀ 1 = ⋃ n, u ⁻¹' Ioc t₀ (r n) := by
    ext x
    constructor
    · intro hx
      obtain ⟨n, hn⟩ := (hrlim.eventually (eventually_gt_nhds hx.2)).exists
      exact mem_iUnion.mpr ⟨n, hx.1, hn.le⟩
    · intro hx
      obtain ⟨n, hn⟩ := mem_iUnion.mp hx
      exact ⟨hn.1, hn.2.trans_lt (hrmem n).2⟩
  refine ne_top_of_le_ne_top (ENNReal.ofReal_ne_top (r := B - levelP U u t₀)) ?_
  rw [hunion, hsets.measure_iUnion]
  exact iSup_le (fun n => hmass (r n) (hrmem n))

/-- The canonical endpoint limits exist under the collar bounds, without
asserting any identification with integrals on the boundary. -/
theorem Kp_KFhat_tendsto_one_of_collar {U : Set E3} (hU : IsOpen U) {u : E3 → ℝ}
    (humeas : Measurable u) (hu : ContDiffOn ℝ 3 u U) (hΔ : ∀ x ∈ U, laplacianN u x = 0)
    {μ : Measure E3} (hμU : μ Uᶜ = 0)
    (hμK : ∀ K : Set E3, IsCompact K → K ⊆ U → μ K < ⊤)
    (hμ : ∀ φ : E3 → ℝ, ContDiff ℝ (⊤ : ℕ∞) φ → HasCompactSupport φ → tsupport φ ⊆ U →
        ∫ x, gradNorm u x * laplacianN φ x = ∫ x, φ x ∂μ)
    (hslabs : ∀ a b, 0 < a → a < b → b < 1 →
      IsCompact (closure (U ∩ u ⁻¹' Ioo a b)) ∧ closure (U ∩ u ⁻¹' Ioo a b) ⊆ U)
    {t₀ : ℝ} (ht₀ : t₀ ∈ Ioo (0 : ℝ) 1)
    (ht₀R : ∀ x ∈ U, u x = t₀ → gradient u x ≠ 0)
    (hcollar : ∃ t₁ < 1, ∃ c > 0, ∃ M, ∀ x ∈ U, t₁ < u x →
      c ≤ gradNorm u x ∧ |meanCurv u x * gradNorm u x| ≤ M) :
    Tendsto (Kp μ u t₀ (levelP U u t₀)) (𝓝[<] 1)
        (𝓝 (levelP U u t₀ + (μ (u ⁻¹' Ioo t₀ 1)).toReal)) ∧
      Tendsto (KFhat μ u t₀ (levelP U u t₀) (levelF U u t₀)) (𝓝[<] 1)
        (𝓝 (levelF U u t₀ + ∫ t in t₀..1, Kp μ u t₀ (levelP U u t₀) t)) :=
  Kp_KFhat_tendsto_one humeas ht₀
    (collar_mass_ne_top hU humeas hu hΔ hμU hμK hμ hslabs ht₀ ht₀R hcollar)

end LiquidDrop.CapacitaryK

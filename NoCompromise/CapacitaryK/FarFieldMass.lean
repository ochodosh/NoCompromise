import NoCompromise.CapacitaryK.Representatives
import Mathlib.Analysis.Asymptotics.Lemmas

/-!
# `p` as the mass of the far region (chapter 31, towards `eq:K-p-expansion`)

When `p(0+) = 0` (proved for the capacitary potential in `Kp_tendsto_zero_of_decay`), the canonical
representative of `def:K-p` is the `μ`-mass of the far region: `p(t) = μ{0 < u ≤ t}`. Hence
`eq:K-p-expansion`, `p(t) = 8πt + O(t⁴)`, is equivalent to the volume statement
`μ{0 < u ≤ t} = 8πt + O(t⁴)` for `μ = Δ|∇u|`, which involves no level-surface geometry.
-/

noncomputable section
open Real Set Filter MeasureTheory Topology Asymptotics
open scoped ENNReal

namespace LiquidDrop.CapacitaryK

variable {X : Type*} [MeasurableSpace X]

/-- If `p(0+) = 0` then `p(t) = μ{0 < u ≤ t}` (and this mass is finite) for `t ∈ (0,1)`. -/
theorem Kp_eq_measure_of_tendsto_zero {μ : Measure X} {u : X → ℝ} (hu : Measurable u)
    {t₀ p₀ : ℝ} (ht₀ : t₀ ∈ Ioo (0 : ℝ) 1)
    (hfin : ∀ a b, 0 < a → a ≤ b → b < 1 → μ (u ⁻¹' Ioc a b) ≠ ⊤)
    (h0 : Tendsto (Kp μ u t₀ p₀) (𝓝[>] 0) (𝓝 0)) {t : ℝ} (ht : 0 < t) (ht1 : t < 1) :
    μ (u ⁻¹' Ioc 0 t) = ENNReal.ofReal (Kp μ u t₀ p₀ t) ∧ 0 ≤ Kp μ u t₀ p₀ t := by
  let s : ℕ → ℝ := fun n => t / (n + 2)
  have hs0 : ∀ n, 0 < s n := fun n => div_pos ht (by positivity)
  have hst : ∀ n, s n ≤ t := fun n =>
    div_le_self ht.le (by linarith [(Nat.cast_nonneg n : (0:ℝ) ≤ n)])
  let S : ℕ → Set X := fun n => u ⁻¹' Ioc (s n) t
  have hmono : Monotone S := by
    intro m n hmn
    apply preimage_mono
    apply Ioc_subset_Ioc_left
    apply div_le_div_of_nonneg_left ht.le (by positivity)
    have : (m : ℝ) ≤ n := Nat.cast_le.mpr hmn
    linarith
  have hU : (⋃ n, S n) = u ⁻¹' Ioc 0 t := by
    ext x
    simp only [S, mem_iUnion, mem_preimage, mem_Ioc]
    constructor
    · rintro ⟨n, hn1, hn2⟩
      exact ⟨(hs0 n).trans hn1, hn2⟩
    · rintro ⟨hx1, hx2⟩
      obtain ⟨n, hn⟩ := exists_nat_gt (t / u x)
      refine ⟨n, ?_, hx2⟩
      rw [div_lt_iff₀ (by positivity : (0:ℝ) < (n:ℝ) + 2)]
      rw [div_lt_iff₀ hx1] at hn
      nlinarith
  have hinc : ∀ n, μ (S n) = ENNReal.ofReal (Kp μ u t₀ p₀ t - Kp μ u t₀ p₀ (s n)) := by
    intro n
    have he := Kp_increment hu ht₀ hfin (hs0 n) (hst n) ht1 (p₀ := p₀)
    rw [Measure.map_apply hu measurableSet_Ioc] at he
    rw [he, ENNReal.ofReal_toReal (hfin _ _ (hs0 n) (hst n) ht1)]
  have hsl : Tendsto s atTop (𝓝[>] 0) := by
    apply tendsto_nhdsWithin_of_tendsto_nhds_of_eventually_within
    · refine tendsto_const_nhds.div_atTop ?_
      exact tendsto_atTop_add_const_right _ 2 tendsto_natCast_atTop_atTop
    · exact Eventually.of_forall hs0
  have hKp := h0.comp hsl
  have hlim1 : Tendsto (μ ∘ S) atTop (𝓝 (ENNReal.ofReal (Kp μ u t₀ p₀ t - 0))) := by
    have h := (ENNReal.continuous_ofReal.tendsto _).comp
      ((tendsto_const_nhds (x := Kp μ u t₀ p₀ t)).sub hKp)
    refine h.congr' (Eventually.of_forall fun n => ?_)
    simp only [Function.comp, hinc n]
  have hlim2 := tendsto_measure_iUnion_atTop (μ := μ) hmono
  rw [hU] at hlim2
  rw [sub_zero] at hlim1
  refine ⟨tendsto_nhds_unique hlim2 hlim1, ?_⟩
  have hge : ∀ n, 0 ≤ Kp μ u t₀ p₀ t - Kp μ u t₀ p₀ (s n) := by
    intro n
    have he := Kp_increment hu ht₀ hfin (hs0 n) (hst n) ht1 (p₀ := p₀)
    rw [he]
    exact ENNReal.toReal_nonneg
  have hlim3 : Tendsto (fun n => Kp μ u t₀ p₀ t - Kp μ u t₀ p₀ (s n)) atTop
      (𝓝 (Kp μ u t₀ p₀ t - 0)) := (tendsto_const_nhds).sub hKp
  rw [sub_zero] at hlim3
  exact ge_of_tendsto' hlim3 hge

/-- With `p(0+) = 0`, `eq:K-p-expansion` for `p` is equivalent to the far-region mass expansion
`μ{0 < u ≤ t} = 8πt + O(t⁴)`. -/
theorem Kp_expansion_iff_measure_expansion {μ : Measure X} {u : X → ℝ} (hu : Measurable u)
    {t₀ p₀ : ℝ} (ht₀ : t₀ ∈ Ioo (0 : ℝ) 1)
    (hfin : ∀ a b, 0 < a → a ≤ b → b < 1 → μ (u ⁻¹' Ioc a b) ≠ ⊤)
    (h0 : Tendsto (Kp μ u t₀ p₀) (𝓝[>] 0) (𝓝 0)) :
    (fun t => Kp μ u t₀ p₀ t - 8 * π * t) =O[𝓝[>] 0] (fun t => t ^ 4) ↔
      (fun t => (μ (u ⁻¹' Ioc 0 t)).toReal - 8 * π * t) =O[𝓝[>] 0] (fun t => t ^ 4) := by
  have heq : (fun t => Kp μ u t₀ p₀ t - 8 * π * t) =ᶠ[𝓝[>] 0]
      (fun t => (μ (u ⁻¹' Ioc 0 t)).toReal - 8 * π * t) := by
    filter_upwards [Ioo_mem_nhdsGT (zero_lt_one' ℝ)] with t ht
    obtain ⟨hm, hnn⟩ := Kp_eq_measure_of_tendsto_zero hu ht₀ hfin h0 ht.1 ht.2
    rw [hm, ENNReal.toReal_ofReal hnn]
  exact isBigO_congr heq EventuallyEq.rfl

end LiquidDrop.CapacitaryK

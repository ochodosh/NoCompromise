module

public import NoCompromise.CapacitaryK.OneDim
public import Mathlib.Analysis.SpecialFunctions.Pow.Real
public import Mathlib.Topology.Order.Basic

@[expose] public section

/-!
# The measure inequality and the capacitary inequalities (chapter 31)

This file collects the one-dimensional arguments of `lem:K-h-monotone`, `prop:K-two-ineq` and
`thm:capacitary-inequalities` in terms of abstract level functionals `F, p : ℝ → ℝ` on `(0,1)`.

The hypotheses encode the conclusions of `prop:K-structure` (`DF = p dt`),
`prop:K-measure-inequality` (`Dp ≥ (p²/F - 8π) dt`, as `∫_a^b (p²/F - 8π) ≤ p b - p a` for
the right-continuous `p`) and `lem:K-far-field`; those items are not yet formalised, so the
results here are the one-dimensional cores only. The analysis is in `CapacitaryK/OneDim.lean`.

* `CapacitaryK.K_h_monotone_core`: `lem:K-h-monotone`.
* `CapacitaryK.K_two_ineq_core`: `prop:K-two-ineq`.
* `CapacitaryK.capacitary_inequalities_core`: `thm:capacitary-inequalities` from the level
  inequalities and the endpoint limits.
* `CapacitaryK.capacitary_endpoint_inequalities`: the endpoint step of
  `thm:capacitary-inequalities`. If `p(t) ≥ 4F(t)/t - 8πt` and `F(t) ≥ 4πt²` on `(0,1)` and
  `F(t) → F(1)`, `p(t) → p(1)` as `t ↑ 1`, then `F(1) ≥ 4π` and `p(1) ≥ 4F(1) - 8π`.
-/

noncomputable section

open Real Set Filter MeasureTheory intervalIntegral Topology

namespace LiquidDrop
open CapacitaryK

/-- Endpoint step of `thm:capacitary-inequalities`: the two level inequalities of
`prop:K-two-ineq` pass to the left limits `F(1) := lim_{t↑1} F(t)`, `p(1) := lim_{t↑1} p(t)`. -/
theorem CapacitaryK.capacitary_endpoint_inequalities {F p : ℝ → ℝ} {F1 p1 : ℝ}
    (hineq : ∀ t, 0 < t → t < 1 → 4 * F t / t - 8 * π * t ≤ p t ∧ 4 * π * t ^ 2 ≤ F t)
    (hF1 : Tendsto F (𝓝[<] 1) (𝓝 F1)) (hp1 : Tendsto p (𝓝[<] 1) (𝓝 p1)) :
    4 * π ≤ F1 ∧ 4 * F1 - 8 * π ≤ p1 := by
  have hev : ∀ᶠ t in 𝓝[<] (1:ℝ), 0 < t ∧ t < 1 := by
    have h0 : ∀ᶠ t in 𝓝[<] (1:ℝ), 0 < t :=
      nhdsWithin_le_nhds (eventually_gt_nhds (by norm_num : (0:ℝ) < 1))
    filter_upwards [h0, self_mem_nhdsWithin] with t ht0 ht1 using ⟨ht0, ht1⟩
  have hid : Tendsto (fun t : ℝ => t) (𝓝[<] (1:ℝ)) (𝓝 1) := nhdsWithin_le_nhds
  constructor
  · have hlim : Tendsto (fun t : ℝ => 4 * π * t ^ 2) (𝓝[<] (1:ℝ)) (𝓝 (4 * π * 1 ^ 2)) :=
      (hid.pow 2).const_mul _
    have := le_of_tendsto_of_tendsto hlim hF1 (hev.mono fun t ht => (hineq t ht.1 ht.2).2)
    simpa using this
  · have hlim : Tendsto (fun t : ℝ => 4 * F t / t - 8 * π * t) (𝓝[<] (1:ℝ))
        (𝓝 (4 * F1 / 1 - 8 * π * 1)) :=
      ((hF1.const_mul 4).div hid one_ne_zero).sub (hid.const_mul _)
    have := le_of_tendsto_of_tendsto hlim hp1 (hev.mono fun t ht => (hineq t ht.1 ht.2).1)
    simpa using this

/-- `lem:K-h-monotone`, one-dimensional core. On `(0,1)` let `DF = p dt`
(`F b - F a = ∫_a^b p`) and let `Dp ≥ (p²/F - 8π) dt` for the right-continuous `p`
(`∫_a^b (p²/F - 8π) ≤ p b - p a`), with `F > 0`. Then `h = p - 4F/t + 8πt` satisfies
`Dh ≥ (p/√F - 2√F/t)² dt` on every `[a,b] ⊆ (0,1)` and is nondecreasing on `(0,1)`.
The hypotheses are the conclusions of `prop:K-structure` and `prop:K-measure-inequality`. -/
theorem CapacitaryK.K_h_monotone_core {F p : ℝ → ℝ}
    (hpint : ∀ a b, 0 < a → a ≤ b → b < 1 → IntervalIntegrable p volume a b)
    (hF : ∀ a b, 0 < a → a ≤ b → b < 1 → F b - F a = ∫ t in a..b, p t)
    (hFpos : ∀ t, 0 < t → t < 1 → 0 < F t)
    (hq : ∀ a b, 0 < a → a ≤ b → b < 1 →
      IntervalIntegrable (fun t => p t ^ 2 / F t) volume a b)
    (hDp : ∀ a b, 0 < a → a ≤ b → b < 1 → ∫ t in a..b, (p t ^ 2 / F t - 8 * π) ≤ p b - p a) :
    (∀ a b, 0 < a → a ≤ b → b < 1 →
      ∫ t in a..b, (p t / √(F t) - 2 * √(F t) / t) ^ 2 ≤ levelH F p b - levelH F p a) ∧
    MonotoneOn (levelH F p) (Ioo 0 1) :=
  ⟨fun _ _ ha hab hb => levelH_increment_ge hpint hF hFpos hq hDp ha hab hb,
    levelH_monotoneOn hpint hF hFpos hq hDp⟩

/-- `prop:K-two-ineq`, one-dimensional core: from the hypotheses of `K_h_monotone_core`
and the far-field limits `h(t) → 0`, `(F(t) - 4πt²)/t⁴ → 0` as `t ↓ 0`
(`eq:K-far-field-limits`), `p(t) ≥ 4F(t)/t - 8πt` and `F(t) ≥ 4πt²` on `(0,1)`. -/
theorem CapacitaryK.K_two_ineq_core {F p : ℝ → ℝ}
    (hpint : ∀ a b, 0 < a → a ≤ b → b < 1 → IntervalIntegrable p volume a b)
    (hF : ∀ a b, 0 < a → a ≤ b → b < 1 → F b - F a = ∫ t in a..b, p t)
    (hFpos : ∀ t, 0 < t → t < 1 → 0 < F t)
    (hq : ∀ a b, 0 < a → a ≤ b → b < 1 →
      IntervalIntegrable (fun t => p t ^ 2 / F t) volume a b)
    (hDp : ∀ a b, 0 < a → a ≤ b → b < 1 → ∫ t in a..b, (p t ^ 2 / F t - 8 * π) ≤ p b - p a)
    (hh0 : Tendsto (levelH F p) (𝓝[>] 0) (𝓝 0))
    (hz0 : Tendsto (fun t => (F t - 4 * π * t ^ 2) / t ^ 4) (𝓝[>] 0) (𝓝 0)) :
    ∀ t, 0 < t → t < 1 → 4 * F t / t - 8 * π * t ≤ p t ∧ 4 * π * t ^ 2 ≤ F t :=
  fun _ ht0 ht1 => two_level_inequalities hpint hF (levelH_monotoneOn hpint hF hFpos hq hDp)
    hh0 hz0 ht0 ht1

/-- `thm:capacitary-inequalities`, one-dimensional core: with the endpoint values
`F(1) = lim_{t↑1} F(t)` and `p(1) = lim_{t↑1} p(t)`, `F(1) ≥ 4π` and `p(1) ≥ 4F(1) - 8π`. -/
theorem CapacitaryK.capacitary_inequalities_core {F p : ℝ → ℝ} {F1 p1 : ℝ}
    (hpint : ∀ a b, 0 < a → a ≤ b → b < 1 → IntervalIntegrable p volume a b)
    (hF : ∀ a b, 0 < a → a ≤ b → b < 1 → F b - F a = ∫ t in a..b, p t)
    (hFpos : ∀ t, 0 < t → t < 1 → 0 < F t)
    (hq : ∀ a b, 0 < a → a ≤ b → b < 1 →
      IntervalIntegrable (fun t => p t ^ 2 / F t) volume a b)
    (hDp : ∀ a b, 0 < a → a ≤ b → b < 1 → ∫ t in a..b, (p t ^ 2 / F t - 8 * π) ≤ p b - p a)
    (hh0 : Tendsto (levelH F p) (𝓝[>] 0) (𝓝 0))
    (hz0 : Tendsto (fun t => (F t - 4 * π * t ^ 2) / t ^ 4) (𝓝[>] 0) (𝓝 0))
    (hF1 : Tendsto F (𝓝[<] 1) (𝓝 F1)) (hp1 : Tendsto p (𝓝[<] 1) (𝓝 p1)) :
    4 * π ≤ F1 ∧ 4 * F1 - 8 * π ≤ p1 :=
  capacitary_endpoint_inequalities (K_two_ineq_core hpint hF hFpos hq hDp hh0 hz0) hF1 hp1

end LiquidDrop

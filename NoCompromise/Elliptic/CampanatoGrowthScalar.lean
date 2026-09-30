module

public import NoCompromise.Elliptic.CampanatoIteration
public import Mathlib.Analysis.SpecialFunctions.Pow.Continuity

@[expose] public section

/-!
# Uniform subcritical energy iteration

The contraction is chosen before the starting radius. Both depend only on the
recurrence constants, and the final bound is uniform over all functions with
the prescribed initial energy bound.
-/

noncomputable section
open Set Filter Topology
open scoped Topology
namespace LiquidDrop

lemma campanato_exists_small_power {a R ε C : ℝ}
    (ha : 0 < a) (hR : 0 < R) (hε : 0 < ε) :
    ∃ r : ℝ, 0 < r ∧ r < R ∧ C * r ^ a < ε := by
  have ht : Tendsto (fun r : ℝ => C * r ^ a) (𝓝[>] 0) (𝓝 0) := by
    have hc := ((Real.continuous_rpow_const ha.le).continuousAt (x := (0 : ℝ))).const_mul C
    simpa only [Real.zero_rpow ha.ne', mul_zero] using
      hc.tendsto.mono_left nhdsWithin_le_nhds
  have hv := (tendsto_order.mp ht).2 ε hε
  have hr : ∀ᶠ r : ℝ in 𝓝[>] 0, r < R :=
    mem_nhdsWithin_of_mem_nhds (Iio_mem_nhds hR)
  have hp : ∀ᶠ r : ℝ in 𝓝[>] 0, 0 < r := self_mem_nhdsWithin
  exact (hp.and (hr.and hv)).exists

/-- A recurrence with principal exponent `d` and a vanishing error of order
`a` gives every smaller positive exponent, uniformly in the energy function. -/
theorem campanato_subcritical_growth_uniform {d a β R C D M : ℝ}
    (ha : 0 < a) (hβ : 0 < β) (hβd : β < d)
    (hR : 0 < R) (hR1 : R ≤ 1) (hC : 0 ≤ C) (hD : 0 ≤ D) (hM : 0 ≤ M) :
    ∃ K : ℝ, 0 < K ∧ ∀ Φ : ℝ → ℝ,
      (∀ r ∈ Ioc 0 R, 0 ≤ Φ r) → MonotoneOn Φ (Ioc 0 R) →
      (∀ r ∈ Ioc 0 R, Φ r ≤ M) →
      (∀ r ∈ Ioc 0 R, ∀ θ : ℝ, 0 < θ → θ < 1 →
        Φ (θ * r) ≤ C * (θ ^ d + r ^ a) * Φ r + D * r ^ (d + a)) →
      ∀ r ∈ Ioc 0 R, Φ r ≤ K * r ^ β := by
  obtain ⟨θ, hθ, hθ1, hθpow⟩ :=
    campanato_exists_small_power (sub_pos.mpr hβd) (by norm_num : (0 : ℝ) < 1)
      (by norm_num : (0 : ℝ) < 1 / 4) (C := C)
  have hθβ : 0 < θ ^ β := Real.rpow_pos_of_pos hθ β
  have hθdecay : C * θ ^ d ≤ (1 / 4 : ℝ) * θ ^ β := by
    have ht := mul_le_mul_of_nonneg_right hθpow.le hθβ.le
    have heq : θ ^ (d - β) * θ ^ β = θ ^ d := by
      rw [← Real.rpow_add hθ]
      congr 1
      ring
    simpa only [mul_assoc, heq] using ht
  obtain ⟨r₀, hr₀, hr₀R, hr₀pow⟩ := campanato_exists_small_power ha hR
    (div_pos hθβ (by norm_num : (0 : ℝ) < 4)) (C := C)
  have hr₀β : 0 < r₀ ^ β := Real.rpow_pos_of_pos hr₀ β
  let L := max (M / r₀ ^ β) (2 * D / θ ^ β)
  have hL : 0 ≤ L := (div_nonneg hM hr₀β.le).trans (le_max_left _ _)
  let K := max (L / θ ^ β) (M / r₀ ^ β) + 1
  have hK : 0 < K := by
    have : 0 ≤ max (L / θ ^ β) (M / r₀ ^ β) :=
      (div_nonneg hL hθβ.le).trans (le_max_left _ _)
    dsimp [K]
    linarith
  refine ⟨K, hK, ?_⟩
  intro Φ hnonneg hmono hbound hrec r hr
  have hrec' : ∀ s ∈ Ioc 0 r₀,
      Φ (θ * s) ≤ (1 / 2 : ℝ) * θ ^ β * Φ s + D * s ^ β := by
    intro s hs
    have hsR : s ∈ Ioc 0 R := ⟨hs.1, hs.2.trans hr₀R.le⟩
    have hs1 : s ≤ 1 := hsR.2.trans hR1
    have hspow : C * s ^ a ≤ (1 / 4 : ℝ) * θ ^ β := by
      have ht := mul_le_mul_of_nonneg_left
        (Real.rpow_le_rpow hs.1.le hs.2 ha.le) hC
      linarith only [ht, hr₀pow]
    have hb : C * (θ ^ d + s ^ a) ≤ (1 / 2 : ℝ) * θ ^ β := by
      nlinarith only [hθdecay, hspow]
    exact (hrec s hsR θ hθ hθ1).trans (add_le_add
      (mul_le_mul_of_nonneg_right hb (hnonneg s hsR))
      (mul_le_mul_of_nonneg_left
        (Real.rpow_le_rpow_of_exponent_ge hs.1 hs1 (by linarith)) hD))
  have hinit : Φ r₀ ≤ L * r₀ ^ β :=
    (hbound r₀ ⟨hr₀, hr₀R.le⟩).trans ((div_le_iff₀ hr₀β).mp (le_max_left _ _))
  have hforce : D ≤ (1 / 2 : ℝ) * θ ^ β * L := by
    have ht : 2 * D ≤ L * θ ^ β := (div_le_iff₀ hθβ).mp (le_max_right _ _)
    nlinarith only [ht]
  by_cases hrr₀ : r ≤ r₀
  · have hsmall := campanato_bound_all_radii hθ hθ1 hr₀ hβ.le hL
      (hmono.mono (Ioc_subset_Ioc_right hr₀R.le))
      (campanato_geometric_bound hθ hθ1 hr₀ hinit hforce hrec') r ⟨hr.1, hrr₀⟩
    exact hsmall.trans (mul_le_mul_of_nonneg_right
      ((le_max_left _ _).trans (le_add_of_nonneg_right zero_le_one))
      (Real.rpow_nonneg hr.1.le β))
  · have hlarge : M ≤ (M / r₀ ^ β) * r ^ β := by
      have hp := Real.rpow_le_rpow hr₀.le (le_of_not_ge hrr₀) hβ.le
      calc
        M = (M / r₀ ^ β) * r₀ ^ β := (div_mul_cancel₀ M hr₀β.ne').symm
        _ ≤ _ := mul_le_mul_of_nonneg_left hp (div_nonneg hM hr₀β.le)
    exact (hbound r hr).trans (hlarge.trans (mul_le_mul_of_nonneg_right
      ((le_max_right _ _).trans (le_add_of_nonneg_right zero_le_one))
      (Real.rpow_nonneg hr.1.le β)))

end LiquidDrop

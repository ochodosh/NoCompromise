import NoCompromise.CapacitaryK.FarFieldUnconditional
import NoCompromise.CapacitaryK.MuMeasure

/-!
# `eq:K-p-expansion` for the geometric level integral

Chapter 31, `lem:K-level-asymptotics`: with `H` the mean curvature of the level and
`p(t) := ∫_{u=t} H |∇u| dH²` (`levelP`), `p(t) = 8πt + O(t⁴)` as `t ↓ 0`, for the capacitary
potential. No measure or base level appears in the statement: `μ = Δ|∇u|` is supplied by
`K_mu_measure`, a base level is taken among the small (regular) levels, the canonical
representative satisfies the expansion (`capacitary_Kp_expansion_unconditional`, volume route),
and it equals `levelP` at every small level, all of which are regular
(`capacitary_small_level_decay`, `K_p_geometric_of_harmonic`).
-/

noncomputable section
open Real Set Filter Metric MeasureTheory Asymptotics
open scoped Topology Gradient ENNReal

namespace LiquidDrop.CapacitaryK

/-- `eq:K-p-expansion`, geometric form: `∫_{u=t} H |∇u| dH² = 8πt + O(t⁴)` as `t ↓ 0`. -/
theorem capacitary_levelP_expansion
    {K : Set E3} (hK : IsCompact K) (hzero : (0 : E3) ∈ interior K)
    {u : E3 → ℝ} (hu : Continuous u)
    (hh : HasDistributionalLaplacianOn u (fun _ => 0) Kᶜ)
    (hb : ∀ x ∈ K, u x = 1) (hinf : Tendsto u (cocompact E3) (𝓝 0)) :
    (fun t => levelP Kᶜ u t - 8 * π * t) =O[𝓝[>] 0] (fun t => t ^ 4) := by
  obtain ⟨R, hR⟩ := hK.isBounded.subset_closedBall 0
  have hR₀ : (0 : ℝ) < max R 1 := lt_max_of_lt_right one_pos
  have hKR : K ⊆ closedBall 0 (max R 1) :=
    hR.trans (closedBall_subset_closedBall (le_max_left _ _))
  have hU : IsOpen Kᶜ := hK.isClosed.isOpen_compl
  have hu3 : ContDiffOn ℝ 3 u Kᶜ := (capacitary_potential_contDiffOn hK hu hh).of_le (by norm_num)
  have hΔ := kelvin_laplacianN_eq_zero_of_distributional hU hu.continuousOn hh
  obtain ⟨μ, hμU, hμK, hμ⟩ := K_mu_measure hU hu3 hΔ
  obtain ⟨t₁, ht₁, M, hsmall⟩ := capacitary_small_level_decay hK hR₀ hKR hzero hu hh hb hinf
  set t₀ : ℝ := t₁ / 2 with ht₀def
  have ht₀ : t₀ ∈ Ioo (0 : ℝ) 1 := ⟨by linarith [ht₁.1], by linarith [ht₁.1, ht₁.2]⟩
  have ht₀R : ∀ x ∈ Kᶜ, u x = t₀ → gradient u x ≠ 0 := fun x hx hxt =>
    (hsmall x hx (by rw [hxt]; linarith [ht₁.1])).1
  have hKp := capacitary_Kp_expansion_unconditional hK hzero hu hh hb hinf hμU hμK hμ ht₀ ht₀R
  have hslabs := capacitary_slabs hu hb hinf
  refine hKp.congr' ?_ EventuallyEq.rfl
  filter_upwards [Ioo_mem_nhdsGT (lt_min ht₁.1 one_pos)] with t ht
  have ht1 : t < t₁ := lt_of_lt_of_le ht.2 (min_le_left _ _)
  have ht2 : t < 1 := lt_of_lt_of_le ht.2 (min_le_right _ _)
  rw [K_p_geometric_of_harmonic hU hu.measurable hu3 hΔ hμU hμK hμ hslabs ht₀ ht₀R t
    (fun x hx hxt => (hsmall x hx (hxt ▸ ht1)).1) ht.1 ht2]

end LiquidDrop.CapacitaryK

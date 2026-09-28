import NoCompromise.CapacitaryK.MeasureInequality
import NoCompromise.CapacitaryK.DensityInput

/-!
# Capacitary inequalities from the level-set data (chapter 31, `thm:capacitary-inequalities`)

`capacitary_inequalities_of_expansions` with its density hypotheses (`hdmeas`, `hdens`)
discharged by `K_pushforward_lower_density` (`lem:K-pushforward-density`), and the slab
finiteness `hfin` discharged from compactness of the slab closures in `U` (`K_slab_mass_finite`).
The remaining hypotheses are the pointwise inequality `p²/F - 8π ≤ ∫_{u=t}(|A|² + |∇_Σ log w|²)`
at a.e. level (`eq:K-measure-ineq-pointwise`), the far-field expansions (`lem:K-far-field`) and
the endpoint limits.
-/

noncomputable section
open Real Set Filter MeasureTheory Topology
open scoped Gradient ENNReal

namespace LiquidDrop.CapacitaryK

/-- Slabs `{a < u ≤ b}`, `0 < a ≤ b < 1`, have finite `μ`-mass when the open slabs of `(0,1)` have
compact closure in `U` and `μ` is carried by `U`. -/
theorem K_slab_mass_finite {U : Set E3} {u : E3 → ℝ} {μ : Measure E3} (hμU : μ Uᶜ = 0)
    (hμK : ∀ K : Set E3, IsCompact K → K ⊆ U → μ K < ⊤)
    (hslabs : ∀ a b, 0 < a → a < b → b < 1 →
      IsCompact (closure (U ∩ u ⁻¹' Ioo a b)) ∧ closure (U ∩ u ⁻¹' Ioo a b) ⊆ U) :
    ∀ a b, 0 < a → a ≤ b → b < 1 → μ (u ⁻¹' Ioc a b) ≠ ⊤ := by
  intro a b ha hab hb
  have hb' : b < (b + 1) / 2 := by linarith
  obtain ⟨hK, hKU⟩ := hslabs a ((b + 1) / 2) ha (lt_of_le_of_lt hab hb') (by linarith)
  apply ne_of_lt
  calc μ (u ⁻¹' Ioc a b) ≤ μ (U ∩ u ⁻¹' Ioo a ((b + 1) / 2) ∪ Uᶜ) := by
        apply measure_mono
        intro x hx
        by_cases hxU : x ∈ U
        · exact Or.inl ⟨hxU, hx.1, lt_of_le_of_lt hx.2 hb'⟩
        · exact Or.inr hxU
    _ ≤ μ (U ∩ u ⁻¹' Ioo a ((b + 1) / 2)) + μ Uᶜ := measure_union_le _ _
    _ = μ (U ∩ u ⁻¹' Ioo a ((b + 1) / 2)) := by rw [hμU, add_zero]
    _ ≤ μ (closure (U ∩ u ⁻¹' Ioo a ((b + 1) / 2))) := measure_mono subset_closure
    _ < ⊤ := hμK _ hK hKU

/-- `thm:capacitary-inequalities` for `μ = Δ|∇u|` (`prop:K-mu`) and the canonical `p = Kp`,
`F = KFhat`, from the pointwise level inequality `p²/F - 8π ≤ levelDensity` at a.e. level, the
far-field expansions and the endpoint limits. -/
theorem capacitary_inequalities_of_levels {U : Set E3} (hU : IsOpen U) {u : E3 → ℝ}
    (humeas : Measurable u) (hu : ContDiffOn ℝ 3 u U) (hΔ : ∀ x ∈ U, laplacianN u x = 0)
    {μ : Measure E3} (hμU : μ Uᶜ = 0)
    (hμK : ∀ K : Set E3, IsCompact K → K ⊆ U → μ K < ⊤)
    (hμ : ∀ φ : E3 → ℝ, ContDiff ℝ (⊤ : ℕ∞) φ → HasCompactSupport φ → tsupport φ ⊆ U →
        ∫ x, gradNorm u x * laplacianN φ x = ∫ x, φ x ∂μ)
    (hslabs : ∀ a b, 0 < a → a < b → b < 1 →
      IsCompact (closure (U ∩ u ⁻¹' Ioo a b)) ∧ closure (U ∩ u ⁻¹' Ioo a b) ⊆ U)
    {t₀ p₀ F₀ F1 p1 : ℝ} (ht₀ : t₀ ∈ Ioo (0 : ℝ) 1)
    (hd : ∀ᵐ t, t ∈ Ioo (0 : ℝ) 1 →
      Kp μ u t₀ p₀ t ^ 2 / KFhat μ u t₀ p₀ F₀ t - 8 * π ≤ levelDensity U u t)
    (hFexp : (fun t => KFhat μ u t₀ p₀ F₀ t - 4 * π * t ^ 2) =O[𝓝[>] 0] (fun t => t ^ 5))
    (hpexp : (fun t => Kp μ u t₀ p₀ t - 8 * π * t) =O[𝓝[>] 0] (fun t => t ^ 4))
    (hF1 : Tendsto (KFhat μ u t₀ p₀ F₀) (𝓝[<] 1) (𝓝 F1))
    (hp1 : Tendsto (Kp μ u t₀ p₀) (𝓝[<] 1) (𝓝 p1)) :
    4 * π ≤ F1 ∧ 4 * F1 - 8 * π ≤ p1 := by
  have hfin := K_slab_mass_finite hμU hμK hslabs
  obtain ⟨d, hdm, hdeq, hdens⟩ :=
    K_pushforward_lower_density hU humeas hu hΔ hμU hμK hμ hfin
  refine capacitary_inequalities_of_expansions humeas ht₀ hfin hdm hdens ?_ hFexp hpexp hF1 hp1
  filter_upwards [hd, hdeq] with t h1 h2 ht
  rw [h2 ht]
  exact h1 ht

/-- `thm:capacitary-inequalities` from `eq:K-p-expansion` alone at the far end: the `F`-expansion
of `lem:K-far-field` is derived from `F' = p` and `F(0+) = 0` (`F_expansion_of_p_expansion`). -/
theorem capacitary_inequalities_of_p_expansion {U : Set E3} (hU : IsOpen U) {u : E3 → ℝ}
    (humeas : Measurable u) (hu : ContDiffOn ℝ 3 u U) (hΔ : ∀ x ∈ U, laplacianN u x = 0)
    {μ : Measure E3} (hμU : μ Uᶜ = 0)
    (hμK : ∀ K : Set E3, IsCompact K → K ⊆ U → μ K < ⊤)
    (hμ : ∀ φ : E3 → ℝ, ContDiff ℝ (⊤ : ℕ∞) φ → HasCompactSupport φ → tsupport φ ⊆ U →
        ∫ x, gradNorm u x * laplacianN φ x = ∫ x, φ x ∂μ)
    (hslabs : ∀ a b, 0 < a → a < b → b < 1 →
      IsCompact (closure (U ∩ u ⁻¹' Ioo a b)) ∧ closure (U ∩ u ⁻¹' Ioo a b) ⊆ U)
    {t₀ p₀ F₀ F1 p1 : ℝ} (ht₀ : t₀ ∈ Ioo (0 : ℝ) 1)
    (hd : ∀ᵐ t, t ∈ Ioo (0 : ℝ) 1 →
      Kp μ u t₀ p₀ t ^ 2 / KFhat μ u t₀ p₀ F₀ t - 8 * π ≤ levelDensity U u t)
    (hF0 : Tendsto (KFhat μ u t₀ p₀ F₀) (𝓝[>] 0) (𝓝 0))
    (hpexp : (fun t => Kp μ u t₀ p₀ t - 8 * π * t) =O[𝓝[>] 0] (fun t => t ^ 4))
    (hF1 : Tendsto (KFhat μ u t₀ p₀ F₀) (𝓝[<] 1) (𝓝 F1))
    (hp1 : Tendsto (Kp μ u t₀ p₀) (𝓝[<] 1) (𝓝 p1)) :
    4 * π ≤ F1 ∧ 4 * F1 - 8 * π ≤ p1 := by
  obtain ⟨_, _, hi, hF, _, _⟩ :=
    K_structure humeas ht₀ (K_slab_mass_finite hμU hμK hslabs) (p₀ := p₀) (F₀ := F₀)
  exact capacitary_inequalities_of_levels hU humeas hu hΔ hμU hμK hμ hslabs ht₀ hd
    (F_expansion_of_p_expansion hi hF hF0 hpexp) hpexp hF1 hp1

end LiquidDrop.CapacitaryK

import NoCompromise.Surface.GaussSardMain
import NoCompromise.Surface.TotalCurvatureIndex
import NoCompromise.CapacitaryK.FarFieldUnconditional
import NoCompromise.CapacitaryK.GaussBonnetInput
import NoCompromise.CapacitaryK.LevelInequality

/-!
# `thm:total-curvature-bound`, unconditionally, and its consumers in chapter 31

`total_curvature_le_of_index` (Surface/GaussSardMain.lean) is `thm:total-curvature-bound` modulo
the named hypothesis `h_total_curvature_index`, which is `thm:total-curvature-index` in the form
`total_curvature_index_integrable_and_eq` (Surface/TotalCurvatureIndex.lean). Hence:

* `total_curvature_bound`: `∫_Σ κ dH² ≤ 4π` for every compact connected smooth embedded surface
  `Σ ⊆ ℝ³` and every unit normal field on it, with no hypothesis beyond these;
* `total_curvature_bound_forall`: the same, in the exact shape of the named hypothesis
  `h_of_total_curvature_bound` of chapter 31;
* `capacitary_inequalities_of_potential_collar_only`: `thm:capacitary-inequalities` for the
  capacitary potential with only the collar bounds near `∂K` (`hcollar`) remaining;
* `K_gauss_bonnet_input_of_level_connected`, `K_gauss_bonnet_input_of_harmonic_of_level_connected`
  and `K_level_inequality_of_level_connected`: `lem:K-gauss-bonnet-input` and
  `eq:K-measure-ineq-pointwise` with `h_of_total_curvature_bound` discharged (only
  `h_of_level_connected`, `lem:level-connected`, remaining among the named hypotheses).
-/

noncomputable section

open Set Filter MeasureTheory Topology
open scoped Gradient ENNReal

namespace LiquidDrop

/-- **thm:total-curvature-bound.** For a compact connected smooth embedded surface `S ⊆ ℝ³` with
a unit normal field `n`, `∫_S κ dH² ≤ 4π`. -/
theorem total_curvature_bound {S : Set E₃} {n : E₃ → E₃}
    (hS : IsSmoothEmbeddedSurface S) (hc : IsCompact S) (hconn : IsConnected S)
    (hn : IsUnitNormalField S n) :
    ∫ x in S, gaussCurvature S n x ∂(hausdorffMeasure2 3) ≤ 4 * Real.pi :=
  total_curvature_le_of_index hS hc hconn hn (total_curvature_index_integrable_and_eq hS hc hn)

/-- thm:total-curvature-bound in the exact shape of the named hypothesis
`h_of_total_curvature_bound` of chapter 31 (`CapacitaryK`). -/
theorem total_curvature_bound_forall :
    ∀ (S : Set E₃) (n : E₃ → E₃), IsCompact S → IsConnected S →
      IsSmoothEmbeddedSurface S → IsUnitNormalField S n →
      ∫ x in S, gaussCurvature S n x ∂(Measure.euclideanHausdorffMeasure 2) ≤ 4 * Real.pi :=
  fun _ _ hc hconn hS hn => total_curvature_bound hS hc hconn hn

end LiquidDrop

namespace LiquidDrop.CapacitaryK

/-- `thm:capacitary-inequalities` for the capacitary potential with `eq:K-p-expansion` and
`thm:total-curvature-bound` discharged; the only remaining input is the collar bound near `∂K`
(`hcollar`, endpoint identification). -/
theorem capacitary_inequalities_of_potential_collar_only
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
    (ht₀R : ∀ x ∈ Kᶜ, u x = t₀ → gradient u x ≠ 0)
    (hcollar : ∃ t₁ < 1, ∃ c > 0, ∃ M, ∀ x ∈ Kᶜ, t₁ < u x →
      c ≤ gradNorm u x ∧ |meanCurv u x * gradNorm u x| ≤ M) :
    4 * Real.pi ≤ levelF Kᶜ u t₀ + ∫ t in t₀..1, Kp μ u t₀ (levelP Kᶜ u t₀) t ∧
      4 * (levelF Kᶜ u t₀ + ∫ t in t₀..1, Kp μ u t₀ (levelP Kᶜ u t₀) t) - 8 * Real.pi ≤
        levelP Kᶜ u t₀ + (μ (u ⁻¹' Ioo t₀ 1)).toReal :=
  capacitary_inequalities_of_potential_far_unconditional hK hKconn hcompl hzero hu hh hb hinf
    hμU hμK hμ total_curvature_bound_forall ht₀ ht₀R hcollar

/-- `lem:K-gauss-bonnet-input` with `thm:total-curvature-bound` discharged: for every regular
value `t ∈ (0,1)` whose level is compact and contained in the open set where `u` is smooth,
`∫_{u=t} κ dH² ≤ 4π`. The remaining named hypothesis is `h_of_level_connected`
(`lem:level-connected`). -/
theorem K_gauss_bonnet_input_of_level_connected {Ω : Set E3} (hΩ : IsOpen Ω) {u : E3 → ℝ}
    (hu : ContDiffOn ℝ (⊤ : ℕ∞) u Ω) {t : ℝ} (ht0 : 0 < t) (ht1 : t < 1)
    (hsub : u ⁻¹' {t} ⊆ Ω) (hreg : ∀ x ∈ u ⁻¹' {t}, gradient u x ≠ 0)
    (hcompact : IsCompact (u ⁻¹' {t}))
    (h_of_level_connected : ∀ s : ℝ, 0 < s → s < 1 → (∀ x ∈ u ⁻¹' {s}, gradient u x ≠ 0) →
      IsConnected (u ⁻¹' {s})) :
    ∫ x in u ⁻¹' {t}, gaussCurvature (u ⁻¹' {t}) (unitNormal u) x
        ∂(Measure.euclideanHausdorffMeasure 2) ≤ 4 * Real.pi :=
  K_gauss_bonnet_input hΩ hu ht0 ht1 hsub hreg hcompact h_of_level_connected
    total_curvature_bound_forall

/-- `lem:K-gauss-bonnet-input` for a `C²` function harmonic on `Ω`, with
`thm:total-curvature-bound` discharged; the remaining named hypothesis is
`h_of_level_connected` (`lem:level-connected`). -/
theorem K_gauss_bonnet_input_of_harmonic_of_level_connected {Ω : Set E3} (hΩ : IsOpen Ω)
    {u : E3 → ℝ}
    (hu : ContDiffOn ℝ 2 u Ω) (hΔ : ∀ x ∈ Ω, laplacianN u x = 0) {t : ℝ} (ht0 : 0 < t)
    (ht1 : t < 1) (hsub : u ⁻¹' {t} ⊆ Ω) (hreg : ∀ x ∈ u ⁻¹' {t}, gradient u x ≠ 0)
    (hcompact : IsCompact (u ⁻¹' {t}))
    (h_of_level_connected : ∀ s : ℝ, 0 < s → s < 1 → (∀ x ∈ u ⁻¹' {s}, gradient u x ≠ 0) →
      IsConnected (u ⁻¹' {s})) :
    ∫ x in u ⁻¹' {t}, gaussCurvature (u ⁻¹' {t}) (unitNormal u) x
        ∂(Measure.euclideanHausdorffMeasure 2) ≤ 4 * Real.pi :=
  K_gauss_bonnet_input_of_harmonic hΩ hu hΔ ht0 ht1 hsub hreg hcompact h_of_level_connected
    total_curvature_bound_forall

/-- `eq:K-measure-ineq-pointwise` on one regular level, with `thm:total-curvature-bound`
discharged: `p²/F − 8π ≤ ∫_{u=t}(|A|² + |∇_Σ log w|²)`. The remaining named hypothesis is
`h_of_level_connected` (`lem:level-connected`). -/
theorem K_level_inequality_of_level_connected {U : Set E3} (hU : IsOpen U) {u : E3 → ℝ}
    (hu : ContDiffOn ℝ 3 u U) (hΔ : ∀ x ∈ U, laplacianN u x = 0)
    {t : ℝ} (ht0 : 0 < t) (ht1 : t < 1) (hsub : u ⁻¹' {t} ⊆ U)
    (hreg : ∀ x ∈ u ⁻¹' {t}, gradient u x ≠ 0) (hcompact : IsCompact (u ⁻¹' {t}))
    (hfin : Measure.euclideanHausdorffMeasure 2 (u ⁻¹' {t}) < ⊤)
    (hFpos : 0 < levelF U u t)
    (h_of_level_connected : ∀ s : ℝ, 0 < s → s < 1 → (∀ x ∈ u ⁻¹' {s}, gradient u x ≠ 0) →
      IsConnected (u ⁻¹' {s})) :
    levelP U u t ^ 2 / levelF U u t - 8 * Real.pi ≤ levelDensity U u t :=
  K_level_inequality hU hu hΔ ht0 ht1 hsub hreg hcompact hfin hFpos h_of_level_connected
    total_curvature_bound_forall

end LiquidDrop.CapacitaryK

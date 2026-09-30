module

public import NoCompromise.CapacitaryK.FarMassExpansion
public import NoCompromise.CapacitaryK.GradNormFarExpansion

@[expose] public section

/-!
# `eq:K-p-expansion`, `lem:K-far-field`, `thm:capacitary-inequalities`: `hpexp` discharged

`GradNormLaplacianFarExpansion` holds (`gradNorm_laplacian_far_expansion`), so the far-field
statements of `FarMassExpansion` hold unconditionally for the capacitary potential.
-/

noncomputable section
open Real Set Filter MeasureTheory Topology Asymptotics
open scoped Gradient ENNReal

namespace LiquidDrop.CapacitaryK

theorem gradNormLaplacianFarExpansion_holds : GradNormLaplacianFarExpansion :=
  fun _ _ _ _ _ hC hR hU hUh hQ hQh hQl hW =>
    gradNorm_laplacian_far_expansion hC hR hU hUh hQ hQh hQl hW

/-- `eq:K-p-expansion` for the capacitary potential: `p(t) = 8πt + O(t⁴)`. -/
theorem capacitary_Kp_expansion_unconditional
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
    (fun t => Kp μ u t₀ (levelP Kᶜ u t₀) t - 8 * π * t) =O[𝓝[>] 0] (fun t => t ^ 4) :=
  capacitary_Kp_expansion gradNormLaplacianFarExpansion_holds hK hzero hu hh hb hinf hμU hμK hμ
    ht₀ ht₀R

/-- `lem:K-far-field` for the capacitary potential. -/
theorem capacitary_K_far_field_unconditional
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
    (fun t => KFhat μ u t₀ (levelP Kᶜ u t₀) (levelF Kᶜ u t₀) t - 4 * π * t ^ 2)
        =O[𝓝[>] 0] (fun t => t ^ 5) ∧
      (fun t => Kp μ u t₀ (levelP Kᶜ u t₀) t - 8 * π * t) =O[𝓝[>] 0] (fun t => t ^ 4) ∧
      Tendsto (fun t => (KFhat μ u t₀ (levelP Kᶜ u t₀) (levelF Kᶜ u t₀) t - 4 * π * t ^ 2) /
        t ^ 4) (𝓝[>] 0) (𝓝 0) ∧
      Tendsto (levelH (KFhat μ u t₀ (levelP Kᶜ u t₀) (levelF Kᶜ u t₀))
        (Kp μ u t₀ (levelP Kᶜ u t₀))) (𝓝[>] 0) (𝓝 0) :=
  capacitary_K_far_field gradNormLaplacianFarExpansion_holds hK hzero hu hh hb hinf hμU hμK hμ
    ht₀ ht₀R

/-- `thm:capacitary-inequalities` for the capacitary potential with `eq:K-p-expansion`
discharged; remaining inputs: `thm:total-curvature-bound` and the collar bounds near `∂K`. -/
theorem capacitary_inequalities_of_potential_far_unconditional
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
    (hcollar : ∃ t₁ < 1, ∃ c > 0, ∃ M, ∀ x ∈ Kᶜ, t₁ < u x →
      c ≤ gradNorm u x ∧ |meanCurv u x * gradNorm u x| ≤ M) :
    4 * π ≤ levelF Kᶜ u t₀ + ∫ t in t₀..1, Kp μ u t₀ (levelP Kᶜ u t₀) t ∧
      4 * (levelF Kᶜ u t₀ + ∫ t in t₀..1, Kp μ u t₀ (levelP Kᶜ u t₀) t) - 8 * π ≤
        levelP Kᶜ u t₀ + (μ (u ⁻¹' Ioo t₀ 1)).toReal :=
  capacitary_inequalities_of_potential_far gradNormLaplacianFarExpansion_holds hK hKconn hcompl
    hzero hu hh hb hinf hμU hμK hμ h_of_total_curvature_bound ht₀ ht₀R hcollar

end LiquidDrop.CapacitaryK

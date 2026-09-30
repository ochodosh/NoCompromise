module

public import NoCompromise.CapacitaryK.CollarC2
public import NoCompromise.CapacitaryK.FarFieldUnconditional

@[expose] public section

/-!
# `thm:capacitary-inequalities` modulo `thm:total-curvature-bound` and the `C²` extension

The collar hypothesis of `capacitary_inequalities_of_potential_far_unconditional` is discharged
by `capacitary_collar_of_C2_extension`. The endpoint values are the canonical ones
`F(1) = F(t₀) + ∫_{t₀}^1 p` and `p(1) = p(t₀) + μ{t₀ < u < 1}`; they are the left limits of
the geometric level integrals `F(t) = ∫_{u=t} w²` and `p(t) = ∫_{u=t} Hw` whenever those
limits exist (`capacitary_endpoint_values_of_level_limits`).
-/

noncomputable section
open Real Set Filter Metric MeasureTheory Topology
open scoped Gradient ENNReal

namespace LiquidDrop.CapacitaryK

/-- `thm:capacitary-inequalities` for the capacitary potential of `K`, in the endpoint form
`F(1) ≥ 4π`, `p(1) ≥ 4F(1) - 8π` with the canonical endpoint values, modulo only
`thm:total-curvature-bound` and the `C²` extension `g` of `u` across `∂K`. -/
theorem capacitary_inequalities_of_C2_extension
    {K : Set E3} (hK : IsCompact K) (hKconn : IsConnected K) (hcompl : IsPreconnected Kᶜ)
    (hreg : K = closure (interior K)) (hC1 : HasC1Boundary (interior K))
    (hC2 : HasC2Boundary (interior K))
    {R₀ : ℝ} (hR₀ : 0 < R₀) (hKR : K ⊆ closedBall 0 R₀)
    (hzero : (0 : E3) ∈ interior K)
    {u : E3 → ℝ} (hu : Continuous u)
    (hh : HasDistributionalLaplacianOn u (fun _ => 0) Kᶜ)
    (hb : ∀ x ∈ K, u x = 1) (hinf : Tendsto u (cocompact E3) (𝓝 0))
    {g : E3 → ℝ} (hg : ContDiff ℝ 2 g) (hug : EqOn u g (closure Kᶜ))
    {μ : Measure E3} (hμU : μ Kᶜᶜ = 0)
    (hμK : ∀ L : Set E3, IsCompact L → L ⊆ Kᶜ → μ L < ⊤)
    (hμ : ∀ φ : E3 → ℝ, ContDiff ℝ (⊤ : ℕ∞) φ → HasCompactSupport φ → tsupport φ ⊆ Kᶜ →
        ∫ x, gradNorm u x * laplacianN φ x = ∫ x, φ x ∂μ)
    (h_of_total_curvature_bound : ∀ (S : Set E3) (n : E3 → E3), IsCompact S → IsConnected S →
      IsSmoothEmbeddedSurface S → IsUnitNormalField S n →
      ∫ x in S, gaussCurvature S n x ∂(Measure.euclideanHausdorffMeasure 2) ≤ 4 * Real.pi)
    {t₀ : ℝ} (ht₀ : t₀ ∈ Ioo (0 : ℝ) 1)
    (ht₀R : ∀ x ∈ Kᶜ, u x = t₀ → gradient u x ≠ 0) :
    4 * π ≤ levelF Kᶜ u t₀ + ∫ t in t₀..1, Kp μ u t₀ (levelP Kᶜ u t₀) t ∧
      4 * (levelF Kᶜ u t₀ + ∫ t in t₀..1, Kp μ u t₀ (levelP Kᶜ u t₀) t) - 8 * π ≤
        levelP Kᶜ u t₀ + (μ (u ⁻¹' Ioo t₀ 1)).toReal :=
  capacitary_inequalities_of_potential_far_unconditional hK hKconn hcompl hzero hu hh hb hinf
    hμU hμK hμ h_of_total_curvature_bound ht₀ ht₀R
    (capacitary_collar_of_C2_extension hK hreg hC1 hR₀ hKR hzero hu hh hb hinf hg hug hC2
      hcompl)

/-- Endpoint identification: under the collar bounds, if the geometric level integrals
`F(t) = ∫_{u=t} w²` and `p(t) = ∫_{u=t} Hw` converge as `t ↑ 1`, then the canonical endpoint
values `F(t₀) + ∫_{t₀}^1 p` and `p(t₀) + μ{t₀ < u < 1}` are these limits. -/
theorem capacitary_endpoint_values_of_level_limits
    {K : Set E3} (hK : IsCompact K)
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
      c ≤ gradNorm u x ∧ |meanCurv u x * gradNorm u x| ≤ M)
    {F1 p1 : ℝ} (hF : Tendsto (levelF Kᶜ u) (𝓝[<] 1) (𝓝 F1))
    (hp : Tendsto (levelP Kᶜ u) (𝓝[<] 1) (𝓝 p1)) :
    levelF Kᶜ u t₀ + ∫ t in t₀..1, Kp μ u t₀ (levelP Kᶜ u t₀) t = F1 ∧
      levelP Kᶜ u t₀ + (μ (u ⁻¹' Ioo t₀ 1)).toReal = p1 := by
  have hU : IsOpen Kᶜ := hK.isClosed.isOpen_compl
  have hu3 : ContDiffOn ℝ 3 u Kᶜ := (capacitary_potential_contDiffOn hK hu hh).of_le (by norm_num)
  have hΔ := kelvin_laplacianN_eq_zero_of_distributional hU hu.continuousOn hh
  have hslabs := capacitary_slabs hu hb hinf
  obtain ⟨hKp, hKF⟩ := Kp_KFhat_tendsto_one_of_collar hU hu.measurable hu3 hΔ hμU hμK hμ hslabs
    ht₀ ht₀R hcollar
  obtain ⟨t₁, ht₁, c, hc, M, hcol⟩ := hcollar
  have hreg : ∀ᶠ t in 𝓝[<] (1 : ℝ), 0 < t ∧ t < 1 ∧ ∀ x ∈ Kᶜ, u x = t → gradient u x ≠ 0 := by
    filter_upwards [Ioo_mem_nhdsLT (max_lt ht₁ one_pos : max t₁ 0 < 1)] with t ht
    refine ⟨(le_max_right _ _).trans_lt ht.1, ht.2, fun x hx hxt => ?_⟩
    have hw := (hcol x hx (hxt ▸ (le_max_left _ _).trans_lt ht.1)).1
    intro hz
    have : gradNorm u x = 0 := by rw [gradNorm, hz, norm_zero]
    linarith
  have hevp : Kp μ u t₀ (levelP Kᶜ u t₀) =ᶠ[𝓝[<] 1] levelP Kᶜ u := by
    filter_upwards [hreg] with t ht
    exact K_p_geometric_of_harmonic hU hu.measurable hu3 hΔ hμU hμK hμ hslabs ht₀ ht₀R t
      ht.2.2 ht.1 ht.2.1
  have hevF : KFhat μ u t₀ (levelP Kᶜ u t₀) (levelF Kᶜ u t₀) =ᶠ[𝓝[<] 1] levelF Kᶜ u := by
    filter_upwards [hreg] with t ht
    exact KFhat_eq_levelF hU hu.measurable hu3 hΔ hμU hμK hμ hslabs ht₀ ht₀R t
      ht.2.2 ht.1 ht.2.1
  exact ⟨tendsto_nhds_unique (hKF.congr' hevF) hF, tendsto_nhds_unique (hKp.congr' hevp) hp⟩

/-- `thm:capacitary-inequalities` with the endpoint values given as the left limits
`F(1) = lim_{t↑1} ∫_{u=t} w²`, `p(1) = lim_{t↑1} ∫_{u=t} Hw`: `F(1) ≥ 4π` and
`p(1) ≥ 4F(1) - 8π`, modulo `thm:total-curvature-bound` and the `C²` extension. -/
theorem capacitary_inequalities_of_C2_extension_of_level_limits
    {K : Set E3} (hK : IsCompact K) (hKconn : IsConnected K) (hcompl : IsPreconnected Kᶜ)
    (hreg : K = closure (interior K)) (hC1 : HasC1Boundary (interior K))
    (hC2 : HasC2Boundary (interior K))
    {R₀ : ℝ} (hR₀ : 0 < R₀) (hKR : K ⊆ closedBall 0 R₀)
    (hzero : (0 : E3) ∈ interior K)
    {u : E3 → ℝ} (hu : Continuous u)
    (hh : HasDistributionalLaplacianOn u (fun _ => 0) Kᶜ)
    (hb : ∀ x ∈ K, u x = 1) (hinf : Tendsto u (cocompact E3) (𝓝 0))
    {g : E3 → ℝ} (hg : ContDiff ℝ 2 g) (hug : EqOn u g (closure Kᶜ))
    {μ : Measure E3} (hμU : μ Kᶜᶜ = 0)
    (hμK : ∀ L : Set E3, IsCompact L → L ⊆ Kᶜ → μ L < ⊤)
    (hμ : ∀ φ : E3 → ℝ, ContDiff ℝ (⊤ : ℕ∞) φ → HasCompactSupport φ → tsupport φ ⊆ Kᶜ →
        ∫ x, gradNorm u x * laplacianN φ x = ∫ x, φ x ∂μ)
    (h_of_total_curvature_bound : ∀ (S : Set E3) (n : E3 → E3), IsCompact S → IsConnected S →
      IsSmoothEmbeddedSurface S → IsUnitNormalField S n →
      ∫ x in S, gaussCurvature S n x ∂(Measure.euclideanHausdorffMeasure 2) ≤ 4 * Real.pi)
    {t₀ : ℝ} (ht₀ : t₀ ∈ Ioo (0 : ℝ) 1)
    (ht₀R : ∀ x ∈ Kᶜ, u x = t₀ → gradient u x ≠ 0)
    {F1 p1 : ℝ} (hF : Tendsto (levelF Kᶜ u) (𝓝[<] 1) (𝓝 F1))
    (hp : Tendsto (levelP Kᶜ u) (𝓝[<] 1) (𝓝 p1)) :
    4 * π ≤ F1 ∧ 4 * F1 - 8 * π ≤ p1 := by
  obtain ⟨hF1, hp1⟩ := capacitary_endpoint_values_of_level_limits hK hu hh hb hinf hμU hμK hμ
    ht₀ ht₀R (capacitary_collar_of_C2_extension hK hreg hC1 hR₀ hKR hzero hu hh hb hinf hg hug
      hC2 hcompl) hF hp
  have h := capacitary_inequalities_of_C2_extension hK hKconn hcompl hreg hC1 hC2 hR₀ hKR hzero
    hu hh hb hinf hg hug hμU hμK hμ h_of_total_curvature_bound ht₀ ht₀R
  rw [hF1, hp1] at h
  exact h

end LiquidDrop.CapacitaryK

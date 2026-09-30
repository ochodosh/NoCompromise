module

public import NoCompromise.CapacitaryK.CapacitaryHarmonic
public import NoCompromise.Capacity.LevelsMain
public import NoCompromise.Capacity.LowerBarrier
public import NoCompromise.Capacity.Kelvin

@[expose] public section

/-!
# `thm:capacitary-inequalities` for the capacitary potential (chapter 31)

This assembly discharges measurability, exterior smoothness and harmonicity, compactness of
slabs, existence and compactness of levels, and connectedness of regular levels from the
capacitary-potential hypotheses. The remaining inputs are `hF0` and `hpexp` from
`lem:K-level-asymptotics` / `eq:K-p-expansion`, the endpoint limits `hF1` and `hp1` from
boundary regularity, and `h_of_total_curvature_bound` from `thm:total-curvature-bound`.
The measure `μ` and its stated properties are supplied by `prop:K-mu` (`CapacitaryK.K_mu`).
-/

noncomputable section
open Real Set Filter MeasureTheory Topology
open scoped Gradient ENNReal

namespace LiquidDrop.CapacitaryK

/-- Positive slabs below the boundary value have compact closure contained in the exterior,
for a continuous potential equal to one on `K` and tending to zero at infinity. -/
theorem capacitary_slabs {K : Set E3} {u : E3 → ℝ} (hu : Continuous u)
    (hb : ∀ x ∈ K, u x = 1) (hinf : Tendsto u (cocompact E3) (𝓝 0)) :
    ∀ a b, 0 < a → a < b → b < 1 →
      IsCompact (closure (Kᶜ ∩ u ⁻¹' Ioo a b)) ∧
        closure (Kᶜ ∩ u ⁻¹' Ioo a b) ⊆ Kᶜ := by
  intro a b ha _hab hb1
  have hclosure : closure (Kᶜ ∩ u ⁻¹' Ioo a b) ⊆ u ⁻¹' Icc a b := by
    apply closure_minimal _ (isClosed_Icc.preimage hu)
    intro x hx
    exact ⟨hx.2.1.le, hx.2.2.le⟩
  obtain ⟨L, hL, hsub⟩ := Filter.mem_cocompact.mp (hinf.eventually (gt_mem_nhds ha))
  refine ⟨hL.of_isClosed_subset isClosed_closure ?_, ?_⟩
  · intro x hx
    by_contra hn
    exact (not_lt_of_ge (hclosure hx).1) (hsub hn)
  · intro x hx hxK
    have hle := (hclosure hx).2
    rw [hb x hxK] at hle
    exact (not_le_of_gt hb1) hle

/-- Every level strictly between zero and one is a nonempty compact subset of the exterior,
provided `K` is nonempty and the continuous potential is one on `K` and zero at infinity. -/
theorem capacitary_levels {K : Set E3} (hK : K.Nonempty) {u : E3 → ℝ}
    (hu : Continuous u) (hb : ∀ x ∈ K, u x = 1)
    (hinf : Tendsto u (cocompact E3) (𝓝 0)) :
    ∀ t, 0 < t → t < 1 →
      u ⁻¹' {t} ⊆ Kᶜ ∧ IsCompact (u ⁻¹' {t}) ∧ (u ⁻¹' {t}).Nonempty := by
  intro t ht ht1
  exact ⟨levelSet_subset_compl hb ht1, isCompact_levelSet hu hinf ht,
    levelSet_nonempty hK hu hb hinf ht ht1⟩

/-- Chapter 31, `thm:capacitary-inequalities`: the capacitary potential satisfies the two
endpoint inequalities, assuming the measure identity, total curvature bound, asymptotics
at zero, and endpoint limits at one. -/
theorem capacitary_inequalities_of_potential
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
    {t₀ F1 p1 : ℝ} (ht₀ : t₀ ∈ Ioo (0 : ℝ) 1)
    (ht₀R : ∀ x ∈ Kᶜ, u x = t₀ → gradient u x ≠ 0)
    (hF0 : Tendsto (KFhat μ u t₀ (levelP Kᶜ u t₀) (levelF Kᶜ u t₀)) (𝓝[>] 0) (𝓝 0))
    (hpexp : (fun t => Kp μ u t₀ (levelP Kᶜ u t₀) t - 8 * π * t) =O[𝓝[>] 0]
      (fun t => t ^ 4))
    (hF1 : Tendsto (KFhat μ u t₀ (levelP Kᶜ u t₀) (levelF Kᶜ u t₀)) (𝓝[<] 1) (𝓝 F1))
    (hp1 : Tendsto (Kp μ u t₀ (levelP Kᶜ u t₀)) (𝓝[<] 1) (𝓝 p1)) :
    4 * π ≤ F1 ∧ 4 * F1 - 8 * π ≤ p1 := by
  have hsmooth := capacitary_potential_contDiffOn hK hu hh
  have hΔ := kelvin_laplacianN_eq_zero_of_distributional hK.isClosed.isOpen_compl
    hu.continuousOn hh
  have hsigns := capacitary_signs hK hzero hu hh hb hinf
  have hstrict : ∀ x ∉ K, 0 < u x ∧ u x < 1 :=
    fun x hx => ⟨(hsigns.1 x hx).1, hsigns.2 hcompl x hx⟩
  refine capacitary_inequalities_of_harmonic hK.isClosed.isOpen_compl hu.measurable
    (hsmooth.of_le (by norm_num)) hΔ hμU hμK hμ (capacitary_slabs hu hb hinf)
    (capacitary_levels ⟨0, interior_subset hzero⟩ hu hb hinf) ?_
    h_of_total_curvature_bound ht₀ ht₀R hF0 hpexp hF1 hp1
  intro s hs hs1 hreg
  exact level_connected hK hKconn hu hb hh hsmooth hinf hstrict hs hs1 hreg

end LiquidDrop.CapacitaryK

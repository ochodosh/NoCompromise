import NoCompromise.CapacitaryK.LevelAreaDensity
import NoCompromise.CapacitaryK.CapacitaryRadialGraph

/-!
# Small capacitary levels as radial graphs: the level set and the Kelvin data

Chapter 31, `lem:K-level-asymptotics`. Two bookkeeping facts for assembling the lemma:

* `level_eq_radial_image`: if every ray from `z` meets `{u = t}` exactly once, at radius
  `ρ θ > 0`, and `t < 1 = u` on `K`, `u z ≠ t`, then the level `Kᶜ ∩ {u = t}` is exactly the
  radial graph `{ρ θ • θ + z : ‖θ‖ = 1}`.
* `kelvin_extension_data_eq`: two smooth extensions of the Kelvin transform across `0` have the
  same value, gradient and translated quadrupole at `0`, so the constants `C`, `z` and `Q`
  produced by the separate existence statements of the lemma agree.
-/

noncomputable section

open Set Filter Metric InnerProductSpace
open scoped Topology Gradient RealInnerProductSpace

namespace LiquidDrop.CapacitaryK

/-- A level met exactly once by every ray from `z` is the radial graph over the unit sphere. -/
theorem level_eq_radial_image {K : Set E3} {u : E3 → ℝ} (hb : ∀ x ∈ K, u x = 1) {t : ℝ}
    (ht1 : t < 1) {z : E3} (hz : u z ≠ t) {ρ : E3 → ℝ}
    (hρ : ∀ θ : E3, ‖θ‖ = 1 → 0 < ρ θ ∧ u (ρ θ • θ + z) = t ∧
      ∀ s' : ℝ, 0 < s' → u (s' • θ + z) = t → s' = ρ θ) :
    Kᶜ ∩ u ⁻¹' {t} = (fun θ => ρ θ • θ + z) '' sphere (0 : E3) 1 := by
  ext x
  constructor
  · rintro ⟨_, hxt⟩
    have hxt' : u x = t := hxt
    have hxz : x - z ≠ 0 := by
      intro h
      rw [sub_eq_zero] at h
      exact hz (h ▸ hxt')
    have hn : 0 < ‖x - z‖ := norm_pos_iff.mpr hxz
    set θ : E3 := ‖x - z‖⁻¹ • (x - z) with hθdef
    have hθ : ‖θ‖ = 1 := by
      rw [hθdef, norm_smul, norm_inv, norm_norm, inv_mul_cancel₀ hn.ne']
    have hsx : ‖x - z‖ • θ + z = x := by
      rw [hθdef, smul_smul, mul_inv_cancel₀ hn.ne', one_smul, sub_add_cancel]
    obtain ⟨_, _, huniq⟩ := hρ θ hθ
    have hs : ‖x - z‖ = ρ θ := huniq _ hn (by rw [hsx]; exact hxt')
    refine ⟨θ, by simpa [mem_sphere_zero_iff_norm] using hθ, ?_⟩
    simp only
    rw [← hs, hsx]
  · rintro ⟨θ, hθ, rfl⟩
    have hθ' : ‖θ‖ = 1 := by simpa [mem_sphere_zero_iff_norm] using hθ
    obtain ⟨_, hut, _⟩ := hρ θ hθ'
    refine ⟨fun hK => ?_, hut⟩
    have := hb _ hK
    rw [hut] at this
    exact ht1.ne this

/-- Two smooth extensions across `0` of the Kelvin transform agree near `0`. -/
theorem kelvin_extension_eventuallyEq {u v v' : E3 → ℝ} {r r' : ℝ} (hr : 0 < r) (hr' : 0 < r')
    (hv : ContDiffOn ℝ (⊤ : ℕ∞) v (ball 0 r)) (hv' : ContDiffOn ℝ (⊤ : ℕ∞) v' (ball 0 r'))
    (he : EqOn v (kelvinTransform u) (ball 0 r \ {0}))
    (he' : EqOn v' (kelvinTransform u) (ball 0 r' \ {0})) :
    v =ᶠ[𝓝 0] v' := by
  set m := min r r' with hm
  have hm0 : 0 < m := lt_min hr hr'
  have hball : ball (0 : E3) m ∈ 𝓝 (0 : E3) := ball_mem_nhds 0 hm0
  have hsub : ball (0 : E3) m ⊆ ball 0 r := ball_subset_ball (min_le_left _ _)
  have hsub' : ball (0 : E3) m ⊆ ball 0 r' := ball_subset_ball (min_le_right _ _)
  have hoff : ∀ y ∈ ball (0 : E3) m, y ≠ 0 → v y = v' y := fun y hy hy0 =>
    (he ⟨hsub hy, hy0⟩).trans (he' ⟨hsub' hy, hy0⟩).symm
  have hc : ContinuousAt v 0 :=
    (hv.continuousOn.mono hsub).continuousAt hball
  have hc' : ContinuousAt v' 0 :=
    (hv'.continuousOn.mono hsub').continuousAt hball
  have h0 : v 0 = v' 0 := by
    have hev : (fun y => v y) =ᶠ[𝓝[≠] (0 : E3)] fun y => v' y := by
      filter_upwards [nhdsWithin_le_nhds hball, self_mem_nhdsWithin] with y hy hy0
      exact hoff y hy hy0
    have h1 : Tendsto v (𝓝[≠] (0 : E3)) (𝓝 (v 0)) := hc.tendsto.mono_left nhdsWithin_le_nhds
    have h2 : Tendsto v' (𝓝[≠] (0 : E3)) (𝓝 (v' 0)) := hc'.tendsto.mono_left nhdsWithin_le_nhds
    exact tendsto_nhds_unique h1 (h2.congr' hev.symm)
  filter_upwards [hball] with y hy
  by_cases hy0 : y = 0
  · rw [hy0]; exact h0
  · exact hoff y hy hy0

/-- The constants `C = v 0`, `∇v(0)` and the translated quadrupole do not depend on the choice of
smooth Kelvin extension. -/
theorem kelvin_extension_data_eq {u v v' : E3 → ℝ} {r r' : ℝ} (hr : 0 < r) (hr' : 0 < r')
    (hv : ContDiffOn ℝ (⊤ : ℕ∞) v (ball 0 r)) (hv' : ContDiffOn ℝ (⊤ : ℕ∞) v' (ball 0 r'))
    (he : EqOn v (kelvinTransform u) (ball 0 r \ {0}))
    (he' : EqOn v' (kelvinTransform u) (ball 0 r' \ {0})) :
    v 0 = v' 0 ∧ gradient v 0 = gradient v' 0 ∧
      kelvinTranslatedQuadrupole v = kelvinTranslatedQuadrupole v' := by
  have hev := kelvin_extension_eventuallyEq hr hr' hv hv' he he'
  have h0 : v 0 = v' 0 := hev.eq_of_nhds
  have hd1 : fderiv ℝ v =ᶠ[𝓝 0] fderiv ℝ v' := hev.fderiv
  have hd2 : fderiv ℝ (fderiv ℝ v) 0 = fderiv ℝ (fderiv ℝ v') 0 := hd1.fderiv_eq
  have hg : gradient v 0 = gradient v' 0 := by
    simp only [gradient, hd1.eq_of_nhds]
  refine ⟨h0, hg, ?_⟩
  funext x
  simp only [kelvinTranslatedQuadrupole, h0, hg, hd2]

end LiquidDrop.CapacitaryK

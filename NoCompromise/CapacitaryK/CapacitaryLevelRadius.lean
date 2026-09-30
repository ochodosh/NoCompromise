module

public import NoCompromise.CapacitaryK.LevelRadialArea
public import NoCompromise.CapacitaryK.LevelRadiusSmooth
public import NoCompromise.CapacitaryK.RadialGraphArea

@[expose] public section

/-!
# The capacitary level radius: smoothness, the level set and the area factor

Chapter 31, `lem:K-level-asymptotics`. For small `t > 0` the level radius `ρ_t` about the
normalized dipole center `z = (v 0)⁻¹ • ∇v(0)`, extended zero-homogeneously, exists, is smooth
off `0`, the level `Kᶜ ∩ {u = t}` is exactly the radial graph `{ρ_t θ • θ + z : ‖θ‖ = 1}`,
`ρ_t θ = C/t + t Q(θ)/C² + O(t²)` (`eq:K-rt`), and the radial-graph area factor
`ρ_t √(ρ_t² + |∇_T ρ_t|²)` equals `C²/t² + 2 Q(θ)/C + O(t)` uniformly in `θ` (`eq:K-dA`,
area factor form), where `C = v 0` and `Q = kelvinTranslatedQuadrupole v`.
-/

noncomputable section

open Set Filter Metric InnerProductSpace
open scoped Topology Gradient RealInnerProductSpace

namespace LiquidDrop.CapacitaryK

/-- `lem:K-level-asymptotics`: the small capacitary levels are smooth radial graphs about the
normalized dipole center, with `eq:K-rt` and the area factor of `eq:K-dA`. -/
theorem capacitary_level_radius_smooth
    {K : Set E3} (hK : IsCompact K) {R₀ : ℝ} (hR₀ : 0 < R₀)
    (hKR : K ⊆ Metric.closedBall 0 R₀) (hzero : (0 : E3) ∈ interior K)
    {u : E3 → ℝ} (hu : Continuous u)
    (hh : HasDistributionalLaplacianOn u (fun _ => 0) Kᶜ)
    (hb : ∀ x ∈ K, u x = 1) (hinf : Tendsto u (cocompact E3) (𝓝 0)) :
    ∃ (v : E3 → ℝ) (r : ℝ), 0 < r ∧ ContDiffOn ℝ (⊤ : ℕ∞) v (Metric.ball 0 r) ∧
      EqOn v (kelvinTransform u) (Metric.ball 0 r \ {0}) ∧ 0 < v 0 ∧
      ∃ A : ℝ, 0 ≤ A ∧ ∀ᶠ t in 𝓝[>] (0 : ℝ),
        (∃ ρ : E3 → ℝ, (∀ y : E3, y ≠ 0 → ρ y = ρ (‖y‖⁻¹ • y)) ∧
          ∀ θ : E3, ‖θ‖ = 1 → 0 < ρ θ ∧ u (ρ θ • θ + (v 0)⁻¹ • gradient v 0) = t) ∧
        ∀ ρ : E3 → ℝ, (∀ y : E3, y ≠ 0 → ρ y = ρ (‖y‖⁻¹ • y)) →
          (∀ θ : E3, ‖θ‖ = 1 → 0 < ρ θ ∧ u (ρ θ • θ + (v 0)⁻¹ • gradient v 0) = t) →
          ContDiffOn ℝ (⊤ : ℕ∞) ρ {y | y ≠ 0} ∧
          Kᶜ ∩ u ⁻¹' {t} = (fun θ => ρ θ • θ + (v 0)⁻¹ • gradient v 0) '' sphere (0 : E3) 1 ∧
          ∀ θ : E3, ‖θ‖ = 1 →
            ⟪gradient u (ρ θ • θ + (v 0)⁻¹ • gradient v 0), θ⟫ < 0 ∧
            |ρ θ - (v 0 / t + t * kelvinTranslatedQuadrupole v θ / (v 0) ^ 2)| ≤ A * t ^ 2 ∧
            |ρ θ * Real.sqrt (ρ θ ^ 2 + ‖gradient ρ θ - ⟪gradient ρ θ, θ⟫ • θ‖ ^ 2) -
              ((v 0) ^ 2 / t ^ 2 + 2 * kelvinTranslatedQuadrupole v θ / v 0)| ≤ A * t := by
  obtain ⟨v, r, hr, hv, he, hv0, A₁, hA₁, hev₁⟩ :=
    capacitary_level_radial_graph hK hR₀ hKR hzero hu hh hb hinf
  obtain ⟨v', r', hr', hv', he', _, A₂, _, hev₂⟩ :=
    capacitary_level_area_density_expansion hK hR₀ hKR hzero hu hh hb hinf
  obtain ⟨h0, hg, hQ⟩ := kelvin_extension_data_eq hr hr' hv hv' he he'
  refine ⟨v, r, hr, hv, he, hv0, max A₁ A₂, le_max_of_le_left hA₁, ?_⟩
  set z : E3 := (v 0)⁻¹ • gradient v 0 with hz
  have hz0 : 0 < u z := capacitary_pos_everywhere hK hzero hu hh hb hinf z
  have hsmooth := capacitary_potential_contDiffOn hK hu hh
  filter_upwards [hev₁, hev₂, Ioo_mem_nhdsGT (lt_min hz0 one_pos)] with t h₁ h₂ ht
  rw [← h0, ← hg, ← hQ] at h₂
  have ht0 : 0 < t := ht.1
  have ht1 : t < 1 := lt_of_lt_of_le ht.2 (min_le_right _ _)
  have htz : u z ≠ t := (lt_of_lt_of_le ht.2 (min_le_left _ _)).ne'
  refine ⟨?_, ?_⟩
  · classical
    let s₀ : E3 → ℝ := fun θ => if h : ‖θ‖ = 1 then Classical.choose (h₁ θ h) else 1
    have hs₀ : ∀ θ : E3, ‖θ‖ = 1 → 0 < s₀ θ ∧ u (s₀ θ • θ + z) = t := by
      intro θ hθ
      have hc := Classical.choose_spec (h₁ θ hθ)
      simp only [s₀, hθ, ↓reduceDIte]
      exact ⟨hc.1, hc.2.1⟩
    refine ⟨fun y => s₀ (‖y‖⁻¹ • y), fun y hy => ?_, fun θ hθ => ?_⟩
    · have hny : 0 < ‖y‖ := norm_pos_iff.mpr hy
      have h1 : ‖‖y‖⁻¹ • y‖ = 1 := by
        rw [norm_smul, norm_inv, norm_norm, inv_mul_cancel₀ hny.ne']
      simp only [h1, inv_one, one_smul]
    · simp only [hθ, inv_one, one_smul]
      exact hs₀ θ hθ
  intro ρ hhom hroot
  have hroot' : ∀ θ : E3, ‖θ‖ = 1 → 0 < ρ θ ∧ u (ρ θ • θ + z) = t ∧
      ∀ s' : ℝ, 0 < s' → u (s' • θ + z) = t → s' = ρ θ := by
    intro θ hθ
    obtain ⟨s, _, _, _, huniq⟩ := h₁ θ hθ
    obtain ⟨hρ, hut⟩ := hroot θ hθ
    have hρs : ρ θ = s := huniq _ hρ hut
    exact ⟨hρ, hut, fun s' hs' hu' => (huniq s' hs' hu').trans hρs.symm⟩
  let U : E3 → ℝ := fun y => u (y + z)
  let O : Set E3 := {y | y + z ∈ Kᶜ}
  have hO : IsOpen O :=
    hK.isClosed.isOpen_compl.preimage (continuous_id.add continuous_const)
  have hUs : ContDiffOn ℝ (⊤ : ℕ∞) U O :=
    hsmooth.comp (contDiff_id.add contDiff_const).contDiffOn (fun y hy => hy)
  have hgradU : ∀ y : E3, gradient U y = gradient u (y + z) := fun y => by
    simp only [U, gradient, fderiv_comp_add_right]
  have hmemK : ∀ θ : E3, ‖θ‖ = 1 → ρ θ • θ + z ∈ Kᶜ := fun θ hθ hKx => by
    have h := hb _ hKx
    rw [(hroot θ hθ).2] at h
    exact ht1.ne h
  have hneg : ∀ θ : E3, ‖θ‖ = 1 → ⟪gradient u (ρ θ • θ + z), θ⟫ < 0 := fun θ hθ =>
    (h₂ θ hθ (ρ θ) (hroot θ hθ).1 (hroot θ hθ).2).1
  have hder : ∀ θ : E3, ‖θ‖ = 1 → ⟪gradient U (ρ θ • θ), θ⟫ ≠ 0 := fun θ hθ => by
    rw [hgradU]
    exact (hneg θ hθ).ne
  have hρs : ContDiffOn ℝ (⊤ : ℕ∞) ρ {y | y ≠ 0} :=
    levelRadius_contDiffOn hO hUs hhom (fun θ hθ => (hroot θ hθ).1)
      (fun θ hθ s hs hus => (hroot' θ hθ).2.2 s hs hus) (fun θ hθ => (hroot θ hθ).2) hmemK hder
  refine ⟨hρs, level_eq_radial_image hb ht1 htz hroot', fun θ hθ => ⟨hneg θ hθ, ?_, ?_⟩⟩
  · obtain ⟨s, _, _, hbd, huniq⟩ := h₁ θ hθ
    rw [huniq _ (hroot θ hθ).1 (hroot θ hθ).2]
    exact hbd.trans (mul_le_mul_of_nonneg_right (le_max_left _ _) (by positivity))
  · have hθ0 : θ ≠ 0 := by
      rintro rfl
      simp at hθ
    have hρd : DifferentiableAt ℝ ρ θ :=
      (hρs.contDiffAt (isOpen_ne.mem_nhds hθ0)).differentiableAt (by simp)
    have hUd : DifferentiableAt ℝ U (ρ θ • θ) :=
      (hUs.contDiffAt (hO.mem_nhds (hmemK θ hθ))).differentiableAt (by simp)
    have hgr := levelRadius_gradient hhom (fun θ hθ => (hroot θ hθ).2) hθ hρd hUd (hder θ hθ)
    rw [radial_graph_jacobian_of_implicit hθ (hroot θ hθ).1 (hder θ hθ) hgr, hgradU]
    exact (h₂ θ hθ _ (hroot θ hθ).1 (hroot θ hθ).2).2.trans
      (mul_le_mul_of_nonneg_right (le_max_right _ _) ht0.le)

end LiquidDrop.CapacitaryK

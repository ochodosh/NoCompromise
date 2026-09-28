import NoCompromise.Capacity.LevelAreaElement

/-!
# `lem:level-asymptotics` in one statement

Chapter 30, `lem:level-asymptotics`: all clauses with one and the same Kelvin coefficient
`Cinf`. The coefficient is determined by the value expansion
(`kelvin_coefficient_unique`), so the separately proved statements glue.
-/

noncomputable section
open Set Filter Metric MeasureTheory InnerProductSpace
open scoped Topology Gradient RealInnerProductSpace ENNReal
namespace LiquidDrop
local notation "E₃" => EuclideanSpace ℝ (Fin 3)

/-- The coefficient of `1/|x|` in a far-field expansion with `O(|x|⁻²)` error is unique. -/
lemma kelvin_coefficient_unique {u : E₃ → ℝ} {a b R₁ R₂ C₁ C₂ : ℝ}
    (h₁ : ∀ x : E₃, R₁ ≤ ‖x‖ → |u x - a / ‖x‖| ≤ C₁ / ‖x‖ ^ 2)
    (h₂ : ∀ x : E₃, R₂ ≤ ‖x‖ → |u x - b / ‖x‖| ≤ C₂ / ‖x‖ ^ 2) : a = b := by
  by_contra hab
  have hd : 0 < |a - b| := abs_pos.mpr (sub_ne_zero.mpr hab)
  set s : ℝ := max (max R₁ R₂) (max 1 (2 * (|C₁| + |C₂|) / |a - b| + 1)) with hs
  have hs1 : 1 ≤ s := (le_max_left _ _).trans (le_max_right _ _)
  have hs0 : 0 < s := lt_of_lt_of_le one_pos hs1
  have hsbig : 2 * (|C₁| + |C₂|) / |a - b| < s :=
    lt_of_lt_of_le (lt_add_one _) ((le_max_right _ _).trans (le_max_right _ _))
  let e : E₃ := EuclideanSpace.single 0 1
  have he : ‖e‖ = 1 := by simp [e]
  have hx : ‖s • e‖ = s := by rw [norm_smul, he, mul_one, Real.norm_eq_abs, abs_of_pos hs0]
  have hb₁ := h₁ (s • e) (by rw [hx]; exact (le_max_left _ _).trans (le_max_left _ _))
  have hb₂ := h₂ (s • e) (by rw [hx]; exact (le_max_right _ _).trans (le_max_left _ _))
  rw [hx] at hb₁ hb₂
  have htri : |a / s - b / s| ≤ C₁ / s ^ 2 + C₂ / s ^ 2 := by
    calc |a / s - b / s| = |(u (s • e) - b / s) - (u (s • e) - a / s)| := by ring_nf
      _ ≤ |u (s • e) - b / s| + |u (s • e) - a / s| := abs_sub _ _
      _ ≤ C₁ / s ^ 2 + C₂ / s ^ 2 := by linarith
  have hleft : |a / s - b / s| = |a - b| / s := by
    rw [← sub_div, abs_div, abs_of_pos hs0]
  rw [hleft] at htri
  have hC : C₁ / s ^ 2 + C₂ / s ^ 2 ≤ (|C₁| + |C₂|) / s ^ 2 := by
    rw [← add_div]
    exact div_le_div_of_nonneg_right (add_le_add (le_abs_self _) (le_abs_self _))
      (by positivity)
  have h3 : |a - b| * s ≤ |C₁| + |C₂| := by
    have := htri.trans hC
    rw [div_le_div_iff₀ hs0 (by positivity)] at this
    nlinarith
  have h4 : 2 * (|C₁| + |C₂|) < s * |a - b| := by
    rwa [div_lt_iff₀ hd] at hsbig
  have hCpos : 0 ≤ |C₁| + |C₂| := by positivity
  nlinarith

/-- Blueprint `lem:level-asymptotics`, all clauses with one Kelvin coefficient `Cinf`: the value,
gradient and Hessian expansions; for small `ε` the level `{u = ε}` is the radial graph of one
zero-homogeneous smooth `ρ` with `ρ = Cinf/ε + O(1)` and two angular derivatives bounded
uniformly; on the level `w = ε²/Cinf + O(ε³)` with `∇u ≠ 0` and `H = 2ε/Cinf + O(ε²)`; the area
element is `dH² = J dω` with `J = (Cinf²/ε²)(1 + O(ε))`; and
`∫ (H w - 4 ε⁻¹ w²) dH² = -8π ε + O(ε²)` (`eq:level-Hw-asymptotics`). -/
theorem capacitary_level_asymptotics_full
    {K : Set E₃} (hK : IsCompact K) {R₀ : ℝ} (hR₀ : 0 < R₀)
    (hKR : K ⊆ closedBall 0 R₀) (hzero : (0 : E₃) ∈ interior K)
    {u : E₃ → ℝ} (hu : Continuous u)
    (hh : HasDistributionalLaplacianOn u (fun _ => 0) Kᶜ)
    (hb : ∀ x ∈ K, u x = 1) (hinf : Tendsto u (cocompact E₃) (𝓝 0)) :
    ∃ Cinf : ℝ, 0 < Cinf ∧
      (∃ R C' : ℝ, 0 < R ∧ ∀ x : E₃, R ≤ ‖x‖ →
        |u x - Cinf / ‖x‖| ≤ C' / ‖x‖ ^ 2 ∧
        ‖gradient u x + (Cinf / ‖x‖ ^ 3) • x‖ ≤ C' / ‖x‖ ^ 3 ∧
        ‖fderiv ℝ (gradient u) x -
          ((3 * Cinf / ‖x‖ ^ 5) • (innerSL ℝ x).smulRight x -
            (Cinf / ‖x‖ ^ 3) • ContinuousLinearMap.id ℝ E₃)‖ ≤ C' / ‖x‖ ^ 4) ∧
      ∃ ε₀ : ℝ, 0 < ε₀ ∧ ∃ M : ℝ, ∀ ε : ℝ, 0 < ε → ε < ε₀ →
        (∃ ρ : E₃ → ℝ, ContDiffOn ℝ (⊤ : ℕ∞) ρ {θ | θ ≠ 0} ∧
          (∀ θ : E₃, θ ≠ 0 → ρ θ = ρ (‖θ‖⁻¹ • θ)) ∧
          (∀ θ : E₃, ‖θ‖ = 1 → 0 < ρ θ ∧ |ρ θ - Cinf / ε| ≤ M) ∧
          u ⁻¹' {ε} = (fun θ => ρ θ • θ) '' sphere (0 : E₃) 1 ∧
          (∀ θ : E₃, ‖θ‖ = 1 → ‖fderiv ℝ ρ θ‖ ≤ M ∧ ‖fderiv ℝ (fderiv ℝ ρ) θ‖ ≤ M) ∧
          (∀ q : E₃ → ℝ≥0∞, Measurable q →
            ∫⁻ x in u ⁻¹' {ε}, q x ∂hausdorffMeasure2 3 =
              ∫⁻ θ in sphere (0 : E₃) 1, q (ρ θ • θ) *
                ENNReal.ofReal (ρ θ * Real.sqrt (ρ θ ^ 2 +
                  ‖gradient ρ θ - ⟪gradient ρ θ, θ⟫ • θ‖ ^ 2)) ∂hausdorffMeasure2 3) ∧
          ∀ θ : E₃, ‖θ‖ = 1 →
            |ρ θ * Real.sqrt (ρ θ ^ 2 + ‖gradient ρ θ - ⟪gradient ρ θ, θ⟫ • θ‖ ^ 2) -
              Cinf ^ 2 / ε ^ 2| ≤ M * ε * (Cinf ^ 2 / ε ^ 2)) ∧
        (∀ x : E₃, u x = ε →
          x ∉ K ∧ gradient u x ≠ 0 ∧ |‖x‖ - Cinf / ε| ≤ M ∧
          |‖gradient u x‖ - ε ^ 2 / Cinf| ≤ M * ε ^ 3 ∧
          |CapacitaryK.meanCurv u x - 2 * ε / Cinf| ≤ M * ε ^ 2) ∧
        (∫ x in u ⁻¹' {ε}, ‖gradient u x‖ ∂hausdorffMeasure2 3) = 4 * Real.pi * Cinf ∧
        |(∫ x in u ⁻¹' {ε}, (CapacitaryK.meanCurv u x * ‖gradient u x‖ -
            4 * ε⁻¹ * ‖gradient u x‖ ^ 2) ∂hausdorffMeasure2 3) + 8 * Real.pi * ε| ≤
          M * ε ^ 2 := by
  obtain ⟨C₁, hC₁, ⟨R₁, D₁, hR₁, hexp₁⟩, ε₁, hε₁, -, M₁, hM₁⟩ :=
    capacitary_level_asymptotics hK hR₀ hKR hzero hu hh hb hinf
  obtain ⟨C₂, -, ⟨R₂, D₂, -, hexp₂⟩, ε₂, hε₂, M₂, hM₂⟩ :=
    capacitary_level_radial_geometry hK hR₀ hKR hzero hu hh hb hinf
  have hCeq : C₂ = C₁ :=
    kelvin_coefficient_unique hexp₂ (fun x hx => (hexp₁ x hx).1)
  subst hCeq
  set M : ℝ := max M₁ M₂ with hM
  refine ⟨C₂, hC₁, ⟨R₁, D₁, hR₁, hexp₁⟩, min ε₁ ε₂, lt_min hε₁ hε₂, M, fun ε hε hεε => ?_⟩
  have h1 := hM₁ ε hε (lt_of_lt_of_le hεε (min_le_left _ _))
  obtain ⟨ρ, hρs, hhom, hρ, himg, -, hD, hL, -, hJ⟩ :=
    hM₂ ε hε (lt_of_lt_of_le hεε (min_le_right _ _))
  obtain ⟨-, hpt, hflux, hHw⟩ := h1
  have hl : M₁ ≤ M := le_max_left _ _
  have hr : M₂ ≤ M := le_max_right _ _
  have hε2 : 0 ≤ ε ^ 2 := by positivity
  have hε3 : 0 ≤ ε ^ 3 := by positivity
  refine ⟨⟨ρ, hρs, hhom, fun θ hθ => ⟨(hρ θ hθ).1, (hρ θ hθ).2.trans hr⟩, himg,
      fun θ hθ => ⟨(hD θ hθ).1.trans hr, (hD θ hθ).2.trans hr⟩, hL, fun θ hθ => (hJ θ hθ).trans
        (mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right hr hε.le) (by positivity))⟩,
    fun x hx => ?_, hflux, hHw.trans (mul_le_mul_of_nonneg_right hl hε2)⟩
  obtain ⟨hxK, hg, hn, hw, hH⟩ := hpt x hx
  exact ⟨hxK, hg, hn.trans hl, hw.trans (mul_le_mul_of_nonneg_right hl hε3),
    hH.trans (mul_le_mul_of_nonneg_right hl hε2)⟩

end LiquidDrop

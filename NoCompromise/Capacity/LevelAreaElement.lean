import NoCompromise.Capacity.LevelRadiusSecondDeriv
import NoCompromise.CapacitaryK.RadialGraphAreaFormula
import NoCompromise.CapacitaryK.LevelRadiusDerivatives

/-!
# The area element of small capacitary levels (`lem:level-asymptotics`)

Chapter 30, `lem:level-asymptotics`, third display of `eq:level-asymptotics`: on the small level
`{u = ε}`, written as the radial graph `θ ↦ ρ θ • θ` over the unit sphere, the two-dimensional
Hausdorff measure is the pushforward of `J dω` with the explicit density
`J = ρ √(ρ² + |∇_T ρ|²)`, and `J = (Cinf²/ε²)(1 + O(ε))` uniformly in `θ`, i.e.
`dH² = (Cinf²/ε²)(1 + O(ε)) dω`, with the same Kelvin coefficient `Cinf` as the value expansion.
-/

noncomputable section
open Set Filter Metric MeasureTheory InnerProductSpace
open scoped Topology Gradient RealInnerProductSpace ENNReal
namespace LiquidDrop
local notation "E₃" => EuclideanSpace ℝ (Fin 3)

/-- The radial-graph area factor lies between `a²` and `a² + b²/2`. -/
lemma levelArea_factor_bounds {a b : ℝ} (ha : 0 < a) :
    a ^ 2 ≤ a * Real.sqrt (a ^ 2 + b ^ 2) ∧
      a * Real.sqrt (a ^ 2 + b ^ 2) ≤ a ^ 2 + b ^ 2 / 2 := by
  have hlow : a ≤ Real.sqrt (a ^ 2 + b ^ 2) :=
    Real.le_sqrt_of_sq_le (by nlinarith [sq_nonneg b])
  have hup : Real.sqrt (a ^ 2 + b ^ 2) ≤ a + b ^ 2 / (2 * a) := by
    rw [Real.sqrt_le_left]
    · have h2a : 0 < 2 * a := by positivity
      have : (a + b ^ 2 / (2 * a)) ^ 2 = a ^ 2 + b ^ 2 + (b ^ 2 / (2 * a)) ^ 2 := by
        field_simp
        ring
      rw [this]
      nlinarith [sq_nonneg (b ^ 2 / (2 * a))]
    · positivity
  refine ⟨by nlinarith, ?_⟩
  calc a * Real.sqrt (a ^ 2 + b ^ 2) ≤ a * (a + b ^ 2 / (2 * a)) :=
        mul_le_mul_of_nonneg_left hup ha.le
    _ = a ^ 2 + b ^ 2 / 2 := by field_simp

/-- The area element of a radial graph `ρ = Cinf/ε + O(1)` with bounded first derivative:
the graph is the radial image of the sphere, `H²` on it is the pushforward of `J dω`, and
`|J - Cinf²/ε²| ≤ M ε · Cinf²/ε²` with `M = N + (2 N Cinf + 3 N²)/Cinf²`. -/
lemma levelArea_of_radial {Cinf N ε : ℝ} (hC : 0 < Cinf) (hN0 : 0 ≤ N) (hε : 0 < ε)
    (hε1 : ε < 1) (hεC : ε < Cinf / (2 * (N + 1))) {ρ : E₃ → ℝ}
    (hρs : ContDiffOn ℝ (⊤ : ℕ∞) ρ {θ | θ ≠ 0})
    (hρbd : ∀ θ : E₃, ‖θ‖ = 1 → |ρ θ - Cinf / ε| ≤ N)
    (hDρ : ∀ θ : E₃, ‖θ‖ = 1 → ‖fderiv ℝ ρ θ‖ ≤ N) {S : Set E₃}
    (hlevel : S = {x | x ≠ 0 ∧ ‖x‖ = ρ (‖x‖⁻¹ • x)}) :
    (∀ θ : E₃, ‖θ‖ = 1 → 0 < ρ θ) ∧
      S = (fun θ => ρ θ • θ) '' sphere (0 : E₃) 1 ∧
      (∀ q : E₃ → ℝ≥0∞, Measurable q →
        ∫⁻ x in S, q x ∂hausdorffMeasure2 3 =
          ∫⁻ θ in sphere (0 : E₃) 1, q (ρ θ • θ) *
            ENNReal.ofReal (ρ θ * Real.sqrt (ρ θ ^ 2 +
              ‖gradient ρ θ - ⟪gradient ρ θ, θ⟫ • θ‖ ^ 2)) ∂hausdorffMeasure2 3) ∧
      (∀ f : E₃ → ℝ, Measurable f →
        ∫ x in S, f x ∂hausdorffMeasure2 3 =
          ∫ θ in sphere (0 : E₃) 1, f (ρ θ • θ) *
            (ρ θ * Real.sqrt (ρ θ ^ 2 +
              ‖gradient ρ θ - ⟪gradient ρ θ, θ⟫ • θ‖ ^ 2)) ∂hausdorffMeasure2 3) ∧
      ∀ θ : E₃, ‖θ‖ = 1 →
        |ρ θ * Real.sqrt (ρ θ ^ 2 + ‖gradient ρ θ - ⟪gradient ρ θ, θ⟫ • θ‖ ^ 2) -
          Cinf ^ 2 / ε ^ 2| ≤
          (N + (2 * N * Cinf + 3 * N ^ 2) / Cinf ^ 2) * ε * (Cinf ^ 2 / ε ^ 2) := by
  have hNC : N + 1 < Cinf / (2 * ε) := by
    rw [lt_div_iff₀ (by positivity)]
    rw [lt_div_iff₀ (by positivity)] at hεC
    linarith
  have hρpos : ∀ θ : E₃, ‖θ‖ = 1 → Cinf / (2 * ε) < ρ θ := by
    intro θ hθ
    have h := (abs_le.mp (hρbd θ hθ)).1
    have h2 : Cinf / ε = 2 * (Cinf / (2 * ε)) := by field_simp
    linarith
  have hρpos' : ∀ θ : E₃, ‖θ‖ = 1 → 0 < ρ θ := fun θ hθ =>
    lt_trans (by positivity) (hρpos θ hθ)
  have himage : S = (fun θ => ρ θ • θ + (0 : E₃)) '' sphere (0 : E₃) 1 := by
    rw [hlevel]
    ext x
    simp only [mem_ofPred_eq, mem_image, mem_sphere_zero_iff_norm, add_zero]
    constructor
    · rintro ⟨hx0, hxn⟩
      have hn : 0 < ‖x‖ := norm_pos_iff.mpr hx0
      refine ⟨‖x‖⁻¹ • x, ?_, ?_⟩
      · rw [norm_smul, norm_inv, norm_norm, inv_mul_cancel₀ hn.ne']
      · rw [← hxn, smul_smul, mul_inv_cancel₀ hn.ne', one_smul]
    · rintro ⟨θ, hθ, rfl⟩
      have hp := hρpos' θ hθ
      have hnorm : ‖ρ θ • θ‖ = ρ θ := by
        rw [norm_smul, hθ, mul_one, Real.norm_eq_abs, abs_of_pos hp]
      refine ⟨fun h => ?_, ?_⟩
      · rw [h, norm_zero] at hnorm
        exact hp.ne' hnorm.symm
      · rw [hnorm, smul_smul, inv_mul_cancel₀ hp.ne', one_smul]
  have himage' : S = (fun θ => ρ θ • θ) '' sphere (0 : E₃) 1 := by
    rw [himage]
    simp only [add_zero]
  have hρ1 : ContDiffOn ℝ 1 ρ {y : E₃ | y ≠ 0} := hρs.of_le (by exact_mod_cast le_top)
  refine ⟨hρpos', himage', ?_, ?_, ?_⟩
  · intro q hq
    rw [himage]
    simpa only [add_zero] using
      CapacitaryK.radial_graph_lintegral hρ1 hρpos' (0 : E₃) hq
  · intro f hf
    rw [himage]
    simpa only [add_zero] using
      CapacitaryK.radial_graph_integral_real hρ1 hρpos' (0 : E₃) hf
  · intro θ hθ
    set b : ℝ := ‖gradient ρ θ - ⟪gradient ρ θ, θ⟫ • θ‖ with hbdef
    have hgn : ‖gradient ρ θ‖ = ‖fderiv ℝ ρ θ‖ := (toDual ℝ E₃).symm.norm_map _
    have hb2 : b ≤ 2 * N := by
      calc b ≤ 2 * ‖gradient ρ θ‖ := CapacitaryK.levelRadius_tangent_norm_le hθ
        _ ≤ 2 * N := by rw [hgn]; linarith [hDρ θ hθ]
    have hb0 : 0 ≤ b := norm_nonneg _
    obtain ⟨hlo, hhi⟩ := levelArea_factor_bounds (b := b) (hρpos' θ hθ)
    have hr := abs_le.mp (hρbd θ hθ)
    have hCε : 0 < Cinf / ε := by positivity
    have hsq : |ρ θ ^ 2 - (Cinf / ε) ^ 2| ≤ N * (2 * (Cinf / ε) + N) := by
      rw [show ρ θ ^ 2 - (Cinf / ε) ^ 2 = (ρ θ - Cinf / ε) * (ρ θ + Cinf / ε) by ring,
        abs_mul]
      have h1 : |ρ θ + Cinf / ε| ≤ 2 * (Cinf / ε) + N := by
        rw [abs_le]; constructor <;> linarith
      exact mul_le_mul (hρbd θ hθ) h1 (abs_nonneg _) hN0
    have hsq' := abs_le.mp hsq
    have hJ : |ρ θ * Real.sqrt (ρ θ ^ 2 + b ^ 2) - Cinf ^ 2 / ε ^ 2| ≤
        N * (2 * (Cinf / ε) + N) + 2 * N ^ 2 := by
      have hdiv : Cinf ^ 2 / ε ^ 2 = (Cinf / ε) ^ 2 := by rw [div_pow]
      rw [hdiv, abs_le]
      constructor
      · nlinarith
      · nlinarith
    refine hJ.trans ?_
    have hrhs : (N + (2 * N * Cinf + 3 * N ^ 2) / Cinf ^ 2) * ε * (Cinf ^ 2 / ε ^ 2) =
        N * Cinf ^ 2 / ε + (2 * N * Cinf + 3 * N ^ 2) / ε := by
      field_simp
    rw [hrhs]
    have hB : 3 * N ^ 2 ≤ 3 * N ^ 2 / ε := by
      rw [le_div_iff₀ hε]
      nlinarith [sq_nonneg N]
    have hNC2 : 0 ≤ N * Cinf ^ 2 / ε := by positivity
    calc N * (2 * (Cinf / ε) + N) + 2 * N ^ 2 = 2 * N * Cinf / ε + 3 * N ^ 2 := by ring
      _ ≤ 2 * N * Cinf / ε + 3 * N ^ 2 / ε := by linarith
      _ = (2 * N * Cinf + 3 * N ^ 2) / ε := by ring
      _ ≤ N * Cinf ^ 2 / ε + (2 * N * Cinf + 3 * N ^ 2) / ε := le_add_of_nonneg_left hNC2

/-- A small level of the capacitary potential avoids `K`. -/
lemma level_preimage_eq_compl {K : Set E₃} {u : E₃ → ℝ} (hb : ∀ x ∈ K, u x = 1) {ε : ℝ}
    (hε1 : ε < 1) : u ⁻¹' {ε} = {x | x ∉ K ∧ u x = ε} := by
  ext x
  simp only [mem_preimage, mem_singleton_iff, mem_ofPred_eq]
  refine ⟨fun hx => ⟨fun hxK => ?_, hx⟩, fun hx => hx.2⟩
  rw [hb x hxK] at hx
  exact hε1.ne' hx

/-- Blueprint `lem:level-asymptotics`, area element: for small `ε`, the level `{u = ε}` is the
radial graph `θ ↦ ρ θ • θ` over the unit sphere, `H²` on it is the pushforward of
`J dω` with `J = ρ √(ρ² + |∇_T ρ|²)` (for every Borel weight, and in Bochner form for every
measurable real function), and `|J - Cinf²/ε²| ≤ M ε · Cinf²/ε²` uniformly on the sphere, i.e.
`dH² = (Cinf²/ε²)(1 + O(ε)) dω`. -/
theorem capacitary_level_area_element
    {K : Set E₃} (hK : IsCompact K) {R₀ : ℝ} (hR₀ : 0 < R₀)
    (hKR : K ⊆ closedBall 0 R₀) (hzero : (0 : E₃) ∈ interior K)
    {u : E₃ → ℝ} (hu : Continuous u)
    (hh : HasDistributionalLaplacianOn u (fun _ => 0) Kᶜ)
    (hb : ∀ x ∈ K, u x = 1) (hinf : Tendsto u (cocompact E₃) (𝓝 0)) :
    ∃ Cinf : ℝ, 0 < Cinf ∧
      (∃ R C' : ℝ, 0 < R ∧ ∀ x : E₃, R ≤ ‖x‖ → |u x - Cinf / ‖x‖| ≤ C' / ‖x‖ ^ 2) ∧
      ∃ ε₀ : ℝ, 0 < ε₀ ∧ ∃ M : ℝ, ∀ ε : ℝ, 0 < ε → ε < ε₀ →
        ∃ ρ : E₃ → ℝ, ContDiffOn ℝ (⊤ : ℕ∞) ρ {θ | θ ≠ 0} ∧
          (∀ θ : E₃, ‖θ‖ = 1 → 0 < ρ θ ∧ |ρ θ - Cinf / ε| ≤ M) ∧
          u ⁻¹' {ε} = (fun θ => ρ θ • θ) '' sphere (0 : E₃) 1 ∧
          (∀ q : E₃ → ℝ≥0∞, Measurable q →
            ∫⁻ x in u ⁻¹' {ε}, q x ∂hausdorffMeasure2 3 =
              ∫⁻ θ in sphere (0 : E₃) 1, q (ρ θ • θ) *
                ENNReal.ofReal (ρ θ * Real.sqrt (ρ θ ^ 2 +
                  ‖gradient ρ θ - ⟪gradient ρ θ, θ⟫ • θ‖ ^ 2)) ∂hausdorffMeasure2 3) ∧
          (∀ f : E₃ → ℝ, Measurable f →
            ∫ x in u ⁻¹' {ε}, f x ∂hausdorffMeasure2 3 =
              ∫ θ in sphere (0 : E₃) 1, f (ρ θ • θ) *
                (ρ θ * Real.sqrt (ρ θ ^ 2 +
                  ‖gradient ρ θ - ⟪gradient ρ θ, θ⟫ • θ‖ ^ 2)) ∂hausdorffMeasure2 3) ∧
          ∀ θ : E₃, ‖θ‖ = 1 →
            |ρ θ * Real.sqrt (ρ θ ^ 2 + ‖gradient ρ θ - ⟪gradient ρ θ, θ⟫ • θ‖ ^ 2) -
              Cinf ^ 2 / ε ^ 2| ≤ M * ε * (Cinf ^ 2 / ε ^ 2) := by
  obtain ⟨Cinf, hC, hexp, ε₀, hε₀, M, hM⟩ :=
    capacitary_level_radius_fderiv_bound hK hR₀ hKR hzero hu hh hb hinf
  set N : ℝ := |M| with hN
  have hN0 : 0 ≤ N := abs_nonneg M
  refine ⟨Cinf, hC, hexp, min (min ε₀ 1) (Cinf / (2 * (N + 1))),
    lt_min (lt_min hε₀ one_pos) (by positivity), N + (2 * N * Cinf + 3 * N ^ 2) / Cinf ^ 2,
    fun ε hε hεε₁ => ?_⟩
  have hεε₀ : ε < ε₀ := lt_of_lt_of_le hεε₁ ((min_le_left _ _).trans (min_le_left _ _))
  have hε1 : ε < 1 := lt_of_lt_of_le hεε₁ ((min_le_left _ _).trans (min_le_right _ _))
  have hεC : ε < Cinf / (2 * (N + 1)) := lt_of_lt_of_le hεε₁ (min_le_right _ _)
  obtain ⟨ρ, hρs, hρM, hlevel, -, hDρ⟩ := hM ε hε hεε₀
  have hρbd : ∀ θ : E₃, ‖θ‖ = 1 → |ρ θ - Cinf / ε| ≤ N := fun θ hθ =>
    (hρM θ hθ).trans (le_abs_self M)
  obtain ⟨hpos, himage, hL, hB, hJ⟩ := levelArea_of_radial hC hN0 hε hε1 hεC hρs hρbd
    (fun θ hθ => (hDρ θ hθ).trans (le_abs_self M))
    ((level_preimage_eq_compl hb hε1).trans hlevel)
  have hMle : N ≤ N + (2 * N * Cinf + 3 * N ^ 2) / Cinf ^ 2 :=
    le_add_of_nonneg_right (by positivity)
  exact ⟨ρ, hρs, fun θ hθ => ⟨hpos θ hθ, (hρbd θ hθ).trans hMle⟩, himage, hL, hB, hJ⟩

/-- Blueprint `lem:level-asymptotics`, radial-graph part in one statement: for small `ε` the
level `{u = ε}` is the radial graph of one zero-homogeneous smooth `ρ` with
`ρ = Cinf/ε + O(1)`, two angular derivatives bounded uniformly, `w = ε²/Cinf + O(ε³)` with
`∇u ≠ 0`, and area element `dH² = J dω`, `J = (Cinf²/ε²)(1 + O(ε))`. -/
theorem capacitary_level_radial_geometry
    {K : Set E₃} (hK : IsCompact K) {R₀ : ℝ} (hR₀ : 0 < R₀)
    (hKR : K ⊆ closedBall 0 R₀) (hzero : (0 : E₃) ∈ interior K)
    {u : E₃ → ℝ} (hu : Continuous u)
    (hh : HasDistributionalLaplacianOn u (fun _ => 0) Kᶜ)
    (hb : ∀ x ∈ K, u x = 1) (hinf : Tendsto u (cocompact E₃) (𝓝 0)) :
    ∃ Cinf : ℝ, 0 < Cinf ∧
      (∃ R C' : ℝ, 0 < R ∧ ∀ x : E₃, R ≤ ‖x‖ → |u x - Cinf / ‖x‖| ≤ C' / ‖x‖ ^ 2) ∧
      ∃ ε₀ : ℝ, 0 < ε₀ ∧ ∃ M : ℝ, ∀ ε : ℝ, 0 < ε → ε < ε₀ →
        ∃ ρ : E₃ → ℝ, ContDiffOn ℝ (⊤ : ℕ∞) ρ {θ | θ ≠ 0} ∧
          (∀ θ : E₃, θ ≠ 0 → ρ θ = ρ (‖θ‖⁻¹ • θ)) ∧
          (∀ θ : E₃, ‖θ‖ = 1 → 0 < ρ θ ∧ |ρ θ - Cinf / ε| ≤ M) ∧
          u ⁻¹' {ε} = (fun θ => ρ θ • θ) '' sphere (0 : E₃) 1 ∧
          (∀ x : E₃, u x = ε →
            gradient u x ≠ 0 ∧ |‖gradient u x‖ - ε ^ 2 / Cinf| ≤ M * ε ^ 3) ∧
          (∀ θ : E₃, ‖θ‖ = 1 → ‖fderiv ℝ ρ θ‖ ≤ M ∧ ‖fderiv ℝ (fderiv ℝ ρ) θ‖ ≤ M) ∧
          (∀ q : E₃ → ℝ≥0∞, Measurable q →
            ∫⁻ x in u ⁻¹' {ε}, q x ∂hausdorffMeasure2 3 =
              ∫⁻ θ in sphere (0 : E₃) 1, q (ρ θ • θ) *
                ENNReal.ofReal (ρ θ * Real.sqrt (ρ θ ^ 2 +
                  ‖gradient ρ θ - ⟪gradient ρ θ, θ⟫ • θ‖ ^ 2)) ∂hausdorffMeasure2 3) ∧
          (∀ f : E₃ → ℝ, Measurable f →
            ∫ x in u ⁻¹' {ε}, f x ∂hausdorffMeasure2 3 =
              ∫ θ in sphere (0 : E₃) 1, f (ρ θ • θ) *
                (ρ θ * Real.sqrt (ρ θ ^ 2 +
                  ‖gradient ρ θ - ⟪gradient ρ θ, θ⟫ • θ‖ ^ 2)) ∂hausdorffMeasure2 3) ∧
          ∀ θ : E₃, ‖θ‖ = 1 →
            |ρ θ * Real.sqrt (ρ θ ^ 2 + ‖gradient ρ θ - ⟪gradient ρ θ, θ⟫ • θ‖ ^ 2) -
              Cinf ^ 2 / ε ^ 2| ≤ M * ε * (Cinf ^ 2 / ε ^ 2) := by
  obtain ⟨Cinf, hC, hexp, ε₀, hε₀, M, hM⟩ :=
    capacitary_level_radius_fderiv_two_bound hK hR₀ hKR hzero hu hh hb hinf
  set N : ℝ := |M| with hN
  have hN0 : 0 ≤ N := abs_nonneg M
  set M' : ℝ := N + (2 * N * Cinf + 3 * N ^ 2) / Cinf ^ 2 with hM'
  have hMle : N ≤ M' := le_add_of_nonneg_right (by positivity)
  have hMM : M ≤ M' := (le_abs_self M).trans hMle
  refine ⟨Cinf, hC, hexp, min (min ε₀ 1) (Cinf / (2 * (N + 1))),
    lt_min (lt_min hε₀ one_pos) (by positivity), M', fun ε hε hεε₁ => ?_⟩
  have hεε₀ : ε < ε₀ := lt_of_lt_of_le hεε₁ ((min_le_left _ _).trans (min_le_left _ _))
  have hε1 : ε < 1 := lt_of_lt_of_le hεε₁ ((min_le_left _ _).trans (min_le_right _ _))
  have hεC : ε < Cinf / (2 * (N + 1)) := lt_of_lt_of_le hεε₁ (min_le_right _ _)
  obtain ⟨ρ, hρs, hhom, hρM, hlevel, hgrad, hD⟩ := hM ε hε hεε₀
  have hρbd : ∀ θ : E₃, ‖θ‖ = 1 → |ρ θ - Cinf / ε| ≤ N := fun θ hθ =>
    (hρM θ hθ).trans (le_abs_self M)
  obtain ⟨hpos, himage, hL, hB, hJ⟩ := levelArea_of_radial hC hN0 hε hε1 hεC hρs hρbd
    (fun θ hθ => (hD θ hθ).1.trans (le_abs_self M))
    ((level_preimage_eq_compl hb hε1).trans hlevel)
  refine ⟨ρ, hρs, hhom, fun θ hθ => ⟨hpos θ hθ, (hρbd θ hθ).trans hMle⟩, himage,
    fun x hx => ⟨(hgrad x hx).1, (hgrad x hx).2.trans
      (mul_le_mul_of_nonneg_right hMM (by positivity))⟩,
    fun θ hθ => ⟨(hD θ hθ).1.trans hMM, (hD θ hθ).2.trans hMM⟩, hL, hB, hJ⟩

end LiquidDrop

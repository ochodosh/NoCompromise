module

public import NoCompromise.CapacitaryK.KelvinSecondOrder
public import NoCompromise.CapacitaryK.KelvinTranslation
public import NoCompromise.Capacity.KelvinLevels

@[expose] public section

/-!
# `lem:K-normalization`: the translated expansion (chapter 31)

Translating the origin by `a / C`, with `C = v 0` and `a = ∇v(0)` the value and gradient at `0` of
the smooth Kelvin extension `v`, removes the dipole term: combining the second-order Kelvin
expansion (`kelvin_second_order_value`) with the kernel expansions under translation
(`inv_norm_add_expansion`, `dipole_add_expansion`, `quadrupole_add_bound`),
`u(x + a/C) = C/|x| + Q(x)/|x|⁵ + O(|x|⁻⁴)` with the quadratic
`Q(x) = -(3⟪a,x⟫² - |a|²|x|²)/(2C) + D²v(0)(x,x)/2` (eq:K-expansion, `Q(θ) = Q(x)/|x|²`).
`capacitary_translated_expansion` specialises this to the capacitary potential (`C = v 0 > 0`).
Harmonicity of `Q` is available in parts: the dipole-induced part is harmonic
(`translationQuadrupolePolynomial_laplacian`) and `D²v(0)` is trace-free
(`kelvin_quadrupole_trace_zero`). The zero spherical mean of `Q` and the differentiated remainders
after translation are not formalised here.
-/

noncomputable section
open Set Filter Metric InnerProductSpace
open scoped Topology Gradient RealInnerProductSpace
namespace LiquidDrop.CapacitaryK
local notation "E₃" => EuclideanSpace ℝ (Fin 3)

/-- The translated quadrupole of `eq:K-expansion`. -/
def kelvinTranslatedQuadrupole (v : E₃ → ℝ) (x : E₃) : ℝ :=
  -(3 * ⟪gradient v 0, x⟫ ^ 2 - ‖gradient v 0‖ ^ 2 * ‖x‖ ^ 2) / (2 * v 0) +
    (1 / 2 : ℝ) * fderiv ℝ (fderiv ℝ v) 0 x x

/-- `lem:K-normalization` (`eq:K-expansion`, value part): after translating the origin by
`∇v(0)/v(0)`, `u = C/|x| + Q(x)/|x|⁵ + O(|x|⁻⁴)`. -/
theorem kelvin_translated_expansion {u v : E₃ → ℝ} {r : ℝ} (hr : 0 < r)
    (hv : ContDiffOn ℝ (⊤ : ℕ∞) v (ball 0 r))
    (he : EqOn v (kelvinTransform u) (ball 0 r \ {0})) (hC : v 0 ≠ 0) :
    ∃ R M : ℝ, 0 < R ∧ ∀ x : E₃, R ≤ ‖x‖ →
      |u (x + (v 0)⁻¹ • gradient v 0) - v 0 / ‖x‖ -
        kelvinTranslatedQuadrupole v x / ‖x‖ ^ 5| ≤ M / ‖x‖ ^ 4 := by
  obtain ⟨R₁, M₁, hR₁, hb⟩ := kelvin_second_order_value hr hv he
  set C := v 0 with hCdef
  set a := gradient v 0 with hadef
  set B := fderiv ℝ (fderiv ℝ v) 0 with hBdef
  set z : E₃ := C⁻¹ • a with hzdef
  have hL : ∀ y, fderiv ℝ v 0 y = ⟪a, y⟫ := by
    intro y
    rw [hadef, gradient, InnerProductSpace.toDual_symm_apply]
  let R := max (R₁ + ‖z‖) (max (2 * ‖z‖) 1)
  refine ⟨R, 16 * M₁ + |C| * (5 * ‖z‖ ^ 3) + 39 * ‖a‖ * ‖z‖ ^ 2 +
    (1 / 2) * (158 * ‖B‖ * ‖z‖), lt_of_lt_of_le one_pos ((le_max_right _ _).trans
      (le_max_right _ _)), ?_⟩
  intro x hx
  have hx1 : 1 ≤ ‖x‖ := ((le_max_right _ _).trans (le_max_right _ _)).trans hx
  have hx2 : 2 * ‖z‖ ≤ ‖x‖ := ((le_max_left _ _).trans (le_max_right _ _)).trans hx
  have hxR : R₁ + ‖z‖ ≤ ‖x‖ := (le_max_left _ _).trans hx
  have hn : 0 < ‖x‖ := lt_of_lt_of_le one_pos hx1
  have hx0 : x ≠ 0 := norm_pos_iff.mp hn
  have hxz : ‖x‖ - ‖z‖ ≤ ‖x + z‖ := by
    have := norm_sub_norm_le x (-z)
    simpa [sub_neg_eq_add] using this
  have hxzR : R₁ ≤ ‖x + z‖ := by linarith
  have hxzh : ‖x‖ / 2 ≤ ‖x + z‖ := by linarith
  have hxzpos : 0 < ‖x + z‖ := by linarith
  have h1 := hb (x + z) hxzR
  have h2 := inv_norm_add_expansion x z hx2 hx0
  have h3 := dipole_add_expansion a x z hx2 hx0
  have h4 := quadrupole_add_bound B x z hx2 hx0
  -- the model at `x + z`
  have hmodel : kelvinSecondOrderModel v (x + z) =
      C / ‖x + z‖ + ⟪a, x + z⟫ / ‖x + z‖ ^ 3 + (1 / 2 : ℝ) * B (x + z) (x + z) / ‖x + z‖ ^ 5 := by
    simp only [kelvinSecondOrderModel, hL, ← hCdef, ← hBdef]
  rw [hmodel] at h1
  have hM₁ : 0 ≤ M₁ := by
    have h0 := (abs_nonneg _).trans h1
    rwa [le_div_iff₀ (by positivity), zero_mul] at h0
  -- the algebraic identity: the dipole cancels and the quadrupole is `kelvinTranslatedQuadrupole`
  have hzx : ⟪z, x⟫ = C⁻¹ * ⟪a, x⟫ := by rw [hzdef, real_inner_smul_left]
  have haz : ⟪a, z⟫ = C⁻¹ * ‖a‖ ^ 2 := by
    rw [hzdef, real_inner_smul_right, real_inner_self_eq_norm_sq]
  have hzz : ‖z‖ ^ 2 = C⁻¹ ^ 2 * ‖a‖ ^ 2 := by
    rw [hzdef, norm_smul, Real.norm_eq_abs, mul_pow, sq_abs]
  have hid : C * (1 / ‖x‖ - ⟪z, x⟫ / ‖x‖ ^ 3 +
        (3 * ⟪z, x⟫ ^ 2 - ‖z‖ ^ 2 * ‖x‖ ^ 2) / (2 * ‖x‖ ^ 5)) +
      (⟪a, x⟫ / ‖x‖ ^ 3 + (⟪a, z⟫ * ‖x‖ ^ 2 - 3 * ⟪a, x⟫ * ⟪z, x⟫) / ‖x‖ ^ 5) +
      (1 / 2 : ℝ) * B x x / ‖x‖ ^ 5 =
      C / ‖x‖ + kelvinTranslatedQuadrupole v x / ‖x‖ ^ 5 := by
    simp only [kelvinTranslatedQuadrupole, ← hCdef, ← hadef, ← hBdef]
    rw [hzx, haz, hzz]
    field_simp
    ring
  have hfour : ‖x‖ ^ 4 ≤ 16 * ‖x + z‖ ^ 4 := by
    have : (‖x‖ / 2) ^ 4 ≤ ‖x + z‖ ^ 4 := pow_le_pow_left₀ (by positivity) hxzh 4
    nlinarith
  have hM1' : M₁ / ‖x + z‖ ^ 4 ≤ 16 * M₁ / ‖x‖ ^ 4 := by
    rw [div_le_div_iff₀ (by positivity) (by positivity)]
    nlinarith
  have hq : |(1 / 2 : ℝ) * B (x + z) (x + z) / ‖x + z‖ ^ 5 - (1 / 2 : ℝ) * B x x / ‖x‖ ^ 5| ≤
      (1 / 2) * (158 * ‖B‖ * ‖z‖ / ‖x‖ ^ 4) := by
    have : (1 / 2 : ℝ) * B (x + z) (x + z) / ‖x + z‖ ^ 5 - (1 / 2 : ℝ) * B x x / ‖x‖ ^ 5 =
        (1 / 2) * (B (x + z) (x + z) / ‖x + z‖ ^ 5 - B x x / ‖x‖ ^ 5) := by ring
    rw [this, abs_mul, abs_of_pos (by norm_num : (0 : ℝ) < 1 / 2)]
    exact mul_le_mul_of_nonneg_left h4 (by norm_num)
  have hc : |C * (1 / ‖x + z‖ - 1 / ‖x‖ + ⟪z, x⟫ / ‖x‖ ^ 3 -
      (3 * ⟪z, x⟫ ^ 2 - ‖z‖ ^ 2 * ‖x‖ ^ 2) / (2 * ‖x‖ ^ 5))| ≤ |C| * (5 * ‖z‖ ^ 3 / ‖x‖ ^ 4) := by
    rw [abs_mul]
    exact mul_le_mul_of_nonneg_left h2 (abs_nonneg _)
  have hsplit : u (x + z) - C / ‖x‖ - kelvinTranslatedQuadrupole v x / ‖x‖ ^ 5 =
      (u (x + z) - (C / ‖x + z‖ + ⟪a, x + z⟫ / ‖x + z‖ ^ 3 +
        (1 / 2 : ℝ) * B (x + z) (x + z) / ‖x + z‖ ^ 5)) +
      C * (1 / ‖x + z‖ - 1 / ‖x‖ + ⟪z, x⟫ / ‖x‖ ^ 3 -
        (3 * ⟪z, x⟫ ^ 2 - ‖z‖ ^ 2 * ‖x‖ ^ 2) / (2 * ‖x‖ ^ 5)) +
      (⟪a, x + z⟫ / ‖x + z‖ ^ 3 - ⟪a, x⟫ / ‖x‖ ^ 3 -
        (⟪a, z⟫ * ‖x‖ ^ 2 - 3 * ⟪a, x⟫ * ⟪z, x⟫) / ‖x‖ ^ 5) +
      ((1 / 2 : ℝ) * B (x + z) (x + z) / ‖x + z‖ ^ 5 - (1 / 2 : ℝ) * B x x / ‖x‖ ^ 5) := by
    rw [show u (x + z) - C / ‖x‖ - kelvinTranslatedQuadrupole v x / ‖x‖ ^ 5 =
      u (x + z) - (C / ‖x‖ + kelvinTranslatedQuadrupole v x / ‖x‖ ^ 5) by ring, ← hid]
    ring
  rw [hsplit]
  have hsum : ∀ p q s w : ℝ, |p + q + s + w| ≤ |p| + |q| + |s| + |w| := fun p q s w =>
    (abs_add_le _ _).trans (add_le_add ((abs_add_le _ _).trans
      (add_le_add (abs_add_le _ _) le_rfl)) le_rfl)
  refine (hsum _ _ _ _).trans ?_
  have hfin : 16 * M₁ / ‖x‖ ^ 4 + |C| * (5 * ‖z‖ ^ 3 / ‖x‖ ^ 4) +
      39 * ‖a‖ * ‖z‖ ^ 2 / ‖x‖ ^ 4 + (1 / 2) * (158 * ‖B‖ * ‖z‖ / ‖x‖ ^ 4) =
      (16 * M₁ + |C| * (5 * ‖z‖ ^ 3) + 39 * ‖a‖ * ‖z‖ ^ 2 +
        (1 / 2) * (158 * ‖B‖ * ‖z‖)) / ‖x‖ ^ 4 := by
    field_simp
  rw [← hfin]
  gcongr
  · exact h1.trans hM1'

/-- `lem:K-normalization` (`eq:K-expansion`, value part) for the capacitary potential: with the
smooth harmonic Kelvin extension `v` (`kelvin_smooth_extension`), `C = v 0 > 0`, and after
translating by `∇v(0)/C`, `u = C/|x| + Q(x)/|x|⁵ + O(|x|⁻⁴)`, `Q = kelvinTranslatedQuadrupole v`. -/
theorem capacitary_translated_expansion
    {K : Set E₃} (hK : IsCompact K) {R₀ : ℝ} (hR₀ : 0 < R₀)
    (hKR : K ⊆ closedBall 0 R₀) (hzero : (0 : E₃) ∈ interior K)
    {u : E₃ → ℝ} (hu : Continuous u)
    (hh : HasDistributionalLaplacianOn u (fun _ => 0) Kᶜ)
    (hb : ∀ x ∈ K, u x = 1) (hinf : Tendsto u (cocompact E₃) (𝓝 0)) :
    ∃ (v : E₃ → ℝ) (r : ℝ), 0 < r ∧ ContDiffOn ℝ (⊤ : ℕ∞) v (ball 0 r) ∧
      EqOn v (kelvinTransform u) (ball 0 r \ {0}) ∧ (∀ y ∈ ball 0 r, laplacianN v y = 0) ∧
      0 < v 0 ∧
      ∃ R M : ℝ, 0 < R ∧ ∀ x : E₃, R ≤ ‖x‖ →
        |u (x + (v 0)⁻¹ • gradient v 0) - v 0 / ‖x‖ -
          kelvinTranslatedQuadrupole v x / ‖x‖ ^ 5| ≤ M / ‖x‖ ^ 4 := by
  obtain ⟨v, hv, he, hharm⟩ := kelvin_smooth_extension hK hR₀ hKR hzero hu hh hb hinf
  have hr : 0 < 1 / R₀ := by positivity
  obtain ⟨a, ha, haK⟩ := Metric.mem_nhds_iff.mp (mem_interior_iff_mem_nhds.mp hzero)
  have hl := div_norm_le_of_exterior_harmonic hK ha haK hu hh
    (fun x hx => (hb x hx).ge) hinf
  obtain ⟨R, C', _, hexp⟩ := kelvin_expansion_of_smooth_extension hr hv he
  have haC : a ≤ v 0 := kelvin_coefficient_ge_of_lower_bound
    (R₀ := R₀) (R := R) (C' := C') (fun x hx => hl x (by
      intro hxK
      have hxR : ‖x‖ ≤ R₀ := by simpa using hKR hxK
      exact (not_lt_of_ge hxR) hx)) (fun x hx => (hexp x hx).1)
  have hC : 0 < v 0 := ha.trans_le haC
  exact ⟨v, 1 / R₀, hr, hv, he, hharm, hC, kelvin_translated_expansion hr hv he hC.ne'⟩

end LiquidDrop.CapacitaryK

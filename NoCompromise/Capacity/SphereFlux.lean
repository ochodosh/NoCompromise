import NoCompromise.Capacity.Kelvin
import NoCompromise.Area.Sphere

/-!
# Flux of the capacitary potential through large spheres

Blueprint `lem:kelvin` (the flux step `4π C_∞ + o(1)` of its proof, towards `C_∞ = C` and
`lem:flux-identity`): the gradient expansion `∇u = -C_∞ x/|x|³ + O(|x|⁻³)` gives the outward
flux `-4π C_∞ + O(1/r)` through the sphere of radius `r`.
-/

noncomputable section
open Set Filter Metric MeasureTheory InnerProductSpace
open scoped Topology Gradient RealInnerProductSpace
namespace LiquidDrop

/-- Blueprint `lem:kelvin`: the outward flux through a large sphere of a function whose
gradient has the Kelvin expansion is `-4π C_∞` up to `4π C' / r`. -/
theorem sphere_flux_of_gradient_expansion {u : EuclideanSpace ℝ (Fin 3) → ℝ}
    {Cinf C' R : ℝ} (hR : 0 < R)
    (hexp : ∀ x : EuclideanSpace ℝ (Fin 3), R ≤ ‖x‖ →
      ‖gradient u x + (Cinf / ‖x‖ ^ 3) • x‖ ≤ C' / ‖x‖ ^ 3)
    {r : ℝ} (hr : R ≤ r) :
    |(∫ x in sphere (0 : EuclideanSpace ℝ (Fin 3)) r,
        inner ℝ (gradient u x) (r⁻¹ • x) ∂hausdorffMeasure2 3) + 4 * Real.pi * Cinf| ≤
      4 * Real.pi * C' / r := by
  have hr0 : 0 < r := hR.trans_le hr
  set μ := hausdorffMeasure2 3
  set S := sphere (0 : EuclideanSpace ℝ (Fin 3)) r
  have hμS : μ S = ENNReal.ofReal (4 * Real.pi * r ^ 2) := hausdorffMeasure2_sphere 0 hr0
  have hμSfin : μ S < ⊤ := by rw [hμS]; exact ENNReal.ofReal_lt_top
  have hμSreal : μ.real S = 4 * Real.pi * r ^ 2 := by
    rw [measureReal_def, hμS, ENNReal.toReal_ofReal (by positivity)]
  let e : EuclideanSpace ℝ (Fin 3) → ℝ := fun x =>
    inner ℝ (gradient u x + (Cinf / r ^ 3) • x) (r⁻¹ • x)
  have hsplit : EqOn (fun x => inner ℝ (gradient u x) (r⁻¹ • x))
      (fun x => e x + (-(Cinf / r ^ 2))) S := by
    intro x hx
    have hxn : ‖x‖ = r := by simpa [S] using hx
    simp only [e, inner_add_left, real_inner_smul_left, real_inner_smul_right,
      real_inner_self_eq_norm_sq, hxn]
    field_simp
    ring
  have hmeas : Measurable (fun x : EuclideanSpace ℝ (Fin 3) => gradient u x) := by
    have : (fun x => gradient u x) =
        fun x => (toDual ℝ (EuclideanSpace ℝ (Fin 3))).symm (fderiv ℝ u x) := rfl
    rw [this]
    exact (toDual ℝ (EuclideanSpace ℝ (Fin 3))).symm.continuous.measurable.comp
      (measurable_fderiv ℝ u)
  have he_meas : Measurable e := by
    have hs1 : Measurable (fun x : EuclideanSpace ℝ (Fin 3) => (Cinf / r ^ 3) • x) :=
      (continuous_const_smul _).measurable
    have hs2 : Measurable (fun x : EuclideanSpace ℝ (Fin 3) => r⁻¹ • x) :=
      (continuous_const_smul _).measurable
    exact (hmeas.add hs1).inner hs2
  have hbound : ∀ x ∈ S, ‖e x‖ ≤ C' / r ^ 3 := by
    intro x hx
    have hxn : ‖x‖ = r := by simpa [S] using hx
    have h1 := hexp x (by rw [hxn]; exact hr)
    rw [hxn] at h1
    calc ‖e x‖ ≤ ‖gradient u x + (Cinf / r ^ 3) • x‖ * ‖r⁻¹ • x‖ :=
          norm_inner_le_norm _ _
      _ = ‖gradient u x + (Cinf / r ^ 3) • x‖ := by
          rw [norm_smul, hxn, Real.norm_eq_abs, abs_inv, abs_of_pos hr0,
            inv_mul_cancel₀ hr0.ne', mul_one]
      _ ≤ C' / r ^ 3 := h1
  have hint_e : IntegrableOn e S μ := by
    refine Measure.integrableOn_of_bounded (M := C' / r ^ 3) hμSfin.ne
      he_meas.aestronglyMeasurable ?_
    exact (ae_restrict_iff' (isClosed_sphere.measurableSet)).mpr
      (Eventually.of_forall hbound)
  have hint_c : IntegrableOn (fun _ : EuclideanSpace ℝ (Fin 3) => -(Cinf / r ^ 2)) S μ :=
    integrableOn_const hμSfin.ne
  rw [setIntegral_congr_fun isClosed_sphere.measurableSet hsplit,
    integral_add hint_e hint_c, setIntegral_const, hμSreal, smul_eq_mul]
  have hconst : 4 * Real.pi * r ^ 2 * -(Cinf / r ^ 2) + 4 * Real.pi * Cinf = 0 := by
    field_simp
    ring
  have hmain : (∫ x in S, e x ∂μ) + 4 * Real.pi * r ^ 2 * -(Cinf / r ^ 2) +
      4 * Real.pi * Cinf = ∫ x in S, e x ∂μ := by linarith
  rw [hmain]
  have hle := norm_setIntegral_le_of_norm_le_const hμSfin hbound
  rw [hμSreal, Real.norm_eq_abs] at hle
  calc |∫ x in S, e x ∂μ| ≤ C' / r ^ 3 * (4 * Real.pi * r ^ 2) := hle
    _ = 4 * Real.pi * C' / r := by field_simp

/-- Blueprint `lem:kelvin`: for the capacitary potential, the value and gradient expansions
hold with a coefficient `C_∞`, and the outward flux through the sphere of radius `r ≥ R` is
`-4π C_∞` up to `4π C' / r`. -/
theorem capacitary_sphere_flux
    {K : Set (EuclideanSpace ℝ (Fin 3))} (hK : IsCompact K) {R₀ : ℝ} (hR₀ : 0 < R₀)
    (hKR : K ⊆ closedBall 0 R₀) (hzero : (0 : EuclideanSpace ℝ (Fin 3)) ∈ interior K)
    {u : EuclideanSpace ℝ (Fin 3) → ℝ} (hu : Continuous u)
    (hh : HasDistributionalLaplacianOn u (fun _ => 0) Kᶜ)
    (hb : ∀ x ∈ K, u x = 1)
    (hinf : Tendsto u (cocompact (EuclideanSpace ℝ (Fin 3))) (𝓝 0)) :
    ∃ Cinf R C' : ℝ, 0 < R ∧
      (∀ x : EuclideanSpace ℝ (Fin 3), R ≤ ‖x‖ →
        |u x - Cinf / ‖x‖| ≤ C' / ‖x‖ ^ 2 ∧
        ‖gradient u x + (Cinf / ‖x‖ ^ 3) • x‖ ≤ C' / ‖x‖ ^ 3) ∧
      ∀ r : ℝ, R ≤ r →
        |(∫ x in sphere (0 : EuclideanSpace ℝ (Fin 3)) r,
            inner ℝ (gradient u x) (r⁻¹ • x) ∂hausdorffMeasure2 3) +
          4 * Real.pi * Cinf| ≤ 4 * Real.pi * C' / r := by
  obtain ⟨Cinf, R, C', hR, hexp⟩ := kelvin_expansion hK hR₀ hKR hzero hu hh hb hinf
  exact ⟨Cinf, R, C', hR, hexp, fun r hr =>
    sphere_flux_of_gradient_expansion hR (fun x hx => (hexp x hx).2) hr⟩

end LiquidDrop

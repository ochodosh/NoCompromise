import NoCompromise.Regularity.TangentRadial

/-!
# Global radial distributional stationarity of a tangent limit

Local minimality and constant density ratios persist under positive dilation.
Transporting each compact test to the inner unit ball extends the proved local
radial pairing identity to every compactly supported test in the whole space.
-/

noncomputable section
open MeasureTheory Set Filter Metric InnerProductSpace
open scoped Topology ENNReal RealInnerProductSpace
namespace LiquidDrop
set_option maxSynthPendingDepth 8

lemma divergenceN_radial_comp_pos_smul (φ : AmbientSpace → ℝ)
    {r : ℝ} (hr : 0 < r) (x : AmbientSpace) :
    divergenceN (fun y => φ (r • y) • y) x =
      divergenceN (fun y => φ y • y) (r • x) := by
  have he : (fun y : AmbientSpace => φ (r • y) • y) =
      r⁻¹ • (fun y => φ (r • y) • (r • y)) := by
    funext y
    simp only [Pi.smul_apply, smul_smul]
    congr 1
    field_simp
  rw [he, divergenceN_const_smul]
  have hc := divergenceN_comp_smul (fun y => φ y • y) r x
  rw [hc, ← mul_assoc, inv_mul_cancel₀ hr.ne', one_mul]

lemma IsLocallyPerimeterMinimizing.blowup_density_ratio {F : Set AmbientSpace}
    (hF : IsLocallyPerimeterMinimizing F) {θ : ℝ}
    (hd : ∀ R : ℝ, 0 < R → (perimeterIn F (ball 0 R)).toReal / R ^ 2 = θ)
    {r : ℝ} (hr : 0 < r) {R : ℝ} (hR : 0 < R) :
    (perimeterIn (LiquidDrop.blowupSet F 0 r) (ball 0 R)).toReal / R ^ 2 = θ := by
  have hmin := hF.isOmegaMinimal
  have h := hd (r * R) (mul_pos hr hR)
  rw [perimeterIn_blowupSet_ball_real F hmin.locallyFinite hmin.nullMeasurable 0 hr,
    measureReal_def, canonicalPerimeterMeasure_open F hmin.locallyFinite
      hmin.nullMeasurable isOpen_ball]
  convert h using 1
  field_simp [hr.ne', hR.ne']

/-- The radial distributional derivative of a minimizing constant-density set
vanishes on the whole space, with no support-radius restriction. -/
theorem IsLocallyPerimeterMinimizing.radial_pairing_eq_zero {F : Set AmbientSpace}
    (hF : IsLocallyPerimeterMinimizing F) {θ : ℝ}
    (hd : ∀ R : ℝ, 0 < R → (perimeterIn F (ball 0 R)).toReal / R ^ 2 = θ)
    {φ : AmbientSpace → ℝ} (hφ : ContDiff ℝ 1 φ) (hcφ : HasCompactSupport φ) :
    (∫ y in F, divergenceN (fun z => φ z • z) y) = 0 := by
  obtain ⟨R, hR, hs⟩ := hcφ.isBounded.subset_ball_lt 0 (0 : AmbientSpace)
  let r := 2 * R
  have hr : 0 < r := by dsimp [r]; positivity
  let ψ : AmbientSpace → ℝ := fun y => φ (r • y)
  have hψ : ContDiff ℝ 1 ψ := hφ.comp (contDiff_id.const_smul r)
  have hcψ : HasCompactSupport ψ :=
    hcφ.comp_homeomorph (Homeomorph.smulOfNeZero r hr.ne')
  have hsψ : tsupport ψ ⊆ ball 0 (1 / 2 : ℝ) := by
    intro y hy
    have hcont : Continuous (fun z : AmbientSpace => r • z) := by fun_prop
    have hyφ : r • y ∈ tsupport φ := tsupport_comp_subset_preimage φ hcont hy
    have hyn := hs hyφ
    simp only [mem_ball, dist_zero_right, norm_smul, Real.norm_eq_abs, abs_of_pos hr] at hyn ⊢
    dsimp [r] at hyn
    nlinarith
  have hmin := (hF.blowupSet 0 hr).isOmegaMinimal
  have hz := hmin.radial_pairing_eq_zero_halfBall
    (fun S hS => hF.blowup_density_ratio hd hr hS) hψ hcψ hsψ
  have hscale := setIntegral_image_smul
    (fun y => divergenceN (fun z => φ z • z) y) (LiquidDrop.blowupSet F 0 r) hr
  have he : (fun y : AmbientSpace => r • y) '' LiquidDrop.blowupSet F 0 r = F := by
    simpa only [zero_add] using image_blowupSet F 0 hr
  rw [he] at hscale
  simp_rw [← divergenceN_radial_comp_pos_smul φ hr] at hscale
  change (∫ y in F, divergenceN (fun z => φ z • z) y) = r ^ 3 *
    ∫ y in LiquidDrop.blowupSet F 0 r, divergenceN (fun z => ψ z • z) y at hscale
  rw [hz, mul_zero] at hscale
  exact hscale

end LiquidDrop

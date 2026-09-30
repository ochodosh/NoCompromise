module

public import NoCompromise.Regularity.OmegaMinimal
public import NoCompromise.DeGiorgi.BlowupPolar

@[expose] public section

/-!
# Quasiminimality under actual blow-up transformations

Competitors, their compact differences, perimeter, and volume are transported by
the same affine homeomorphism. No comparison property of the dilated set is
assumed. Its error coefficient is exactly ωr and its admissible scale is 1/r.
-/

noncomputable section
open MeasureTheory Set Filter Metric
open scoped Topology ENNReal symmDiff
namespace LiquidDrop
set_option maxSynthPendingDepth 8

lemma image_ball_blowupHomeomorph (x y : AmbientSpace) {r : ℝ} (hr : 0 < r) (R : ℝ) :
    blowupHomeomorph x hr '' ball y R = ball (x + r • y) (r * R) := by
  change (fun z => x + r • z) '' ball y R = _
  rw [← image_image (fun z => x + z) (fun z => r • z), Metric.smul_image_ball hr.ne']
  simp only [Real.norm_eq_abs, abs_of_pos hr]
  exact (IsometryEquiv.addLeft x).image_ball (r • y) (r * R)

lemma image_blowupHomeomorph_eq_blowupSet (F : Set AmbientSpace)
    (x : AmbientSpace) {r : ℝ} (hr : 0 < r) :
    blowupHomeomorph x hr '' F = blowupSet F (-(r⁻¹ • x)) r⁻¹ := by
  rw [← (blowupHomeomorph x hr).preimage_symm]
  change (fun y => (blowupHomeomorph x hr).symm y) ⁻¹' F = _
  congr 1
  funext y
  simp only [blowupHomeomorph_symm_apply, smul_sub]
  abel

lemma volume_image_blowupHomeomorph (F : Set AmbientSpace)
    (x : AmbientSpace) {r : ℝ} (hr : 0 < r) :
    volume (blowupHomeomorph x hr '' F) = ENNReal.ofReal (r ^ 3) * volume F := by
  change volume ((fun z => x + r • z) '' F) = _
  rw [← image_image (fun z => x + z) (fun z => r • z),
    volume_image_add_left, volume_image_pos_smul _ hr]

/-- Actual quasiminimality under positive dilation, at any admissible target scale. -/
theorem IsOmegaMinimalAtScales.blowupSet
    {E : Set AmbientSpace} {ω : ℝ} {s t : ℝ≥0∞}
    (hE : IsOmegaMinimalAtScales E ω s) (x : AmbientSpace)
    {r : ℝ} (hr : 0 < r) (ht : 0 < t) (hst : ENNReal.ofReal r * t ≤ s) :
    IsOmegaMinimalAtScales (LiquidDrop.blowupSet E x r) (ω * r) t := by
  let e := blowupHomeomorph x hr
  have heE : e '' LiquidDrop.blowupSet E x r = E := image_blowupSet E x hr
  have hmul : ENNReal.ofReal (r⁻¹ ^ 2) * ENNReal.ofReal (r ^ 2) = 1 := by
    rw [← ENNReal.ofReal_mul (sq_nonneg _)]
    have h : r⁻¹ ^ 2 * r ^ 2 = (1 : ℝ) := by field_simp
    rw [h, ENNReal.ofReal_one]
  refine ⟨mul_nonneg hE.nonneg hr.le, ht,
    nullMeasurableSet_blowupSet hE.nullMeasurable x hr,
    hE.locallyFinite.blowupSet (by norm_num) x hr, ?_⟩
  intro y R hR hRt F hmF hpF hc hs
  have hmG : NullMeasurableSet (e '' F) volume := by
    rw [image_blowupHomeomorph_eq_blowupSet]
    exact nullMeasurableSet_blowupSet hmF _ (inv_pos.mpr hr)
  have hpG : HasLocallyFinitePerimeter (e '' F) := by
    rw [image_blowupHomeomorph_eq_blowupSet]
    exact hpF.blowupSet (by norm_num) _ (inv_pos.mpr hr)
  have hsd : (e '' F) ∆ E = e '' (F ∆ LiquidDrop.blowupSet E x r) := by
    rw [image_symmDiff e.injective, heE]
  have hcG : IsCompact (closure ((e '' F) ∆ E)) := by
    rw [hsd, ← e.image_closure]
    exact hc.image e.continuous
  have hsG : closure ((e '' F) ∆ E) ⊆ ball (x + r • y) (r * R) := by
    rw [hsd, ← e.image_closure, ← image_ball_blowupHomeomorph x y hr R]
    exact image_mono hs
  have hscale : ENNReal.ofReal (r * R) ≤ s := by
    rw [ENNReal.ofReal_mul hr.le]
    exact (mul_le_mul' le_rfl hRt).trans hst
  have heq (G : Set AmbientSpace) :
      perimeterIn (e '' G) (ball (x + r • y) (r * R)) =
        ENNReal.ofReal (r ^ 2) * perimeterIn G (ball y R) := by
    rw [← image_ball_blowupHomeomorph x y hr R]
    exact perimeterIn_translate_pos_smul (by norm_num) G (ball y R) x hr
  have hv : volume (E ∆ (e '' F)) =
      ENNReal.ofReal (r ^ 3) * volume (LiquidDrop.blowupSet E x r ∆ F) := by
    have he : e '' (LiquidDrop.blowupSet E x r ∆ F) = E ∆ (e '' F) := by
      rw [image_symmDiff e.injective, heE]
    rw [← he]
    exact volume_image_blowupHomeomorph _ x hr
  have hcomp := hE.comparison (x + r • y) (r * R) (mul_pos hr hR) hscale
    (e '' F) hmG hpG hcG hsG
  have hperE := heq (LiquidDrop.blowupSet E x r)
  rw [heE] at hperE
  rw [hperE, heq F, hv] at hcomp
  have h := mul_le_mul' (le_refl (ENNReal.ofReal (r⁻¹ ^ 2))) hcomp
  rw [← mul_assoc, hmul, one_mul, mul_add, ← mul_assoc, hmul, one_mul] at h
  have hcoeff : ENNReal.ofReal (r⁻¹ ^ 2) *
      (ENNReal.ofReal ω * (ENNReal.ofReal (r ^ 3) * volume (LiquidDrop.blowupSet E x r ∆ F))) =
      ENNReal.ofReal (ω * r) * volume (LiquidDrop.blowupSet E x r ∆ F) := by
    rw [← mul_assoc, ← mul_assoc, ← ENNReal.ofReal_mul (sq_nonneg _),
      ← ENNReal.ofReal_mul (mul_nonneg (sq_nonneg _) hE.nonneg)]
    congr 2
    field_simp
  rwa [hcoeff] at h

/-- A unit-scale ω-minimizer blows up to an ωr-minimizer at scale 1/r. -/
theorem IsOmegaMinimal.blowupSet {E : Set AmbientSpace} {ω : ℝ}
    (hE : IsOmegaMinimal E ω) (x : AmbientSpace) {r : ℝ} (hr : 0 < r) :
    IsOmegaMinimalAtScales (LiquidDrop.blowupSet E x r) (ω * r) (ENNReal.ofReal r⁻¹) := by
  apply IsOmegaMinimalAtScales.blowupSet hE x hr
    (ENNReal.ofReal_pos.mpr (inv_pos.mpr hr))
  rw [← ENNReal.ofReal_mul hr.le, mul_inv_cancel₀ hr.ne', ENNReal.ofReal_one]

/-- Local zero-error minimality is preserved by every positive blow-up. -/
theorem IsLocallyPerimeterMinimizing.blowupSet {E : Set AmbientSpace}
    (hE : IsLocallyPerimeterMinimizing E) (x : AmbientSpace) {r : ℝ} (hr : 0 < r) :
    IsLocallyPerimeterMinimizing (LiquidDrop.blowupSet E x r) := by
  rw [isLocallyPerimeterMinimizing_iff] at hE ⊢
  simpa only [zero_mul] using IsOmegaMinimalAtScales.blowupSet hE x hr
    (by simp : (0 : ℝ≥0∞) < ∞) le_top

end LiquidDrop

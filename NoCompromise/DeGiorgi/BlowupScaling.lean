import NoCompromise.Sobolev.RelativeScaling

/-!
# Translation and dilation of perimeter blow-ups

The blow-up set is the actual preimage under `y ↦ x + r • y`. Volume and
perimeter identities follow from the already proved translation and dilation
identities, so compactness arguments can use the original variation definition.
-/

noncomputable section
open MeasureTheory Set Filter Metric
open scoped Topology ENNReal
namespace LiquidDrop

/-- The set seen from `x` at scale `r`. Positive scales are required by the theorems. -/
def blowupSet {n : ℕ} (E : Set (EuclideanSpace ℝ (Fin n)))
    (x : EuclideanSpace ℝ (Fin n)) (r : ℝ) : Set (EuclideanSpace ℝ (Fin n)) :=
  (fun y => x + r • y) ⁻¹' E

lemma image_blowupSet {n : ℕ} (E : Set (EuclideanSpace ℝ (Fin n)))
    (x : EuclideanSpace ℝ (Fin n)) {r : ℝ} (hr : 0 < r) :
    (fun y => x + r • y) '' blowupSet E x r = E := by
  apply image_preimage_eq
  intro y
  refine ⟨r⁻¹ • (y - x), ?_⟩
  simp [smul_smul, hr.ne']

lemma nullMeasurableSet_blowupSet {n : ℕ} {E : Set (EuclideanSpace ℝ (Fin n))}
    (hE : NullMeasurableSet E volume) (x : EuclideanSpace ℝ (Fin n))
    {r : ℝ} (hr : 0 < r) : NullMeasurableSet (blowupSet E x r) volume :=
  (hE.preimage (measurePreserving_add_left volume x).quasiMeasurePreserving).preimage
    (Measure.quasiMeasurePreserving_smul volume hr.ne')

lemma image_ball_translate_pos_smul {n : ℕ} (x : EuclideanSpace ℝ (Fin n))
    {r : ℝ} (hr : 0 < r) (R : ℝ) :
    (fun y => x + r • y) '' ball 0 R = ball x (r * R) := by
  rw [← image_image (fun y => x + y) (fun y => r • y), Metric.smul_image_ball hr.ne']
  simp only [smul_zero, Real.norm_eq_abs, abs_of_pos hr]
  have h := (IsometryEquiv.addLeft x).image_ball 0 (r * R)
  change (fun y => x + y) '' ball 0 (r * R) = ball (x + 0) (r * R) at h
  simpa only [add_zero] using h

lemma perimeterIn_translate_pos_smul {n : ℕ} (hn : 0 < n)
    (E U : Set (EuclideanSpace ℝ (Fin n))) (x : EuclideanSpace ℝ (Fin n))
    {r : ℝ} (hr : 0 < r) :
    perimeterIn ((fun y => x + r • y) '' E) ((fun y => x + r • y) '' U) =
      ENNReal.ofReal (r ^ (n - 1)) * perimeterIn E U := by
  rw [← image_image (fun y => x + y) (fun y => r • y),
    ← image_image (fun y => x + y) (fun y => r • y), perimeterIn_translate]
  exact perimeterIn_smul hn E U hr

/-- Perimeter of a blow-up on a centered ball, before dividing by the scale. -/
theorem perimeterIn_blowupSet_ball_mul {n : ℕ} (hn : 0 < n)
    (E : Set (EuclideanSpace ℝ (Fin n))) (x : EuclideanSpace ℝ (Fin n))
    {r : ℝ} (hr : 0 < r) (R : ℝ) :
    ENNReal.ofReal (r ^ (n - 1)) * perimeterIn (blowupSet E x r) (ball 0 R) =
      perimeterIn E (ball x (r * R)) := by
  rw [← perimeterIn_translate_pos_smul hn _ _ x hr, image_blowupSet E x hr,
    image_ball_translate_pos_smul x hr R]

/-- Exact normalized perimeter of a blow-up on a centered ball. -/
theorem perimeterIn_blowupSet_ball {n : ℕ} (hn : 0 < n)
    (E : Set (EuclideanSpace ℝ (Fin n))) (x : EuclideanSpace ℝ (Fin n))
    {r : ℝ} (hr : 0 < r) (R : ℝ) :
    perimeterIn (blowupSet E x r) (ball 0 R) =
      ENNReal.ofReal ((r⁻¹) ^ (n - 1)) * perimeterIn E (ball x (r * R)) := by
  rw [← perimeterIn_blowupSet_ball_mul hn E x hr R, ← mul_assoc,
    ← ENNReal.ofReal_mul (by positivity : 0 ≤ (r⁻¹) ^ (n - 1)), ← mul_pow,
    inv_mul_cancel₀ hr.ne', one_pow, ENNReal.ofReal_one, one_mul]

/-- Exact normalized volume of a blow-up in a centered ball. -/
theorem volume_blowupSet_inter_ball {n : ℕ}
    (E : Set (EuclideanSpace ℝ (Fin n))) (x : EuclideanSpace ℝ (Fin n))
    {r : ℝ} (hr : 0 < r) (R : ℝ) :
    volume (blowupSet E x r ∩ ball 0 R) =
      ENNReal.ofReal ((r⁻¹) ^ n) * volume (E ∩ ball x (r * R)) := by
  have hinj : Function.Injective (fun y : EuclideanSpace ℝ (Fin n) => x + r • y) := by
    intro a b hab
    exact (smul_right_injective _ hr.ne') (add_left_cancel hab)
  have heq : volume (E ∩ ball x (r * R)) =
      ENNReal.ofReal (r ^ n) * volume (blowupSet E x r ∩ ball 0 R) := by
    calc
      _ = volume ((fun y => x + r • y) '' (blowupSet E x r ∩ ball 0 R)) := by
        rw [image_inter hinj, image_blowupSet E x hr, image_ball_translate_pos_smul x hr R]
      _ = _ := by
        rw [← image_image (fun y => x + y) (fun y => r • y),
          volume_image_add_left, volume_image_pos_smul _ hr]
  rw [heq, ← mul_assoc, ← ENNReal.ofReal_mul (by positivity : 0 ≤ (r⁻¹) ^ n),
    ← mul_pow, inv_mul_cancel₀ hr.ne', one_pow, ENNReal.ofReal_one, one_mul]

/-- Perimeter scaling on arbitrary regions, including infinite perimeter. -/
theorem perimeterIn_blowupSet {n : ℕ} (hn : 0 < n)
    (E U : Set (EuclideanSpace ℝ (Fin n))) (x : EuclideanSpace ℝ (Fin n))
    {r : ℝ} (hr : 0 < r) :
    perimeterIn (blowupSet E x r) U = ENNReal.ofReal ((r⁻¹) ^ (n - 1)) *
      perimeterIn E ((fun y => x + r • y) '' U) := by
  have hs := perimeterIn_translate_pos_smul hn (blowupSet E x r) U x hr
  rw [image_blowupSet E x hr] at hs
  rw [hs, ← mul_assoc, ← ENNReal.ofReal_mul (by positivity : 0 ≤ (r⁻¹) ^ (n - 1)),
    ← mul_pow, inv_mul_cancel₀ hr.ne', one_pow, ENNReal.ofReal_one, one_mul]

/-- A positive-scale blow-up preserves local finite perimeter. -/
theorem HasLocallyFinitePerimeter.blowupSet {n : ℕ} (hn : 0 < n)
    {E : Set (EuclideanSpace ℝ (Fin n))} (hE : HasLocallyFinitePerimeter E)
    (x : EuclideanSpace ℝ (Fin n)) {r : ℝ} (hr : 0 < r) :
    HasLocallyFinitePerimeter (blowupSet E x r) := by
  let e : EuclideanSpace ℝ (Fin n) ≃ₜ EuclideanSpace ℝ (Fin n) :=
    (Homeomorph.smulOfNeZero r hr.ne').trans (Homeomorph.addLeft x)
  have he : ⇑e = (fun y => x + r • y) := rfl
  intro U hU hcU
  have hc : IsCompact (e '' closure U) := hcU.image e.continuous
  have hc' : IsCompact (closure (e '' U)) := hc.of_isClosed_subset isClosed_closure
    (closure_minimal (image_mono subset_closure) hc.isClosed)
  have hp := hE (e '' U) (e.isOpenMap U hU) hc'
  rw [he] at hp
  rw [perimeterIn_blowupSet hn E U x hr]
  exact ENNReal.mul_lt_top ENNReal.ofReal_lt_top hp

end LiquidDrop

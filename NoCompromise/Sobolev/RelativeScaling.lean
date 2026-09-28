import NoCompromise.Sobolev.Relative
import NoCompromise.Sobolev.LipschitzDomains

/-!
# Scale invariance of relative isoperimetry

Translation preserves the domain constant. Dilation by `r > 0` multiplies volume by
`r^n` and perimeter by `r^(n-1)`, so it preserves the constant whenever the volume
exponent is `(n-1)/n`. All estimates allow infinite relative perimeter and require
only Lebesgue measurability of the competing set.
-/

noncomputable section

open MeasureTheory Filter Metric Set
open scoped ENNReal Topology Pointwise

namespace LiquidDrop

/-- A relative isoperimetric inequality with an explicitly fixed domain constant. -/
def HasRelativeIsoperimetricInequality {n : ℕ}
    (D : Set (EuclideanSpace ℝ (Fin n))) (q C : ℝ) : Prop :=
  ∀ E : Set (EuclideanSpace ℝ (Fin n)), NullMeasurableSet E volume →
    (min (volume (E ∩ D)) (volume (D \ E))) ^ q ≤ ENNReal.ofReal C * perimeterIn E D

/-- Translation preserves volume even for nonmeasurable sets. -/
lemma volume_image_add_left {n : ℕ} (a : EuclideanSpace ℝ (Fin n))
    (S : Set (EuclideanSpace ℝ (Fin n))) : volume ((fun x => a + x) '' S) = volume S := by
  rw [image_add_left, measure_preimage_add]

/-- A positive dilation scales Euclidean volume by the dimension power. -/
lemma volume_image_pos_smul {n : ℕ} (S : Set (EuclideanSpace ℝ (Fin n)))
    {r : ℝ} (hr : 0 < r) :
    volume ((fun x => r • x) '' S) = ENNReal.ofReal (r ^ n) * volume S := by
  change volume (r • S) = _
  simpa only [finrank_euclideanSpace, Fintype.card_fin] using
    Measure.addHaar_smul_of_nonneg volume hr.le S

/-- A relative isoperimetric inequality transfers to every translate with the same constant. -/
theorem HasRelativeIsoperimetricInequality.translate {n : ℕ}
    {D : Set (EuclideanSpace ℝ (Fin n))} {q C : ℝ}
    (hD : HasRelativeIsoperimetricInequality D q C) (a : EuclideanSpace ℝ (Fin n)) :
    HasRelativeIsoperimetricInequality ((fun x => a + x) '' D) q C := by
  intro E hE
  let F := (fun x => a + x) ⁻¹' E
  have hF : NullMeasurableSet F volume :=
    hE.preimage (measurePreserving_add_left volume a).quasiMeasurePreserving
  have hinj : Function.Injective (fun x : EuclideanSpace ℝ (Fin n) => a + x) :=
    fun _ _ h => add_left_cancel h
  have hsurj : Function.Surjective (fun x : EuclideanSpace ℝ (Fin n) => a + x) :=
    fun x => ⟨-a + x, by simp⟩
  have hEF : (fun x => a + x) '' F = E := image_preimage_eq E hsurj
  rw [← hEF, ← image_inter hinj, ← image_sdiff hinj,
    volume_image_add_left, volume_image_add_left, perimeterIn_translate]
  exact hD F hF

/-- Dilation preserves the relative isoperimetric constant when the volume exponent has
exactly perimeter homogeneity. No finiteness assumption on volume or perimeter is needed. -/
theorem HasRelativeIsoperimetricInequality.smul {n : ℕ} (hn : 0 < n)
    {D : Set (EuclideanSpace ℝ (Fin n))} {q C : ℝ}
    (hD : HasRelativeIsoperimetricInequality D q C) (hq : 0 ≤ q)
    (hbalance : (n : ℝ) * q = ((n - 1 : ℕ) : ℝ)) {r : ℝ} (hr : 0 < r) :
    HasRelativeIsoperimetricInequality ((fun x => r • x) '' D) q C := by
  intro E hE
  let F := (fun x => r • x) ⁻¹' E
  have hF : NullMeasurableSet F volume :=
    hE.preimage (Measure.quasiMeasurePreserving_smul volume hr.ne')
  have hinj : Function.Injective (fun x : EuclideanSpace ℝ (Fin n) => r • x) :=
    smul_right_injective _ hr.ne'
  have hsurj : Function.Surjective (fun x : EuclideanSpace ℝ (Fin n) => r • x) :=
    (IsUnit.smul_bijective (isUnit_iff_ne_zero.mpr hr.ne')).surjective
  have hEF : (fun x => r • x) '' F = E := image_preimage_eq E hsurj
  have hscale : ENNReal.ofReal (r ^ n) ^ q = ENNReal.ofReal (r ^ (n - 1)) := by
    rw [ENNReal.ofReal_rpow_of_pos (pow_pos hr n),
      ← Real.rpow_natCast_mul hr.le n q, hbalance, Real.rpow_natCast]
  rw [← hEF, ← image_inter hinj, ← image_sdiff hinj,
    volume_image_pos_smul _ hr, volume_image_pos_smul _ hr, ← mul_min,
    ENNReal.mul_rpow_of_nonneg _ _ hq, hscale, perimeterIn_smul hn _ _ hr]
  calc
    _ ≤ ENNReal.ofReal (r ^ (n - 1)) * (ENNReal.ofReal C * perimeterIn F D) :=
      mul_le_mul_of_nonneg_left (hD F hF) (by positivity)
    _ = _ := by ac_rfl

/-- Simultaneous positive dilation and translation preserve the same relative constant. -/
theorem HasRelativeIsoperimetricInequality.translate_smul {n : ℕ} (hn : 0 < n)
    {D : Set (EuclideanSpace ℝ (Fin n))} {q C : ℝ}
    (hD : HasRelativeIsoperimetricInequality D q C) (hq : 0 ≤ q)
    (hbalance : (n : ℝ) * q = ((n - 1 : ℕ) : ℝ))
    (a : EuclideanSpace ℝ (Fin n)) {r : ℝ} (hr : 0 < r) :
    HasRelativeIsoperimetricInequality ((fun x => a + r • x) '' D) q C := by
  simpa only [image_image] using (hD.smul hn hq hbalance hr).translate a

/-- The scale-invariant three-dimensional exponent is 2/3. -/
theorem HasRelativeIsoperimetricInequality.translate_smul_three
    {D : Set (EuclideanSpace ℝ (Fin 3))} {C : ℝ}
    (hD : HasRelativeIsoperimetricInequality D (2 / 3) C)
    (a : EuclideanSpace ℝ (Fin 3)) {r : ℝ} (hr : 0 < r) :
    HasRelativeIsoperimetricInequality ((fun x => a + r • x) '' D) (2 / 3) C :=
  hD.translate_smul (by norm_num) (by norm_num) (by norm_num) a hr

/-- The scale-invariant planar exponent is 1/2. -/
theorem HasRelativeIsoperimetricInequality.translate_smul_two
    {D : Set (EuclideanSpace ℝ (Fin 2))} {C : ℝ}
    (hD : HasRelativeIsoperimetricInequality D (1 / 2) C)
    (a : EuclideanSpace ℝ (Fin 2)) {r : ℝ} (hr : 0 < r) :
    HasRelativeIsoperimetricInequality ((fun x => a + r • x) '' D) (1 / 2) C :=
  hD.translate_smul (by norm_num) (by norm_num) (by norm_num) a hr

/-- One three-dimensional Lipschitz reference domain supplies a uniform constant for
all of its translates and positive dilates. The radius does not occur in the constant. -/
theorem relative_isoperimetric_three_similar_domains
    {D : Set (EuclideanSpace ℝ (Fin 3))} (hD : IsOpen D) (hcD : IsPreconnected D)
    (hbD : Bornology.IsBounded D) (hL : HasLipschitzBoundary D) :
    ∃ C : ℝ, 0 < C ∧ ∀ (a : EuclideanSpace ℝ (Fin 3)) (r : ℝ), 0 < r →
      HasRelativeIsoperimetricInequality ((fun x => a + r • x) '' D) (2 / 3) C := by
  obtain ⟨C, hC, hI⟩ := relative_isoperimetric_three hD hcD hbD hL
  exact ⟨C, hC, fun a r hr =>
    (show HasRelativeIsoperimetricInequality D (2 / 3) C from hI).translate_smul_three a hr⟩

/-- A planar Lipschitz reference domain supplies one constant for all positive dilates
and translates, again with no finiteness assumption on relative perimeter. -/
theorem relative_isoperimetric_two_similar_domains
    {D : Set (EuclideanSpace ℝ (Fin 2))} (hD : IsOpen D) (hcD : IsPreconnected D)
    (hbD : Bornology.IsBounded D) (hL : HasLipschitzBoundary D) :
    ∃ C : ℝ, 0 < C ∧ ∀ (a : EuclideanSpace ℝ (Fin 2)) (r : ℝ), 0 < r →
      HasRelativeIsoperimetricInequality ((fun x => a + r • x) '' D) (1 / 2) C := by
  obtain ⟨C, hC, hI⟩ := relative_isoperimetric_two hD hcD hbD hL
  exact ⟨C, hC, fun a r hr =>
    (show HasRelativeIsoperimetricInequality D (1 / 2) C from hI).translate_smul_two a hr⟩

/-- The affine image of the unit ball under a positive dilation is the ball of that radius. -/
lemma image_unitBall_translate_pos_smul {n : ℕ} (a : EuclideanSpace ℝ (Fin n))
    {r : ℝ} (hr : 0 < r) :
    (fun x => a + r • x) '' ball (0 : EuclideanSpace ℝ (Fin n)) 1 = ball a r := by
  rw [← image_image (fun x => a + x) (fun x => r • x), Metric.smul_image_ball hr.ne']
  simp only [smul_zero, Real.norm_eq_abs, abs_of_pos hr, mul_one]
  have h := (IsometryEquiv.addLeft a).image_ball 0 r
  change (fun x => a + x) '' ball 0 r = ball (a + 0) r at h
  simpa only [add_zero] using h

/-- Blueprint `prop:rel-iso-ball`: one absolute constant works for all three-dimensional
balls of positive radius, with no global or relative finiteness premise on perimeter. -/
theorem relative_isoperimetric_ball_three :
    ∃ C : ℝ, 0 < C ∧ ∀ (a : EuclideanSpace ℝ (Fin 3)) (r : ℝ), 0 < r →
      ∀ E : Set (EuclideanSpace ℝ (Fin 3)), NullMeasurableSet E volume →
        (min (volume (E ∩ ball a r)) (volume (ball a r \ E))) ^ (2 / 3 : ℝ) ≤
          ENNReal.ofReal C * perimeterIn E (ball a r) := by
  obtain ⟨C, hC, hI⟩ := relative_isoperimetric_three_similar_domains
    (D := ball (0 : EuclideanSpace ℝ (Fin 3)) 1) isOpen_ball
    (convex_ball _ _).isPreconnected isBounded_ball (hasLipschitzBoundary_ball 0 zero_lt_one)
  refine ⟨C, hC, fun a r hr E hE => ?_⟩
  have h := hI a r hr
  rw [image_unitBall_translate_pos_smul a hr] at h
  exact h E hE

/-- Blueprint `prop:rel-iso-disk`: one absolute constant works for all planar disks of
positive radius, with relative perimeter taken inside exactly the same disk. -/
theorem relative_isoperimetric_disk_two :
    ∃ C : ℝ, 0 < C ∧ ∀ (a : EuclideanSpace ℝ (Fin 2)) (r : ℝ), 0 < r →
      ∀ E : Set (EuclideanSpace ℝ (Fin 2)), NullMeasurableSet E volume →
        (min (volume (E ∩ ball a r)) (volume (ball a r \ E))) ^ (1 / 2 : ℝ) ≤
          ENNReal.ofReal C * perimeterIn E (ball a r) := by
  obtain ⟨C, hC, hI⟩ := relative_isoperimetric_two_similar_domains
    (D := ball (0 : EuclideanSpace ℝ (Fin 2)) 1) isOpen_ball
    (convex_ball _ _).isPreconnected isBounded_ball (hasLipschitzBoundary_ball 0 zero_lt_one)
  refine ⟨C, hC, fun a r hr E hE => ?_⟩
  have h := hI a r hr
  rw [image_unitBall_translate_pos_smul a hr] at h
  exact h E hE

end LiquidDrop

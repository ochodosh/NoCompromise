module

public import NoCompromise.Value.Defs
public import Mathlib.Analysis.Convex.Continuous

@[expose] public section

/-!
# Normalised concavity and continuity of the value function

Blueprint `lem:m-concave` and `prop:m-continuous`. Rescaling a volume-`V` set
to unit volume identifies `V^{-2/3} m(V)` with an infimum of functions affine
in `V`; this infimum is concave, hence continuous on `(0, ∞)`.
-/

noncomputable section
open MeasureTheory Set
open scoped ENNReal
namespace LiquidDrop

/-- The normalised value function `V ↦ V^{-2/3} m(V)` of blueprint `eq:m-normalised`. -/
def normalisedValue (V : ℝ) : ℝ≥0∞ :=
  ⨅ (U : Set AmbientSpace) (_ : NullMeasurableSet U volume) (_ : volume U = 1),
    perimeter U + ENNReal.ofReal V * coulombEnergy U

lemma normalisedValue_le {V : ℝ} {U : Set AmbientSpace}
    (hU : NullMeasurableSet U volume) (hvol : volume U = 1) :
    normalisedValue V ≤ perimeter U + ENNReal.ofReal V * coulombEnergy U :=
  iInf_le_of_le U (iInf_le_of_le hU (iInf_le_of_le hvol le_rfl))

/-- Energy of the dilate of a set by `V^{1/3}`. -/
lemma energy_smul_cbrt {V : ℝ} (hV : 0 < V) {U : Set AmbientSpace}
    (hU : NullMeasurableSet U volume) :
    energy ((fun x => V ^ ((1 : ℝ) / 3) • x) '' U) =
      ENNReal.ofReal (V ^ ((2 : ℝ) / 3)) *
        (perimeter U + ENNReal.ofReal V * coulombEnergy U) := by
  have hr : 0 < V ^ ((1 : ℝ) / 3) := Real.rpow_pos_of_pos hV _
  have hr2 : (V ^ ((1 : ℝ) / 3)) ^ 2 = V ^ ((2 : ℝ) / 3) := by
    rw [← Real.rpow_natCast, ← Real.rpow_mul hV.le]; norm_num
  have hr3 : (V ^ ((1 : ℝ) / 3)) ^ 3 = V := by
    rw [← Real.rpow_natCast, ← Real.rpow_mul hV.le]; norm_num
  have hr5 : (V ^ ((1 : ℝ) / 3)) ^ 5 = V ^ ((2 : ℝ) / 3) * V := by
    rw [← hr2]; nth_rw 3 [← hr3]; ring
  rw [energy_smul hU hr, hr2, hr5,
    ENNReal.ofReal_mul (Real.rpow_nonneg hV.le _), mul_add, mul_assoc]

/-- Blueprint `lem:m-concave`, the identity in `eq:m-normalised`. -/
theorem valueFunction_eq_normalisedValue {V : ℝ} (hV : 0 < V) :
    valueFunction V = ENNReal.ofReal (V ^ ((2 : ℝ) / 3)) * normalisedValue V := by
  set r : ℝ := V ^ ((1 : ℝ) / 3) with hr_def
  have hr : 0 < r := Real.rpow_pos_of_pos hV _
  have hr3 : r ^ 3 = V := by
    rw [hr_def, ← Real.rpow_natCast, ← Real.rpow_mul hV.le]; norm_num
  have hc0 : ENNReal.ofReal (V ^ ((2 : ℝ) / 3)) ≠ 0 :=
    (ENNReal.ofReal_pos.mpr (Real.rpow_pos_of_pos hV _)).ne'
  apply le_antisymm
  · rw [normalisedValue, ENNReal.mul_iInf_of_ne hc0 ENNReal.ofReal_ne_top]
    refine le_iInf fun U => ?_
    rw [ENNReal.mul_iInf_of_ne hc0 ENNReal.ofReal_ne_top]
    refine le_iInf fun hU => ?_
    rw [ENNReal.mul_iInf_of_ne hc0 ENNReal.ofReal_ne_top]
    refine le_iInf fun hvol => ?_
    rw [← energy_smul_cbrt hV hU]
    have hΦ : Differentiable ℝ (fun x : AmbientSpace => r • x) := by fun_prop
    refine valueFunction_le
      (nullMeasurableSet_image_of_differentiable hΦ (smul_right_injective _ hr.ne') hU) ?_
    rw [volume_image_smul U hr, hvol, mul_one, hr3]
  · refine le_iInf fun E => le_iInf fun hE => le_iInf fun hvol => ?_
    set U : Set AmbientSpace := (fun x => r⁻¹ • x) '' E with hU_def
    have hri : 0 < r⁻¹ := inv_pos.mpr hr
    have hΦ : Differentiable ℝ (fun x : AmbientSpace => r⁻¹ • x) := by fun_prop
    have hU : NullMeasurableSet U volume :=
      nullMeasurableSet_image_of_differentiable hΦ (smul_right_injective _ hri.ne') hE
    have hUvol : volume U = 1 := by
      rw [hU_def, volume_image_smul E hri, hvol, ← ENNReal.ofReal_mul (by positivity),
        inv_pow, hr3, inv_mul_cancel₀ hV.ne', ENNReal.ofReal_one]
    have hEU : (fun x => r • x) '' U = E := by
      rw [hU_def, image_image]
      simp only [smul_smul, mul_inv_cancel₀ hr.ne', one_smul, image_id']
    rw [← hEU, energy_smul_cbrt hV hU]
    exact mul_le_mul_of_nonneg_left (normalisedValue_le hU hUvol) (by positivity)

/-- Blueprint `lem:m-concave`: finiteness. -/
theorem normalisedValue_lt_top {V : ℝ} (hV : 0 < V) : normalisedValue V < ∞ := by
  have h := valueFunction_lt_top hV
  rw [valueFunction_eq_normalisedValue hV] at h
  have hc0 : ENNReal.ofReal (V ^ ((2 : ℝ) / 3)) ≠ 0 :=
    (ENNReal.ofReal_pos.mpr (Real.rpow_pos_of_pos hV _)).ne'
  exact (ENNReal.mul_lt_top_iff.mp h).elim (fun h => h.2)
    (fun h => h.elim (fun h => absurd h hc0) fun h => h ▸ ENNReal.zero_lt_top)

/-- The affine-infimum inequality underlying concavity, in extended reals. -/
lemma normalisedValue_concave_ennreal {x y a b : ℝ} (ha : 0 ≤ a) (hb : 0 ≤ b)
    (hab : a + b = 1) (hx : 0 ≤ x) (hy : 0 ≤ y) :
    ENNReal.ofReal a * normalisedValue x + ENNReal.ofReal b * normalisedValue y ≤
      normalisedValue (a * x + b * y) := by
  refine le_iInf fun U => le_iInf fun hU => le_iInf fun hvol => ?_
  calc
    _ ≤ ENNReal.ofReal a * (perimeter U + ENNReal.ofReal x * coulombEnergy U) +
        ENNReal.ofReal b * (perimeter U + ENNReal.ofReal y * coulombEnergy U) :=
      add_le_add (mul_le_mul_of_nonneg_left (normalisedValue_le hU hvol) (by positivity))
        (mul_le_mul_of_nonneg_left (normalisedValue_le hU hvol) (by positivity))
    _ = (ENNReal.ofReal a + ENNReal.ofReal b) * perimeter U +
        (ENNReal.ofReal a * ENNReal.ofReal x + ENNReal.ofReal b * ENNReal.ofReal y) *
          coulombEnergy U := by ring
    _ = _ := by
      rw [← ENNReal.ofReal_add ha hb, hab, ENNReal.ofReal_one, one_mul,
        ← ENNReal.ofReal_mul ha, ← ENNReal.ofReal_mul hb,
        ← ENNReal.ofReal_add (mul_nonneg ha hx) (mul_nonneg hb hy)]

/-- Blueprint `lem:m-concave`: concavity on `(0, ∞)`. -/
theorem normalisedValue_concaveOn :
    ConcaveOn ℝ (Set.Ioi 0) (fun V => (normalisedValue V).toReal) := by
  refine ⟨convex_Ioi 0, fun x hx y hy a b ha hb hab => ?_⟩
  have hxy : 0 < a • x + b • y := convex_Ioi 0 hx hy ha hb hab
  simp only [smul_eq_mul] at hxy ⊢
  have h := ENNReal.toReal_mono (normalisedValue_lt_top hxy).ne
    (normalisedValue_concave_ennreal ha hb hab (le_of_lt hx) (le_of_lt hy))
  rwa [ENNReal.toReal_add (ENNReal.mul_ne_top ENNReal.ofReal_ne_top
      (normalisedValue_lt_top hx).ne)
      (ENNReal.mul_ne_top ENNReal.ofReal_ne_top (normalisedValue_lt_top hy).ne),
    ENNReal.toReal_mul, ENNReal.toReal_mul, ENNReal.toReal_ofReal ha,
    ENNReal.toReal_ofReal hb] at h

/-- Blueprint `prop:m-continuous`. -/
theorem valueFunction_continuousOn :
    ContinuousOn (fun V => (valueFunction V).toReal) (Set.Ioi 0) := by
  have hcont : ContinuousOn (fun V : ℝ => V ^ ((2 : ℝ) / 3) * (normalisedValue V).toReal)
      (Set.Ioi 0) := by
    refine ContinuousOn.mul ?_ (normalisedValue_concaveOn.continuousOn isOpen_Ioi)
    exact fun V hV => (Real.continuousAt_rpow_const V _ (Or.inl (ne_of_gt hV))).continuousWithinAt
  refine hcont.congr fun V hV => ?_
  simp only
  rw [valueFunction_eq_normalisedValue hV, ENNReal.toReal_mul,
    ENNReal.toReal_ofReal (Real.rpow_nonneg (le_of_lt hV) _)]

end LiquidDrop

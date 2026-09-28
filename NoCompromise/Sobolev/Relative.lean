import NoCompromise.Sobolev.Poincare
import Mathlib.MeasureTheory.Function.LpSeminorm.Indicator

/-!
# Relative isoperimetry on fixed Lipschitz domains

The estimates use the smaller of the volume inside the set and the volume outside it,
both restricted to the specified domain. The constant depends on that domain. Uniform
constants for all dilates of a reference cube, ball, or disk require a separate scaling
argument; no radius or diameter factor is included in these fixed-domain statements.
-/

noncomputable section

open MeasureTheory Filter Metric Set
open scoped ENNReal Topology

namespace LiquidDrop

set_option maxSynthPendingDepth 8

/-- Whichever side of an indicator is smaller, its volume is controlled by the Lᵖ distance
from any constant. No formula for that constant, and no finiteness of the measure, is needed. -/
theorem min_measure_rpow_le_two_mul_eLpNorm_indicator_sub_const
    {α : Type*} [MeasurableSpace α] {μ : Measure α} {E : Set α}
    (hE : NullMeasurableSet E μ) {p : ℝ≥0∞} (hp : p ≠ 0) (hp_top : p ≠ ∞) (c : ℝ) :
    (min (μ E) (μ Eᶜ)) ^ (1 / p.toReal) ≤
      2 * eLpNorm (fun x => E.indicator (fun _ => (1 : ℝ)) x - c) p μ := by
  classical
  have half_norm : ‖(1 / 2 : ℝ)‖ₑ = (1 / 2 : ℝ≥0∞) := by
    rw [← ofReal_norm]
    norm_num [Real.norm_eq_abs, ENNReal.ofReal_div_of_pos]
  have hpow : 0 ≤ 1 / p.toReal := by positivity
  by_cases hc : c ≤ 1 / 2
  · have hm : eLpNorm (E.indicator (fun _ => (1 / 2 : ℝ))) p μ ≤
        eLpNorm (fun x => E.indicator (fun _ => (1 : ℝ)) x - c) p μ := by
      apply eLpNorm_mono (aestronglyMeasurable_const.indicator₀ hE)
      intro x
      by_cases hx : x ∈ E
      · simp only [indicator_of_mem hx, Real.norm_eq_abs]
        rw [abs_of_nonneg (by norm_num : (0 : ℝ) ≤ 1 / 2), abs_of_nonneg (by linarith)]
        linarith
      · simp only [indicator_of_notMem hx, norm_zero]
        exact norm_nonneg _
    rw [eLpNorm_indicator_const₀ hE hp hp_top, half_norm] at hm
    calc
      _ ≤ (μ E) ^ (1 / p.toReal) := ENNReal.rpow_le_rpow (min_le_left _ _) hpow
      _ = 2 * ((1 / 2) * (μ E) ^ (1 / p.toReal)) := by
        simp only [one_div]
        rw [← mul_assoc, ENNReal.mul_inv_cancel (by norm_num) (by finiteness), one_mul]
      _ ≤ _ := mul_le_mul_of_nonneg_left hm (by positivity)
  · have hm : eLpNorm (Eᶜ.indicator (fun _ => (1 / 2 : ℝ))) p μ ≤
        eLpNorm (fun x => E.indicator (fun _ => (1 : ℝ)) x - c) p μ := by
      apply eLpNorm_mono (aestronglyMeasurable_const.indicator₀ hE.compl)
      intro x
      by_cases hx : x ∈ E
      · simp only [mem_compl_iff, not_not, hx, indicator_of_notMem, norm_zero]
        exact norm_nonneg _
      · simp only [indicator_of_mem (show x ∈ Eᶜ from hx), indicator_of_notMem hx,
          zero_sub, norm_neg, Real.norm_eq_abs]
        rw [abs_of_nonneg (by norm_num : (0 : ℝ) ≤ 1 / 2), abs_of_nonneg (by linarith)]
        linarith
    rw [eLpNorm_indicator_const₀ hE.compl hp hp_top, half_norm] at hm
    calc
      _ ≤ (μ Eᶜ) ^ (1 / p.toReal) := ENNReal.rpow_le_rpow (min_le_right _ _) hpow
      _ = 2 * ((1 / 2) * (μ Eᶜ) ^ (1 / p.toReal)) := by
        simp only [one_div]
        rw [← mul_assoc, ENNReal.mul_inv_cancel (by norm_num) (by finiteness), one_mul]
      _ ≤ _ := mul_le_mul_of_nonneg_left hm (by positivity)

/-- The indicator argument converts a BV Poincaré estimate into relative isoperimetry.
The conclusion is extended-real valued and therefore includes infinite relative perimeter. -/
theorem relative_isoperimetric_of_bv_poincare {n : ℕ}
    {D : Set (EuclideanSpace ℝ (Fin n))} (hvol : volume D ≠ ∞)
    {p : ℝ≥0∞} (hp : p ≠ 0) (hp_top : p ≠ ∞) {C : ℝ} (hC : 0 < C)
    (hP : ∀ f : EuclideanSpace ℝ (Fin n) → ℝ, IsBVOn f D →
      MemLp (fun x => f x - ⨍ y in D, f y) p (volume.restrict D) ∧
      lpNorm (fun x => f x - ⨍ y in D, f y) p (volume.restrict D) ≤
        C * (variation f D).toReal)
    {E : Set (EuclideanSpace ℝ (Fin n))} (hE : NullMeasurableSet E volume) :
    (min (volume (E ∩ D)) (volume (D \ E))) ^ (1 / p.toReal) ≤
      ENNReal.ofReal (2 * C) * perimeterIn E D := by
  by_cases hper : perimeterIn E D = ∞
  · rw [hper, ENNReal.mul_top (ENNReal.ofReal_ne_zero_iff.mpr (by positivity))]
    exact le_top
  have hE' : NullMeasurableSet E (volume.restrict D) := hE.mono Measure.restrict_le_self
  let f := E.indicator (fun _ => (1 : ℝ))
  have hif : IntegrableOn f D := (integrableOn_const hvol).indicator₀ hE'
  have hf : IsBVOn f D := ⟨hif, lt_top_iff_ne_top.mpr hper⟩
  obtain ⟨hmem, hbound⟩ := hP f hf
  have hnorm : eLpNorm (fun x => f x - ⨍ y in D, f y) p (volume.restrict D) ≤
      ENNReal.ofReal C * perimeterIn E D := by
    rw [← ofReal_lpNorm hmem]
    calc
      _ ≤ ENNReal.ofReal (C * (variation f D).toReal) := ENNReal.ofReal_le_ofReal hbound
      _ = _ := by
        rw [ENNReal.ofReal_mul hC.le, ENNReal.ofReal_toReal hf.2.ne]
        rfl
  have h := min_measure_rpow_le_two_mul_eLpNorm_indicator_sub_const hE' hp hp_top
    (⨍ y in D, f y)
  rw [Measure.restrict_apply₀ hE', Measure.restrict_apply₀ hE'.compl] at h
  have hset : Eᶜ ∩ D = D \ E := by ext x; simp [and_comm]
  rw [hset] at h
  calc
    _ ≤ 2 * eLpNorm (fun x => f x - ⨍ y in D, f y) p (volume.restrict D) := h
    _ ≤ 2 * (ENNReal.ofReal C * perimeterIn E D) := mul_le_mul_of_nonneg_left hnorm (by positivity)
    _ = _ := by rw [ENNReal.ofReal_mul (by norm_num : (0 : ℝ) ≤ 2)]; norm_num [mul_assoc]

/-- Relative isoperimetry in a fixed bounded connected Lipschitz domain in ℝ³.
Only Lebesgue measurability of the set is assumed; infinite relative perimeter is allowed. -/
theorem relative_isoperimetric_three
    {D : Set (EuclideanSpace ℝ (Fin 3))} (hD : IsOpen D) (hcD : IsPreconnected D)
    (hbD : Bornology.IsBounded D) (hL : HasLipschitzBoundary D) :
    ∃ C : ℝ, 0 < C ∧ ∀ E : Set (EuclideanSpace ℝ (Fin 3)),
      NullMeasurableSet E volume →
        (min (volume (E ∩ D)) (volume (D \ E))) ^ (2 / 3 : ℝ) ≤
          ENNReal.ofReal C * perimeterIn E D := by
  obtain ⟨C, hC, hP⟩ := bv_poincare_three hD hcD hbD hL
  refine ⟨2 * C, by positivity, fun E hE => ?_⟩
  have h := relative_isoperimetric_of_bv_poincare hbD.measure_lt_top.ne
    (p := 3 / 2) (by norm_num) (by finiteness) hC (fun f hf => (hP f hf).2) hE
  norm_num only [ENNReal.toReal_div, ENNReal.toReal_ofNat] at h
  exact h

/-- Relative isoperimetry in a fixed bounded connected Lipschitz domain in ℝ².
The exponent is 1/2, and the perimeter is computed only inside that same domain. -/
theorem relative_isoperimetric_two
    {D : Set (EuclideanSpace ℝ (Fin 2))} (hD : IsOpen D) (hcD : IsPreconnected D)
    (hbD : Bornology.IsBounded D) (hL : HasLipschitzBoundary D) :
    ∃ C : ℝ, 0 < C ∧ ∀ E : Set (EuclideanSpace ℝ (Fin 2)),
      NullMeasurableSet E volume →
        (min (volume (E ∩ D)) (volume (D \ E))) ^ (1 / 2 : ℝ) ≤
          ENNReal.ofReal C * perimeterIn E D := by
  obtain ⟨C, hC, hP⟩ := bv_poincare_two hD hcD hbD hL
  refine ⟨2 * C, by positivity, fun E hE => ?_⟩
  have h := relative_isoperimetric_of_bv_poincare hbD.measure_lt_top.ne
    (p := 2) (by norm_num) (by finiteness) hC (fun f hf => (hP f hf).2) hE
  norm_num only [ENNReal.toReal_ofNat] at h
  exact h

end LiquidDrop

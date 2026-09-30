module

public import NoCompromise.Variation.FiniteFreezing
public import NoCompromise.DeGiorgi.AmbientPolar

@[expose] public section

/-!
# Boundary flux error for finite freezing

The partition sum controls the error without a factor depending on the number
of regions. All integrals use the actual locally finite perimeter polar measure.
-/

noncomputable section
open MeasureTheory Set Filter Metric
open scoped Topology ENNReal
namespace LiquidDrop

variable {E : Set AmbientSpace} {μ : Measure AmbientSpace}
  {ν X : AmbientSpace → AmbientSpace} {K A : Set AmbientSpace} {η : ℝ} {N : ℕ}

lemma FiniteFieldFreezing.integrable_weight
    (d : FiniteFieldFreezing X K A η N) (h : IsAmbientOutwardPerimeterPolar E μ ν)
    (j : Fin N) : Integrable (d.weight j) μ := by
  let := h.finiteOnCompacts
  exact (d.weight_contDiff j).continuous.integrable_of_hasCompactSupport (d.weight_compact j)

lemma FiniteFieldFreezing.integrable_weighted_flux
    (d : FiniteFieldFreezing X K A η N) (h : IsAmbientOutwardPerimeterPolar E μ ν)
    (j : Fin N) : Integrable (fun x => d.weight j x * |inner ℝ (d.constantVector j) (ν x)|) μ := by
  have hmi : Measurable (fun x => inner ℝ (d.constantVector j) (ν x)) :=
    (continuous_inner (𝕜 := ℝ)).measurable.comp (measurable_const.prodMk h.measurable)
  have hm : Measurable (fun x => |inner ℝ (d.constantVector j) (ν x)|) := by
    simpa only [Real.norm_eq_abs] using hmi.norm
  apply ((d.integrable_weight h j).mul_const ‖d.constantVector j‖).mono'
    (((d.weight_contDiff j).continuous.measurable.mul hm).aestronglyMeasurable)
  filter_upwards [h.norm_ae] with x hx
  rw [Pi.mul_apply, Real.norm_eq_abs, abs_mul, abs_of_nonneg (d.weight_nonneg j x), abs_abs]
  exact mul_le_mul_of_nonneg_left
    (by simpa only [Real.norm_eq_abs, hx, mul_one] using
      norm_inner_le_norm (𝕜 := ℝ) (d.constantVector j) (ν x)) (d.weight_nonneg j x)

lemma integrable_abs_inner_perimeter_polar
    (h : IsAmbientOutwardPerimeterPolar E μ ν) (hX : Continuous X)
    (hcX : HasCompactSupport X) : Integrable (fun x => |inner ℝ (X x) (ν x)|) μ := by
  let := h.finiteOnCompacts
  have hmi : Measurable (fun x => inner ℝ (X x) (ν x)) :=
    (continuous_inner (𝕜 := ℝ)).measurable.comp (hX.measurable.prodMk h.measurable)
  have hm : Measurable (fun x => |inner ℝ (X x) (ν x)|) := by
    simpa only [Real.norm_eq_abs] using hmi.norm
  apply (hX.norm.integrable_of_hasCompactSupport hcX.norm).mono' hm.aestronglyMeasurable
  filter_upwards [h.norm_ae] with x hx
  simpa only [Real.norm_eq_abs, abs_abs, hx, mul_one] using norm_inner_le_norm (𝕜 := ℝ) (X x) (ν x)

lemma FiniteFieldFreezing.weight_eq_zero_outside
    (d : FiniteFieldFreezing X K A η N) (j : Fin N) {x : AmbientSpace} (hx : x ∉ A) :
    d.weight j x = 0 := by
  apply Function.notMem_support.mp
  intro hxw
  exact hx (d.closure_region_subset j (subset_closure
    (d.weight_support j (subset_tsupport _ hxw))))

lemma FiniteFieldFreezing.sum_integral_weight_le
    (d : FiniteFieldFreezing X K A η N) (h : IsAmbientOutwardPerimeterPolar E μ ν) :
    ∑ j, ∫ x, d.weight j x ∂μ ≤ μ.real A := by
  classical
  let := h.finiteOnCompacts
  have hfin : μ A < ∞ := d.bounded_ambient.measure_lt_top
  let : IsFiniteMeasure (μ.restrict A) := ⟨by simpa using hfin⟩
  rw [← integral_finsetSum _ (fun j _ => d.integrable_weight h j)]
  have hz (x : AmbientSpace) (hx : x ∉ A) : ∑ j, d.weight j x = 0 := by
    simp only [d.weight_eq_zero_outside _ hx, Finset.sum_const_zero]
  rw [← setIntegral_eq_integral_of_forall_compl_eq_zero hz]
  calc
    _ ≤ ∫ _ in A, (1 : ℝ) ∂μ := integral_mono
      (Integrable.integrableOn (integrable_finsetSum _ (fun j _ => d.integrable_weight h j)))
      (integrable_const _) (fun x => d.sum_le_one x)
    _ = _ := by simp

/-- Pointwise flux freezing costs at most the tolerance times the partition sum. -/
lemma FiniteFieldFreezing.abs_flux_sum_sub_le
    (d : FiniteFieldFreezing X K A η N) (hsX : tsupport X ⊆ K)
    {x : AmbientSpace} (hn : ‖ν x‖ = 1) :
    |(∑ j, d.weight j x * |inner ℝ (d.constantVector j) (ν x)|) -
      (|inner ℝ (X x) (ν x)|)| ≤ η * ∑ j, d.weight j x := by
  classical
  have hsplit : ∑ j, d.weight j x * |inner ℝ (X x) (ν x)| =
      |inner ℝ (X x) (ν x)| := by
    rw [← Finset.sum_mul]
    by_cases hx : x ∈ K
    · rw [d.sum_eq_one x hx, one_mul]
    · have hxX : X x = 0 := Function.notMem_support.mp
        (fun hz => hx (hsX (subset_tsupport _ hz)))
      simp only [hxX, inner_zero_left, abs_zero, mul_zero]
  rw [← hsplit, ← Finset.sum_sub_distrib]
  calc
    _ ≤ ∑ j, |d.weight j x * |inner ℝ (d.constantVector j) (ν x)| -
        d.weight j x * (|inner ℝ (X x) (ν x)|)| := Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ j, d.weight j x * η := by
      apply Finset.sum_le_sum
      intro j _
      rw [← mul_sub, abs_mul, abs_of_nonneg (d.weight_nonneg j x)]
      by_cases hj : x ∈ d.region j
      · apply mul_le_mul_of_nonneg_left _ (d.weight_nonneg j x)
        calc
          _ ≤ |inner ℝ (d.constantVector j) (ν x) - inner ℝ (X x) (ν x)| :=
            abs_abs_sub_abs_le_abs_sub _ _
          _ = |inner ℝ (d.constantVector j - X x) (ν x)| := by rw [inner_sub_left]
          _ ≤ ‖d.constantVector j - X x‖ := by
            simpa only [Real.norm_eq_abs, hn, mul_one] using
              norm_inner_le_norm (𝕜 := ℝ) (d.constantVector j - X x) (ν x)
          _ ≤ η := by rw [norm_sub_rev]; exact d.oscillation_le j x hj
      · have hz : d.weight j x = 0 := Function.notMem_support.mp
          (fun hz => hj (d.weight_support j (subset_tsupport _ hz)))
        simp only [hz, zero_mul, le_refl]
    _ = _ := by rw [← Finset.sum_mul, mul_comm]

/-- Integrated boundary flux error, still retaining the actual partition mass. -/
theorem FiniteFieldFreezing.integral_flux_error_le_weight
    (d : FiniteFieldFreezing X K A η N) (h : IsAmbientOutwardPerimeterPolar E μ ν)
    (hX : Continuous X) (hcX : HasCompactSupport X) (hsX : tsupport X ⊆ K) :
    |(∑ j, ∫ x, d.weight j x * |inner ℝ (d.constantVector j) (ν x)| ∂μ) -
      ∫ x, |inner ℝ (X x) (ν x)| ∂μ| ≤ η * ∑ j, ∫ x, d.weight j x ∂μ := by
  classical
  have hi := integrable_finsetSum Finset.univ (fun j _ => d.integrable_weighted_flux h j)
  have hiX := integrable_abs_inner_perimeter_polar h hX hcX
  have hiw := integrable_finsetSum Finset.univ (fun j _ => d.integrable_weight h j)
  rw [← integral_finsetSum _ (fun j _ => d.integrable_weighted_flux h j),
    ← integral_sub hi hiX, ← integral_finsetSum _ (fun j _ => d.integrable_weight h j),
    ← integral_const_mul]
  exact abs_integral_le_integral_abs.trans
    (integral_mono_ae (hi.sub hiX).abs (hiw.const_mul η)
      (h.norm_ae.mono fun x hx => d.abs_flux_sum_sub_le hsX hx))

/-- The flux error is controlled by tolerance times the fixed ambient perimeter mass. -/
theorem FiniteFieldFreezing.integral_flux_error_le
    (d : FiniteFieldFreezing X K A η N) (h : IsAmbientOutwardPerimeterPolar E μ ν)
    (hX : Continuous X) (hcX : HasCompactSupport X) (hsX : tsupport X ⊆ K) (hη : 0 ≤ η) :
    |(∑ j, ∫ x, d.weight j x * |inner ℝ (d.constantVector j) (ν x)| ∂μ) -
      ∫ x, |inner ℝ (X x) (ν x)| ∂μ| ≤ η * μ.real A :=
  (d.integral_flux_error_le_weight h hX hcX hsX).trans
    (mul_le_mul_of_nonneg_left (d.sum_integral_weight_le h) hη)

end LiquidDrop

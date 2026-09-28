import NoCompromise.Elliptic.CampanatoHolderEmbedding
import NoCompromise.Elliptic.HolderInterpolationNorm
import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic

/-! Segment averages for blueprint `lem:Gh`. The domain contains precisely the
points whose entire displacement segment remains in the original open set.
The averaging parameter runs from zero to one, so both signs of a displacement
are covered and the Hölder norm has no loss. -/

noncomputable section
open MeasureTheory Filter Metric Set InnerProductSpace
open scoped ENNReal NNReal Topology Gradient
namespace LiquidDrop
set_option maxSynthPendingDepth 8

/-- The segment interior for a prescribed displacement vector. -/
def campanatoSegmentDomain {n : ℕ} (U : Set (EuclideanSpace ℝ (Fin n)))
    (v : EuclideanSpace ℝ (Fin n)) : Set (EuclideanSpace ℝ (Fin n)) :=
  {x | ∀ t ∈ Icc (0 : ℝ) 1, x + t • v ∈ U}

/-- A probability average over the actual displacement segment. -/
def campanatoSegmentAverage {n : ℕ} (g : EuclideanSpace ℝ (Fin n) → ℝ)
    (v : EuclideanSpace ℝ (Fin n)) (x : EuclideanSpace ℝ (Fin n)) : ℝ :=
  ∫ t in Icc (0 : ℝ) 1, g (x + t • v)

/-- The vector field whose divergence is the directional difference quotient. -/
def campanatoSegmentField {n : ℕ} (g : EuclideanSpace ℝ (Fin n) → ℝ)
    (h : ℝ) (e : EuclideanSpace ℝ (Fin n)) (x : EuclideanSpace ℝ (Fin n)) :=
  campanatoSegmentAverage g (h • e) x • e

lemma campanatoSegmentDomain_subset {n : ℕ} (U : Set (EuclideanSpace ℝ (Fin n)))
    (v : EuclideanSpace ℝ (Fin n)) : campanatoSegmentDomain U v ⊆ U := by
  intro x hx
  simpa using hx 0 (by simp)

lemma isOpen_campanatoSegmentDomain {n : ℕ} {U : Set (EuclideanSpace ℝ (Fin n))}
    (hU : IsOpen U) (v : EuclideanSpace ℝ (Fin n)) :
    IsOpen (campanatoSegmentDomain U v) := by
  apply Metric.isOpen_iff.mpr
  intro x hx
  let K := (fun t : ℝ => x + t • v) '' Icc (0 : ℝ) 1
  have hK : IsCompact K := isCompact_Icc.image (continuous_const.add
    (continuous_id.smul continuous_const))
  have hKU : K ⊆ U := by rintro y ⟨t, ht, rfl⟩; exact hx t ht
  obtain ⟨δ, hδ, hδU⟩ := hK.exists_thickening_subset_open hU hKU
  refine ⟨δ, hδ, ?_⟩
  intro y hy t ht
  apply hδU
  exact mem_thickening_iff.mpr ⟨x + t • v, mem_image_of_mem _ ht,
    by simpa only [dist_add_right] using (mem_ball.mp hy)⟩

lemma campanatoSegmentAverage_integrable_path {n : ℕ}
    {U : Set (EuclideanSpace ℝ (Fin n))} {g : EuclideanSpace ℝ (Fin n) → ℝ}
    (hg : ContinuousOn g U) {v x : EuclideanSpace ℝ (Fin n)}
    (hx : x ∈ campanatoSegmentDomain U v) :
    IntegrableOn (fun t : ℝ => g (x + t • v)) (Icc (0 : ℝ) 1) :=
  (hg.comp (continuous_const.add (continuous_id.smul continuous_const)).continuousOn hx)
    |>.integrableOn_compact isCompact_Icc

lemma campanato_holder_norm_sub_le {E F : Type*} [NormedAddCommGroup E]
    [NormedAddCommGroup F] {a : ℝ} {f : E → F} {U : Set E}
    (hf : HasFiniteHolderNormOn a f U) {x y : E} (hx : x ∈ U) (hy : y ∈ U) :
    ‖f x - f y‖ ≤ holderSeminorm a f U * ‖x - y‖ ^ a := by
  by_cases he : x = y
  · subst y
    simp only [sub_self, norm_zero]
    exact mul_nonneg hf.seminorm_nonneg (Real.rpow_nonneg (le_refl 0) a)
  · apply (div_le_iff₀ (Real.rpow_pos_of_pos
      (norm_pos_iff.mpr (sub_ne_zero.mpr he)) a)).mp
    exact le_csSup hf.seminorm_bounded
      (mem_insert_of_mem 0 (mem_image_of_mem _ (show (x, y) ∈ U ×ˢ U from ⟨hx, hy⟩)))

lemma campanatoSegmentAverage_norm_le {n : ℕ}
    {U : Set (EuclideanSpace ℝ (Fin n))} {g : EuclideanSpace ℝ (Fin n) → ℝ}
    {M : ℝ} (hb : ∀ x ∈ U, ‖g x‖ ≤ M) {v x : EuclideanSpace ℝ (Fin n)}
    (hx : x ∈ campanatoSegmentDomain U v) : ‖campanatoSegmentAverage g v x‖ ≤ M := by
  simpa only [campanatoSegmentAverage, Measure.real, Real.volume_Icc, sub_zero,
    ENNReal.ofReal_one, ENNReal.toReal_one, mul_one] using
    norm_setIntegral_le_of_norm_le_const (μ := volume) (f := fun t : ℝ => g (x + t • v))
      (isCompact_Icc.measure_lt_top) (fun t ht => hb _ (hx t ht))

lemma campanatoSegmentAverage_holder_bound {n : ℕ}
    {U : Set (EuclideanSpace ℝ (Fin n))} {g : EuclideanSpace ℝ (Fin n) → ℝ}
    {a H : ℝ} (hg : ContinuousOn g U)
    (hb : ∀ x ∈ U, ∀ y ∈ U, ‖g x - g y‖ ≤ H * ‖x - y‖ ^ a)
    {v x y : EuclideanSpace ℝ (Fin n)}
    (hx : x ∈ campanatoSegmentDomain U v) (hy : y ∈ campanatoSegmentDomain U v) :
    ‖campanatoSegmentAverage g v x - campanatoSegmentAverage g v y‖ ≤ H * ‖x - y‖ ^ a := by
  rw [campanatoSegmentAverage, campanatoSegmentAverage,
    ← integral_sub (campanatoSegmentAverage_integrable_path hg hx)
      (campanatoSegmentAverage_integrable_path hg hy)]
  have hbound (t : ℝ) (ht : t ∈ Icc (0 : ℝ) 1) :
      ‖g (x + t • v) - g (y + t • v)‖ ≤ H * ‖x - y‖ ^ a := by
    simpa only [add_sub_add_right_eq_sub] using hb _ (hx t ht) _ (hy t ht)
  simpa only [Measure.real, Real.volume_Icc, sub_zero, ENNReal.ofReal_one,
    ENNReal.toReal_one, mul_one] using
      norm_setIntegral_le_of_norm_le_const (μ := volume) isCompact_Icc.measure_lt_top hbound

/-- Unit directions preserve the full sum Hölder norm, with constant exactly one.
The step may have either sign; the norm estimate itself also holds at zero. -/
theorem campanatoSegmentField_holder {n : ℕ}
    {U : Set (EuclideanSpace ℝ (Fin n))} {g : EuclideanSpace ℝ (Fin n) → ℝ}
    {a : ℝ} (hg : ContinuousOn g U) (hf : HasFiniteHolderNormOn a g U)
    (h : ℝ) (e : EuclideanSpace ℝ (Fin n)) (he : ‖e‖ = 1) :
    HasFiniteHolderNormOn a (campanatoSegmentField g h e) (campanatoSegmentDomain U (h • e)) ∧
      holderNorm a (campanatoSegmentField g h e) (campanatoSegmentDomain U (h • e)) ≤
        holderNorm a g U := by
  have hM := holderUniformNorm_nonneg hf.uniform_bounded
  have hH := hf.seminorm_nonneg
  have hv : ∀ x ∈ campanatoSegmentDomain U (h • e), ‖campanatoSegmentField g h e x‖ ≤
      holderUniformNorm g U := by
    intro x hx
    simpa only [campanatoSegmentField, norm_smul, he, mul_one] using
      campanatoSegmentAverage_norm_le
        (fun _ hy => norm_le_holderUniformNorm hf.uniform_bounded hy) hx
  have hh : ∀ x ∈ campanatoSegmentDomain U (h • e), ∀ y ∈ campanatoSegmentDomain U (h • e),
      ‖campanatoSegmentField g h e x - campanatoSegmentField g h e y‖ ≤
        holderSeminorm a g U * ‖x - y‖ ^ a := by
    intro x hx y hy
    simpa only [campanatoSegmentField, ← sub_smul, norm_smul, he, mul_one] using
      campanatoSegmentAverage_holder_bound hg
        (fun _ hx _ hy => campanato_holder_norm_sub_le hf hx hy) hx hy
  have hq : ∀ x ∈ campanatoSegmentDomain U (h • e), ∀ y ∈ campanatoSegmentDomain U (h • e),
      ‖campanatoSegmentField g h e x - campanatoSegmentField g h e y‖ / ‖x - y‖ ^ a ≤
        holderSeminorm a g U := by
    intro x hx y hy
    by_cases hxy : x = y
    · subst y
      simp only [sub_self, norm_zero, zero_div]
      exact hH
    · exact (div_le_iff₀ (Real.rpow_pos_of_pos
        (norm_pos_iff.mpr (sub_ne_zero.mpr hxy)) a)).mpr (hh x hx y hy)
  exact ⟨HasFiniteHolderNormOn.of_bounds hM hH hv hq, holderNorm_le hM hH hv hq⟩

lemma campanatoSegmentAverage_eq_oriented {n : ℕ}
    (g : EuclideanSpace ℝ (Fin n) → ℝ) {h : ℝ} (hh : h ≠ 0)
    (e x : EuclideanSpace ℝ (Fin n)) :
    campanatoSegmentAverage g (h • e) x = h⁻¹ * ∫ t in (0 : ℝ)..h, g (x + t • e) := by
  rw [campanatoSegmentAverage, integral_Icc_eq_integral_Ioc,
    ← intervalIntegral.integral_of_le (by norm_num : (0 : ℝ) ≤ 1)]
  simpa only [mul_zero, mul_one, smul_eq_mul, smul_smul, mul_comm] using
    intervalIntegral.integral_comp_mul_left (a := 0) (b := 1)
      (fun t : ℝ => g (x + t • e)) hh

end LiquidDrop

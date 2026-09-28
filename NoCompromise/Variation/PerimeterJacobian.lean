import NoCompromise.Variation.Volume
import NoCompromise.Measure.QuadraticIntegral

/-!
# Differentiating the cofactor area integral

The uniform quadratic straight-map expansion differentiates surface area against
any finite measure carrying a measurable unit normal. The first-order term is
the tangential divergence relative to that normal.
-/

noncomputable section
open MeasureTheory Set Filter Metric
open scoped Topology ENNReal
namespace LiquidDrop

/-- Divergence on the plane orthogonal to the given normal. -/
def tangentialDivergence (X ν : AmbientSpace → AmbientSpace) (x : AmbientSpace) : ℝ :=
  divergenceN X x - inner ℝ (ν x) (fderiv ℝ X x (ν x))

lemma tangentialDivergence_eq_zero_of_notMem_tsupport
    {X ν : AmbientSpace → AmbientSpace} {x : AmbientSpace} (hx : x ∉ tsupport X) :
    tangentialDivergence X ν x = 0 := by
  simp only [tangentialDivergence, divergenceN_eq_zero_of_notMem_tsupport hx,
    fderiv_of_notMem_tsupport ℝ hx, zero_apply, inner_zero_right, sub_self]

lemma measurable_tangentialDivergence {X ν : AmbientSpace → AmbientSpace}
    (hX : ContDiff ℝ 1 X) (hν : Measurable ν) : Measurable (tangentialDivergence X ν) := by
  have hd := hX.continuous_fderiv one_ne_zero
  have hm : Measurable (fun x => fderiv ℝ X x (ν x)) := by fun_prop
  exact (continuous_divergenceN hX).measurable.sub
    (continuous_inner.measurable.comp (hν.prodMk hm))

lemma integrable_tangentialDivergence
    {μ : Measure AmbientSpace} [IsFiniteMeasure μ]
    {X ν : AmbientSpace → AmbientSpace} (hX : ContDiff ℝ 1 X)
    (hcX : HasCompactSupport X) (hν : Measurable ν) (hn : ∀ᵐ x ∂μ, ‖ν x‖ = 1) :
    Integrable (tangentialDivergence X ν) μ := by
  have hcdiv : HasCompactSupport (divergenceN X) := by
    apply hcX.mono'
    intro x hx
    by_contra hx'
    exact hx (divergenceN_eq_zero_of_notMem_tsupport hx')
  obtain ⟨B, hB⟩ := hcdiv.exists_bound_of_continuous (continuous_divergenceN hX)
  let M := ‖straightDerivativeField hX hcX‖
  apply (integrable_const (B + M)).mono'
    (measurable_tangentialDivergence hX hν).aestronglyMeasurable
  filter_upwards [hn] with x hx
  have hi : ‖inner ℝ (ν x) (fderiv ℝ X x (ν x))‖ ≤ M := by
    calc
      _ ≤ ‖ν x‖ * ‖fderiv ℝ X x (ν x)‖ := norm_inner_le_norm _ _
      _ ≤ ‖ν x‖ * (‖fderiv ℝ X x‖ * ‖ν x‖) :=
        mul_le_mul_of_nonneg_left ((fderiv ℝ X x).le_opNorm _) (norm_nonneg _)
      _ ≤ M := by simpa only [hx, one_mul, mul_one] using
        norm_fderiv_le_straightDerivativeField hX hcX x
  exact (norm_sub_le _ _).trans (add_le_add (hB x) hi)

/-- First variation of a finite cofactor-weighted area measure. -/
theorem hasDerivAt_integral_straight_cofactor_norm
    {μ : Measure AmbientSpace} [IsFiniteMeasure μ]
    {X ν : AmbientSpace → AmbientSpace} (hX : ContDiff ℝ 1 X)
    (hcX : HasCompactSupport X) (hν : Measurable ν) (hn : ∀ᵐ x ∂μ, ‖ν x‖ = 1) :
    HasDerivAt (fun t : ℝ => ∫ x,
      ‖cofactor3 (fderiv ℝ (straightPerturbation X t) x) (ν x)‖ ∂μ)
      (∫ x, tangentialDivergence X ν x ∂μ) 0 := by
  obtain ⟨C, _, hR⟩ := exists_uniform_straight_cofactor_expansion hX hcX
  apply hasDerivAt_integral_of_quadratic_remainder (C := C)
    (integrable_tangentialDivergence hX hcX hν hn)
  · intro t _
    let C (x : AmbientSpace) := cofactor3 (fderiv ℝ (straightPerturbation X t) x)
    have hc : Continuous C := continuous_cofactor3.comp
      ((contDiff_straightPerturbation hX t).continuous_fderiv one_ne_zero)
    have hm : Measurable (fun x => C x (ν x)) := by fun_prop
    exact hm.norm.aestronglyMeasurable
  · filter_upwards [hn] with x hx
    rw [cofactor3_fderiv_straightPerturbation (hX.differentiable one_ne_zero x)]
    simpa using hx
  · intro t ht
    filter_upwards [hn] with x hx
    exact (hR t ht x).2.2 (ν x) hx

end LiquidDrop

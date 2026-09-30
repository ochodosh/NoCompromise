module

public import NoCompromise.Variation.PerimeterJacobian
public import Mathlib.Analysis.SpecialFunctions.Pow.Deriv

@[expose] public section

/-! # Tangential divergence of radial vector fields -/

noncomputable section
open MeasureTheory Set Filter Metric
open scoped Topology
namespace LiquidDrop

lemma hasFDerivAt_radial_norm {y : AmbientSpace} (hy : y ≠ 0) :
    HasFDerivAt (fun z : AmbientSpace => ‖z‖) (‖y‖⁻¹ • innerSL ℝ y) y := by
  have hn : ‖y‖ ≠ 0 := norm_ne_zero_iff.mpr hy
  have h := (hasStrictFDerivAt_norm_sq y).hasFDerivAt.sqrt (pow_ne_zero 2 hn)
  convert! h using 1
  · ext z
    simp only [Real.sqrt_sq (norm_nonneg z)]
  · ext v
    simp only [smul_apply, innerSL_apply_apply, smul_eq_mul,
      Real.sqrt_sq (norm_nonneg y)]
    field_simp
    ring

lemma hasFDerivAt_radial_field {η : ℝ → ℝ} {a : ℝ} {y : AmbientSpace}
    (hy : y ≠ 0) (hη : HasDerivAt η a ‖y‖) :
    HasFDerivAt (fun z : AmbientSpace => η ‖z‖ • z)
      (η ‖y‖ • ContinuousLinearMap.id ℝ AmbientSpace +
        (a / ‖y‖) • (innerSL ℝ y).smulRight y) y := by
  have h := (hη.comp_hasFDerivAt y (hasFDerivAt_radial_norm hy)).smul (hasFDerivAt_id y)
  convert! h using 1
  ext v
  simp only [add_apply, smul_apply, ContinuousLinearMap.id_apply,
    ContinuousLinearMap.smulRight_apply, innerSL_apply_apply, smul_smul]
  simp only [Function.comp_apply, id_eq, smul_eq_mul, div_eq_mul_inv, mul_assoc]

lemma divergenceN_of_radial_derivative {X : AmbientSpace → AmbientSpace}
    {y : AmbientSpace} {a b : ℝ}
    (hX : fderiv ℝ X y = a • ContinuousLinearMap.id ℝ AmbientSpace +
      b • (innerSL ℝ y).smulRight y) :
    divergenceN X y = 3 * a + b * ‖y‖ ^ 2 := by
  rw [divergenceN, hX]
  simp only [add_apply, smul_apply, ContinuousLinearMap.id_apply,
    ContinuousLinearMap.smulRight_apply, innerSL_apply_apply,
    EuclideanSpace.inner_single_right, RCLike.conj_to_real, one_mul, mul_one,
    PiLp.add_apply, PiLp.smul_apply, smul_eq_mul,
    PiLp.single_apply, ite_true, Finset.sum_add_distrib]
  have hn : (∑ i : Fin 3, y i * y i) = ‖y‖ ^ 2 := by
    simpa only [PiLp.inner_apply, Real.inner_apply] using (real_inner_self_eq_norm_sq y)
  simp only [← Finset.mul_sum]
  rw [hn]
  norm_num

/-- The radial-field tangential divergence, with the normal component written
as its scalar projection on the unit normal. -/
theorem radial_tangential_divergence {η : ℝ → ℝ} {a : ℝ}
    {y : AmbientSpace} {ν : AmbientSpace → AmbientSpace}
    (hy : y ≠ 0) (hη : HasDerivAt η a ‖y‖) (hν : ‖ν y‖ = 1) :
    tangentialDivergence (fun z => η ‖z‖ • z) ν y =
      2 * η ‖y‖ + (a / ‖y‖) * (‖y‖ ^ 2 - (inner ℝ y (ν y)) ^ 2) := by
  have hD := (hasFDerivAt_radial_field hy hη).fderiv
  rw [tangentialDivergence, divergenceN_of_radial_derivative hD, hD]
  simp only [add_apply, smul_apply, ContinuousLinearMap.id_apply,
    ContinuousLinearMap.smulRight_apply, innerSL_apply_apply,
    inner_add_right, inner_smul_right, real_inner_self_eq_norm_sq, hν, one_pow,
    mul_one, real_inner_comm (ν y) y]
  ring

lemma radial_normal_norm {y v : AmbientSpace} (hv : ‖v‖ = 1) :
    ‖(inner ℝ y v) • v‖ = |inner ℝ y v| := by
  simp only [norm_smul, Real.norm_eq_abs, hv, mul_one]

lemma radial_tangent_norm_sq {y v : AmbientSpace} (hv : ‖v‖ = 1) :
    ‖y - (inner ℝ y v) • v‖ ^ 2 = ‖y‖ ^ 2 - (inner ℝ y v) ^ 2 := by
  rw [norm_sub_sq_real, inner_smul_right, norm_smul, Real.norm_eq_abs, hv, mul_one,
    sq_abs]
  ring

/-- Both equivalent formulas in `lem:radial-divergence`. -/
theorem radial_tangential_divergence_components {η : ℝ → ℝ} {a : ℝ}
    {y : AmbientSpace} {ν : AmbientSpace → AmbientSpace}
    (hy : y ≠ 0) (hη : HasDerivAt η a ‖y‖) (hν : ‖ν y‖ = 1) :
    tangentialDivergence (fun z => η ‖z‖ • z) ν y =
      2 * η ‖y‖ + (a / ‖y‖) * ‖y - (inner ℝ y (ν y)) • ν y‖ ^ 2 ∧
    tangentialDivergence (fun z => η ‖z‖ • z) ν y =
      2 * η ‖y‖ + a * ‖y‖ - (a / ‖y‖) * ‖(inner ℝ y (ν y)) • ν y‖ ^ 2 := by
  constructor
  · rw [radial_tangent_norm_sq hν]
    exact radial_tangential_divergence hy hη hν
  · rw [radial_normal_norm hν, sq_abs, radial_tangential_divergence hy hη hν]
    have hn : ‖y‖ ≠ 0 := norm_ne_zero_iff.mpr hy
    field_simp
    ring

/-- The radial field's normal component has precisely the stated size. -/
lemma radial_field_normal_abs (η : ℝ → ℝ) {y v : AmbientSpace} (hv : ‖v‖ = 1) :
    |inner ℝ (η ‖y‖ • y) v| = |η ‖y‖| * ‖(inner ℝ y v) • v‖ := by
  rw [inner_smul_left, RCLike.conj_to_real, abs_mul, radial_normal_norm hv]

end LiquidDrop

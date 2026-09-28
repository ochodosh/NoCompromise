import NoCompromise.BV.SphericalSlicing
import NoCompromise.Energy.Coulomb
import Mathlib.Analysis.InnerProductSpace.Projection.Reflection

/-!
# Elementary angular integration for the ball potential

The scalar antiderivative computes the angular integral of the Newtonian kernel
on every shell whose radius differs from the observation radius. The remaining
one-dimensional shell is a null set in radial integration. The measure change
here is an ordinary linear product-coordinate equivalence.
-/

noncomputable section
open MeasureTheory Set Filter Metric
open scoped ENNReal NNReal Topology RealInnerProductSpace
namespace LiquidDrop

lemma ballPotential_radicand_pos {a r : ℝ} (ha : 0 < a) (hr : 0 < r) (hne : a ≠ r)
    (θ : ℝ) : 0 < a ^ 2 + r ^ 2 - 2 * a * r * Real.cos θ := by
  have hp : 0 < (a - r)^2 := sq_pos_of_ne_zero (sub_ne_zero.mpr hne)
  have hc := mul_le_mul_of_nonneg_left (Real.cos_le_one θ) (show 0 ≤ 2 * a * r by positivity)
  nlinarith

/-- Direct colatitude integration for a shell away from the observation radius. -/
lemma integral_ballPotential_colatitude {a r : ℝ}
    (ha : 0 < a) (hr : 0 < r) (hne : a ≠ r) :
    (∫ θ in (0 : ℝ)..Real.pi,
      Real.sin θ / Real.sqrt (a ^ 2 + r ^ 2 - 2 * a * r * Real.cos θ)) =
      (a + r - |a - r|) / (a * r) := by
  have hs (θ : ℝ) : Real.sqrt (a ^ 2 + r ^ 2 - 2 * a * r * Real.cos θ) ≠ 0 :=
    (Real.sqrt_pos.mpr (ballPotential_radicand_pos ha hr hne θ)).ne'
  have hd (θ : ℝ) : HasDerivAt
      (fun t => Real.sqrt (a ^ 2 + r ^ 2 - 2 * a * r * Real.cos t) / (a * r))
      (Real.sin θ / Real.sqrt (a ^ 2 + r ^ 2 - 2 * a * r * Real.cos θ)) θ := by
    have hh := (((hasDerivAt_const θ (a ^ 2 + r ^ 2)).sub
      ((Real.hasDerivAt_cos θ).const_mul (2 * a * r))).sqrt
        (ballPotential_radicand_pos ha hr hne θ).ne').div_const (a * r)
    convert! hh using 1
    simp only [Pi.sub_apply]
    field_simp [ha.ne', hr.ne']
    ring
  have hc : Continuous (fun θ : ℝ =>
      Real.sin θ / Real.sqrt (a ^ 2 + r ^ 2 - 2 * a * r * Real.cos θ)) :=
    Real.continuous_sin.div (by fun_prop) hs
  rw [intervalIntegral.integral_eq_sub_of_hasDerivAt (fun θ _ => hd θ) (hc.intervalIntegrable _ _)]
  have hp : a ^ 2 + r ^ 2 - 2 * a * r * Real.cos Real.pi = (a + r)^2 := by
    rw [Real.cos_pi]
    ring
  have hz : a ^ 2 + r ^ 2 - 2 * a * r * Real.cos 0 = (a - r)^2 := by
    rw [Real.cos_zero]
    ring
  rw [hp, hz, Real.sqrt_sq (by positivity), Real.sqrt_sq_eq_abs]
  ring

/-- Distance from an axial observation point to a spherical-coordinate point. -/
lemma norm_axis_sub_sphereParam (a r : ℝ) (p : EuclideanSpace ℝ (Fin 2)) :
    ‖EuclideanSpace.single 2 a - r • sphereParam p‖ =
      Real.sqrt (a ^ 2 + r ^ 2 - 2 * a * r * Real.cos (p 1)) := by
  have hn : ‖EuclideanSpace.single (2 : Fin 3) a - r • sphereParam p‖ ^ 2 =
      a ^ 2 + r ^ 2 - 2 * a * r * Real.cos (p 1) := by
    rw [norm_sub_sq_real]
    simp only [PiLp.norm_single, Real.norm_eq_abs, sq_abs, norm_smul,
      norm_sphereParam, mul_one, inner_smul_right,
      EuclideanSpace.inner_single_left, sphereParam_two, starRingEnd_apply, star_trivial]
    ring
  rw [← hn, Real.sqrt_sq (norm_nonneg _)]


/-- The longitude/colatitude coordinate equivalence, used only for elementary
product integration on the spherical parameter rectangle. -/
def ballPotentialAngleEquiv : (ℝ × ℝ) ≃L[ℝ] EuclideanSpace ℝ (Fin 2) :=
  LinearEquiv.toContinuousLinearEquiv
    { toFun := fun p => WithLp.toLp 2 ![p.1, p.2]
      invFun := fun x => (x 0, x 1)
      left_inv := by intro p; rcases p with ⟨x, y⟩; rfl
      right_inv := by intro x; apply PiLp.ext; intro i; fin_cases i <;> rfl
      map_add' := by intro p q; apply PiLp.ext; intro i; fin_cases i <;> rfl
      map_smul' := by intro r p; apply PiLp.ext; intro i; fin_cases i <;> rfl }

lemma measurePreserving_ballPotentialAngleEquiv : MeasurePreserving ballPotentialAngleEquiv := by
  have h : MeasurePreserving ballPotentialAngleEquiv.symm := by
    have h := (volume_preserving_finTwoArrow ℝ).comp (PiLp.volume_preserving_ofLp (Fin 2))
    convert h using 1 <;> rfl
  exact MeasurePreserving.symm ballPotentialAngleEquiv.symm.toHomeomorph.toMeasurableEquiv h

lemma integral_sphereParamDomain_colatitude (f : ℝ → ℝ) :
    (∫ p in sphereParamDomain, f (p 1)) =
      2 * Real.pi * ∫ θ in Ioo (0 : ℝ) Real.pi, f θ := by
  have h := measurePreserving_ballPotentialAngleEquiv.setIntegral_preimage_emb
    ballPotentialAngleEquiv.toHomeomorph.measurableEmbedding (fun p => f (p 1)) sphereParamDomain
  have he : ballPotentialAngleEquiv ⁻¹' sphereParamDomain =
      Ioo (-Real.pi) Real.pi ×ˢ Ioo (0 : ℝ) Real.pi := by
    ext p
    rfl
  rw [he] at h
  rw [← h]
  change (∫ p in Ioo (-Real.pi) Real.pi ×ˢ Ioo (0 : ℝ) Real.pi, f p.2) = _
  rw [Measure.volume_eq_prod, ← Measure.prod_restrict, integral_fun_snd]
  simp only [Measure.real, Measure.restrict_apply_univ, Real.volume_Ioo,
    ENNReal.toReal_ofReal (by linarith [Real.pi_pos] : 0 ≤ Real.pi - -Real.pi), smul_eq_mul]
  ring

/-- The complete angular shell integral, before the radial integration.
The excluded shell radius is a singleton, hence irrelevant to that integration. -/
lemma integral_ballPotential_shell_param {a r : ℝ}
    (ha : 0 < a) (hr : 0 < r) (hne : a ≠ r) :
    (∫ p in sphereParamDomain, (r ^ 2 * Real.sin (p 1)) *
      ‖EuclideanSpace.single 2 a - r • sphereParam p‖⁻¹) =
      2 * Real.pi * r ^ 2 * ((a + r - |a - r|) / (a * r)) := by
  calc
    _ = ∫ p in sphereParamDomain, r ^ 2 *
        (Real.sin (p 1) / Real.sqrt (a ^ 2 + r ^ 2 - 2 * a * r * Real.cos (p 1))) := by
      apply integral_congr_ae
      filter_upwards [] with p
      rw [norm_axis_sub_sphereParam]
      ring
    _ = _ := by
      rw [integral_sphereParamDomain_colatitude (fun θ => r ^ 2 *
        (Real.sin θ / Real.sqrt (a ^ 2 + r ^ 2 - 2 * a * r * Real.cos θ))),
        integral_const_mul, ← integral_Ioc_eq_integral_Ioo,
        ← intervalIntegral.integral_of_le Real.pi_pos.le,
        integral_ballPotential_colatitude ha hr hne]
      ring


lemma integral_ballPotential_shell_param_piecewise {a r : ℝ}
    (ha : 0 < a) (hr : 0 < r) (hne : a ≠ r) :
    (∫ p in sphereParamDomain, (r ^ 2 * Real.sin (p 1)) *
      ‖EuclideanSpace.single 2 a - r • sphereParam p‖⁻¹) =
      4 * Real.pi * (if r < a then r ^ 2 / a else r) := by
  rw [integral_ballPotential_shell_param ha hr hne]
  split_ifs with h
  · rw [abs_of_pos (sub_pos.mpr h)]
    field_simp
    ring
  · rw [abs_of_nonpos (sub_nonpos.mpr (not_lt.mp h))]
    field_simp
    ring

end LiquidDrop

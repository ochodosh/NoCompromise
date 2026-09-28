import NoCompromise.Variation.TransportC2

/-!
# C¹ transport by smooth approximation of the indicator

The smooth integration-by-parts identity uses only first derivatives of the
coordinate map and its inverse. The cofactor pullback needs only continuity.
-/

noncomputable section
open MeasureTheory Set Filter Metric
open scoped Topology ENNReal Gradient Convolution
namespace LiquidDrop

lemma integral_mul_divergence_eq_neg_gradient_pairing
    {u : AmbientSpace → ℝ} (hu : ContDiff ℝ 1 u)
    {X : AmbientSpace → AmbientSpace} (hX : ContDiff ℝ 1 X)
    (hcX : HasCompactSupport X) :
    (∫ x, u x * divergenceN X x) = -∫ x, inner ℝ (X x) (gradient u x) := by
  have hi : Integrable (fun x => inner ℝ (X x) (gradient u x)) := by
    apply Continuous.integrable_of_hasCompactSupport
    · exact continuous_inner.comp (hX.continuous.prodMk (continuous_gradient_of_contDiff hu))
    · apply hcX.mono
      intro x hx hz
      exact hx (by simp only [hz, inner_zero_left])
  have hfdiv := integrable_mul_divergenceN
    (hu.continuous.locallyIntegrable.locallyIntegrableOn univ) hX hcX (subset_univ _)
  have hz := integral_divergenceN_eq_zero (hu.smul hX) hcX.smul_left
  change (∫ x, divergenceN (fun y => u y • X y) x) = 0 at hz
  simp_rw [divergenceN_smul hu hX] at hz
  have hcomm (x : AmbientSpace) : inner ℝ (gradient u x) (X x) =
      inner ℝ (X x) (gradient u x) := real_inner_comm _ _
  simp_rw [hcomm] at hz
  rw [integral_add hfdiv hi] at hz
  linarith

lemma continuous_piolaPullback {Φ X : AmbientSpace → AmbientSpace}
    (hΦ : ContDiff ℝ 1 Φ) (hX : Continuous X) : Continuous (piolaPullback Φ X) := by
  have hC := continuous_cofactor3.comp (hΦ.continuous_fderiv one_ne_zero)
  unfold piolaPullback
  fun_prop

lemma cofactor_adjoint_eq_det_smul_inverse
    (Φ : AmbientSpace ≃ₜ AmbientSpace) (hΦ : Differentiable ℝ Φ)
    (hiΦ : Differentiable ℝ Φ.symm) (x v : AmbientSpace) :
    (cofactor3 (fderiv ℝ Φ x)).adjoint v =
      (fderiv ℝ Φ x).det • fderiv ℝ Φ.symm (Φ x) v := by
  have hh := (hiΦ (Φ x)).hasFDerivAt.comp x (hΦ x).hasFDerivAt
  have hid : (Φ.symm : AmbientSpace → AmbientSpace) ∘ Φ = id := by
    funext y
    exact Φ.symm_apply_apply y
  rw [hid] at hh
  have hc := hh.unique (hasFDerivAt_id x)
  have hc' (w) : fderiv ℝ Φ.symm (Φ x) (fderiv ℝ Φ x w) = w :=
    congrArg (fun A : AmbientSpace →L[ℝ] AmbientSpace => A w) hc
  have hp : fderiv ℝ Φ x ((cofactor3 (fderiv ℝ Φ x)).adjoint v) =
      (fderiv ℝ Φ x).det • v :=
    congrArg (fun A : AmbientSpace →L[ℝ] AmbientSpace => A v)
      (comp_cofactor3_adjoint (fderiv ℝ Φ x))
  have h := congrArg (fderiv ℝ Φ.symm (Φ x)) hp
  simpa only [hc', map_smul] using h

lemma gradient_inverse_cofactor_pairing
    (Φ : AmbientSpace ≃ₜ AmbientSpace) (hΦ : Differentiable ℝ Φ)
    (hiΦ : Differentiable ℝ Φ.symm) {u : AmbientSpace → ℝ}
    (hu : Differentiable ℝ u) (x v : AmbientSpace) :
    (fderiv ℝ Φ x).det * inner ℝ v (gradient (u ∘ Φ.symm) (Φ x)) =
      inner ℝ ((cofactor3 (fderiv ℝ Φ x)).adjoint v) (gradient u x) := by
  rw [inner_gradient_right, inner_gradient_right, conj_trivial, conj_trivial,
    fderiv_comp (Φ x) (hu _) (hiΦ _), ContinuousLinearMap.comp_apply,
    Φ.symm_apply_apply, cofactor_adjoint_eq_det_smul_inverse Φ hΦ hiΦ, map_smul,
    smul_eq_mul]

/-- The smooth transport identity uses only C¹ changes of coordinates. -/
theorem smooth_transport_pairing
    (Φ : AmbientSpace ≃ₜ AmbientSpace) (hΦ : ContDiff ℝ 1 Φ)
    (hiΦ : ContDiff ℝ 1 Φ.symm) {u : AmbientSpace → ℝ} (hu : ContDiff ℝ 1 u)
    {X : AmbientSpace → AmbientSpace} (hX : ContDiff ℝ 1 X)
    (hcX : HasCompactSupport X) {s : ℝ}
    (hsgn : ∀ x, |(fderiv ℝ Φ x).det| = s * (fderiv ℝ Φ x).det) :
    (∫ x, u x * (|(fderiv ℝ Φ x).det| * divergenceN X (Φ x))) =
      -s * ∫ x, inner ℝ (piolaPullback Φ X x) (gradient u x) := by
  have hchange (f : AmbientSpace → ℝ) :
      (∫ y, f y) = ∫ x, |(fderiv ℝ Φ x).det| * f (Φ x) := by
    have hh := integral_image_eq_integral_abs_det_fderiv_smul volume MeasurableSet.univ
      (fun x (_ : x ∈ (univ : Set AmbientSpace)) =>
        (hΦ.differentiable one_ne_zero x).hasFDerivAt.hasFDerivWithinAt)
      Φ.injective.injOn f
    simpa only [image_univ, Φ.surjective.range_eq, setIntegral_univ, smul_eq_mul] using hh
  have hp := integral_mul_divergence_eq_neg_gradient_pairing (hu.comp hiΦ) hX hcX
  rw [hchange (fun x => (u ∘ Φ.symm) x * divergenceN X x),
    hchange (fun x => inner ℝ (X x) (gradient (u ∘ Φ.symm) x))] at hp
  simp only [Function.comp_apply, Φ.symm_apply_apply] at hp
  have hl : (∫ x, |(fderiv ℝ Φ x).det| * (u x * divergenceN X (Φ x))) =
      ∫ x, u x * (|(fderiv ℝ Φ x).det| * divergenceN X (Φ x)) := by
    congr 1
    funext x
    ring
  rw [hl] at hp
  rw [hp, neg_mul, ← integral_const_mul]
  congr 1
  apply integral_congr_ae
  filter_upwards [] with x
  rw [hsgn x, mul_assoc,
    gradient_inverse_cofactor_pairing Φ (hΦ.differentiable one_ne_zero)
      (hiΦ.differentiable one_ne_zero) (hu.differentiable one_ne_zero)]
  rfl

end LiquidDrop

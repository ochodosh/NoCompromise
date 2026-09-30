module

public import NoCompromise.Sobolev.Extension

@[expose] public section

/-!
# Exact variation of functions with a weak gradient

The Lebesgue density of the weak gradient gives a locally finite polar measure
on an open domain. The proved polar representation theorem identifies its mass
with the defining variation supremum, including infinite total masses.
-/

noncomputable section

open MeasureTheory Filter Metric Set InnerProductSpace
open scoped ENNReal Topology Gradient CompactlySupported

namespace LiquidDrop

set_option maxSynthPendingDepth 8

/-- A locally integrable weak gradient induces a regular polar measure whose full mass
is the extended integral of the gradient norm. No global integrability is required. -/
theorem HasWeakGradientOn.exists_polar_with_gradient_mass {n : ℕ}
    {U : Set (EuclideanSpace ℝ (Fin n))} (hU : IsOpen U)
    {f : EuclideanSpace ℝ (Fin n) → ℝ}
    {G : EuclideanSpace ℝ (Fin n) → EuclideanSpace ℝ (Fin n)}
    (hf : HasWeakGradientOn f G U) :
    ∃ ρ : Measure U, ∃ σ : U → EuclideanSpace ℝ (Fin n),
      ρ.Regular ∧ IsDistributionalPolarRepresentation f U ρ σ ∧
        ρ univ = ∫⁻ x in U, ENNReal.ofReal ‖G x‖ := by
  let : LocallyCompactSpace U := hU.locallyCompactSpace
  let μ : Measure U := volume.comap (Subtype.val : U → EuclideanSpace ℝ (Fin n))
  have hG : LocallyIntegrable (fun x : U => G x) μ :=
    (locallyIntegrable_comap hU.measurableSet).mpr hf.locallyIntegrable_gradient
  let g : U → EuclideanSpace ℝ (Fin n) := hG.aestronglyMeasurable.mk (fun x : U => G x)
  have hg : Measurable g := hG.aestronglyMeasurable.stronglyMeasurable_mk.measurable
  have hgeq : (fun x : U => G x) =ᵐ[μ] g := hG.aestronglyMeasurable.ae_eq_mk
  have hgloc : LocallyIntegrable g μ := hG.congr hgeq
  let ρ : Measure U := μ.withDensity (fun x => ENNReal.ofReal ‖g x‖)
  let σ : U → EuclideanSpace ℝ (Fin n) := fun x => ‖g x‖⁻¹ • g x
  let : IsFiniteMeasureOnCompacts ρ := ⟨fun K hK => by
    change μ.withDensity (fun x => ENNReal.ofReal ‖g x‖) K < ∞
    rw [withDensity_apply _ hK.measurableSet]
    simpa only [HasFiniteIntegral, ← ofReal_norm] using (hgloc.integrableOn_isCompact hK).2⟩
  have hnorm (x : U) : ‖g x‖ • σ x = g x := by
    by_cases hx : g x = 0
    · simp [σ, hx]
    · simp [σ, smul_smul, norm_ne_zero_iff.mpr hx]
  refine ⟨ρ, σ, inferInstance, ⟨hg.norm.inv.smul hg, ?_, ?_⟩, ?_⟩
  · change ∀ᵐ x ∂μ.withDensity (fun x => ENNReal.ofReal ‖g x‖), ‖σ x‖ = 1
    rw [ae_withDensity_iff hg.norm.ennreal_ofReal]
    exact Eventually.of_forall fun x hx => by
      have hn : ‖g x‖ ≠ 0 := fun h => hx (by simp [h])
      simp [σ, norm_smul, inv_mul_cancel₀ hn]
  · intro i φ hφ hsφ
    rw [hf.test_eq i φ hφ φ.hasCompactSupport hsφ]
    change (∫ x in U, φ x * G x i) =
      ∫ x : U, φ x * σ x i ∂μ.withDensity (fun x => ENNReal.ofReal ‖g x‖)
    rw [integral_withDensity_eq_integral_toReal_smul hg.norm.ennreal_ofReal
      (Eventually.of_forall fun _ => ENNReal.ofReal_lt_top)]
    rw [← integral_subtype_comap hU.measurableSet (f := fun x => φ x * G x i)]
    apply integral_congr_ae
    filter_upwards [hgeq] with x hx
    simp only [ENNReal.toReal_ofReal (norm_nonneg _), smul_eq_mul]
    have hcoord := congrArg (fun v : EuclideanSpace ℝ (Fin n) => v i) (hnorm x)
    simp only [PiLp.smul_apply, smul_eq_mul] at hcoord
    rw [hx, ← hcoord]
    ring
  · change μ.withDensity (fun x => ENNReal.ofReal ‖g x‖) univ = _
    rw [withDensity_apply _ MeasurableSet.univ, Measure.restrict_univ]
    calc
      _ = ∫⁻ x : U, ENNReal.ofReal ‖G x‖ ∂μ := by
        apply lintegral_congr_ae
        filter_upwards [hgeq] with x hx
        rw [hx]
      _ = _ := lintegral_subtype_comap hU.measurableSet (fun x => ENNReal.ofReal ‖G x‖)

/-- On an open set, the defining BV variation equals the extended integral of any genuine
weak gradient. Both sides may be infinite. -/
theorem HasWeakGradientOn.variation_eq_lintegral_norm {n : ℕ}
    {U : Set (EuclideanSpace ℝ (Fin n))} (hU : IsOpen U)
    {f : EuclideanSpace ℝ (Fin n) → ℝ}
    {G : EuclideanSpace ℝ (Fin n) → EuclideanSpace ℝ (Fin n)}
    (hf : HasWeakGradientOn f G U) :
    variation f U = ∫⁻ x in U, ENNReal.ofReal ‖G x‖ := by
  obtain ⟨ρ, σ, hρ, hpolar, hmass⟩ := hf.exists_polar_with_gradient_mass hU
  let : ρ.Regular := hρ
  have h := hpolar.variation_eq_measure hU hU Subset.rfl hf.locallyIntegrable_function
  have hpre : (Subtype.val ⁻¹' U : Set U) = univ := by ext x; simp
  rw [hpre, hmass] at h
  exact h

/-- If the weak gradient is globally integrable on the domain, variation is its ordinary
L¹ norm embedded in the extended nonnegative reals. -/
theorem HasWeakGradientOn.variation_eq_integral_norm {n : ℕ}
    {U : Set (EuclideanSpace ℝ (Fin n))} (hU : IsOpen U)
    {f : EuclideanSpace ℝ (Fin n) → ℝ}
    {G : EuclideanSpace ℝ (Fin n) → EuclideanSpace ℝ (Fin n)}
    (hf : HasWeakGradientOn f G U) (hG : IntegrableOn G U) :
    variation f U = ENNReal.ofReal (∫ x in U, ‖G x‖) := by
  rw [hf.variation_eq_lintegral_norm hU, ofReal_integral_norm_eq_lintegral_enorm hG]
  simp only [ofReal_norm]

/-- Smooth variation equals the integral of the classical gradient, with infinite total
mass allowed and only C¹ regularity on the open domain. -/
theorem variation_eq_lintegral_norm_gradient_of_contDiffOn {n : ℕ}
    {U : Set (EuclideanSpace ℝ (Fin n))} (hU : IsOpen U)
    {f : EuclideanSpace ℝ (Fin n) → ℝ} (hf : ContDiffOn ℝ 1 f U) :
    variation f U = ∫⁻ x in U, ENNReal.ofReal ‖gradient f x‖ :=
  (hasWeakGradientOn_of_contDiffOn hU hf).variation_eq_lintegral_norm hU

/-- The finite-mass C¹ form of the exact variation formula. -/
theorem variation_eq_integral_norm_gradient_of_contDiffOn {n : ℕ}
    {U : Set (EuclideanSpace ℝ (Fin n))} (hU : IsOpen U)
    {f : EuclideanSpace ℝ (Fin n) → ℝ} (hf : ContDiffOn ℝ 1 f U)
    (hgrad : IntegrableOn (gradient f) U) :
    variation f U = ENNReal.ofReal (∫ x in U, ‖gradient f x‖) :=
  (hasWeakGradientOn_of_contDiffOn hU hf).variation_eq_integral_norm hU hgrad

end LiquidDrop

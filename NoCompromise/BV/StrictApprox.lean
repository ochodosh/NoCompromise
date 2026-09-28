import NoCompromise.BV.Basic
import Mathlib.Analysis.Calculus.Gradient.Basic
import Mathlib.MeasureTheory.Function.LpSpace.ContinuousCompMeasurePreserving

/-!
# BV products and strict smooth approximation

The product rule is obtained directly from the distributional test-field identity.
The gradient is mathlib's real Hilbert-space gradient, with no new convention.
-/

open MeasureTheory Filter Metric Set InnerProductSpace
open scoped ENNReal Topology Gradient CompactlySupported BoundedContinuousFunction Convolution
open scoped Manifold

namespace LiquidDrop

set_option maxSynthPendingDepth 8

/-- A C¹ real function has a continuous Hilbert-space gradient. -/
lemma continuous_gradient_of_contDiff {n : ℕ}
    {ζ : EuclideanSpace ℝ (Fin n) → ℝ} (hζ : ContDiff ℝ 1 ζ) : Continuous (gradient ζ) := by
  exact (toDual ℝ (EuclideanSpace ℝ (Fin n))).symm.continuous.comp
    (hζ.continuous_fderiv one_ne_zero)

lemma gradient_eq_zero_of_notMem_tsupport {n : ℕ}
    {ζ : EuclideanSpace ℝ (Fin n) → ℝ} {x : EuclideanSpace ℝ (Fin n)}
    (hx : x ∉ tsupport ζ) : gradient ζ x = 0 := by
  rw [gradient, fderiv_of_notMem_tsupport ℝ hx, map_zero]

lemma tsupport_gradient_subset {n : ℕ} (ζ : EuclideanSpace ℝ (Fin n) → ℝ) :
    tsupport (gradient ζ) ⊆ tsupport ζ := by
  apply closure_minimal _ (isClosed_tsupport ζ)
  intro x hx
  by_contra hx'
  exact hx (gradient_eq_zero_of_notMem_tsupport hx')

lemma gradient_apply_eq_fderiv_single {n : ℕ}
    (ζ : EuclideanSpace ℝ (Fin n) → ℝ) (x : EuclideanSpace ℝ (Fin n)) (i : Fin n) :
    gradient ζ x i = fderiv ℝ ζ x (EuclideanSpace.single i 1) := by
  rw [← inner_gradient_left (f := ζ) (x := x) (y := EuclideanSpace.single i 1),
    EuclideanSpace.inner_single_right]
  simp

/-- The scalar–vector divergence product rule, with the usual Hilbert gradient. -/
lemma divergenceN_smul {n : ℕ}
    {ζ : EuclideanSpace ℝ (Fin n) → ℝ}
    {X : EuclideanSpace ℝ (Fin n) → EuclideanSpace ℝ (Fin n)}
    (hζ : ContDiff ℝ 1 ζ) (hX : ContDiff ℝ 1 X) (x : EuclideanSpace ℝ (Fin n)) :
    divergenceN (fun y => ζ y • X y) x =
      ζ x * divergenceN X x + inner ℝ (gradient ζ x) (X x) := by
  simp only [divergenceN, fderiv_fun_smul (hζ.differentiable one_ne_zero x)
    (hX.differentiable one_ne_zero x), add_apply,
    smul_apply, ContinuousLinearMap.smulRight_apply,
    PiLp.add_apply, PiLp.smul_apply, smul_eq_mul, Finset.sum_add_distrib, Finset.mul_sum,
    PiLp.inner_apply, Real.inner_apply, gradient_apply_eq_fderiv_single]

/-- Local integrability suffices after multiplication by a continuous compact factor. -/
lemma integrable_mul_compact_factor {n : ℕ}
    {U : Set (EuclideanSpace ℝ (Fin n))} {f ζ : EuclideanSpace ℝ (Fin n) → ℝ}
    (hf : LocallyIntegrableOn f U) (hζ : Continuous ζ) (hcζ : HasCompactSupport ζ)
    (hsζ : tsupport ζ ⊆ U) : Integrable (fun x => ζ x * f x) := by
  have hi := (hf.integrableOn_compact_subset hsζ hcζ).mul_continuousOn hζ.continuousOn hcζ
  have hi' : IntegrableOn (fun x => ζ x * f x) (tsupport ζ) volume := by
    simpa only [mul_comm] using hi
  apply (integrableOn_iff_integrable_of_support_subset ?_).mp hi'
  intro x hx
  by_contra hx'
  exact hx (by change ζ x * f x = 0; rw [image_eq_zero_of_notMem_tsupport hx', zero_mul])

/-- The product-rule correction term is integrable on the whole ambient space. -/
lemma integrable_smul_gradient {n : ℕ}
    {U : Set (EuclideanSpace ℝ (Fin n))} {f ζ : EuclideanSpace ℝ (Fin n) → ℝ}
    (hf : LocallyIntegrableOn f U) (hζ : ContDiff ℝ 1 ζ) (hcζ : HasCompactSupport ζ)
    (hsζ : tsupport ζ ⊆ U) : Integrable (fun x => f x • gradient ζ x) := by
  have hi := (hf.integrableOn_compact_subset hsζ hcζ).smul_continuousOn
    (continuous_gradient_of_contDiff hζ).continuousOn hcζ
  apply (integrableOn_iff_integrable_of_support_subset ?_).mp hi
  intro x hx
  by_contra hx'
  exact hx (by
    change f x • gradient ζ x = 0
    rw [gradient_eq_zero_of_notMem_tsupport hx', smul_zero])


/-- Pairing an integrable field with an almost-everywhere bounded field is integrable. -/
lemma integrable_inner_of_bound {S : Type*} [MeasurableSpace S] {μ : Measure S} {n : ℕ}
    {G X : S → EuclideanSpace ℝ (Fin n)} (hG : Integrable G μ)
    (hX : AEStronglyMeasurable X μ) {C : ℝ} (hb : ∀ᵐ x ∂μ, ‖X x‖ ≤ C) :
    Integrable (fun x => inner ℝ (G x) (X x)) μ := by
  apply (hG.norm.mul_const C).mono'
    (hG.aestronglyMeasurable.aemeasurable.inner hX.aemeasurable).aestronglyMeasurable
  filter_upwards [hb] with x hx
  exact (norm_inner_le_norm _ _).trans
    (mul_le_mul_of_nonneg_left hx (norm_nonneg _))

lemma IsDistributionalPolarRepresentation.integrable_smul_compact_factor {n : ℕ}
    {U : Set (EuclideanSpace ℝ (Fin n))} {f ζ : EuclideanSpace ℝ (Fin n) → ℝ}
    {ρ : Measure U} [IsFiniteMeasureOnCompacts ρ] {σ : U → EuclideanSpace ℝ (Fin n)}
    (hpolar : IsDistributionalPolarRepresentation f U ρ σ)
    (hζ : Continuous ζ) (hcζ : HasCompactSupport ζ) (hsζ : tsupport ζ ⊆ U) :
    Integrable (fun x : U => ζ x • σ x) ρ := by
  let ζc : C_c(EuclideanSpace ℝ (Fin n), ℝ) :=
    { toFun := ζ, continuous_toFun := hζ, hasCompactSupport' := hcζ }
  have hiζ : Integrable (fun x : U => ζ x) ρ := (restrictSupportedCC ⟨ζc, hsζ⟩).integrable
  apply hiζ.norm.mono'
    (((hζ.comp continuous_subtype_val).measurable.smul hpolar.measurable).aestronglyMeasurable)
  filter_upwards [hpolar.norm_ae] with x hx
  change ‖ζ x • σ x‖ ≤ ‖ζ x‖
  rw [norm_smul, hx, mul_one]

/-- The direct weak product identity. The test field need not be supported in `U`, since
the compact factor and its gradient vanish outside a compact subset of `U`. -/
theorem IsDistributionalPolarRepresentation.integral_mul_divergence_eq {n : ℕ}
    {U : Set (EuclideanSpace ℝ (Fin n))} {f ζ : EuclideanSpace ℝ (Fin n) → ℝ}
    {ρ : Measure U} [IsFiniteMeasureOnCompacts ρ] {σ : U → EuclideanSpace ℝ (Fin n)}
    (hpolar : IsDistributionalPolarRepresentation f U ρ σ) (hf : LocallyIntegrableOn f U)
    (hζ : ContDiff ℝ 1 ζ) (hcζ : HasCompactSupport ζ) (hsζ : tsupport ζ ⊆ U)
    {X : EuclideanSpace ℝ (Fin n) → EuclideanSpace ℝ (Fin n)}
    (hX : ContDiff ℝ 1 X) (hcX : HasCompactSupport X) :
    -(∫ x, (ζ x * f x) * divergenceN X x) =
      (∫ x : U, inner ℝ (ζ x • σ x) (X x) ∂ρ) +
        ∫ x, inner ℝ (f x • gradient ζ x) (X x) := by
  let Y := fun x => ζ x • X x
  have hY : ContDiff ℝ 1 Y := hζ.smul hX
  have hcY : HasCompactSupport Y := hcζ.smul_right
  have hsY : tsupport Y ⊆ U := (tsupport_smul_subset_left ζ X).trans hsζ
  have hiY := integrable_mul_divergenceN hf hY hcY hsY
  have hiG := integrable_smul_gradient hf hζ hcζ hsζ
  obtain ⟨C, hC⟩ := hcX.exists_bound_of_continuous hX.continuous
  have hiGX : Integrable (fun x => inner ℝ (f x • gradient ζ x) (X x)) :=
    integrable_inner_of_bound hiG hX.continuous.aestronglyMeasurable
      (Eventually.of_forall hC)
  have hpoint (x) : (ζ x * f x) * divergenceN X x =
      f x * divergenceN Y x - inner ℝ (f x • gradient ζ x) (X x) := by
    rw [show divergenceN Y x = _ from divergenceN_smul hζ hX x, real_inner_smul_left]
    ring
  simp_rw [hpoint]
  rw [integral_sub hiY hiGX]
  have hI : (∫ x in U, f x * divergenceN Y x) = ∫ x, f x * divergenceN Y x := by
    apply setIntegral_eq_integral_of_forall_compl_eq_zero
    intro x hx
    rw [divergenceN_eq_zero_of_notMem_tsupport (fun h => hx (hsY h)), mul_zero]
  have hpair := hpolar.integral_divergence_eq hf hY hcY hsY
  rw [hI] at hpair
  rw [neg_sub, sub_eq_add_neg, hpair, add_comm]
  congr 1
  apply integral_congr_ae
  exact Eventually.of_forall fun x => by
    change inner ℝ (ζ x • X x) (σ x) = inner ℝ (ζ x • σ x) (X x)
    rw [real_inner_smul_left, real_inner_smul_left, real_inner_comm]

/-- Multiplication by a compact C¹ factor has finite total variation. The estimate is
expressed using the original polar measure and the integrable gradient correction. -/
theorem IsDistributionalPolarRepresentation.variation_mul_le {n : ℕ}
    {U : Set (EuclideanSpace ℝ (Fin n))} {f ζ : EuclideanSpace ℝ (Fin n) → ℝ}
    {ρ : Measure U} [IsFiniteMeasureOnCompacts ρ] {σ : U → EuclideanSpace ℝ (Fin n)}
    (hpolar : IsDistributionalPolarRepresentation f U ρ σ) (hf : LocallyIntegrableOn f U)
    (hζ : ContDiff ℝ 1 ζ) (hcζ : HasCompactSupport ζ) (hsζ : tsupport ζ ⊆ U) :
    variation (fun x => ζ x * f x) univ ≤
      ENNReal.ofReal ((∫ x : U, ‖ζ x • σ x‖ ∂ρ) + ∫ x, ‖f x • gradient ζ x‖) := by
  have hiζσ := hpolar.integrable_smul_compact_factor hζ.continuous hcζ hsζ
  have hiG := integrable_smul_gradient hf hζ hcζ hsζ
  apply iSup_le
  intro X
  apply iSup_le
  intro hX
  simp only [setIntegral_univ]
  have hpair := hpolar.integral_mul_divergence_eq hf hζ hcζ hsζ hX.1 hX.2.1
  have hbρ : ‖∫ x : U, inner ℝ (ζ x • σ x) (X x) ∂ρ‖ ≤ ∫ x : U, ‖ζ x • σ x‖ ∂ρ := by
    apply norm_integral_le_of_norm_le hiζσ.norm
    exact Eventually.of_forall fun x => (norm_inner_le_norm _ _).trans
      (by simpa only [mul_one] using mul_le_mul_of_nonneg_left (hX.2.2.2 x) (norm_nonneg _))
  have hbG : ‖∫ x, inner ℝ (f x • gradient ζ x) (X x)‖ ≤ ∫ x, ‖f x • gradient ζ x‖ := by
    apply norm_integral_le_of_norm_le hiG.norm
    exact Eventually.of_forall fun x => (norm_inner_le_norm _ _).trans
      (by simpa only [mul_one] using mul_le_mul_of_nonneg_left (hX.2.2.2 x) (norm_nonneg _))
  apply ENNReal.ofReal_le_ofReal
  calc
    _ ≤ ‖∫ x, (ζ x * f x) * divergenceN X x‖ := le_abs_self _
    _ = ‖-(∫ x, (ζ x * f x) * divergenceN X x)‖ := (norm_neg _).symm
    _ ≤ _ := by rw [hpair]; exact (norm_add_le _ _).trans (add_le_add hbρ hbG)

/-- A compactly supported C¹ factor turns a locally BV function into a globally
integrable function of finite total variation. -/
theorem IsLocallyBVOn.isBVOn_mul_compact_factor {n : ℕ}
    {U : Set (EuclideanSpace ℝ (Fin n))} (hU : IsOpen U)
    {f ζ : EuclideanSpace ℝ (Fin n) → ℝ} (hf : IsLocallyBVOn f U)
    (hζ : ContDiff ℝ 1 ζ) (hcζ : HasCompactSupport ζ) (hsζ : tsupport ζ ⊆ U) :
    IsBVOn (fun x => ζ x * f x) univ := by
  obtain ⟨ρ, σ, _, hρ, hpolar⟩ := exists_distributional_polar_representation hU hf
  let : IsFiniteMeasureOnCompacts ρ := hρ
  refine ⟨(integrable_mul_compact_factor hf.1 hζ.continuous hcζ hsζ).integrableOn, ?_⟩
  exact (hpolar.variation_mul_le hf.1 hζ hcζ hsζ).trans_lt ENNReal.ofReal_lt_top

/-! ## Uniqueness of finite density representatives -/

section DensityUniqueness

variable {S : Type*} [TopologicalSpace S] [MeasurableSpace S] [BorelSpace S]

lemma integral_density_pos_sub_neg {μ : Measure S} {u : S → ℝ}
    (hu : Integrable u μ) (φ : C_c(S, ℝ)) :
    (∫ x, φ x ∂μ.withDensity (fun x => ENNReal.ofReal (u x))) -
      ∫ x, φ x ∂μ.withDensity (fun x => ENNReal.ofReal (-u x)) =
        ∫ x, φ x * u x ∂μ := by
  obtain ⟨C, hC⟩ := φ.hasCompactSupport.exists_bound_of_continuous φ.continuous
  have hp : Integrable (fun x => max (u x) 0 * φ x) μ :=
    hu.pos_part.mul_bdd φ.continuous.aestronglyMeasurable (Eventually.of_forall hC)
  have hn : Integrable (fun x => max (-u x) 0 * φ x) μ :=
    hu.neg.pos_part.mul_bdd φ.continuous.aestronglyMeasurable (Eventually.of_forall hC)
  rw [integral_withDensity_eq_integral_toReal_smul₀
    hu.aestronglyMeasurable.aemeasurable.ennreal_ofReal
    (Eventually.of_forall fun _ => ENNReal.ofReal_lt_top) φ,
    integral_withDensity_eq_integral_toReal_smul₀ (f := fun x => ENNReal.ofReal (-u x))
      hu.neg.aestronglyMeasurable.aemeasurable.ennreal_ofReal
      (Eventually.of_forall fun _ => ENNReal.ofReal_lt_top) φ]
  simp only [ENNReal.toReal_ofReal', smul_eq_mul]
  rw [← integral_sub hp hn]
  apply integral_congr_ae
  exact Eventually.of_forall fun x => by
    by_cases hx : 0 ≤ u x
    · simp [max_eq_left hx, max_eq_right (neg_nonpos.mpr hx), mul_comm]
    · have hx' : u x ≤ 0 := le_of_not_ge hx
      simp [max_eq_right hx', max_eq_left (neg_nonneg.mpr hx'), mul_comm]

variable [T2Space S] [LocallyCompactSpace S]

/-- Equality on continuous compactly supported tests identifies finite signed measure pairs. -/
theorem signedPair_eq_of_integral_cc_eq (μp μn νp νn : Measure S)
    [IsFiniteMeasure μp] [IsFiniteMeasure μn] [IsFiniteMeasure νp] [IsFiniteMeasure νn]
    [μp.Regular] [μn.Regular] [νp.Regular] [νn.Regular]
    (h : ∀ φ : C_c(S, ℝ), (∫ x, φ x ∂μp) - ∫ x, φ x ∂μn =
      (∫ x, φ x ∂νp) - ∫ x, φ x ∂νn) :
    μp.toSignedMeasure - μn.toSignedMeasure = νp.toSignedMeasure - νn.toSignedMeasure := by
  have hm : μp + νn = νp + μn := by
    apply Measure.ext_of_integral_eq_on_compactlySupported
    intro φ
    rw [integral_add_measure φ.integrable φ.integrable,
      integral_add_measure φ.integrable φ.integrable]
    linarith [h φ]
  apply sub_eq_sub_iff_add_eq_add.mpr
  simpa only [Measure.toSignedMeasure_add] using Measure.toSignedMeasure_congr hm

end DensityUniqueness

section ScalarDensityUniqueness

variable {S : Type*} [MetricSpace S] [MeasurableSpace S] [BorelSpace S]
  [LocallyCompactSpace S] [SigmaCompactSpace S]

/-- A scalar identity on all compactly supported continuous tests gives the corresponding
identity of finite signed density measures. Only positive Riesz uniqueness is used. -/
theorem withDensityVec_eq_add_of_integral_cc_eq
    {μ ν κ : Measure S} {u v w : S → ℝ}
    (hu : Integrable u μ) (hv : Integrable v ν) (hw : Integrable w κ)
    (h : ∀ φ : C_c(S, ℝ), (∫ x, φ x * u x ∂μ) =
      (∫ x, φ x * v x ∂ν) + ∫ x, φ x * w x ∂κ) :
    μ.withDensityᵥ u = ν.withDensityᵥ v + κ.withDensityᵥ w := by
  let P := μ.withDensity (fun x => ENNReal.ofReal (u x))
  let N := μ.withDensity (fun x => ENNReal.ofReal (-u x))
  let Q := ν.withDensity (fun x => ENNReal.ofReal (v x))
  let R := ν.withDensity (fun x => ENNReal.ofReal (-v x))
  let A := κ.withDensity (fun x => ENNReal.ofReal (w x))
  let B := κ.withDensity (fun x => ENNReal.ofReal (-w x))
  let : IsFiniteMeasure P := isFiniteMeasure_withDensity_ofReal hu.hasFiniteIntegral
  let : IsFiniteMeasure N := isFiniteMeasure_withDensity_ofReal hu.neg.hasFiniteIntegral
  let : IsFiniteMeasure Q := isFiniteMeasure_withDensity_ofReal hv.hasFiniteIntegral
  let : IsFiniteMeasure R := isFiniteMeasure_withDensity_ofReal hv.neg.hasFiniteIntegral
  let : IsFiniteMeasure A := isFiniteMeasure_withDensity_ofReal hw.hasFiniteIntegral
  let : IsFiniteMeasure B := isFiniteMeasure_withDensity_ofReal hw.neg.hasFiniteIntegral
  have hp : P.toSignedMeasure - N.toSignedMeasure =
      (Q + A).toSignedMeasure - (R + B).toSignedMeasure := by
    apply signedPair_eq_of_integral_cc_eq
    intro φ
    rw [integral_add_measure φ.integrable φ.integrable,
      integral_add_measure φ.integrable φ.integrable]
    have hu' := integral_density_pos_sub_neg hu φ
    have hv' := integral_density_pos_sub_neg hv φ
    have hw' := integral_density_pos_sub_neg hw φ
    change (∫ x, φ x ∂P) - ∫ x, φ x ∂N = ∫ x, φ x * u x ∂μ at hu'
    change (∫ x, φ x ∂Q) - ∫ x, φ x ∂R = ∫ x, φ x * v x ∂ν at hv'
    change (∫ x, φ x ∂A) - ∫ x, φ x ∂B = ∫ x, φ x * w x ∂κ at hw'
    linarith [h φ]
  rw [Measure.toSignedMeasure_add, Measure.toSignedMeasure_add] at hp
  rw [withDensityᵥ_eq_withDensity_pos_part_sub_withDensity_neg_part hu,
    withDensityᵥ_eq_withDensity_pos_part_sub_withDensity_neg_part hv,
    withDensityᵥ_eq_withDensity_pos_part_sub_withDensity_neg_part hw]
  change P.toSignedMeasure - N.toSignedMeasure =
    (Q.toSignedMeasure - R.toSignedMeasure) + (A.toSignedMeasure - B.toSignedMeasure)
  rw [hp]
  abel

end ScalarDensityUniqueness


/-- An integrable density defines a bounded functional on ambient bounded continuous fields. -/
noncomputable def integrableDensityFunctional {n : ℕ}
    {U : Set (EuclideanSpace ℝ (Fin n))} {μ : Measure U}
    {g : U → EuclideanSpace ℝ (Fin n)} (hg : Integrable g μ) :
    (EuclideanSpace ℝ (Fin n) →ᵇ EuclideanSpace ℝ (Fin n)) →L[ℝ] ℝ := by
  let I (X : EuclideanSpace ℝ (Fin n) →ᵇ EuclideanSpace ℝ (Fin n)) :=
    ∫ x : U, inner ℝ (g x) (X x) ∂μ
  have hi (X : EuclideanSpace ℝ (Fin n) →ᵇ EuclideanSpace ℝ (Fin n)) :
      Integrable (fun x : U => inner ℝ (g x) (X x)) μ :=
    integrable_inner_of_bound hg (X.continuous.comp continuous_subtype_val).aestronglyMeasurable
      (Eventually.of_forall fun x => X.norm_coe_le_norm x)
  let L : (EuclideanSpace ℝ (Fin n) →ᵇ EuclideanSpace ℝ (Fin n)) →ₗ[ℝ] ℝ :=
    { toFun := I
      map_add' X Y := by
        change (∫ x : U, inner ℝ (g x) ((X + Y) x) ∂μ) = _
        simp only [BoundedContinuousFunction.coe_add, Pi.add_apply, inner_add_right]
        exact integral_add (hi X) (hi Y)
      map_smul' c X := by
        change (∫ x : U, inner ℝ (g x) ((c • X) x) ∂μ) = c * I X
        simp only [BoundedContinuousFunction.coe_smul, real_inner_smul_right]
        exact integral_const_mul _ _ }
  apply L.mkContinuous (∫ x, ‖g x‖ ∂μ)
  intro X
  change ‖∫ x : U, inner ℝ (g x) (X x) ∂μ‖ ≤ _
  calc
    _ ≤ ∫ x, ‖g x‖ * ‖X‖ ∂μ := norm_integral_le_of_norm_le (hg.norm.mul_const ‖X‖)
      (Eventually.of_forall fun x => (norm_inner_le_norm _ _).trans
        (mul_le_mul_of_nonneg_left (X.norm_coe_le_norm x) (norm_nonneg _)))
    _ = _ := integral_mul_const _ _

lemma integrableDensityFunctional_apply {n : ℕ}
    {U : Set (EuclideanSpace ℝ (Fin n))} {μ : Measure U}
    {g : U → EuclideanSpace ℝ (Fin n)} (hg : Integrable g μ)
    (X : EuclideanSpace ℝ (Fin n) →ᵇ EuclideanSpace ℝ (Fin n)) :
    integrableDensityFunctional hg X = ∫ x : U, inner ℝ (g x) (X x) ∂μ := rfl

/-- Finite vector density measures are determined by supported smooth field pairings.
This transfers the distributional identity to an actual equality of vector measures. -/
theorem vectorDensity_eq_add_of_smooth_pairings {n : ℕ}
    {U : Set (EuclideanSpace ℝ (Fin n))} (hU : IsOpen U)
    {μ ν κ : Measure U} {a b c : U → EuclideanSpace ℝ (Fin n)}
    (ha : Integrable a μ) (hb : Integrable b ν) (hc : Integrable c κ)
    (h : ∀ X : EuclideanSpace ℝ (Fin n) →ᵇ EuclideanSpace ℝ (Fin n),
      ContDiff ℝ 1 X → HasCompactSupport X → tsupport X ⊆ U →
      (∫ x : U, inner ℝ (a x) (X x) ∂μ) =
        (∫ x : U, inner ℝ (b x) (X x) ∂ν) + ∫ x : U, inner ℝ (c x) (X x) ∂κ) :
    μ.withDensityᵥ a = ν.withDensityᵥ b + κ.withDensityᵥ c := by
  let : LocallyCompactSpace U := hU.locallyCompactSpace
  have hcc (X : EuclideanSpace ℝ (Fin n) →ᵇ EuclideanSpace ℝ (Fin n))
      (hcX : HasCompactSupport X) (hsX : tsupport X ⊆ U) :
      integrableDensityFunctional ha X =
        (integrableDensityFunctional hb + integrableDensityFunctional hc) X :=
    vectorFunctionals_eq_on_compactSupport hU _ _ h X hcX hsX
  have hcoord (i : Fin n) : μ.withDensityᵥ (fun x => a x i) =
      ν.withDensityᵥ (fun x => b x i) + κ.withDensityᵥ (fun x => c x i) := by
    apply withDensityVec_eq_add_of_integral_cc_eq (ha.eval_piLp i) (hb.eval_piLp i) (hc.eval_piLp i)
    intro φ
    let φ' := zeroExtendCC hU φ
    let X := coordinateTestField i φ'.toBoundedContinuousFunction
    have hcX : HasCompactSupport X := φ'.hasCompactSupport.smul_right
    have hsX : tsupport X ⊆ U :=
      (tsupport_smul_subset_left φ' (fun _ => EuclideanSpace.single i 1)).trans
        (tsupport_zeroExtendCC_subset hU φ)
    have hX := hcc X hcX hsX
    simp only [integrableDensityFunctional_apply, add_apply, X, coordinateTestField_apply,
      CompactlySupportedContinuousMap.toBoundedContinuousFunction_apply, φ', zeroExtendCC_apply_coe,
      real_inner_smul_right, EuclideanSpace.inner_single_right, one_mul, conj_trivial] at hX
    exact hX
  ext1 A hA
  apply PiLp.ext
  intro i
  have hi := congrArg (fun v : SignedMeasure U => v A) (hcoord i)
  rw [withDensityᵥ_apply (ha.eval_piLp i) hA,
    add_apply, withDensityᵥ_apply (hb.eval_piLp i) hA,
    withDensityᵥ_apply (hc.eval_piLp i) hA] at hi
  rw [withDensityᵥ_apply ha hA, add_apply, withDensityᵥ_apply hb hA, withDensityᵥ_apply hc hA]
  simpa only [PiLp.add_apply, eval_integral_piLp (ha.integrableOn.eval_piLp),
    eval_integral_piLp (hb.integrableOn.eval_piLp), eval_integral_piLp (hc.integrableOn.eval_piLp)]
    using hi

/-! ## Product rule as an equality of vector measures -/

/-- For any two polar representatives of `f` and `ζ f`, the product derivative is the
weighted original derivative plus the Lebesgue-density gradient term. All three vector
measures in this identity are finite, because the factor is compactly supported in `U`. -/
theorem IsDistributionalPolarRepresentation.mul_vectorMeasure_eq {n : ℕ}
    {U : Set (EuclideanSpace ℝ (Fin n))} (hU : IsOpen U)
    {f ζ : EuclideanSpace ℝ (Fin n) → ℝ}
    {ρ τ : Measure U} [IsFiniteMeasureOnCompacts ρ] [τ.Regular]
    {σ θ : U → EuclideanSpace ℝ (Fin n)}
    (hpolar : IsDistributionalPolarRepresentation f U ρ σ)
    (hprod : IsDistributionalPolarRepresentation (fun x => ζ x * f x) U τ θ)
    (hf : LocallyIntegrableOn f U) (hζ : ContDiff ℝ 1 ζ)
    (hcζ : HasCompactSupport ζ) (hsζ : tsupport ζ ⊆ U) :
    τ.withDensityᵥ θ = ρ.withDensityᵥ (fun x : U => ζ x • σ x) +
      (volume.comap (Subtype.val : U → EuclideanSpace ℝ (Fin n))).withDensityᵥ
        (fun x : U => f x • gradient ζ x) := by
  have hiprod := integrable_mul_compact_factor hf hζ.continuous hcζ hsζ
  have hlocal := hiprod.locallyIntegrable.locallyIntegrableOn U
  have hpre : (Subtype.val ⁻¹' U : Set U) = univ := by ext x; simp
  have hvar : variation (fun x => ζ x * f x) U = τ univ := by
    simpa only [hpre] using hprod.variation_eq_measure hU hU Subset.rfl hlocal
  let : IsFiniteMeasure τ := ⟨by
    rw [← hvar]
    exact ((variation_mono MeasurableSet.univ (subset_univ U)).trans
      (hpolar.variation_mul_le hf hζ hcζ hsζ)).trans_lt ENNReal.ofReal_lt_top⟩
  have hiθ : Integrable θ τ := Integrable.of_bound hprod.measurable.aestronglyMeasurable 1
    (hprod.norm_ae.mono fun _ hx => hx.le)
  have hiζσ := hpolar.integrable_smul_compact_factor hζ.continuous hcζ hsζ
  have hiG := integrable_smul_gradient hf hζ hcζ hsζ
  have hiGU : Integrable (fun x : U => f x • gradient ζ x)
      (volume.comap (Subtype.val : U → EuclideanSpace ℝ (Fin n))) :=
    (integrableOn_iff_comap_subtypeVal hU.measurableSet).mp hiG.integrableOn
  apply vectorDensity_eq_add_of_smooth_pairings hU hiθ hiζσ hiGU
  intro X hX hcX hsX
  have hpair := hprod.integral_divergence_eq hlocal hX hcX hsX
  have hwhole := hpolar.integral_mul_divergence_eq hf hζ hcζ hsζ hX hcX
  have hI : (∫ x in U, (ζ x * f x) * divergenceN X x) =
      ∫ x, (ζ x * f x) * divergenceN X x := by
    apply setIntegral_eq_integral_of_forall_compl_eq_zero
    intro x hx
    rw [divergenceN_eq_zero_of_notMem_tsupport (fun h => hx (hsX h)), mul_zero]
  rw [hI] at hpair
  have hG : (∫ x : U, inner ℝ (f x • gradient ζ x) (X x)
      ∂volume.comap (Subtype.val : U → EuclideanSpace ℝ (Fin n))) =
        ∫ x, inner ℝ (f x • gradient ζ x) (X x) := by
    rw [integral_subtype_comap hU.measurableSet
      (f := fun x => inner ℝ (f x • gradient ζ x) (X x))]
    apply setIntegral_eq_integral_of_forall_compl_eq_zero
    intro x hx
    rw [gradient_eq_zero_of_notMem_tsupport (fun h => hx (hsζ h)), smul_zero, inner_zero_left]
  calc
    (∫ x : U, inner ℝ (θ x) (X x) ∂τ) = ∫ x : U, inner ℝ (X x) (θ x) ∂τ :=
      integral_congr_ae (Eventually.of_forall fun x => real_inner_comm _ _)
    _ = -(∫ x, (ζ x * f x) * divergenceN X x) := hpair.symm
    _ = _ := hwhole
    _ = _ := by rw [hG]

/-- Blueprint `lem:bv-product-smooth`, strengthened to a C¹ compact factor. The original
derivative is a compatible local vector measure; multiplying it by the compact factor
produces the finite density measure in the displayed identity. -/
theorem bv_product_rule {n : ℕ} {U : Set (EuclideanSpace ℝ (Fin n))} (hU : IsOpen U)
    {f ζ : EuclideanSpace ℝ (Fin n) → ℝ} (hf : IsLocallyBVOn f U)
    (hζ : ContDiff ℝ 1 ζ) (hcζ : HasCompactSupport ζ) (hsζ : tsupport ζ ⊆ U) :
    IsBVOn (fun x => ζ x * f x) univ ∧
      ∃ ρ τ : Measure U, ∃ σ θ : U → EuclideanSpace ℝ (Fin n),
        ρ.Regular ∧ τ.Regular ∧
        IsDistributionalPolarRepresentation f U ρ σ ∧
        IsDistributionalPolarRepresentation (fun x => ζ x * f x) U τ θ ∧
        τ.withDensityᵥ θ = ρ.withDensityᵥ (fun x : U => ζ x • σ x) +
          (volume.comap (Subtype.val : U → EuclideanSpace ℝ (Fin n))).withDensityᵥ
            (fun x : U => f x • gradient ζ x) := by
  have hprodBV := hf.isBVOn_mul_compact_factor hU hζ hcζ hsζ
  have hiprod : Integrable (fun x => ζ x * f x) := integrableOn_univ.mp hprodBV.1
  have hprodloc : IsLocallyBVOn (fun x => ζ x * f x) U := by
    refine ⟨hiprod.locallyIntegrable.locallyIntegrableOn U, fun A _ _ _ => ?_⟩
    exact (variation_mono MeasurableSet.univ (subset_univ A)).trans_lt hprodBV.2
  obtain ⟨ρ, σ, hρ, _, hpolar⟩ := exists_distributional_polar_representation hU hf
  obtain ⟨τ, θ, hτ, _, hprod⟩ := exists_distributional_polar_representation hU hprodloc
  let : ρ.Regular := hρ
  let : τ.Regular := hτ
  exact ⟨hprodBV, ρ, τ, σ, θ, hρ, hτ, hpolar, hprod,
    hpolar.mul_vectorMeasure_eq hU hprod hf.1 hζ hcζ hsζ⟩

/-! ## L¹ mollification and support control -/

/-- Translation acts continuously in L¹, for scalar or vector-valued integrable functions. -/
lemma continuous_integral_norm_translate_sub {n : ℕ} {F : Type*}
    [NormedAddCommGroup F] {f : EuclideanSpace ℝ (Fin n) → F} (hf : Integrable f) :
    Continuous (fun y => ∫ x, ‖f (x - y) - f x‖) := by
  let g (y : EuclideanSpace ℝ (Fin n)) :
      C(EuclideanSpace ℝ (Fin n), EuclideanSpace ℝ (Fin n)) :=
    ⟨fun x => x - y, continuous_id.sub continuous_const⟩
  have hg : Continuous g := ContinuousMap.continuous_of_continuous_uncurry _ (by
    change Continuous (fun p : EuclideanSpace ℝ (Fin n) × EuclideanSpace ℝ (Fin n) => p.2 - p.1)
    fun_prop)
  have hm (y) : MeasurePreserving (g y) volume volume := measurePreserving_sub_right volume y
  have ht := (continuous_const (y := hf.toL1 f)).compMeasurePreservingLp hg hm (by simp)
  have hn := (ht.sub (continuous_const (y := hf.toL1 f))).norm
  convert hn using 1
  ext y
  rw [L1.norm_eq_integral_norm]
  apply integral_congr_ae
  filter_upwards [Lp.coeFn_sub (Lp.compMeasurePreserving (g y) (hm y) (hf.toL1 f))
      (hf.toL1 f), Lp.coeFn_compMeasurePreserving (hf.toL1 f) (hm y), hf.coeFn_toL1,
      (hm y).quasiMeasurePreserving.ae hf.coeFn_toL1] with x hx1 hx2 hx3 hx4
  exact (congrArg norm (hx1.trans (congrArg₂ (· - ·) (hx2.trans hx4) hx3))).symm

/-- Convolution by an integrable nonnegative kernel satisfies the L¹ norm bound. -/
lemma integral_norm_convolution_le {n : ℕ} {F : Type*}
    [NormedAddCommGroup F] [NormedSpace ℝ F] [CompleteSpace F]
    {k : EuclideanSpace ℝ (Fin n) → ℝ} {f : EuclideanSpace ℝ (Fin n) → F}
    (hk : Integrable k) (hf : Integrable f) (hk₀ : ∀ x, 0 ≤ k x) :
    (∫ x, ‖(k ⋆[ContinuousLinearMap.lsmul ℝ ℝ] f) x‖) ≤
      (∫ x, k x) * ∫ x, ‖f x‖ := by
  have hconv := hk.integrable_convolution (ContinuousLinearMap.lsmul ℝ ℝ) hf
  have hconvnorm := hk.integrable_convolution (ContinuousLinearMap.lsmul ℝ ℝ) hf.norm
  calc
    _ ≤ ∫ x, (k ⋆[ContinuousLinearMap.lsmul ℝ ℝ] (fun y => ‖f y‖)) x := by
      apply integral_mono_ae hconv.norm hconvnorm
      exact Eventually.of_forall fun x => by
        simpa only [convolution_def, ContinuousLinearMap.lsmul_apply, norm_smul,
          Real.norm_of_nonneg (hk₀ _), smul_eq_mul] using
          norm_integral_le_integral_norm (fun y => k y • f (x - y))
    _ = _ := integral_convolution (ContinuousLinearMap.lsmul ℝ ℝ) hk hf.norm

/-- The L¹ convolution error is bounded by the kernel average of translation errors. -/
lemma integral_norm_convolution_sub_le {n : ℕ} {F : Type*}
    [NormedAddCommGroup F] [NormedSpace ℝ F] [CompleteSpace F]
    {k : EuclideanSpace ℝ (Fin n) → ℝ} {f : EuclideanSpace ℝ (Fin n) → F}
    (hk : Integrable k) (hf : Integrable f) (hk₀ : ∀ x, 0 ≤ k x) (hk₁ : ∫ x, k x = 1) :
    (∫ x, ‖(k ⋆[ContinuousLinearMap.lsmul ℝ ℝ] f) x - f x‖) ≤
      ∫ y, k y * ∫ x, ‖f (x - y) - f x‖ := by
  have hconv := hk.convolution_integrand (ContinuousLinearMap.lsmul ℝ ℝ) hf
  have hprod := (hk.smul_prod hf).swap
  have hdiff : Integrable (fun p : EuclideanSpace ℝ (Fin n) × EuclideanSpace ℝ (Fin n) =>
      k p.2 • (f (p.1 - p.2) - f p.1)) (volume.prod volume) := by
    have hs := hconv.sub hprod
    change Integrable (fun p => k p.2 • f (p.1 - p.2) - k p.2 • f p.1)
      (volume.prod volume) at hs
    simpa only [smul_sub] using hs
  calc
    _ ≤ ∫ x, ∫ y, ‖k y • (f (x - y) - f x)‖ := by
      apply integral_mono_ae
        ((hk.integrable_convolution (ContinuousLinearMap.lsmul ℝ ℝ) hf).sub hf).norm
        hdiff.integral_norm_prod_left
      filter_upwards [hconv.prod_right_ae] with x hx
      change Integrable (fun y => k y • f (x - y)) at hx
      have hId : (k ⋆[ContinuousLinearMap.lsmul ℝ ℝ] f) x - f x =
          ∫ y, k y • (f (x - y) - f x) := by
        simp only [convolution_def, ContinuousLinearMap.lsmul_apply, smul_sub]
        rw [integral_sub hx (hk.smul_const (f x)), integral_smul_const, hk₁, one_smul]
      change ‖(k ⋆[ContinuousLinearMap.lsmul ℝ ℝ] f) x - f x‖ ≤ _
      rw [hId]
      exact norm_integral_le_integral_norm _
    _ = ∫ y, ∫ x, ‖k y • (f (x - y) - f x)‖ := integral_integral_swap hdiff.norm
    _ = _ := by
      simp_rw [norm_smul, Real.norm_of_nonneg (hk₀ _), integral_const_mul]


/-- A supported probability kernel inherits any uniform bound on nearby translation errors. -/
lemma integral_norm_convolution_sub_le_of_support {n : ℕ} {F : Type*}
    [NormedAddCommGroup F] [NormedSpace ℝ F] [CompleteSpace F]
    {k : EuclideanSpace ℝ (Fin n) → ℝ} {f : EuclideanSpace ℝ (Fin n) → F}
    (hk : Integrable k) (hf : Integrable f) (hk₀ : ∀ x, 0 ≤ k x) (hk₁ : ∫ x, k x = 1)
    {ε : ℝ} (hε : ∀ y ∈ Function.support k, (∫ x, ‖f (x - y) - f x‖) ≤ ε) :
    (∫ x, ‖(k ⋆[ContinuousLinearMap.lsmul ℝ ℝ] f) x - f x‖) ≤ ε := by
  calc
    _ ≤ ∫ y, k y * ∫ x, ‖f (x - y) - f x‖ :=
      integral_norm_convolution_sub_le hk hf hk₀ hk₁
    _ ≤ ∫ y, k y * ε := by
      apply integral_mono_of_nonneg
        (Eventually.of_forall fun y => mul_nonneg (hk₀ y) (integral_nonneg fun _ => norm_nonneg _))
        (hk.mul_const ε)
      exact Eventually.of_forall fun y => by
        by_cases hy : y ∈ Function.support k
        · exact mul_le_mul_of_nonneg_left (hε y hy) (hk₀ y)
        · change k y * _ ≤ k y * ε
          rw [Function.notMem_support.mp hy, zero_mul, zero_mul]
    _ = ε := by rw [integral_mul_const, hk₁, one_mul]

/-- Normalized bump convolution converges in global L¹ for every integrable vector function. -/
theorem tendsto_integral_norm_bump_convolution_sub {n : ℕ} {F : Type*}
    [NormedAddCommGroup F] [NormedSpace ℝ F] [CompleteSpace F]
    {f : EuclideanSpace ℝ (Fin n) → F} (hf : Integrable f)
    {ι : Type*} {l : Filter ι} {φ : ι → ContDiffBump (0 : EuclideanSpace ℝ (Fin n))}
    (hφ : Tendsto (fun i => (φ i).rOut) l (𝓝 0)) :
    Tendsto (fun i => ∫ x, ‖((φ i).normed volume ⋆[ContinuousLinearMap.lsmul ℝ ℝ] f) x - f x‖)
      l (𝓝 0) := by
  rw [Metric.tendsto_nhds]
  intro ε hε
  obtain ⟨δ, hδ, hb⟩ := Metric.continuousAt_iff.mp
    (continuous_integral_norm_translate_sub hf).continuousAt (ε / 2) (half_pos hε)
  have hsmall : ∀ᶠ i in l, (φ i).rOut < δ := (tendsto_order.mp hφ).2 δ hδ
  filter_upwards [hsmall] with i hi
  rw [Real.dist_eq, sub_zero, abs_of_nonneg (integral_nonneg fun _ => norm_nonneg _)]
  apply lt_of_le_of_lt (integral_norm_convolution_sub_le_of_support (φ i).integrable_normed hf
    (φ i).nonneg_normed (φ i).integral_normed ?_) (half_lt_self hε)
  intro y hy
  rw [(φ i).support_normed_eq] at hy
  have hyδ : dist y 0 < δ := (mem_ball.mp hy).trans hi
  have hyb := hb hyδ
  simp only [sub_zero, sub_self, norm_zero, integral_zero, Real.dist_eq] at hyb
  exact (le_abs_self _).trans hyb.le


/-- Bump convolution expands the support by at most its outer radius. -/
lemma tsupport_bump_convolution_subset {n : ℕ} {F : Type*}
    [NormedAddCommGroup F] [NormedSpace ℝ F]
    (φ : ContDiffBump (0 : EuclideanSpace ℝ (Fin n)))
    {f : EuclideanSpace ℝ (Fin n) → F} {δ : ℝ} (hδ : φ.rOut ≤ δ) :
    tsupport (φ.normed volume ⋆[ContinuousLinearMap.lsmul ℝ ℝ] f) ⊆
      cthickening δ (tsupport f) := by
  apply closure_minimal _ isClosed_cthickening
  intro x hx
  obtain ⟨a, ha, b, hb, rfl⟩ := support_convolution_subset_swap
    (ContinuousLinearMap.lsmul ℝ ℝ) hx
  apply mem_cthickening_of_dist_le (a + b) a δ _ (subset_closure ha)
  have hb' : ‖b‖ < φ.rOut := by
    simpa only [φ.support_normed_eq, mem_ball_zero_iff] using hb
  simpa only [dist_eq_norm, add_sub_cancel_left] using hb'.le.trans hδ

/-- One can meet an arbitrary L¹ error budget while choosing an arbitrarily small radius. -/
theorem exists_bump_l1_approximation {n : ℕ} {F : Type*}
    [NormedAddCommGroup F] [NormedSpace ℝ F] [CompleteSpace F]
    {f : EuclideanSpace ℝ (Fin n) → F} (hf : Integrable f)
    {ε δ : ℝ} (hε : 0 < ε) (hδ : 0 < δ) :
    ∃ φ : ContDiffBump (0 : EuclideanSpace ℝ (Fin n)), φ.rOut < δ ∧
      (∫ x, ‖(φ.normed volume ⋆[ContinuousLinearMap.lsmul ℝ ℝ] f) x - f x‖) < ε := by
  let φ (j : ℕ) : ContDiffBump (0 : EuclideanSpace ℝ (Fin n)) :=
    ⟨(δ / ((j : ℝ) + 1)) / 2, δ / ((j : ℝ) + 1), by positivity,
      half_lt_self (by positivity)⟩
  have hφlim : Tendsto (fun j => (φ j).rOut) atTop (𝓝 0) := by
    simpa only [mul_one_div, mul_zero] using
      (tendsto_one_div_add_atTop_nhds_zero_nat (𝕜 := ℝ)).const_mul δ
  have herror := (tendsto_order.mp (tendsto_integral_norm_bump_convolution_sub hf hφlim)).2 ε hε
  obtain ⟨j, hj, hj'⟩ := ((tendsto_order.mp hφlim).2 δ hδ |>.and herror).exists
  exact ⟨φ j, hj, hj'⟩

/-- A compactly supported integrable function has smooth compactly supported global L¹
approximations inside any open neighborhood of its support. The approximant's L¹ norm
does not exceed the original norm. This also applies to vector-valued correction terms. -/
theorem exists_smooth_compact_l1_approximation {n : ℕ} {F : Type*}
    [NormedAddCommGroup F] [NormedSpace ℝ F] [CompleteSpace F]
    {U : Set (EuclideanSpace ℝ (Fin n))} (hU : IsOpen U)
    {f : EuclideanSpace ℝ (Fin n) → F} (hf : Integrable f)
    (hcf : HasCompactSupport f) (hsf : tsupport f ⊆ U) {ε : ℝ} (hε : 0 < ε) :
    ∃ g : EuclideanSpace ℝ (Fin n) → F,
      ContDiff ℝ (⊤ : ℕ∞) g ∧ HasCompactSupport g ∧ tsupport g ⊆ U ∧
      Integrable g ∧ (∫ x, ‖g x - f x‖) < ε ∧ (∫ x, ‖g x‖) ≤ ∫ x, ‖f x‖ := by
  obtain ⟨δ, hδ, hδU⟩ := hcf.exists_cthickening_subset_open hU hsf
  obtain ⟨φ, hφδ, hφε⟩ := exists_bump_l1_approximation hf hε hδ
  refine ⟨φ.normed volume ⋆[ContinuousLinearMap.lsmul ℝ ℝ] f,
    φ.hasCompactSupport_normed.contDiff_convolution_left _ φ.contDiff_normed hf.locallyIntegrable,
    φ.hasCompactSupport_normed.convolution _ hcf,
    (tsupport_bump_convolution_subset φ hφδ.le).trans hδU,
    φ.integrable_normed.integrable_convolution _ hf, hφε, ?_⟩
  simpa only [φ.integral_normed, one_mul] using
    integral_norm_convolution_le φ.integrable_normed hf φ.nonneg_normed


/-! ## Convolution of density measures and differentiation of kernels -/

/-- Fubini integrability for convolution of a finite vector density with a continuous kernel. -/
lemma integrable_measure_convolution_integrand {n : ℕ} {F S : Type*}
    [NormedAddCommGroup F] [NormedSpace ℝ F] [MeasurableSpace S]
    {μ : Measure S} [SFinite μ] {T : S → EuclideanSpace ℝ (Fin n)} (hT : Measurable T)
    {k : EuclideanSpace ℝ (Fin n) → ℝ} (hk : Integrable k) (hkc : Continuous k)
    {g : S → F} (hg : Integrable g μ) :
    Integrable (fun p : EuclideanSpace ℝ (Fin n) × S => k (p.1 - T p.2) • g p.2)
      (volume.prod μ) := by
  have hm : AEStronglyMeasurable
      (fun p : EuclideanSpace ℝ (Fin n) × S => k (p.1 - T p.2) • g p.2)
      (volume.prod μ) :=
    (hkc.stronglyMeasurable.comp_measurable
      (measurable_fst.sub (hT.comp measurable_snd))).aestronglyMeasurable.smul
        hg.aestronglyMeasurable.comp_snd
  apply (integrable_prod_iff' hm).mpr
  refine ⟨Eventually.of_forall (fun y => (hk.comp_sub_right (T y)).smul_const (g y)), ?_⟩
  simpa only [norm_smul, integral_mul_const, integral_sub_right_eq_self (fun x => ‖k x‖)] using
    hg.norm.const_mul (∫ x, ‖k x‖)

/-- Convolution of a vector density obeys the expected L¹ bound, including measures on an
open subtype. This is the measure term in the strict-approximation estimate. -/
lemma integral_norm_measure_convolution_le {n : ℕ} {F S : Type*}
    [NormedAddCommGroup F] [NormedSpace ℝ F] [CompleteSpace F] [MeasurableSpace S]
    {μ : Measure S} [SFinite μ] {T : S → EuclideanSpace ℝ (Fin n)} (hT : Measurable T)
    {k : EuclideanSpace ℝ (Fin n) → ℝ} (hk : Integrable k) (hkc : Continuous k)
    (hk₀ : ∀ x, 0 ≤ k x) {g : S → F} (hg : Integrable g μ) :
    (∫ x, ‖∫ y, k (x - T y) • g y ∂μ‖) ≤ (∫ x, k x) * ∫ y, ‖g y‖ ∂μ := by
  have hi := integrable_measure_convolution_integrand hT hk hkc hg
  calc
    _ ≤ ∫ x, ∫ y, ‖k (x - T y) • g y‖ ∂μ :=
      integral_mono hi.integral_prod_left.norm hi.integral_norm_prod_left
        (fun _ => norm_integral_le_integral_norm _)
    _ = ∫ y, (∫ x, ‖k (x - T y) • g y‖) ∂μ := integral_integral_swap hi.norm
    _ = _ := by
      simp_rw [norm_smul, Real.norm_of_nonneg (hk₀ _), integral_mul_const,
        integral_sub_right_eq_self k, integral_const_mul]

/-- Differentiate a scalar convolution by differentiating its compact C¹ kernel. -/
lemma gradient_convolution_right {n : ℕ}
    {f k : EuclideanSpace ℝ (Fin n) → ℝ}
    (hf : LocallyIntegrable f) (hk : ContDiff ℝ 1 k) (hck : HasCompactSupport k)
    (x : EuclideanSpace ℝ (Fin n)) :
    gradient (f ⋆[ContinuousLinearMap.lsmul ℝ ℝ] k) x =
      ∫ y, f y • gradient k (x - y) := by
  have hpre : (ContinuousLinearMap.lsmul ℝ ℝ (E := ℝ)).precompR
      (EuclideanSpace ℝ (Fin n)) = ContinuousLinearMap.lsmul ℝ ℝ := by
    ext
    rfl
  have hd := (hck.hasFDerivAt_convolution_right (μ := volume)
    (ContinuousLinearMap.lsmul ℝ ℝ) hf hk x).fderiv
  rw [hpre] at hd
  let D := (toDual ℝ (EuclideanSpace ℝ (Fin n))).symm.toContinuousLinearEquiv.toContinuousLinearMap
  change D (fderiv ℝ (f ⋆[ContinuousLinearMap.lsmul ℝ ℝ] k) x) = _
  rw [hd]
  have hi := (hck.fderiv ℝ).convolutionExists_right (μ := volume)
    (ContinuousLinearMap.lsmul ℝ ℝ) hf (hk.continuous_fderiv one_ne_zero) x
  rw [convolution_def, ← D.integral_comp_comm hi]
  simp only [ContinuousLinearMap.lsmul_apply, map_smul]
  rfl

/-- The kernel-first form of the scalar convolution gradient identity. -/
lemma gradient_convolution_left {n : ℕ}
    {f k : EuclideanSpace ℝ (Fin n) → ℝ}
    (hf : LocallyIntegrable f) (hk : ContDiff ℝ 1 k) (hck : HasCompactSupport k)
    (x : EuclideanSpace ℝ (Fin n)) :
    gradient (k ⋆[ContinuousLinearMap.lsmul ℝ ℝ] f) x =
      ∫ y, f y • gradient k (x - y) := by
  have hflip : (ContinuousLinearMap.lsmul ℝ ℝ (E := ℝ)).flip =
      ContinuousLinearMap.lsmul ℝ ℝ := by
    ext
    exact mul_comm _ _
  have hc : k ⋆[ContinuousLinearMap.lsmul ℝ ℝ] f =
      f ⋆[ContinuousLinearMap.lsmul ℝ ℝ] k := by
    simpa only [hflip] using
      (convolution_flip (ContinuousLinearMap.lsmul ℝ ℝ) (f := f) (g := k))
  rw [hc]
  exact gradient_convolution_right hf hk hck x

/-! ## BV mollification and its strict gradient limit -/

/-- Differentiating a translated reflection introduces the expected minus sign. -/
lemma fderiv_comp_const_sub {n : ℕ} {k : EuclideanSpace ℝ (Fin n) → ℝ}
    (hk : ContDiff ℝ 1 k) (x y v : EuclideanSpace ℝ (Fin n)) :
    fderiv ℝ (fun z => k (x - z)) y v = -fderiv ℝ k (x - y) v := by
  have h := ((hk.differentiable one_ne_zero (x - y)).hasFDerivAt.comp y
    ((hasFDerivAt_const x y).sub (hasFDerivAt_id y))).fderiv
  simpa [Function.comp_def] using congrArg (fun A => A v) h

/-- Mollification differentiates the polar derivative measure of a locally BV function. -/
theorem IsDistributionalPolarRepresentation.gradient_convolution_eq {n : ℕ}
    {f k : EuclideanSpace ℝ (Fin n) → ℝ}
    {ρ : Measure (univ : Set (EuclideanSpace ℝ (Fin n)))} [IsFiniteMeasureOnCompacts ρ]
    {σ : ↑(univ : Set (EuclideanSpace ℝ (Fin n))) → EuclideanSpace ℝ (Fin n)}
    (hpolar : IsDistributionalPolarRepresentation f univ ρ σ)
    (hf : LocallyIntegrable f) (hk : ContDiff ℝ 1 k) (hck : HasCompactSupport k)
    (x : EuclideanSpace ℝ (Fin n)) :
    gradient (k ⋆[ContinuousLinearMap.lsmul ℝ ℝ] f) x =
      ∫ y, k (x - y) • σ y ∂ρ := by
  let φ : C_c(EuclideanSpace ℝ (Fin n), ℝ) :=
    ⟨⟨fun y => k (x - y), hk.continuous.comp (continuous_const.sub continuous_id)⟩,
      hck.comp_homeomorph (Homeomorph.subLeft x)⟩
  have hφ : ContDiff ℝ 1 φ := hk.comp (contDiff_const.sub contDiff_id)
  have hiσ := hpolar.integrable_smul_compact_factor hφ.continuous φ.hasCompactSupport
    (subset_univ _)
  have hcgrad : HasCompactSupport (gradient k) :=
    hck.of_isClosed_subset (isClosed_tsupport _) (tsupport_gradient_subset k)
  have hiG := hcgrad.convolutionExists_right (μ := volume) (ContinuousLinearMap.lsmul ℝ ℝ)
    hf (continuous_gradient_of_contDiff hk) x
  change Integrable (fun y => f y • gradient k (x - y)) at hiG
  change Integrable (fun y : ↑(univ : Set (EuclideanSpace ℝ (Fin n))) =>
    k (x - y) • σ y) ρ at hiσ
  rw [gradient_convolution_left hf hk hck x]
  apply PiLp.ext
  intro i
  rw [eval_integral_piLp hiG.eval_piLp, eval_integral_piLp hiσ.eval_piLp]
  have h := hpolar.test_eq i φ hφ (subset_univ _)
  simp only [setIntegral_univ] at h
  have hderiv (y) : fderiv ℝ φ y (EuclideanSpace.single i 1) =
      -gradient k (x - y) i := by
    rw [gradient_apply_eq_fderiv_single]
    exact fderiv_comp_const_sub hk x y _
  simp_rw [hderiv, mul_neg, integral_neg, neg_neg] at h
  change (∫ y, f y * gradient k (x - y) i) =
    ∫ y : ↑(univ : Set (EuclideanSpace ℝ (Fin n))), k (x - y) * σ y i ∂ρ at h
  simpa only [PiLp.smul_apply, smul_eq_mul] using h

/-- A normalized bump does not increase the total derivative mass. Global local
integrability and finite variation suffice; no global L¹ hypothesis is needed here. -/
theorem integrable_gradient_bump_convolution_and_bound {n : ℕ}
    {f : EuclideanSpace ℝ (Fin n) → ℝ} (hf : LocallyIntegrable f)
    (hfin : variation f univ < ∞) (φ : ContDiffBump (0 : EuclideanSpace ℝ (Fin n))) :
    Integrable (gradient (φ.normed volume ⋆[ContinuousLinearMap.lsmul ℝ ℝ] f)) ∧
      ENNReal.ofReal (∫ x, ‖gradient (φ.normed volume ⋆[ContinuousLinearMap.lsmul ℝ ℝ] f) x‖) ≤
        variation f univ := by
  obtain ⟨ρ, σ, _, hpolar, hvar⟩ := exists_polar_representation_with_variation isOpen_univ
    (isLocallyBVOn_of_variation_lt_top isOpen_univ (hf.locallyIntegrableOn univ) hfin)
  have hmass : variation f univ = ρ univ := by
    simpa only [preimage_univ] using hvar univ isOpen_univ (Subset.rfl)
  let : IsFiniteMeasure ρ := ⟨by rw [← hmass]; exact hfin⟩
  have hiσ : Integrable σ ρ := Integrable.of_bound hpolar.measurable.aestronglyMeasurable 1
    (hpolar.norm_ae.mono fun _ hx => hx.le)
  have hgrad (x : EuclideanSpace ℝ (Fin n)) := hpolar.gradient_convolution_eq hf
    (φ.contDiff_normed (μ := volume)) φ.hasCompactSupport_normed x
  have hprod := integrable_measure_convolution_integrand measurable_subtype_coe
    φ.integrable_normed φ.continuous_normed hiσ
  have hbound := integral_norm_measure_convolution_le measurable_subtype_coe
    φ.integrable_normed φ.continuous_normed φ.nonneg_normed hiσ
  have hnorm : (∫ y, ‖σ y‖ ∂ρ) = (variation f univ).toReal := by
    calc
      _ = ∫ _ : (univ : Set (EuclideanSpace ℝ (Fin n))), (1 : ℝ) ∂ρ :=
        integral_congr_ae hpolar.norm_ae
      _ = _ := by simp [Measure.real, hmass]
  refine ⟨?_, ?_⟩
  · simpa only [← hgrad] using hprod.integral_prod_left
  · have hb : (∫ x, ‖gradient (φ.normed volume ⋆[ContinuousLinearMap.lsmul ℝ ℝ] f) x‖) ≤
        (variation f univ).toReal := by
      simpa only [← hgrad, φ.integral_normed, one_mul, hnorm] using hbound
    exact (ENNReal.ofReal_le_ofReal hb).trans_eq (ENNReal.ofReal_toReal hfin.ne)


/-- The variation of a C¹ function is bounded by the integral of its gradient. -/
lemma variation_le_integral_norm_gradient {n : ℕ} {f : EuclideanSpace ℝ (Fin n) → ℝ}
    (hf : ContDiff ℝ 1 f) (hgrad : Integrable (gradient f)) :
    variation f univ ≤ ENNReal.ofReal (∫ x, ‖gradient f x‖) := by
  apply iSup_le
  intro X
  apply iSup_le
  intro hX
  apply ENNReal.ofReal_le_ofReal
  rw [setIntegral_univ]
  have hi := integrable_inner_of_bound hgrad hX.1.continuous.aestronglyMeasurable
    (Eventually.of_forall hX.2.2.2)
  have hfdiv := integrable_mul_divergenceN
    (hf.continuous.locallyIntegrable.locallyIntegrableOn univ)
    hX.1 hX.2.1 hX.2.2.1
  have hzero := integral_divergenceN_eq_zero (hf.smul hX.1) hX.2.1.smul_left
  change (∫ x, divergenceN (fun y => f y • X y) x) = 0 at hzero
  simp_rw [divergenceN_smul hf hX.1] at hzero
  rw [integral_add hfdiv hi] at hzero
  have hnorm : ‖∫ x, inner ℝ (gradient f x) (X x)‖ ≤ ∫ x, ‖gradient f x‖ := by
    apply norm_integral_le_of_norm_le hgrad.norm
    exact Eventually.of_forall fun x => by
      simpa only [mul_one] using (norm_inner_le_norm (gradient f x) (X x)).trans
        (mul_le_mul_of_nonneg_left (hX.2.2.2 x) (norm_nonneg _))
  have habs := neg_le_abs (∫ x, inner ℝ (gradient f x) (X x))
  rw [Real.norm_eq_abs] at hnorm
  linarith

/-- Global BV mollification is strict before the final compact cutoffs: the gradient
integrals tend to the original variation. -/
theorem tendsto_integral_norm_gradient_bump_convolution {n : ℕ}
    {f : EuclideanSpace ℝ (Fin n) → ℝ} (hf : IsBVOn f univ)
    {φ : ℕ → ContDiffBump (0 : EuclideanSpace ℝ (Fin n))}
    (hφ : Tendsto (fun j => (φ j).rOut) atTop (𝓝 0)) :
    Tendsto (fun j => ∫ x,
      ‖gradient ((φ j).normed volume ⋆[ContinuousLinearMap.lsmul ℝ ℝ] f) x‖)
      atTop (𝓝 (variation f univ).toReal) := by
  have hif : Integrable f := integrableOn_univ.mp hf.1
  let g (j : ℕ) := (φ j).normed volume ⋆[ContinuousLinearMap.lsmul ℝ ℝ] f
  have hg (j) : ContDiff ℝ 1 (g j) :=
    (φ j).hasCompactSupport_normed.contDiff_convolution_left _
      (φ j).contDiff_normed hif.locallyIntegrable
  have hig (j) : Integrable (g j) := (φ j).integrable_normed.integrable_convolution _ hif
  have hgrad (j) : Integrable (gradient (g j)) ∧
      ENNReal.ofReal (∫ x, ‖gradient (g j) x‖) ≤ variation f univ :=
    integrable_gradient_bump_convolution_and_bound hif.locallyIntegrable hf.2 (φ j)
  have hl1 : Tendsto (fun j => ∫ x, |g j x - f x|) atTop (𝓝 0) := by
    simpa only [Real.norm_eq_abs] using tendsto_integral_norm_bump_convolution_sub hif hφ
  have hlocal (K : Set (EuclideanSpace ℝ (Fin n))) :
      Tendsto (fun j => ∫ x in K, |g j x - f x|) atTop (𝓝 0) := by
    apply squeeze_zero (fun j => integral_nonneg fun _ => abs_nonneg _) (fun j => ?_) hl1
    exact setIntegral_le_integral ((hig j).sub hif).abs (Eventually.of_forall fun _ => abs_nonneg _)
  have hlsc := variation_le_liminf_of_locally_l1 isOpen_univ
    (fun j => (hig j).locallyIntegrable.locallyIntegrableOn univ)
    (hif.locallyIntegrable.locallyIntegrableOn univ) (fun K _ _ => hlocal K)
  have hlower : variation f univ ≤
      liminf (fun j => ENNReal.ofReal (∫ x, ‖gradient (g j) x‖)) atTop :=
    hlsc.trans (liminf_le_liminf (Eventually.of_forall fun j =>
      variation_le_integral_norm_gradient (hg j) (hgrad j).1))
  have ht : Tendsto (fun j => ENNReal.ofReal (∫ x, ‖gradient (g j) x‖)) atTop
      (𝓝 (variation f univ)) := by
    apply tendsto_order.mpr
    constructor
    · intro a ha
      exact eventually_lt_of_lt_liminf (ha.trans_le hlower)
    · intro a ha
      exact Eventually.of_forall fun j => (hgrad j).2.trans_lt ha
  have hreal := (ENNReal.continuousAt_toReal hf.2.ne).tendsto.comp ht
  simpa only [Function.comp_def,
    ENNReal.toReal_ofReal (integral_nonneg fun _ => norm_nonneg _)] using hreal


/-! ## Compact cutoffs and whole-space strict approximation -/

lemma gradient_mul {n : ℕ} {f g : EuclideanSpace ℝ (Fin n) → ℝ}
    (hf : ContDiff ℝ 1 f) (hg : ContDiff ℝ 1 g) (x : EuclideanSpace ℝ (Fin n)) :
    gradient (fun y => f y * g y) x = f x • gradient g x + g x • gradient f x := by
  apply PiLp.ext
  intro i
  rw [gradient_apply_eq_fderiv_single, fderiv_fun_mul (hf.differentiable one_ne_zero x)
    (hg.differentiable one_ne_zero x)]
  simp only [add_apply, smul_apply, PiLp.add_apply, PiLp.smul_apply, smul_eq_mul,
    gradient_apply_eq_fderiv_single]

lemma gradient_comp_const_smul {n : ℕ} {f : EuclideanSpace ℝ (Fin n) → ℝ}
    (hf : ContDiff ℝ 1 f) (a : ℝ) (x : EuclideanSpace ℝ (Fin n)) :
    gradient (fun y => f (a • y)) x = a • gradient f (a • x) := by
  have h := ((hf.differentiable one_ne_zero (a • x)).hasFDerivAt.comp x
    ((hasFDerivAt_id x).const_smul a)).fderiv
  apply PiLp.ext
  intro i
  rw [gradient_apply_eq_fderiv_single]
  change fderiv ℝ (f ∘ fun y => a • y) x (EuclideanSpace.single i 1) = _
  rw [h]
  simp only [ContinuousLinearMap.comp_apply, smul_apply, ContinuousLinearMap.id_apply,
    map_smul, PiLp.smul_apply, gradient_apply_eq_fderiv_single]

/-- Smooth compact cutoffs tend pointwise to one and have gradients tending uniformly to zero. -/
theorem exists_smooth_exhaustion_cutoffs {n : ℕ} :
    ∃ χ : ℕ → EuclideanSpace ℝ (Fin n) → ℝ, ∃ C : ℝ, 0 ≤ C ∧
      (∀ j, ContDiff ℝ (⊤ : ℕ∞) (χ j) ∧ HasCompactSupport (χ j) ∧
        (∀ x, 0 ≤ χ j x ∧ χ j x ≤ 1) ∧
        (∀ x, ‖gradient (χ j) x‖ ≤ C / ((j : ℝ) + 1))) ∧
      (∀ x, Tendsto (fun j => χ j x) atTop (𝓝 1)) := by
  let φ : ContDiffBump (0 : EuclideanSpace ℝ (Fin n)) := ⟨1, 2, zero_lt_one, one_lt_two⟩
  have hgradc : HasCompactSupport (gradient φ) :=
    φ.hasCompactSupport.of_isClosed_subset (isClosed_tsupport _) (tsupport_gradient_subset φ)
  obtain ⟨C, hC⟩ := hgradc.exists_bound_of_continuous
    (continuous_gradient_of_contDiff φ.contDiff)
  have hC₀ : 0 ≤ C := (norm_nonneg (gradient φ 0)).trans (hC 0)
  let χ (j : ℕ) (x : EuclideanSpace ℝ (Fin n)) := φ (((j : ℝ) + 1)⁻¹ • x)
  refine ⟨χ, C, hC₀, fun j => ?_, fun x => ?_⟩
  · have ha : 0 < ((j : ℝ) + 1)⁻¹ := by positivity
    refine ⟨φ.contDiff.comp
      (show ContDiff ℝ (⊤ : ℕ∞) (fun x : EuclideanSpace ℝ (Fin n) =>
        ((j : ℝ) + 1)⁻¹ • x) from contDiff_id.const_smul _), ?_,
      fun x => ⟨φ.nonneg, φ.le_one⟩, fun x => ?_⟩
    · exact φ.hasCompactSupport.comp_homeomorph (Homeomorph.smulOfNeZero _ ha.ne')
    · rw [gradient_comp_const_smul φ.contDiff]
      rw [norm_smul, Real.norm_of_nonneg ha.le]
      calc
        _ ≤ ((j : ℝ) + 1)⁻¹ * C := mul_le_mul_of_nonneg_left (hC _) ha.le
        _ = C / ((j : ℝ) + 1) := by ring
  · have ha : Tendsto (fun j : ℕ => ((j : ℝ) + 1)⁻¹) atTop (𝓝 0) := by
      simpa only [one_div] using (tendsto_one_div_add_atTop_nhds_zero_nat (𝕜 := ℝ))
    have ha' : Tendsto (fun j : ℕ => ((j : ℝ) + 1)⁻¹ • x) atTop (𝓝 0) := by
      simpa only [zero_smul] using ha.smul_const x
    have ht := (φ.continuous.tendsto 0).comp ha'
    have hφ₀ : φ 0 = 1 := φ.one_of_mem_closedBall (by simp [φ])
    simpa only [Function.comp_def, zero_smul, hφ₀, χ] using ht

lemma norm_smul_sub_self_le {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]
    {a : ℝ} (ha₀ : 0 ≤ a) (ha₁ : a ≤ 1) (v : F) : ‖a • v - v‖ ≤ ‖v‖ := by
  have heq : a • v - v = (a - 1) • v := by rw [sub_smul, one_smul]
  rw [heq, norm_smul, Real.norm_eq_abs, abs_of_nonpos (sub_nonpos.mpr ha₁)]
  nlinarith [norm_nonneg v]

/-- Bounded cutoffs tending pointwise to one converge in L¹ after multiplication by any
integrable scalar or vector function. -/
theorem tendsto_integral_norm_cutoff_error {n : ℕ} {F : Type*}
    [NormedAddCommGroup F] [NormedSpace ℝ F]
    {χ : ℕ → EuclideanSpace ℝ (Fin n) → ℝ}
    (hχ : ∀ j, Continuous (χ j)) (hb : ∀ j x, 0 ≤ χ j x ∧ χ j x ≤ 1)
    (hlim : ∀ x, Tendsto (fun j => χ j x) atTop (𝓝 1))
    {f : EuclideanSpace ℝ (Fin n) → F} (hf : Integrable f) :
    Tendsto (fun j => ∫ x, ‖χ j x • f x - f x‖) atTop (𝓝 0) := by
  have h := tendsto_integral_of_dominated_convergence (fun x => ‖f x‖)
    (fun j => (((hχ j).aestronglyMeasurable.smul hf.aestronglyMeasurable).sub
      hf.aestronglyMeasurable).norm) hf.norm
    (fun j => Eventually.of_forall fun x => by
      rw [norm_norm]
      exact norm_smul_sub_self_le (hb j x).1 (hb j x).2 (f x))
    (f := fun _ => (0 : ℝ)) (Eventually.of_forall fun x => by
      simpa only [one_smul, sub_self, norm_zero, Pi.sub_apply, Pi.smul_apply'] using
        (((hlim x).smul_const (f x)).sub (tendsto_const_nhds (x := f x))).norm)
  simpa only [integral_zero, Pi.sub_apply, Pi.smul_apply'] using h

/-- The error from differentiating a cutoff tends to zero in L¹ under a uniform
`C / (j + 1)` gradient bound. -/
theorem tendsto_integral_norm_cutoff_gradient {n : ℕ}
    {χ : ℕ → EuclideanSpace ℝ (Fin n) → ℝ}
    {C : ℝ} (hb : ∀ j x, ‖gradient (χ j) x‖ ≤ C / ((j : ℝ) + 1))
    {f : EuclideanSpace ℝ (Fin n) → ℝ} (hf : Integrable f) :
    Tendsto (fun j => ∫ x, ‖f x • gradient (χ j) x‖) atTop (𝓝 0) := by
  have hbound (j) : (∫ x, ‖f x • gradient (χ j) x‖) ≤
      (∫ x, ‖f x‖) * (C / ((j : ℝ) + 1)) := by
    calc
      _ ≤ ∫ x, ‖f x‖ * (C / ((j : ℝ) + 1)) := by
        apply integral_mono_of_nonneg (Eventually.of_forall fun _ => norm_nonneg _)
          (hf.norm.mul_const _)
        exact Eventually.of_forall fun x => by
          change ‖f x • gradient (χ j) x‖ ≤ ‖f x‖ * (C / ((j : ℝ) + 1))
          rw [norm_smul]
          exact mul_le_mul_of_nonneg_left (hb j x) (norm_nonneg _)
      _ = _ := integral_mul_const _ _
  have ht : Tendsto (fun j : ℕ => (∫ x, ‖f x‖) * (C / ((j : ℝ) + 1))) atTop (𝓝 0) := by
    simpa only [mul_one_div, mul_zero] using
      ((tendsto_one_div_add_atTop_nhds_zero_nat (𝕜 := ℝ)).const_mul C).const_mul
        (∫ x, ‖f x‖)
  exact squeeze_zero (fun _ => integral_nonneg fun _ => norm_nonneg _) hbound ht


/-- Compact cutoffs approximate a smooth integrable function and its integrable gradient
simultaneously in L¹. -/
theorem exists_smooth_compact_gradient_approximation {n : ℕ}
    {f : EuclideanSpace ℝ (Fin n) → ℝ} (hf : ContDiff ℝ (⊤ : ℕ∞) f)
    (hif : Integrable f) (hgrad : Integrable (gradient f)) {ε : ℝ} (hε : 0 < ε) :
    ∃ g : EuclideanSpace ℝ (Fin n) → ℝ,
      ContDiff ℝ (⊤ : ℕ∞) g ∧ HasCompactSupport g ∧ Integrable g ∧
      Integrable (gradient g) ∧ (∫ x, ‖g x - f x‖) < ε ∧
      (∫ x, ‖gradient g x - gradient f x‖) < ε := by
  obtain ⟨χ, C, _, hχ, hχlim⟩ := exists_smooth_exhaustion_cutoffs (n := n)
  have hχ₁ (j) : ContDiff ℝ 1 (χ j) := (hχ j).1.of_le (by simp)
  have hχcont (j) : Continuous (χ j) := (hχ j).1.continuous
  have hχbound (j x) : ‖χ j x‖ ≤ 1 := by
    rw [Real.norm_of_nonneg ((hχ j).2.2.1 x).1]
    exact ((hχ j).2.2.1 x).2
  have hf₁ : ContDiff ℝ 1 f := hf.of_le (by simp)
  let g (j : ℕ) (x : EuclideanSpace ℝ (Fin n)) := χ j x * f x
  have hg (j) : ContDiff ℝ (⊤ : ℕ∞) (g j) := (hχ j).1.mul hf
  have hcg (j) : HasCompactSupport (g j) := (hχ j).2.1.mul_right
  have hig (j) : Integrable (g j) := (hg j).continuous.integrable_of_hasCompactSupport (hcg j)
  have higg (j) : Integrable (gradient (g j)) :=
    (continuous_gradient_of_contDiff ((hg j).of_le (by simp))).integrable_of_hasCompactSupport
      ((hcg j).of_isClosed_subset (isClosed_tsupport _) (tsupport_gradient_subset (g j)))
  have hfirst (j) : Integrable (fun x => χ j x • gradient f x - gradient f x) :=
    (hgrad.bdd_smul 1 (hχcont j).aestronglyMeasurable
      (Eventually.of_forall (hχbound j))).sub hgrad
  have hsecond (j) : Integrable (fun x => f x • gradient (χ j) x) :=
    integrable_smul_gradient (hif.locallyIntegrable.locallyIntegrableOn univ)
      (hχ₁ j) (hχ j).2.1 (subset_univ _)
  have herror (j) : (∫ x, ‖gradient (g j) x - gradient f x‖) ≤
      (∫ x, ‖χ j x • gradient f x - gradient f x‖) +
      ∫ x, ‖f x • gradient (χ j) x‖ := by
    rw [← integral_add (hfirst j).norm (hsecond j).norm]
    apply integral_mono ((higg j).sub hgrad).norm ((hfirst j).norm.add (hsecond j).norm)
    intro x
    have heq : gradient (g j) x - gradient f x =
        (χ j x • gradient f x - gradient f x) + f x • gradient (χ j) x := by
      rw [gradient_mul (hχ₁ j) hf₁]
      abel
    change ‖gradient (g j) x - gradient f x‖ ≤
      ‖χ j x • gradient f x - gradient f x‖ + ‖f x • gradient (χ j) x‖
    rw [heq]
    exact norm_add_le _ _
  have hfirstlim := tendsto_integral_norm_cutoff_error hχcont (fun j => (hχ j).2.2.1) hχlim hgrad
  have hsecondlim := tendsto_integral_norm_cutoff_gradient (fun j => (hχ j).2.2.2) hif
  have hglim : Tendsto (fun j => ∫ x, ‖gradient (g j) x - gradient f x‖) atTop (𝓝 0) :=
    squeeze_zero (fun _ => integral_nonneg fun _ => norm_nonneg _) herror
      (by simpa only [add_zero] using hfirstlim.add hsecondlim)
  have hflim : Tendsto (fun j => ∫ x, ‖g j x - f x‖) atTop (𝓝 0) := by
    simpa only [smul_eq_mul] using
      tendsto_integral_norm_cutoff_error hχcont (fun j => (hχ j).2.2.1) hχlim hif
  obtain ⟨j, hj, hj'⟩ := (((tendsto_order.mp hflim).2 ε hε).and
    ((tendsto_order.mp hglim).2 ε hε)).exists
  exact ⟨g j, hg j, hcg j, hig j, higg j, hj, hj'⟩


lemma abs_integral_norm_sub_le_integral_norm_sub {n : ℕ} {F : Type*}
    [NormedAddCommGroup F] {u v : EuclideanSpace ℝ (Fin n) → F}
    (hu : Integrable u) (hv : Integrable v) :
    |(∫ x, ‖u x‖) - ∫ x, ‖v x‖| ≤ ∫ x, ‖u x - v x‖ := by
  rw [← integral_sub hu.norm hv.norm, ← Real.norm_eq_abs]
  apply norm_integral_le_of_norm_le (hu.sub hv).norm
  exact Eventually.of_forall fun x => abs_norm_sub_norm_le _ _

/-- The whole-space clause of blueprint strict approximation: global BV functions have
smooth compactly supported approximants with global L¹ and strict gradient convergence. -/
theorem strict_approximation_univ {n : ℕ} {f : EuclideanSpace ℝ (Fin n) → ℝ}
    (hf : IsBVOn f univ) :
    ∃ g : ℕ → EuclideanSpace ℝ (Fin n) → ℝ,
      (∀ j, ContDiff ℝ (⊤ : ℕ∞) (g j) ∧ HasCompactSupport (g j) ∧
        Integrable (g j) ∧ Integrable (gradient (g j))) ∧
      Tendsto (fun j => ∫ x, ‖g j x - f x‖) atTop (𝓝 0) ∧
      Tendsto (fun j => ∫ x, ‖gradient (g j) x‖) atTop (𝓝 (variation f univ).toReal) := by
  classical
  have hif : Integrable f := integrableOn_univ.mp hf.1
  let φ (j : ℕ) : ContDiffBump (0 : EuclideanSpace ℝ (Fin n)) :=
    ⟨((j : ℝ) + 1)⁻¹ / 2, ((j : ℝ) + 1)⁻¹, by positivity,
      half_lt_self (by positivity)⟩
  have hφlim : Tendsto (fun j => (φ j).rOut) atTop (𝓝 0) := by
    simpa only [one_div] using tendsto_one_div_add_atTop_nhds_zero_nat (𝕜 := ℝ)
  let h (j : ℕ) := (φ j).normed volume ⋆[ContinuousLinearMap.lsmul ℝ ℝ] f
  have hh (j) : ContDiff ℝ (⊤ : ℕ∞) (h j) :=
    (φ j).hasCompactSupport_normed.contDiff_convolution_left _
      (φ j).contDiff_normed hif.locallyIntegrable
  have hih (j) : Integrable (h j) := (φ j).integrable_normed.integrable_convolution _ hif
  have hihg (j) : Integrable (gradient (h j)) :=
    (integrable_gradient_bump_convolution_and_bound hif.locallyIntegrable hf.2 (φ j)).1
  have happrox (j) := exists_smooth_compact_gradient_approximation (hh j) (hih j) (hihg j)
    (ε := ((j : ℝ) + 1)⁻¹) (by positivity)
  choose g hg hcg hig higg hfgerr hgraderr using happrox
  refine ⟨g, fun j => ⟨hg j, hcg j, hig j, higg j⟩, ?_, ?_⟩
  · have hb (j) : (∫ x, ‖g j x - f x‖) ≤
        ((j : ℝ) + 1)⁻¹ + ∫ x, ‖h j x - f x‖ := by
      calc
        _ ≤ (∫ x, ‖g j x - h j x‖) + ∫ x, ‖h j x - f x‖ := by
          have hadd := integral_add ((hig j).sub (hih j)).norm ((hih j).sub hif).norm
          simp only [Pi.sub_apply] at hadd
          rw [← hadd]
          apply integral_mono ((hig j).sub hif).norm
            (((hig j).sub (hih j)).norm.add ((hih j).sub hif).norm)
          exact fun x => by
            simpa only [dist_eq_norm, Pi.sub_apply, Pi.add_apply] using
              dist_triangle (g j x) (h j x) (f x)
        _ ≤ _ := add_le_add (hfgerr j).le le_rfl
    apply squeeze_zero (fun _ => integral_nonneg fun _ => norm_nonneg _) hb
    simpa only [zero_add] using hφlim.add (tendsto_integral_norm_bump_convolution_sub hif hφlim)
  · apply (tendsto_integral_norm_gradient_bump_convolution hf hφlim).congr_dist
    apply squeeze_zero (fun _ => dist_nonneg) (fun j => ?_) hφlim
    rw [Real.dist_eq, abs_sub_comm]
    exact (abs_integral_norm_sub_le_integral_norm_sub (higg j) (hihg j)).trans (hgraderr j).le


/-! ## Compact partitions and admissible mollification radii on open domains -/

/-- A compact subset of an open Euclidean domain has a smooth compact cutoff equal to
one on a neighborhood, with support remaining in the domain. -/
theorem exists_smooth_cutoff_one_near_compact {n : ℕ}
    {K U : Set (EuclideanSpace ℝ (Fin n))} (hK : IsCompact K) (hU : IsOpen U) (hKU : K ⊆ U) :
    ∃ ζ : EuclideanSpace ℝ (Fin n) → ℝ,
      ContDiff ℝ (⊤ : ℕ∞) ζ ∧ HasCompactSupport ζ ∧ tsupport ζ ⊆ U ∧
      (∀ᶠ x in 𝓝ˢ K, ζ x = 1) ∧ (∀ x, 0 ≤ ζ x ∧ ζ x ≤ 1) := by
  obtain ⟨A, hA, hKA, hAU, hcA⟩ := exists_open_between_and_isCompact_closure hK hU hKU
  obtain ⟨ζ, hζ₁, hζ₀, hζb⟩ := exists_contMDiffMap_one_nhds_of_subset_interior
    (I := 𝓘(ℝ, EuclideanSpace ℝ (Fin n))) (n := (⊤ : ℕ∞)) hK.isClosed
    (hKA.trans hA.subset_interior_closure)
  have hs : tsupport ζ ⊆ closure A := by
    apply closure_minimal _ isClosed_closure
    intro x hx
    by_contra hxA
    exact hx (hζ₀ x hxA)
  exact ⟨ζ, ζ.contMDiff.contDiff, hcA.of_isClosed_subset (isClosed_tsupport _) hs,
    hs.trans hAU, hζ₁, hζb⟩

/-- Smooth ambient cutoffs along a compact exhaustion of an arbitrary open domain.
Each cutoff equals one near its compact core and has compact support inside the domain. -/
theorem exists_open_domain_smooth_cutoffs {n : ℕ}
    {U : Set (EuclideanSpace ℝ (Fin n))} (hU : IsOpen U) :
    ∃ K : CompactExhaustion U, ∃ κ : ℕ → EuclideanSpace ℝ (Fin n) → ℝ,
      ∀ j, ContDiff ℝ (⊤ : ℕ∞) (κ j) ∧ HasCompactSupport (κ j) ∧ tsupport (κ j) ⊆ U ∧
        (∀ᶠ x in 𝓝ˢ (Subtype.val '' K j), κ j x = 1) ∧
        (∀ x, 0 ≤ κ j x ∧ κ j x ≤ 1) := by
  let : LocallyCompactSpace U := hU.locallyCompactSpace
  let K := CompactExhaustion.choice U
  have h (j : ℕ) := exists_smooth_cutoff_one_near_compact
    ((K.isCompact j).image continuous_subtype_val) hU (by rintro _ ⟨x, _, rfl⟩; exact x.property)
  choose κ hκ using h
  exact ⟨K, κ, hκ⟩


/-- The ordered partition pieces obtained from cutoffs by removing all earlier pieces. -/
def sequentialPartitionPiece {n : ℕ} (κ : ℕ → EuclideanSpace ℝ (Fin n) → ℝ)
    (j : ℕ) (x : EuclideanSpace ℝ (Fin n)) : ℝ :=
  κ j x * ∏ i ∈ Finset.range j, (1 - κ i x)

lemma sequentialPartitionPiece_eq_zero {n : ℕ}
    (κ : ℕ → EuclideanSpace ℝ (Fin n) → ℝ) {j m : ℕ} (hm : m < j)
    {x : EuclideanSpace ℝ (Fin n)} (hx : κ m x = 1) :
    sequentialPartitionPiece κ j x = 0 := by
  unfold sequentialPartitionPiece
  rw [Finset.prod_eq_zero (Finset.mem_range.mpr hm) (by rw [hx, sub_self]), mul_zero]

lemma sum_sequentialPartitionPiece {n : ℕ}
    (κ : ℕ → EuclideanSpace ℝ (Fin n) → ℝ) (N : ℕ) (x : EuclideanSpace ℝ (Fin n)) :
    ∑ j ∈ Finset.range N, sequentialPartitionPiece κ j x =
      1 - ∏ i ∈ Finset.range N, (1 - κ i x) := by
  induction N with
  | zero => simp
  | succ N ih =>
    rw [Finset.sum_range_succ, ih, Finset.prod_range_succ, sequentialPartitionPiece]
    ring

lemma sequentialPartitionPiece_bounds {n : ℕ}
    {κ : ℕ → EuclideanSpace ℝ (Fin n) → ℝ} (hκ : ∀ j x, 0 ≤ κ j x ∧ κ j x ≤ 1)
    (j : ℕ) (x : EuclideanSpace ℝ (Fin n)) :
    0 ≤ sequentialPartitionPiece κ j x ∧ sequentialPartitionPiece κ j x ≤ 1 := by
  have hp₀ : 0 ≤ ∏ i ∈ Finset.range j, (1 - κ i x) :=
    Finset.prod_nonneg fun i _ => sub_nonneg.mpr (hκ i x).2
  have hp₁ : (∏ i ∈ Finset.range j, (1 - κ i x)) ≤ 1 :=
    Finset.prod_le_one₀ (fun i _ => sub_nonneg.mpr (hκ i x).2)
      (fun i _ => by linarith [(hκ i x).1])
  exact ⟨mul_nonneg (hκ j x).1 hp₀,
    (mul_le_mul (hκ j x).2 hp₁ hp₀ zero_le_one).trans_eq (one_mul _)⟩

lemma contDiff_sequentialPartitionPiece {n : ℕ}
    {κ : ℕ → EuclideanSpace ℝ (Fin n) → ℝ} (hκ : ∀ j, ContDiff ℝ (⊤ : ℕ∞) (κ j))
    (j : ℕ) : ContDiff ℝ (⊤ : ℕ∞) (sequentialPartitionPiece κ j) :=
  (hκ j).mul (contDiff_prod fun i _ => contDiff_const.sub (hκ i))

lemma tsupport_sequentialPartitionPiece_subset {n : ℕ}
    (κ : ℕ → EuclideanSpace ℝ (Fin n) → ℝ) (j : ℕ) :
    tsupport (sequentialPartitionPiece κ j) ⊆ tsupport (κ j) := by
  exact tsupport_mul_subset_left


lemma disjoint_tsupport_sequentialPartitionPiece_of_one_near {n : ℕ}
    (κ : ℕ → EuclideanSpace ℝ (Fin n) → ℝ) {K : Set (EuclideanSpace ℝ (Fin n))}
    {m j : ℕ} (hm : m < j) (hκ : ∀ᶠ x in 𝓝ˢ K, κ m x = 1) :
    Disjoint (tsupport (sequentialPartitionPiece κ j)) K := by
  apply Set.disjoint_left.mpr
  intro x hx hxK
  apply (notMem_tsupport_iff_eventuallyEq.mpr ?_) hx
  filter_upwards [hκ.filter_mono (nhds_le_nhdsSet hxK)] with y hy
  exact sequentialPartitionPiece_eq_zero κ hm hy

lemma locallyFinite_sequentialPartitionPiece {n : ℕ}
    {U : Set (EuclideanSpace ℝ (Fin n))} (K : CompactExhaustion U)
    (κ : ℕ → EuclideanSpace ℝ (Fin n) → ℝ)
    (hκ : ∀ m, ∀ᶠ x in 𝓝ˢ (Subtype.val '' K m), κ m x = 1) :
    LocallyFinite (fun j => (Subtype.val : U → EuclideanSpace ℝ (Fin n)) ⁻¹'
      tsupport (sequentialPartitionPiece κ j)) := by
  intro x
  obtain ⟨m, hm⟩ := K.exists_mem_nhds x
  refine ⟨K m, hm, (Set.finite_Iic m).subset ?_⟩
  rintro j ⟨y, hy, hyK⟩
  by_contra hj
  exact Set.disjoint_left.mp
    (disjoint_tsupport_sequentialPartitionPiece_of_one_near κ (Nat.lt_of_not_ge hj) (hκ m))
    hy (mem_image_of_mem Subtype.val hyK)

lemma finsum_sequentialPartitionPiece_eq_one {n : ℕ}
    (κ : ℕ → EuclideanSpace ℝ (Fin n) → ℝ) {x : EuclideanSpace ℝ (Fin n)}
    {m : ℕ} (hm : κ m x = 1) : ∑ᶠ j, sequentialPartitionPiece κ j x = 1 := by
  have hs : Function.support (fun j => sequentialPartitionPiece κ j x) ⊆
      (Finset.range (m + 1) : Set ℕ) := by
    intro j hj
    by_contra hj'
    have hmj : m < j := by
      simp only [Finset.mem_coe, Finset.mem_range, not_lt] at hj'
      omega
    exact hj (sequentialPartitionPiece_eq_zero κ hmj hm)
  rw [finsum_eq_sum_of_support_subset _ hs, sum_sequentialPartitionPiece]
  rw [Finset.prod_eq_zero (Finset.mem_range.mpr (Nat.lt_succ_self m)) (by rw [hm, sub_self])]
  exact sub_zero _

/-- A countable smooth partition of an open domain by compactly supported ambient functions.
Its supports are locally finite on the domain, and later pieces avoid every earlier compact core. -/
theorem exists_smooth_partition_open_domain {n : ℕ}
    {U : Set (EuclideanSpace ℝ (Fin n))} (hU : IsOpen U) :
    ∃ K : CompactExhaustion U, ∃ ζ : ℕ → EuclideanSpace ℝ (Fin n) → ℝ,
      (∀ j, ContDiff ℝ (⊤ : ℕ∞) (ζ j) ∧ HasCompactSupport (ζ j) ∧ tsupport (ζ j) ⊆ U ∧
        (∀ x, 0 ≤ ζ j x ∧ ζ j x ≤ 1)) ∧
      LocallyFinite (fun j => (Subtype.val : U → EuclideanSpace ℝ (Fin n)) ⁻¹' tsupport (ζ j)) ∧
      (∀ x ∈ U, ∑ᶠ j, ζ j x = 1) ∧
      (∀ m j, m < j → Disjoint (tsupport (ζ j)) (Subtype.val '' K m)) := by
  obtain ⟨K, κ, hκ⟩ := exists_open_domain_smooth_cutoffs hU
  refine ⟨K, sequentialPartitionPiece κ, fun j => ?_,
    locallyFinite_sequentialPartitionPiece K κ (fun m => (hκ m).2.2.2.1), ?_, ?_⟩
  · refine ⟨contDiff_sequentialPartitionPiece (fun i => (hκ i).1) j,
      (hκ j).2.1.of_isClosed_subset (isClosed_tsupport _)
        (tsupport_sequentialPartitionPiece_subset κ j),
      (tsupport_sequentialPartitionPiece_subset κ j).trans (hκ j).2.2.1,
      sequentialPartitionPiece_bounds (fun i => (hκ i).2.2.2.2) j⟩
  · intro x hx
    obtain ⟨m, hm⟩ := K.exists_mem ⟨x, hx⟩
    exact finsum_sequentialPartitionPiece_eq_one κ
      ((hκ m).2.2.2.1.self_of_nhdsSet x (mem_image_of_mem Subtype.val hm))
  · intro m j hmj
    exact disjoint_tsupport_sequentialPartitionPiece_of_one_near κ hmj (hκ m).2.2.2.1


/-- Compact partition supports may be thickened while preserving local finiteness inside
an open domain. This permits an independently chosen mollification radius for each piece. -/
theorem exists_locallyFinite_thickenings {n : ℕ}
    {U : Set (EuclideanSpace ℝ (Fin n))} (hU : IsOpen U) (K : CompactExhaustion U)
    {ζ : ℕ → EuclideanSpace ℝ (Fin n) → ℝ}
    (hc : ∀ j, HasCompactSupport (ζ j)) (hs : ∀ j, tsupport (ζ j) ⊆ U)
    (hd : ∀ m j, m < j → Disjoint (tsupport (ζ j)) (Subtype.val '' K m)) :
    ∃ δ : ℕ → ℝ, (∀ j, 0 < δ j ∧ cthickening (δ j) (tsupport (ζ j)) ⊆ U) ∧
      LocallyFinite (fun j => (Subtype.val : U → EuclideanSpace ℝ (Fin n)) ⁻¹'
        cthickening (δ j) (tsupport (ζ j))) := by
  have hchoice (j : ℕ) : ∃ r : ℝ, 0 < r ∧ cthickening r (tsupport (ζ j)) ⊆ U ∧
      ∀ m, m < j → Disjoint (cthickening r (tsupport (ζ j))) (Subtype.val '' K m) := by
    cases j with
    | zero =>
      obtain ⟨r, hr, hs⟩ := (hc 0).exists_cthickening_subset_open hU (hs 0)
      exact ⟨r, hr, hs, fun m hm => (Nat.not_lt_zero m hm).elim⟩
    | succ j =>
      have hK : IsCompact (Subtype.val '' K j) := (K.isCompact j).image continuous_subtype_val
      have hsub : tsupport (ζ (j + 1)) ⊆ U ∩ (Subtype.val '' K j)ᶜ :=
        subset_inter (hs _) (disjoint_left.mp (hd j (j + 1) (Nat.lt_succ_self j)))
      obtain ⟨r, hr, hs'⟩ := (hc (j + 1)).exists_cthickening_subset_open
        (hU.inter hK.isClosed.isOpen_compl) hsub
      refine ⟨r, hr, hs'.trans inter_subset_left, fun m hm => ?_⟩
      apply Set.disjoint_left.mpr
      intro x hx hxm
      exact (hs' hx).2 ((image_mono (K.subset (Nat.lt_succ_iff.mp hm))) hxm)
  choose δ hδ hδU hδK using hchoice
  refine ⟨δ, fun j => ⟨hδ j, hδU j⟩, ?_⟩
  intro x
  obtain ⟨m, hm⟩ := K.exists_mem_nhds x
  refine ⟨K m, hm, (Set.finite_Iic m).subset ?_⟩
  rintro j ⟨y, hy, hyK⟩
  by_contra hj
  exact Set.disjoint_left.mp (hδK j m (Nat.lt_of_not_ge hj))
    hy (mem_image_of_mem Subtype.val hyK)


/-- The gradient of a mollified compact product splits into convolution of the weighted
polar derivative and convolution of the integrable product-rule correction. -/
theorem IsDistributionalPolarRepresentation.gradient_convolution_mul_eq {n : ℕ}
    {U : Set (EuclideanSpace ℝ (Fin n))} {f ζ k : EuclideanSpace ℝ (Fin n) → ℝ}
    {ρ : Measure U} [IsFiniteMeasureOnCompacts ρ] {σ : U → EuclideanSpace ℝ (Fin n)}
    (hpolar : IsDistributionalPolarRepresentation f U ρ σ)
    (hf : LocallyIntegrableOn f U) (hζ : ContDiff ℝ 1 ζ)
    (hcζ : HasCompactSupport ζ) (hsζ : tsupport ζ ⊆ U)
    (hk : ContDiff ℝ 1 k) (hck : HasCompactSupport k) (x : EuclideanSpace ℝ (Fin n)) :
    gradient (k ⋆[ContinuousLinearMap.lsmul ℝ ℝ] (fun y => ζ y * f y)) x =
      (∫ y : U, k (x - y) • (ζ y • σ y) ∂ρ) +
      ∫ y, k (x - y) • (f y • gradient ζ y) := by
  have hi := integrable_mul_compact_factor hf hζ.continuous hcζ hsζ
  have hiσ := hpolar.integrable_smul_compact_factor hζ.continuous hcζ hsζ
  have hiG := integrable_smul_gradient hf hζ hcζ hsζ
  let ψ : C_c(EuclideanSpace ℝ (Fin n), ℝ) :=
    ⟨⟨fun y => k (x - y), hk.continuous.comp (continuous_const.sub continuous_id)⟩,
      hck.comp_homeomorph (Homeomorph.subLeft x)⟩
  have hψ : ContDiff ℝ 1 ψ := hk.comp (contDiff_const.sub contDiff_id)
  obtain ⟨C, hC⟩ := ψ.hasCompactSupport.exists_bound_of_continuous ψ.continuous
  have hiσ' : Integrable (fun y : U => k (x - y) • (ζ y • σ y)) ρ :=
    hiσ.bdd_smul C (ψ.continuous.comp continuous_subtype_val).aestronglyMeasurable
      (Eventually.of_forall fun y => hC y)
  have hiG' : Integrable (fun y => k (x - y) • (f y • gradient ζ y)) :=
    hiG.bdd_smul C ψ.continuous.aestronglyMeasurable (Eventually.of_forall hC)
  have hcgrad : HasCompactSupport (gradient k) :=
    hck.of_isClosed_subset (isClosed_tsupport _) (tsupport_gradient_subset k)
  have hiL := hcgrad.convolutionExists_right (μ := volume) (ContinuousLinearMap.lsmul ℝ ℝ)
    hi.locallyIntegrable (continuous_gradient_of_contDiff hk) x
  change Integrable (fun y => (ζ y * f y) • gradient k (x - y)) at hiL
  rw [gradient_convolution_left hi.locallyIntegrable hk hck x]
  apply PiLp.ext
  intro i
  rw [PiLp.add_apply, eval_integral_piLp hiL.eval_piLp,
    eval_integral_piLp hiσ'.eval_piLp, eval_integral_piLp hiG'.eval_piLp]
  let X := coordinateTestField i ψ.toBoundedContinuousFunction
  have hX : ContDiff ℝ 1 X := hψ.smul contDiff_const
  have hcX : HasCompactSupport X := ψ.hasCompactSupport.smul_right
  have h := hpolar.integral_mul_divergence_eq hf hζ hcζ hsζ hX hcX
  have hdiv (y) : divergenceN X y = -gradient k (x - y) i := by
    rw [divergenceN_coordinateTestField i hψ]
    rw [gradient_apply_eq_fderiv_single]
    exact fderiv_comp_const_sub hk x y _
  simp_rw [hdiv, mul_neg, integral_neg, neg_neg] at h
  simp only [X, coordinateTestField_apply, real_inner_smul_right,
    EuclideanSpace.inner_single_right, one_mul, conj_trivial] at h
  change (∫ y, (ζ y * f y) * gradient k (x - y) i) =
    (∫ y : U, k (x - y) * (ζ y • σ y) i ∂ρ) +
      ∫ y, k (x - y) * (f y • gradient ζ y) i at h
  simpa only [PiLp.smul_apply, smul_eq_mul] using h

/-- Local finiteness on an open subtype gives one finite set of active ambient supports
on a whole neighborhood of each point. -/
lemma exists_finite_active_near {n : ℕ} {ι : Type*}
    {U : Set (EuclideanSpace ℝ (Fin n))} (hU : IsOpen U)
    {A : ι → Set (EuclideanSpace ℝ (Fin n))}
    (hloc : LocallyFinite (fun i => (Subtype.val : U → EuclideanSpace ℝ (Fin n)) ⁻¹' A i))
    {x : EuclideanSpace ℝ (Fin n)} (hx : x ∈ U) :
    ∃ s : Finset ι, ∃ V : Set (EuclideanSpace ℝ (Fin n)),
      IsOpen V ∧ x ∈ V ∧ V ⊆ U ∧ ∀ i, i ∉ s → Disjoint (A i) V := by
  classical
  obtain ⟨t, ht, hfin⟩ := hloc ⟨x, hx⟩
  obtain ⟨v, hvt, hv, hxv⟩ := _root_.mem_nhds_iff.mp ht
  refine ⟨hfin.toFinset, Subtype.val '' v, hU.isOpenMap_subtype_val _ hv,
    ⟨⟨x, hx⟩, hxv, rfl⟩, ?_, ?_⟩
  · rintro _ ⟨y, _, rfl⟩
    exact y.property
  · intro i hi
    apply Set.disjoint_left.mpr
    rintro y hAy ⟨z, hz, rfl⟩
    exact hi (hfin.mem_toFinset.mpr ⟨z, hAy, hvt hz⟩)

/-- Near every point of the domain, a locally finite sum is one fixed finite sum. -/
lemma finsum_eventually_eq_finset_sum {n : ℕ} {ι F : Type*}
    [AddCommMonoid F] {U : Set (EuclideanSpace ℝ (Fin n))} (hU : IsOpen U)
    {f : ι → EuclideanSpace ℝ (Fin n) → F}
    (hloc : LocallyFinite (fun i => (Subtype.val : U → EuclideanSpace ℝ (Fin n)) ⁻¹'
      tsupport (f i))) {x : EuclideanSpace ℝ (Fin n)} (hx : x ∈ U) :
    ∃ s : Finset ι, (fun y => ∑ᶠ i, f i y) =ᶠ[𝓝 x] (fun y => ∑ i ∈ s, f i y) ∧
      ∀ i, i ∉ s → f i =ᶠ[𝓝 x] 0 := by
  classical
  obtain ⟨s, V, hV, hxV, _, hs⟩ := exists_finite_active_near hU hloc hx
  refine ⟨s, ?_, ?_⟩
  · filter_upwards [hV.mem_nhds hxV] with y hy
    apply finsum_eq_sum_of_support_subset
    intro i hi
    by_contra his
    exact Set.disjoint_left.mp (hs i his) (subset_tsupport (f i) hi) hy
  · intro i hi
    filter_upwards [hV.mem_nhds hxV] with y hy
    exact image_eq_zero_of_notMem_tsupport (fun h => Set.disjoint_left.mp (hs i hi) h hy)

/-- A locally finite sum of ambient smooth functions is smooth on the open domain. -/
theorem contDiffOn_finsum_of_locallyFinite {n : ℕ} {ι F : Type*}
    [NormedAddCommGroup F] [NormedSpace ℝ F]
    {U : Set (EuclideanSpace ℝ (Fin n))} (hU : IsOpen U)
    {f : ι → EuclideanSpace ℝ (Fin n) → F} {m : ℕ∞}
    (hf : ∀ i, ContDiff ℝ m (f i))
    (hloc : LocallyFinite (fun i => (Subtype.val : U → EuclideanSpace ℝ (Fin n)) ⁻¹'
      tsupport (f i))) : ContDiffOn ℝ m (fun x => ∑ᶠ i, f i x) U := by
  intro x hx
  obtain ⟨s, heq, _⟩ := finsum_eventually_eq_finset_sum hU hloc hx
  exact ((ContDiff.sum fun i _ => hf i).contDiffAt.congr_of_eventuallyEq heq).contDiffWithinAt

lemma gradient_finset_sum {n : ℕ} {ι : Type*} (s : Finset ι)
    {f : ι → EuclideanSpace ℝ (Fin n) → ℝ} (hf : ∀ i ∈ s, ContDiff ℝ 1 (f i))
    (x : EuclideanSpace ℝ (Fin n)) :
    gradient (fun y => ∑ i ∈ s, f i y) x = ∑ i ∈ s, gradient (f i) x := by
  simp only [gradient, fderiv_fun_sum (fun i hi => (hf i hi).differentiable one_ne_zero x),
    map_sum]

/-- Gradients commute with a locally finite sum on its open domain. -/
theorem gradient_finsum_of_locallyFinite {n : ℕ} {ι : Type*}
    {U : Set (EuclideanSpace ℝ (Fin n))} (hU : IsOpen U)
    {f : ι → EuclideanSpace ℝ (Fin n) → ℝ} (hf : ∀ i, ContDiff ℝ 1 (f i))
    (hloc : LocallyFinite (fun i => (Subtype.val : U → EuclideanSpace ℝ (Fin n)) ⁻¹'
      tsupport (f i))) {x : EuclideanSpace ℝ (Fin n)} (hx : x ∈ U) :
    gradient (fun y => ∑ᶠ i, f i y) x = ∑ᶠ i, gradient (f i) x := by
  classical
  obtain ⟨s, heq, hz⟩ := finsum_eventually_eq_finset_sum hU hloc hx
  have hzero (i) (hi : i ∉ s) : gradient (f i) x = 0 := by
    rw [gradient, (hz i hi).fderiv_eq]
    simp
  calc
    _ = gradient (fun y => ∑ i ∈ s, f i y) x :=
      congrArg (fun A => (toDual ℝ (EuclideanSpace ℝ (Fin n))).symm A) heq.fderiv_eq
    _ = ∑ i ∈ s, gradient (f i) x := gradient_finset_sum s (fun i _ => hf i) x
    _ = _ := by
      symm
      apply finsum_eq_sum_of_support_subset
      intro i hi
      by_contra his
      exact hi (hzero i his)

/-- The gradients of a smooth locally finite partition of unity sum to zero. -/
theorem finsum_gradient_partition_eq_zero {n : ℕ} {ι : Type*}
    {U : Set (EuclideanSpace ℝ (Fin n))} (hU : IsOpen U)
    {ζ : ι → EuclideanSpace ℝ (Fin n) → ℝ} (hζ : ∀ i, ContDiff ℝ 1 (ζ i))
    (hloc : LocallyFinite (fun i => (Subtype.val : U → EuclideanSpace ℝ (Fin n)) ⁻¹'
      tsupport (ζ i))) (hsum : ∀ x ∈ U, ∑ᶠ i, ζ i x = 1)
    {x : EuclideanSpace ℝ (Fin n)} (hx : x ∈ U) : ∑ᶠ i, gradient (ζ i) x = 0 := by
  have heq : (fun y => ∑ᶠ i, ζ i y) =ᶠ[𝓝 x] (fun _ => (1 : ℝ)) := by
    filter_upwards [hU.mem_nhds hx] with y hy
    exact hsum y hy
  rw [← gradient_finsum_of_locallyFinite hU hζ hloc hx, gradient, heq.fderiv_eq]
  simp


/-- Pointwise finite sums of a countable family of measurable functions are measurable. -/
lemma aestronglyMeasurable_finsum_of_finite_support {A F : Type*} [MeasurableSpace A]
    [NormedAddCommGroup F] {μ : Measure A} {f : ℕ → A → F}
    (hf : ∀ i, AEStronglyMeasurable (f i) μ)
    (hfin : ∀ x, Function.HasFiniteSupport (fun i => f i x)) :
    AEStronglyMeasurable (fun x => ∑ᶠ i, f i x) μ := by
  apply aestronglyMeasurable_of_tendsto_ae atTop
    (fun j => (Finset.range j).aestronglyMeasurable_fun_sum fun i _ => hf i)
  exact Eventually.of_forall fun x => by
    simpa only [tsum_eq_finsum (hfin x)] using
      (summable_of_hasFiniteSupport (hfin x)).tendsto_sum_tsum_nat

/-- Summable L¹ budgets control a pointwise finite sum, including its integrability. -/
theorem integrable_finsum_and_integral_norm_le {A F : Type*} [MeasurableSpace A]
    [NormedAddCommGroup F] {μ : Measure A} {f : ℕ → A → F}
    (hf : ∀ i, Integrable (f i) μ)
    (hfin : ∀ x, Function.HasFiniteSupport (fun i => f i x))
    {b : ℕ → ℝ} (hb : Summable b) (hbound : ∀ i, (∫ x, ‖f i x‖ ∂μ) ≤ b i) :
    Integrable (fun x => ∑ᶠ i, f i x) μ ∧
      (∫ x, ‖∑ᶠ i, f i x‖ ∂μ) ≤ ∑' i, b i := by
  have hb₀ (i) : 0 ≤ b i := (integral_nonneg fun _ => norm_nonneg _).trans (hbound i)
  have hle : (∫⁻ x, ‖∑ᶠ i, f i x‖ₑ ∂μ) ≤ ENNReal.ofReal (∑' i, b i) := by
    calc
      _ ≤ ∫⁻ x, ∑' i, ‖f i x‖ₑ ∂μ := lintegral_mono fun x => by
        rw [← tsum_eq_finsum (L := SummationFilter.unconditional _) (hfin x)]
        exact enorm_tsum_le_tsum_enorm
      _ = ∑' i, ∫⁻ x, ‖f i x‖ₑ ∂μ := lintegral_tsum fun i => (hf i).1.enorm
      _ ≤ ∑' i, ENNReal.ofReal (b i) := by
        apply ENNReal.tsum_le_tsum
        intro i
        rw [← ofReal_integral_norm_eq_lintegral_enorm (hf i)]
        exact ENNReal.ofReal_le_ofReal (hbound i)
      _ = _ := (ENNReal.ofReal_tsum_of_nonneg hb₀ hb).symm
  have hi : Integrable (fun x => ∑ᶠ i, f i x) μ :=
    ⟨aestronglyMeasurable_finsum_of_finite_support (fun i => (hf i).1) hfin,
      hle.trans_lt ENNReal.ofReal_lt_top⟩
  refine ⟨hi, ?_⟩
  rw [← ofReal_integral_norm_eq_lintegral_enorm hi] at hle
  exact (ENNReal.ofReal_le_ofReal_iff (tsum_nonneg hb₀)).mp hle

/-- Supports locally finite on an open domain, and contained in it, are pointwise finite
also as ambient functions. -/
lemma finite_support_of_locallyFinite_tsupport {n : ℕ} {ι F : Type*} [Zero F]
    {U : Set (EuclideanSpace ℝ (Fin n))} {f : ι → EuclideanSpace ℝ (Fin n) → F}
    (hs : ∀ i, tsupport (f i) ⊆ U)
    (hloc : LocallyFinite (fun i => (Subtype.val : U → EuclideanSpace ℝ (Fin n)) ⁻¹'
      tsupport (f i))) (x : EuclideanSpace ℝ (Fin n)) :
    Function.HasFiniteSupport (fun i => f i x) := by
  by_cases hx : x ∈ U
  · exact (hloc.point_finite ⟨x, hx⟩).subset fun i hi => subset_tsupport (f i) hi
  · apply Set.finite_empty.subset
    intro i hi
    exact hx (hs i (subset_tsupport (f i) hi))


/-- A single arbitrarily small bump meets two L¹ error budgets simultaneously. -/
theorem exists_bump_l1_approximation_pair {n : ℕ} {F G : Type*}
    [NormedAddCommGroup F] [NormedSpace ℝ F] [CompleteSpace F]
    [NormedAddCommGroup G] [NormedSpace ℝ G] [CompleteSpace G]
    {f : EuclideanSpace ℝ (Fin n) → F} {g : EuclideanSpace ℝ (Fin n) → G}
    (hf : Integrable f) (hg : Integrable g) {ε δ : ℝ} (hε : 0 < ε) (hδ : 0 < δ) :
    ∃ φ : ContDiffBump (0 : EuclideanSpace ℝ (Fin n)), φ.rOut < δ ∧
      (∫ x, ‖(φ.normed volume ⋆[ContinuousLinearMap.lsmul ℝ ℝ] f) x - f x‖) < ε ∧
      (∫ x, ‖(φ.normed volume ⋆[ContinuousLinearMap.lsmul ℝ ℝ] g) x - g x‖) < ε := by
  let φ (j : ℕ) : ContDiffBump (0 : EuclideanSpace ℝ (Fin n)) :=
    ⟨(δ / ((j : ℝ) + 1)) / 2, δ / ((j : ℝ) + 1), by positivity,
      half_lt_self (by positivity)⟩
  have hφlim : Tendsto (fun j => (φ j).rOut) atTop (𝓝 0) := by
    simpa only [mul_one_div, mul_zero] using
      (tendsto_one_div_add_atTop_nhds_zero_nat (𝕜 := ℝ)).const_mul δ
  have hferr := (tendsto_order.mp (tendsto_integral_norm_bump_convolution_sub hf hφlim)).2 ε hε
  have hgerr := (tendsto_order.mp (tendsto_integral_norm_bump_convolution_sub hg hφlim)).2 ε hε
  obtain ⟨j, hj, hf', hg'⟩ :=
    ((tendsto_order.mp hφlim).2 δ hδ |>.and (hferr.and hgerr)).exists
  exact ⟨φ j, hj, hf', hg'⟩


/-- Summable errors in a smooth locally finite partition give an L¹ bound on the glued
approximation, without global integrability of the original function. -/
theorem smooth_partition_gluing_l1 {n : ℕ}
    {U : Set (EuclideanSpace ℝ (Fin n))} (hU : IsOpen U)
    {f : EuclideanSpace ℝ (Fin n) → ℝ} (hf : LocallyIntegrableOn f U)
    {ζ g : ℕ → EuclideanSpace ℝ (Fin n) → ℝ}
    (hζ : ∀ i, Continuous (ζ i)) (hcζ : ∀ i, HasCompactSupport (ζ i))
    (hsζ : ∀ i, tsupport (ζ i) ⊆ U)
    (hlocζ : LocallyFinite (fun i => (Subtype.val : U → EuclideanSpace ℝ (Fin n)) ⁻¹'
      tsupport (ζ i))) (hsum : ∀ x ∈ U, ∑ᶠ i, ζ i x = 1)
    (hg : ∀ i, ContDiff ℝ (⊤ : ℕ∞) (g i)) (hig : ∀ i, Integrable (g i))
    (hsg : ∀ i, tsupport (g i) ⊆ U)
    (hlocg : LocallyFinite (fun i => (Subtype.val : U → EuclideanSpace ℝ (Fin n)) ⁻¹'
      tsupport (g i))) {b : ℕ → ℝ} (hb : Summable b)
    (herr : ∀ i, (∫ x, ‖g i x - ζ i x * f x‖) ≤ b i) :
    ContDiffOn ℝ (⊤ : ℕ∞) (fun x => ∑ᶠ i, g i x) U ∧
      IntegrableOn (fun x => (∑ᶠ i, g i x) - f x) U ∧
      (∫ x in U, ‖(∑ᶠ i, g i x) - f x‖) ≤ ∑' i, b i := by
  have hfg := finite_support_of_locallyFinite_tsupport hsg hlocg
  have hfp (x) : Function.HasFiniteSupport (fun i => ζ i x * f x) :=
    (finite_support_of_locallyFinite_tsupport hsζ hlocζ x).subset fun i hi => by
      intro hz
      change ζ i x = 0 at hz
      exact hi (by change ζ i x * f x = 0; rw [hz, zero_mul])
  obtain ⟨hie, he⟩ := integrable_finsum_and_integral_norm_le
    (fun i => (hig i).sub (integrable_mul_compact_factor hf (hζ i) (hcζ i) (hsζ i)))
    (fun x => (hfg x).sub (hfp x)) hb herr
  have heq (x) (hx : x ∈ U) : (∑ᶠ i, (g i x - ζ i x * f x)) = (∑ᶠ i, g i x) - f x := by
    rw [finsum_sub_distrib (hfg x) (hfp x)]
    have hp : (∑ᶠ i, ζ i x * f x) = f x := by
      change (∑ᶠ i, ζ i x • f x) = f x
      rw [← finsum_smul, hsum x hx, one_smul]
    rw [hp]
  have hae : (fun x => ∑ᶠ i, (g i x - ζ i x * f x)) =ᵐ[volume.restrict U]
      (fun x => (∑ᶠ i, g i x) - f x) :=
    (ae_restrict_mem hU.measurableSet).mono fun x hx => heq x hx
  refine ⟨contDiffOn_finsum_of_locallyFinite hU hg hlocg, hie.integrableOn.congr hae, ?_⟩
  calc
    _ = ∫ x in U, ‖∑ᶠ i, (g i x - ζ i x * f x)‖ :=
      (integral_congr_ae (hae.fun_comp norm)).symm
    _ ≤ ∫ x, ‖∑ᶠ i, (g i x - ζ i x * f x)‖ :=
      setIntegral_le_integral hie.norm (Eventually.of_forall fun _ => norm_nonneg _)
    _ ≤ _ := he


/-- In a partition gluing, subtracting the original product-rule corrections preserves
the gradient sum. Summable bounds on these differences control the total gradient. -/
theorem smooth_partition_gluing_gradient {n : ℕ}
    {U : Set (EuclideanSpace ℝ (Fin n))} (hU : IsOpen U)
    {f : EuclideanSpace ℝ (Fin n) → ℝ} (hf : LocallyIntegrableOn f U)
    {ζ g : ℕ → EuclideanSpace ℝ (Fin n) → ℝ}
    (hζ : ∀ i, ContDiff ℝ 1 (ζ i)) (hcζ : ∀ i, HasCompactSupport (ζ i))
    (hsζ : ∀ i, tsupport (ζ i) ⊆ U)
    (hlocζ : LocallyFinite (fun i => (Subtype.val : U → EuclideanSpace ℝ (Fin n)) ⁻¹'
      tsupport (ζ i))) (hsum : ∀ x ∈ U, ∑ᶠ i, ζ i x = 1)
    (hg : ∀ i, ContDiff ℝ 1 (g i)) (hcg : ∀ i, HasCompactSupport (g i))
    (hsg : ∀ i, tsupport (g i) ⊆ U)
    (hlocg : LocallyFinite (fun i => (Subtype.val : U → EuclideanSpace ℝ (Fin n)) ⁻¹'
      tsupport (g i))) {b : ℕ → ℝ} (hb : Summable b)
    (herr : ∀ i, (∫ x, ‖gradient (g i) x - f x • gradient (ζ i) x‖) ≤ b i) :
    IntegrableOn (gradient (fun x => ∑ᶠ i, g i x)) U ∧
      (∫ x in U, ‖gradient (fun x => ∑ᶠ i, g i x) x‖) ≤ ∑' i, b i := by
  have hfg := finite_support_of_locallyFinite_tsupport
    (fun i => (tsupport_gradient_subset (g i)).trans (hsg i))
    (hlocg.subset fun i => preimage_mono (tsupport_gradient_subset (g i)))
  have hsD (i) : tsupport (fun x => f x • gradient (ζ i) x) ⊆ tsupport (ζ i) :=
    (tsupport_smul_subset_right f (gradient (ζ i))).trans (tsupport_gradient_subset (ζ i))
  have hfD := finite_support_of_locallyFinite_tsupport
    (fun i => (hsD i).trans (hsζ i))
    (hlocζ.subset fun i => preimage_mono (hsD i))
  have hig (i) : Integrable (gradient (g i)) :=
    (continuous_gradient_of_contDiff (hg i)).integrable_of_hasCompactSupport
      ((hcg i).of_isClosed_subset (isClosed_tsupport _) (tsupport_gradient_subset (g i)))
  obtain ⟨hie, he⟩ := integrable_finsum_and_integral_norm_le
    (fun i => (hig i).sub (integrable_smul_gradient hf (hζ i) (hcζ i) (hsζ i)))
    (fun x => (hfg x).sub (hfD x)) hb herr
  have heq (x) (hx : x ∈ U) :
      (∑ᶠ i, (gradient (g i) x - f x • gradient (ζ i) x)) =
        gradient (fun y => ∑ᶠ i, g i y) x := by
    rw [finsum_sub_distrib (hfg x) (hfD x), ← smul_finsum,
      finsum_gradient_partition_eq_zero hU hζ hlocζ hsum hx, smul_zero, sub_zero,
      gradient_finsum_of_locallyFinite hU hg hlocg hx]
  have hae : (fun x => ∑ᶠ i, (gradient (g i) x - f x • gradient (ζ i) x))
      =ᵐ[volume.restrict U] gradient (fun x => ∑ᶠ i, g i x) :=
    (ae_restrict_mem hU.measurableSet).mono fun x hx => heq x hx
  refine ⟨hie.integrableOn.congr hae, ?_⟩
  calc
    _ = ∫ x in U, ‖∑ᶠ i, (gradient (g i) x - f x • gradient (ζ i) x)‖ :=
      (integral_congr_ae (hae.fun_comp norm)).symm
    _ ≤ ∫ x, ‖∑ᶠ i, (gradient (g i) x - f x • gradient (ζ i) x)‖ :=
      setIntegral_le_integral hie.norm (Eventually.of_forall fun _ => norm_nonneg _)
    _ ≤ _ := he


/-- Multiplying a function smooth on an open set by a smooth field supported there
produces a globally smooth field. -/
lemma contDiff_smul_of_tsupport_subset {n : ℕ} {F : Type*}
    [NormedAddCommGroup F] [NormedSpace ℝ F]
    {U : Set (EuclideanSpace ℝ (Fin n))} (hU : IsOpen U)
    {f : EuclideanSpace ℝ (Fin n) → ℝ} {X : EuclideanSpace ℝ (Fin n) → F}
    {m : ℕ∞} (hf : ContDiffOn ℝ m f U) (hX : ContDiff ℝ m X)
    (hsX : tsupport X ⊆ U) : ContDiff ℝ m (fun x => f x • X x) := by
  rw [contDiff_iff_contDiffAt]
  intro x
  by_cases hx : x ∈ U
  · exact (hf.contDiffAt (hU.mem_nhds hx)).smul hX.contDiffAt
  · have hz : X =ᶠ[𝓝 x] (fun _ => 0) :=
      notMem_tsupport_iff_eventuallyEq.mp (fun h => hx (hsX h))
    apply (contDiffAt_const (c := (0 : F))).congr_of_eventuallyEq
    filter_upwards [hz] with y hy
    simp [hy]

/-- The divergence product identity needs differentiability only at the evaluation point. -/
lemma divergenceN_smul_of_differentiableAt {n : ℕ}
    {f : EuclideanSpace ℝ (Fin n) → ℝ}
    {X : EuclideanSpace ℝ (Fin n) → EuclideanSpace ℝ (Fin n)}
    {x : EuclideanSpace ℝ (Fin n)} (hf : DifferentiableAt ℝ f x)
    (hX : DifferentiableAt ℝ X x) :
    divergenceN (fun y => f y • X y) x =
      f x * divergenceN X x + inner ℝ (gradient f x) (X x) := by
  simp only [divergenceN, fderiv_fun_smul hf hX, add_apply,
    smul_apply, ContinuousLinearMap.smulRight_apply,
    PiLp.add_apply, PiLp.smul_apply, smul_eq_mul, Finset.sum_add_distrib, Finset.mul_sum,
    PiLp.inner_apply, Real.inner_apply, gradient_apply_eq_fderiv_single]

/-- On an open domain, C¹ regularity there and an integrable gradient give the variation bound. -/
theorem variation_le_integral_norm_gradient_on {n : ℕ}
    {U : Set (EuclideanSpace ℝ (Fin n))} (hU : IsOpen U)
    {f : EuclideanSpace ℝ (Fin n) → ℝ} (hf : ContDiffOn ℝ 1 f U)
    (hgrad : IntegrableOn (gradient f) U) :
    variation f U ≤ ENNReal.ofReal (∫ x in U, ‖gradient f x‖) := by
  apply iSup_le
  intro X
  apply iSup_le
  intro hX
  apply ENNReal.ofReal_le_ofReal
  have hi := integrable_inner_of_bound hgrad hX.1.continuous.aestronglyMeasurable
    (Eventually.of_forall hX.2.2.2)
  have hfdiv := (integrable_mul_divergenceN
    (hf.continuousOn.locallyIntegrableOn hU.measurableSet)
    hX.1 hX.2.1 hX.2.2.1).integrableOn (s := U)
  have hY := contDiff_smul_of_tsupport_subset hU hf hX.1 hX.2.2.1
  have hsY : tsupport (fun y => f y • X y) ⊆ U :=
    (tsupport_smul_subset_right f X).trans hX.2.2.1
  have hcY : HasCompactSupport (fun y => f y • X y) :=
    hX.2.1.of_isClosed_subset (isClosed_tsupport _) (tsupport_smul_subset_right f X)
  have hzero : (∫ x in U, divergenceN (fun y => f y • X y) x) = 0 := by
    rw [setIntegral_eq_integral_of_forall_compl_eq_zero]
    · exact integral_divergenceN_eq_zero (X := fun y => f y • X y) hY hcY
    · intro x hx
      exact divergenceN_eq_zero_of_notMem_tsupport (fun h => hx (hsY h))
  have heq : (∫ x in U, divergenceN (fun y => f y • X y) x) =
      ∫ x in U, f x * divergenceN X x + inner ℝ (gradient f x) (X x) := by
    apply setIntegral_congr_fun hU.measurableSet
    intro x hx
    exact divergenceN_smul_of_differentiableAt
      ((hf.contDiffAt (hU.mem_nhds hx)).differentiableAt one_ne_zero)
      (hX.1.differentiable one_ne_zero x)
  rw [heq, integral_add hfdiv hi] at hzero
  have hnorm : ‖∫ x in U, inner ℝ (gradient f x) (X x)‖ ≤ ∫ x in U, ‖gradient f x‖ := by
    apply norm_integral_le_of_norm_le hgrad.norm
    exact Eventually.of_forall fun x => by
      simpa only [mul_one] using (norm_inner_le_norm (gradient f x) (X x)).trans
        (mul_le_mul_of_nonneg_left (hX.2.2.2 x) (norm_nonneg _))
  have habs := neg_le_abs (∫ x in U, inner ℝ (gradient f x) (X x))
  rw [Real.norm_eq_abs] at hnorm
  linarith


/-- A nonnegative pointwise finite partition of unity splits a finite measure's total mass. -/
theorem hasSum_integral_partition {A : Type*} [MeasurableSpace A]
    {μ : Measure A} [IsFiniteMeasure μ] {ζ : ℕ → A → ℝ}
    (hζ : ∀ i, AEStronglyMeasurable (ζ i) μ) (hζ₀ : ∀ i x, 0 ≤ ζ i x)
    (hfin : ∀ x, Function.HasFiniteSupport (fun i => ζ i x))
    (hsum : ∀ x, ∑ᶠ i, ζ i x = 1) :
    HasSum (fun i => ∫ x, ζ i x ∂μ) (μ univ).toReal := by
  have heq (x) : (∑' i, ζ i x) = 1 := (tsum_eq_finsum (hfin x)).trans (hsum x)
  have hi : Integrable (fun x => ∑' i, ζ i x) μ := by
    simp_rw [heq]
    exact integrable_const 1
  have h := hasSum_integral_of_dominated_convergence (f := fun _ => (1 : ℝ)) ζ hζ
    (fun i => Eventually.of_forall fun x => by rw [Real.norm_of_nonneg (hζ₀ i x)])
    (Eventually.of_forall fun x => summable_of_hasFiniteSupport (hfin x)) hi
    (Eventually.of_forall fun x => by
      simpa only [heq x] using
        (show Summable (fun i => ζ i x) from summable_of_hasFiniteSupport (hfin x)).hasSum)
  simpa only [integral_const, smul_eq_mul, mul_one, Measure.real] using h

/-- The derivative error of one mollified product is bounded by its share of derivative
mass plus the L¹ error in mollifying the product-rule correction. -/
theorem IsDistributionalPolarRepresentation.integral_gradient_product_error_le {n : ℕ}
    {U : Set (EuclideanSpace ℝ (Fin n))} {f ζ : EuclideanSpace ℝ (Fin n) → ℝ}
    {ρ : Measure U} [IsFiniteMeasureOnCompacts ρ] [SFinite ρ]
    {σ : U → EuclideanSpace ℝ (Fin n)}
    (hpolar : IsDistributionalPolarRepresentation f U ρ σ)
    (hf : LocallyIntegrableOn f U) (hζ : ContDiff ℝ 1 ζ)
    (hcζ : HasCompactSupport ζ) (hsζ : tsupport ζ ⊆ U) (hζ₀ : ∀ x, 0 ≤ ζ x)
    (φ : ContDiffBump (0 : EuclideanSpace ℝ (Fin n))) :
    (∫ x, ‖gradient (φ.normed volume ⋆[ContinuousLinearMap.lsmul ℝ ℝ]
      (fun y => ζ y * f y)) x - f x • gradient ζ x‖) ≤
      (∫ y : U, ζ y ∂ρ) + ∫ x,
        ‖(φ.normed volume ⋆[ContinuousLinearMap.lsmul ℝ ℝ]
          (fun y => f y • gradient ζ y)) x - f x • gradient ζ x‖ := by
  let D := fun y => f y • gradient ζ y
  let M := fun x => ∫ y : U, φ.normed volume (x - y) • (ζ y • σ y) ∂ρ
  have hiσ := hpolar.integrable_smul_compact_factor hζ.continuous hcζ hsζ
  have hiD := integrable_smul_gradient hf hζ hcζ hsζ
  have hiM : Integrable M :=
    (integrable_measure_convolution_integrand measurable_subtype_coe
      φ.integrable_normed φ.continuous_normed hiσ).integral_prod_left
  have hiC := (φ.integrable_normed.integrable_convolution
    (ContinuousLinearMap.lsmul ℝ ℝ) hiD).sub hiD
  have hnorm : (∫ y : U, ‖ζ y • σ y‖ ∂ρ) = ∫ y : U, ζ y ∂ρ := by
    apply integral_congr_ae
    filter_upwards [hpolar.norm_ae] with y hy
    rw [norm_smul, hy, mul_one, Real.norm_of_nonneg (hζ₀ y)]
  have hmass : (∫ x, ‖M x‖) ≤ ∫ y : U, ζ y ∂ρ := by
    simpa only [M, φ.integral_normed, one_mul, hnorm] using
      integral_norm_measure_convolution_le measurable_subtype_coe
        φ.integrable_normed φ.continuous_normed φ.nonneg_normed hiσ
  have heq (x) : gradient (φ.normed volume ⋆[ContinuousLinearMap.lsmul ℝ ℝ]
      (fun y => ζ y * f y)) x - D x =
      M x + ((φ.normed volume ⋆[ContinuousLinearMap.lsmul ℝ ℝ] D) x - D x) := by
    rw [hpolar.gradient_convolution_mul_eq hf hζ hcζ hsζ
      φ.contDiff_normed φ.hasCompactSupport_normed]
    rw [add_sub_assoc, convolution_lsmul_swap]
  calc
    _ = ∫ x, ‖M x + ((φ.normed volume ⋆[ContinuousLinearMap.lsmul ℝ ℝ] D) x - D x)‖ := by
      apply integral_congr_ae
      exact Eventually.of_forall fun x => congrArg norm (heq x)
    _ ≤ ∫ x, ‖M x‖ + ‖(φ.normed volume ⋆[ContinuousLinearMap.lsmul ℝ ℝ] D) x - D x‖ :=
      integral_mono (hiM.add hiC).norm (hiM.norm.add hiC.norm) (fun _ => norm_add_le _ _)
    _ = (∫ x, ‖M x‖) + ∫ x, ‖(φ.normed volume ⋆[ContinuousLinearMap.lsmul ℝ ℝ] D) x - D x‖ :=
      integral_add hiM.norm hiC.norm
    _ ≤ _ := add_le_add hmass le_rfl


/-- On any open domain, a locally BV function admits a smooth approximation with an
arbitrary global L¹ error budget. If its variation is finite, the gradient integral is
at most that variation plus the same budget. -/
theorem exists_smooth_bv_approximation_on {n : ℕ}
    {U : Set (EuclideanSpace ℝ (Fin n))} (hU : IsOpen U)
    {f : EuclideanSpace ℝ (Fin n) → ℝ} (hf : IsLocallyBVOn f U)
    {ε : ℝ} (hε : 0 < ε) :
    ∃ g : EuclideanSpace ℝ (Fin n) → ℝ,
      ContDiffOn ℝ (⊤ : ℕ∞) g U ∧ IntegrableOn (fun x => g x - f x) U ∧
      (∫ x in U, ‖g x - f x‖) ≤ ε ∧
      (variation f U < ∞ → IntegrableOn (gradient g) U ∧
        (∫ x in U, ‖gradient g x‖) ≤ (variation f U).toReal + ε) := by
  classical
  obtain ⟨K, ζ, hζ, hlocζ, hsumζ, hdisj⟩ := exists_smooth_partition_open_domain hU
  obtain ⟨δ, hδ, hlocδ⟩ := exists_locallyFinite_thickenings hU K
    (fun i => (hζ i).2.1) (fun i => (hζ i).2.2.1) hdisj
  let b : ℕ → ℝ := fun i => (ε / 2) * (1 / 2 : ℝ) ^ i
  have hb₀ (i) : 0 < b i := by dsimp [b]; positivity
  have hb : HasSum b ε := by
    simpa only [b, show (1 - (1 / 2 : ℝ))⁻¹ = 2 by norm_num,
      div_mul_cancel₀ ε (by norm_num : (2 : ℝ) ≠ 0)] using
      (hasSum_geometric_of_lt_one (r := (1 / 2 : ℝ)) (by norm_num) (by norm_num)).mul_left (ε / 2)
  let p := fun i x => ζ i x * f x
  have hip (i) : Integrable (p i) :=
    integrable_mul_compact_factor hf.1 (hζ i).1.continuous (hζ i).2.1 (hζ i).2.2.1
  have hsp (i) : tsupport (p i) ⊆ tsupport (ζ i) := tsupport_mul_subset_left
  have hcp (i) : HasCompactSupport (p i) :=
    (hζ i).2.1.of_isClosed_subset (isClosed_tsupport _) (hsp i)
  have hζ₁ (i) : ContDiff ℝ 1 (ζ i) := (hζ i).1.of_le (by simp)
  have hiD (i) : Integrable (fun x => f x • gradient (ζ i) x) :=
    integrable_smul_gradient hf.1 (hζ₁ i) (hζ i).2.1 (hζ i).2.2.1
  choose φ hφδ hφp hφD using fun i =>
    exists_bump_l1_approximation_pair (hip i) (hiD i) (hb₀ i) (hδ i).1
  let g := fun i => (φ i).normed volume ⋆[ContinuousLinearMap.lsmul ℝ ℝ] p i
  have hg (i) : ContDiff ℝ (⊤ : ℕ∞) (g i) :=
    (φ i).hasCompactSupport_normed.contDiff_convolution_left _
      (φ i).contDiff_normed (hip i).locallyIntegrable
  have hcg (i) : HasCompactSupport (g i) :=
    (φ i).hasCompactSupport_normed.convolution _ (hcp i)
  have hig (i) : Integrable (g i) := (φ i).integrable_normed.integrable_convolution _ (hip i)
  have hsgδ (i) : tsupport (g i) ⊆ cthickening (δ i) (tsupport (ζ i)) :=
    (tsupport_bump_convolution_subset (φ i) (hφδ i).le).trans
      (cthickening_subset_of_subset _ (hsp i))
  have hsg (i) : tsupport (g i) ⊆ U := (hsgδ i).trans (hδ i).2
  have hlocg : LocallyFinite (fun i =>
      (Subtype.val : U → EuclideanSpace ℝ (Fin n)) ⁻¹' tsupport (g i)) :=
    hlocδ.subset fun i => preimage_mono (hsgδ i)
  obtain ⟨hgs, hige, hge⟩ := smooth_partition_gluing_l1 hU hf.1
    (fun i => (hζ i).1.continuous) (fun i => (hζ i).2.1) (fun i => (hζ i).2.2.1)
    hlocζ hsumζ hg hig hsg hlocg hb.summable (fun i => (hφp i).le)
  refine ⟨fun x => ∑ᶠ i, g i x, hgs, hige, hb.tsum_eq ▸ hge, ?_⟩
  intro hfin
  obtain ⟨ρ, σ, _, hpolar, hvar⟩ := exists_polar_representation_with_variation hU hf
  have hmass : variation f U = ρ univ := by
    simpa only [Subtype.coe_preimage_self] using hvar U hU Subset.rfl
  let : IsFiniteMeasure ρ := ⟨by rw [← hmass]; exact hfin⟩
  have hfm := hasSum_integral_partition
    (fun i => ((hζ i).1.continuous.comp continuous_subtype_val).aestronglyMeasurable)
    (fun i x => ((hζ i).2.2.2 x).1)
    (fun x : U => finite_support_of_locallyFinite_tsupport
      (fun i => (hζ i).2.2.1) hlocζ x)
    (fun x : U => hsumζ x x.property) (μ := ρ)
  have hbudget : HasSum (fun i => (∫ y : U, ζ i y ∂ρ) + b i)
      ((variation f U).toReal + ε) := by
    rw [hmass]
    exact hfm.add hb
  have herr (i) : (∫ x, ‖gradient (g i) x - f x • gradient (ζ i) x‖) ≤
      (∫ y : U, ζ i y ∂ρ) + b i := by
    exact (hpolar.integral_gradient_product_error_le hf.1 (hζ₁ i) (hζ i).2.1
      (hζ i).2.2.1 (fun x => ((hζ i).2.2.2 x).1) (φ i)).trans
        (add_le_add le_rfl (hφD i).le)
  obtain ⟨hi, hbound⟩ := smooth_partition_gluing_gradient hU hf.1 hζ₁
    (fun i => (hζ i).2.1) (fun i => (hζ i).2.2.1) hlocζ hsumζ
    (fun i => (hg i).of_le (by simp)) hcg hsg hlocg hbudget.summable herr
  exact ⟨hi, hbudget.tsum_eq ▸ hbound⟩


/-- Strict approximation on an arbitrary open domain. Local BV suffices for smooth local
L¹ approximation, including when the total variation is infinite. When it is finite,
the gradient norm integrals converge to its value. -/
theorem strict_approximation_on {n : ℕ}
    {U : Set (EuclideanSpace ℝ (Fin n))} (hU : IsOpen U)
    {f : EuclideanSpace ℝ (Fin n) → ℝ} (hf : IsLocallyBVOn f U) :
    ∃ g : ℕ → EuclideanSpace ℝ (Fin n) → ℝ,
      (∀ j, ContDiffOn ℝ (⊤ : ℕ∞) (g j) U) ∧
      (∀ j, IntegrableOn (fun x => g j x - f x) U) ∧
      Tendsto (fun j => ∫ x in U, |g j x - f x|) atTop (𝓝 0) ∧
      (∀ K, IsCompact K → K ⊆ U →
        Tendsto (fun j => ∫ x in K, |g j x - f x|) atTop (𝓝 0)) ∧
      (variation f U < ∞ → (∀ j, IntegrableOn (gradient (g j)) U) ∧
        Tendsto (fun j => ∫ x in U, ‖gradient (g j) x‖) atTop
          (𝓝 (variation f U).toReal)) := by
  have hpos (j : ℕ) : 0 < (1 : ℝ) / (j + 1) := by positivity
  choose g hg hie he hgrad using fun j => exists_smooth_bv_approximation_on hU hf (hpos j)
  have hε : Tendsto (fun j : ℕ => (1 : ℝ) / (j + 1)) atTop (𝓝 0) :=
    tendsto_one_div_add_atTop_nhds_zero_nat
  have hL1 : Tendsto (fun j => ∫ x in U, |g j x - f x|) atTop (𝓝 0) := by
    apply squeeze_zero (fun j => integral_nonneg fun _ => abs_nonneg _) (fun j => ?_) hε
    simpa only [Real.norm_eq_abs] using he j
  have hlocal (K : Set (EuclideanSpace ℝ (Fin n))) (hKU : K ⊆ U) :
      Tendsto (fun j => ∫ x in K, |g j x - f x|) atTop (𝓝 0) := by
    apply squeeze_zero (fun j => integral_nonneg fun _ => abs_nonneg _) (fun j => ?_) hL1
    exact setIntegral_mono_set (hie j).abs (Eventually.of_forall fun _ => abs_nonneg _)
      (Eventually.of_forall hKU)
  refine ⟨g, hg, hie, hL1, fun K _ hKU => hlocal K hKU, ?_⟩
  intro hfin
  refine ⟨fun j => (hgrad j hfin).1, ?_⟩
  have hlsc := variation_le_liminf_of_locally_l1 hU
    (fun j => (hg j).continuousOn.locallyIntegrableOn hU.measurableSet) hf.1
    (fun K _ hKU => hlocal K hKU)
  have hlower : variation f U ≤
      liminf (fun j => ENNReal.ofReal (∫ x in U, ‖gradient (g j) x‖)) atTop :=
    hlsc.trans (liminf_le_liminf (Eventually.of_forall fun j =>
      variation_le_integral_norm_gradient_on hU ((hg j).of_le (by simp)) (hgrad j hfin).1))
  have hupper : Tendsto (fun j : ℕ =>
      ENNReal.ofReal ((variation f U).toReal + (1 : ℝ) / (j + 1))) atTop (𝓝 (variation f U)) := by
    have ha : Tendsto (fun j : ℕ => (variation f U).toReal + (1 : ℝ) / (j + 1))
        atTop (𝓝 (variation f U).toReal) := by
      simpa only [add_zero] using hε.const_add (variation f U).toReal
    have h := (ENNReal.continuous_ofReal.tendsto ((variation f U).toReal)).comp ha
    simpa only [Function.comp_def, ENNReal.ofReal_toReal hfin.ne] using h
  have ht : Tendsto (fun j => ENNReal.ofReal (∫ x in U, ‖gradient (g j) x‖)) atTop
      (𝓝 (variation f U)) := by
    apply tendsto_order.mpr
    constructor
    · intro a ha
      exact eventually_lt_of_lt_liminf (ha.trans_le hlower)
    · intro a ha
      filter_upwards [(tendsto_order.mp hupper).2 a ha] with j hj
      exact (ENNReal.ofReal_le_ofReal (hgrad j hfin).2).trans_lt hj
  have hreal := (ENNReal.continuousAt_toReal hfin.ne).tendsto.comp ht
  simpa only [Function.comp_def,
    ENNReal.toReal_ofReal (integral_nonneg fun _ => norm_nonneg _)] using hreal


end LiquidDrop

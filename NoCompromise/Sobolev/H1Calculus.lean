import NoCompromise.BV.Rellich

/-!
# Compact cutoffs for weak gradients and H¹

The weak product rule gives a globally defined weak gradient after multiplication
by a C¹ factor compactly supported inside the original domain. Bounded supported
multipliers preserve Lᵖ with quantitative bounds; in particular the cutoff and
zero extension preserve H¹. No H¹ extension theorem is assumed.
-/

open MeasureTheory Filter Metric Set InnerProductSpace
open scoped NNReal ENNReal Topology Gradient Pointwise
namespace LiquidDrop
set_option maxSynthPendingDepth 8

/-- A compactly supported continuous scalar factor makes a locally integrable
vector field globally integrable. -/
lemma integrable_smul_compact_factor_vector {n : ℕ}
    {U : Set (EuclideanSpace ℝ (Fin n))}
    {G : EuclideanSpace ℝ (Fin n) → EuclideanSpace ℝ (Fin n)}
    {ζ : EuclideanSpace ℝ (Fin n) → ℝ} (hG : LocallyIntegrableOn G U)
    (hζ : Continuous ζ) (hcζ : HasCompactSupport ζ) (hsζ : tsupport ζ ⊆ U) :
    Integrable (fun x => ζ x • G x) := by
  have hi := (hG.integrableOn_compact_subset hsζ hcζ).continuousOn_smul
    hζ.continuousOn hcζ
  apply (integrableOn_iff_integrable_of_support_subset ?_).mp hi
  intro x hx
  by_contra hx'
  exact hx (by simp [image_eq_zero_of_notMem_tsupport hx'])

/-- The weak product rule for a compact cutoff inside the original domain.
The product is zero outside the domain and has a global weak gradient. -/
theorem HasWeakGradientOn.mul_compact_cutoff {n : ℕ}
    {U : Set (EuclideanSpace ℝ (Fin n))}
    {f ζ : EuclideanSpace ℝ (Fin n) → ℝ}
    {G : EuclideanSpace ℝ (Fin n) → EuclideanSpace ℝ (Fin n)}
    (hf : HasWeakGradientOn f G U) (hζ : ContDiff ℝ 1 ζ)
    (hcζ : HasCompactSupport ζ) (hsζ : tsupport ζ ⊆ U) :
    HasWeakGradientOn (fun x => ζ x * f x)
      (fun x => ζ x • G x + f x • gradient ζ x) univ := by
  have hiζG := integrable_smul_compact_factor_vector hf.locallyIntegrable_gradient
    hζ.continuous hcζ hsζ
  have hifgrad := integrable_smul_gradient hf.locallyIntegrable_function hζ hcζ hsζ
  have hiζf := integrable_mul_compact_factor hf.locallyIntegrable_function
    hζ.continuous hcζ hsζ
  refine ⟨hiζf.locallyIntegrable.locallyIntegrableOn univ,
    (hiζG.add hifgrad).locallyIntegrable.locallyIntegrableOn univ, ?_⟩
  intro i φ hφ hcφ _
  let v := EuclideanSpace.single i (1 : ℝ)
  have hdφ : Continuous (fun x => fderiv ℝ φ x v) :=
    (hφ.continuous_fderiv (by norm_num)).clm_apply continuous_const
  have hdζ : Continuous (fun x => fderiv ℝ ζ x v) :=
    (hζ.continuous_fderiv (by norm_num)).clm_apply continuous_const
  have hsA : tsupport (fun x => ζ x * fderiv ℝ φ x v) ⊆ U :=
    tsupport_mul_subset_left.trans hsζ
  have hsB : tsupport (fun x => φ x * fderiv ℝ ζ x v) ⊆ U :=
    tsupport_mul_subset_right.trans ((tsupport_fderiv_apply_subset (𝕜 := ℝ) (f := ζ) v).trans hsζ)
  have hiA := (integrable_mul_compact_factor hf.locallyIntegrable_function
    (hζ.continuous.mul hdφ) (hcζ.mul_right) hsA).integrableOn (s := U)
  have hiB := (integrable_mul_compact_factor hf.locallyIntegrable_function
    (hφ.continuous.mul hdζ) ((hcζ.fderiv_apply ℝ v).mul_left) hsB).integrableOn (s := U)
  have hiZ := (integrable_mul_compact_factor
    (locallyIntegrableOn_component hf.locallyIntegrable_gradient i)
    (hζ.continuous.mul hφ.continuous) (hcζ.mul_right)
    (tsupport_mul_subset_left.trans hsζ)).integrableOn (s := U)
  change IntegrableOn (fun x => (ζ x * fderiv ℝ φ x v) * f x) U at hiA
  change IntegrableOn (fun x => (φ x * fderiv ℝ ζ x v) * f x) U at hiB
  change IntegrableOn (fun x => (ζ x * φ x) * G x i) U at hiZ
  have htest := hf.test_eq i (fun x => ζ x * φ x) (hζ.mul hφ) (hcζ.mul_right)
    (tsupport_mul_subset_left.trans hsζ)
  have hderiv (x) : f x * fderiv ℝ (fun y => ζ y * φ y) x v =
      (ζ x * fderiv ℝ φ x v) * f x + (φ x * fderiv ℝ ζ x v) * f x := by
    rw [fderiv_fun_mul (hζ.differentiable one_ne_zero x)
      (hφ.differentiable one_ne_zero x)]
    simp only [add_apply, smul_apply, smul_eq_mul]
    ring
  change -(∫ x in U, f x * fderiv ℝ (fun y => ζ y * φ y) x v) = _ at htest
  simp_rw [hderiv] at htest
  rw [integral_add hiA hiB] at htest
  simp only [setIntegral_univ]
  have hζzero (x) (hx : x ∉ U) : ζ x = 0 :=
    image_eq_zero_of_notMem_tsupport (fun h => hx (hsζ h))
  have hgzero (x) (hx : x ∉ U) : gradient ζ x = 0 :=
    gradient_eq_zero_of_notMem_tsupport (fun h => hx (hsζ h))
  have hleft : (∫ x, ζ x * f x * fderiv ℝ φ x v) =
      ∫ x in U, (ζ x * fderiv ℝ φ x v) * f x := by
    rw [← setIntegral_eq_integral_of_forall_compl_eq_zero
      (s := U) (fun x hx => by rw [hζzero x hx]; simp)]
    congr 1
    ext x
    ring
  have hright : (∫ x, φ x * (ζ x • G x + f x • gradient ζ x) i) =
      (∫ x in U, (ζ x * φ x) * G x i) +
        ∫ x in U, (φ x * fderiv ℝ ζ x v) * f x := by
    rw [← setIntegral_eq_integral_of_forall_compl_eq_zero (s := U)
      (fun x hx => by rw [hζzero x hx, hgzero x hx]; simp)]
    calc
      _ = ∫ x in U, (ζ x * φ x) * G x i + (φ x * fderiv ℝ ζ x v) * f x := by
        congr 1
        ext x
        simp only [PiLp.add_apply, PiLp.smul_apply, smul_eq_mul,
          gradient_apply_eq_fderiv_single]
        ring
      _ = _ := integral_add hiZ hiB
  change -(∫ x, ζ x * f x * fderiv ℝ φ x v) = _
  rw [hleft, hright]
  linarith


/-- Bounded scalar multiplication supported in a measurable domain transfers Lᵖ
membership to the whole space with its expected norm bound. -/
lemma memLp_smul_supported_scalar {n : ℕ} {F : Type*}
    [NormedAddCommGroup F] [NormedSpace ℝ F]
    {U : Set (EuclideanSpace ℝ (Fin n))} (hU : MeasurableSet U)
    {G : EuclideanSpace ℝ (Fin n) → F} {ζ : EuclideanSpace ℝ (Fin n) → ℝ}
    {p : ℝ≥0∞} (hG : MemLp G p (volume.restrict U)) (hζ : Continuous ζ)
    (hsζ : tsupport ζ ⊆ U) {A : ℝ} (hbζ : ∀ x, ‖ζ x‖ ≤ A) :
    MemLp (fun x => ζ x • G x) p volume ∧
      eLpNorm (fun x => ζ x • G x) p volume ≤
        ENNReal.ofReal A * eLpNorm G p (volume.restrict U) := by
  have hi : MemLp (U.indicator G) p volume := (memLp_indicator_iff_restrict hU).mpr hG
  have heq : (fun x => ζ x • G x) = fun x => ζ x • U.indicator G x := by
    funext x
    by_cases hx : x ∈ U
    · rw [indicator_of_mem hx]
    · rw [indicator_of_notMem hx, image_eq_zero_of_notMem_tsupport (fun h => hx (hsζ h))]
      simp
  rw [heq]
  have hb : ∀ᵐ x ∂volume, ‖ζ x • U.indicator G x‖ ≤ A * ‖U.indicator G x‖ :=
    Eventually.of_forall fun x => by
      rw [norm_smul]
      exact mul_le_mul_of_nonneg_right (hbζ x) (norm_nonneg _)
  have hm : AEStronglyMeasurable (fun x => ζ x • U.indicator G x) volume :=
    hζ.aestronglyMeasurable.smul hi.aestronglyMeasurable
  refine ⟨hi.of_le_mul hm hb, ?_⟩
  simpa only [eLpNorm_indicator_eq_eLpNorm_restrict hU] using
    eLpNorm_le_mul_eLpNorm_of_ae_le_mul hm hb p

/-- Multiplication by a bounded supported vector field has the analogous Lᵖ bound. -/
lemma memLp_smul_supported_vector {n : ℕ}
    {U : Set (EuclideanSpace ℝ (Fin n))} (hU : MeasurableSet U)
    {f : EuclideanSpace ℝ (Fin n) → ℝ}
    {X : EuclideanSpace ℝ (Fin n) → EuclideanSpace ℝ (Fin n)}
    {p : ℝ≥0∞} (hf : MemLp f p (volume.restrict U)) (hX : Continuous X)
    (hsX : tsupport X ⊆ U) {B : ℝ} (hbX : ∀ x, ‖X x‖ ≤ B) :
    MemLp (fun x => f x • X x) p volume ∧
      eLpNorm (fun x => f x • X x) p volume ≤
        ENNReal.ofReal B * eLpNorm f p (volume.restrict U) := by
  have hi : MemLp (U.indicator f) p volume := (memLp_indicator_iff_restrict hU).mpr hf
  have heq : (fun x => f x • X x) = fun x => U.indicator f x • X x := by
    funext x
    by_cases hx : x ∈ U
    · rw [indicator_of_mem hx]
    · rw [indicator_of_notMem hx, image_eq_zero_of_notMem_tsupport (fun h => hx (hsX h))]
      simp
  rw [heq]
  have hb : ∀ᵐ x ∂volume, ‖U.indicator f x • X x‖ ≤ B * ‖U.indicator f x‖ :=
    Eventually.of_forall fun x => by
      rw [norm_smul, mul_comm B]
      exact mul_le_mul_of_nonneg_left (hbX x) (norm_nonneg _)
  have hm : AEStronglyMeasurable (fun x => U.indicator f x • X x) volume :=
    hi.aestronglyMeasurable.smul hX.aestronglyMeasurable
  refine ⟨hi.of_le_mul hm hb, ?_⟩
  simpa only [eLpNorm_indicator_eq_eLpNorm_restrict hU] using
    eLpNorm_le_mul_eLpNorm_of_ae_le_mul hm hb p

/-- Compact cutoff and zero extension preserve H¹, with the distributional product
formula and separate L² bounds for the function and its gradient. -/
theorem HasH1GradientOn.mul_compact_cutoff {n : ℕ}
    {U : Set (EuclideanSpace ℝ (Fin n))} (hU : MeasurableSet U)
    {f ζ : EuclideanSpace ℝ (Fin n) → ℝ}
    {G : EuclideanSpace ℝ (Fin n) → EuclideanSpace ℝ (Fin n)}
    (hf : HasH1GradientOn f G U) (hζ : ContDiff ℝ 1 ζ)
    (hcζ : HasCompactSupport ζ) (hsζ : tsupport ζ ⊆ U)
    {A B : ℝ} (hbζ : ∀ x, ‖ζ x‖ ≤ A) (hbgrad : ∀ x, ‖gradient ζ x‖ ≤ B) :
    HasH1GradientOn (fun x => ζ x * f x)
      (fun x => ζ x • G x + f x • gradient ζ x) univ ∧
      HasCompactSupport (fun x => ζ x * f x) ∧
      eLpNorm (fun x => ζ x * f x) 2 volume ≤
        ENNReal.ofReal A * eLpNorm f 2 (volume.restrict U) ∧
      eLpNorm (fun x => ζ x • G x + f x • gradient ζ x) 2 volume ≤
        ENNReal.ofReal A * eLpNorm G 2 (volume.restrict U) +
          ENNReal.ofReal B * eLpNorm f 2 (volume.restrict U) := by
  have hmf := memLp_smul_supported_scalar hU hf.memLp_function hζ.continuous hsζ hbζ
  have hmG := memLp_smul_supported_scalar hU hf.memLp_gradient hζ.continuous hsζ hbζ
  have hmgrad := memLp_smul_supported_vector hU hf.memLp_function
    (continuous_gradient_of_contDiff hζ) ((tsupport_gradient_subset ζ).trans hsζ) hbgrad
  have hmadd := hmG.1.add hmgrad.1
  refine ⟨⟨hf.toHasWeakGradientOn.mul_compact_cutoff hζ hcζ hsζ, ?_, ?_⟩,
    hcζ.of_isClosed_subset (isClosed_tsupport _) tsupport_mul_subset_left, hmf.2, ?_⟩
  · simpa only [smul_eq_mul, Measure.restrict_univ] using hmf.1
  · rw [Measure.restrict_univ]
    exact hmadd
  · exact (eLpNorm_add_le (by norm_num)).trans
      (add_le_add hmG.2 hmgrad.2)

end LiquidDrop

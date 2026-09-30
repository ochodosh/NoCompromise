module

public import NoCompromise.Sobolev.W11Approximation
public import NoCompromise.Sobolev.W11Closed
public import NoCompromise.Sobolev.W11Pullback

@[expose] public section

/-!
# W¹,¹ chain rule under bi-Lipschitz changes of variables

Strong L¹ mollification proves the whole-space rule, and compact cutoffs prove
its local form. The weak gradient is the adjoint derivative of the coordinate
map applied to the original gradient. No boundary trace theorem is used.
-/

noncomputable section
open MeasureTheory Set Filter
open scoped NNReal ENNReal Topology Gradient Convolution
namespace LiquidDrop
set_option maxSynthPendingDepth 8

lemma hasW11GradientOn_smooth_comp_homeomorph {n : ℕ}
    (e : EuclideanSpace ℝ (Fin n) ≃ₜ EuclideanSpace ℝ (Fin n))
    {C K : ℝ≥0} (he : LipschitzWith C e) (hi : LipschitzWith K e.symm)
    {g : EuclideanSpace ℝ (Fin n) → ℝ} (hg : ContDiff ℝ 1 g)
    (hmg : Integrable g) (hmG : Integrable (gradient g)) :
    HasW11GradientOn (g ∘ e)
      (fun x => (fderiv ℝ e x).adjoint (gradient g (e x))) univ := by
  have hw := hasWeakGradientOn_comp_of_contDiffOn isOpen_univ isOpen_univ hg.contDiffOn
    he.lipschitzOnWith (mapsTo_univ _ _)
  have heq := ae_gradient_comp_eq_adjoint hg he
  refine ⟨hw.congr_ae EventuallyEq.rfl ?_,
    (integrable_comp_homeomorph e hi hmg).1.integrableOn,
    (integrable_adjoint_comp_homeomorph e he hi hmG).1.integrableOn⟩
  simpa only [Measure.restrict_univ, Filter.EventuallyEq] using heq

theorem HasW11GradientOn.comp_homeomorph {n : ℕ}
    {f : EuclideanSpace ℝ (Fin n) → ℝ}
    {G : EuclideanSpace ℝ (Fin n) → EuclideanSpace ℝ (Fin n)}
    (hf : HasW11GradientOn f G univ)
    (e : EuclideanSpace ℝ (Fin n) ≃ₜ EuclideanSpace ℝ (Fin n))
    {C K : ℝ≥0} (he : LipschitzWith C e) (hi : LipschitzWith K e.symm) :
    HasW11GradientOn (f ∘ e) (fun x => (fderiv ℝ e x).adjoint (G (e x))) univ ∧
      (∫ x, ‖f (e x)‖) ≤ (K : ℝ) ^ n * ∫ x, ‖f x‖ ∧
      (∫ x, ‖(fderiv ℝ e x).adjoint (G (e x))‖) ≤
        C * (K : ℝ) ^ n * ∫ x, ‖G x‖ := by
  have hif : Integrable f := by
    simpa only [IntegrableOn, Measure.restrict_univ] using hf.integrable_function
  have hiG : Integrable G := by
    simpa only [IntegrableOn, Measure.restrict_univ] using hf.integrable_gradient
  obtain ⟨hif', hbf⟩ := integrable_comp_homeomorph e hi hif
  obtain ⟨hiG', hbG⟩ := integrable_adjoint_comp_homeomorph e he hi hiG
  refine ⟨?_, hbf, hbG⟩
  let φ (j : ℕ) : ContDiffBump (0 : EuclideanSpace ℝ (Fin n)) :=
    ⟨(1 / ((j : ℝ) + 1)) / 2, 1 / ((j : ℝ) + 1), by positivity,
      half_lt_self (by positivity)⟩
  have hφ : Tendsto (fun j => (φ j).rOut) atTop (𝓝 0) :=
    tendsto_one_div_add_atTop_nhds_zero_nat
  let g (j : ℕ) := (φ j).normed volume ⋆[ContinuousLinearMap.lsmul ℝ ℝ] f
  have hgs (j : ℕ) : ContDiff ℝ 1 (g j) := (hf.bump_convolution (φ j)).1.of_le (by simp)
  have hgw (j : ℕ) : HasW11GradientOn (g j) (gradient (g j)) univ := by
    have ha := hf.bump_convolution (φ j)
    exact ha.2.2.congr_ae EventuallyEq.rfl
      (Eventually.of_forall fun x => (ha.2.1 x).symm)
  have hgi (j : ℕ) : Integrable (g j) := by
    simpa only [IntegrableOn, Measure.restrict_univ] using (hgw j).integrable_function
  have hgI (j : ℕ) : Integrable (gradient (g j)) := by
    simpa only [IntegrableOn, Measure.restrict_univ] using (hgw j).integrable_gradient
  have hc (j : ℕ) := hasW11GradientOn_smooth_comp_homeomorph e he hi (hgs j) (hgi j) (hgI j)
  have hlim := hf.tendsto_bump_convolution hφ
  apply hasW11GradientOn_of_tendsto_L1 isOpen_univ hc hif'.integrableOn hiG'.integrableOn
  · simp only [Measure.restrict_univ]
    apply squeeze_zero (fun _ => integral_nonneg fun _ => norm_nonneg _)
      (fun j => (integrable_comp_homeomorph e hi ((hgi j).sub hif)).2)
    simpa only [mul_zero, Pi.sub_apply, g] using hlim.1.const_mul ((K : ℝ) ^ n)
  · simp only [Measure.restrict_univ]
    apply squeeze_zero (fun _ => integral_nonneg fun _ => norm_nonneg _)
      (fun j => ?_) (by simpa only [mul_zero] using hlim.2.const_mul (C * (K : ℝ) ^ n))
    simpa only [Pi.sub_def, map_sub, g] using
      (integrable_adjoint_comp_homeomorph e he hi ((hgI j).sub hiG)).2

theorem HasW11GradientOn.comp_homeomorph_on {n : ℕ}
    {U V : Set (EuclideanSpace ℝ (Fin n))} (hU : IsOpen U) (hV : IsOpen V)
    {f : EuclideanSpace ℝ (Fin n) → ℝ}
    {G : EuclideanSpace ℝ (Fin n) → EuclideanSpace ℝ (Fin n)}
    (hf : HasW11GradientOn f G V)
    (e : EuclideanSpace ℝ (Fin n) ≃ₜ EuclideanSpace ℝ (Fin n))
    {C K : ℝ≥0} (he : LipschitzWith C e) (hi : LipschitzWith K e.symm)
    (hmaps : MapsTo e U V) :
    HasW11GradientOn (f ∘ e) (fun x => (fderiv ℝ e x).adjoint (G (e x))) U ∧
      (∫ x in U, ‖f (e x)‖) ≤ (K : ℝ) ^ n * ∫ x in V, ‖f x‖ ∧
      (∫ x in U, ‖(fderiv ℝ e x).adjoint (G (e x))‖) ≤
        C * (K : ℝ) ^ n * ∫ x in V, ‖G x‖ := by
  obtain ⟨hif, hbf⟩ := integrable_comp_homeomorph_on hU.measurableSet e hi hmaps
    hf.integrable_function
  obtain ⟨hiG, hbG⟩ := integrable_adjoint_comp_homeomorph_on hU.measurableSet e he hi hmaps
    hf.integrable_gradient
  refine ⟨⟨⟨hif.locallyIntegrableOn, hiG.locallyIntegrableOn, ?_⟩, hif, hiG⟩, hbf, hbG⟩
  intro i φ hφ hcφ hsφ
  obtain ⟨ζ, hζ, hcζ, hsζ, hζone, _⟩ := exists_smooth_cutoff_one_near_compact
    (hcφ.image e.continuous) hV (by
      rintro _ ⟨x, hx, rfl⟩
      exact hmaps (hsφ hx))
  have hζ1 : ContDiff ℝ 1 ζ := hζ.of_le (by simp)
  have hcut := hf.toHasWeakGradientOn.w11_mul_compact_cutoff hζ1 hcζ hsζ
  have hchain := (hcut.comp_homeomorph e he hi).1
  have hone (x) (hx : x ∈ tsupport φ) : ζ (e x) = 1 ∧ gradient ζ (e x) = 0 := by
    have hnear : ζ =ᶠ[𝓝 (e x)] (fun _ => 1) :=
      hζone.filter_mono (nhds_le_nhdsSet (mem_image_of_mem e hx))
    exact ⟨hnear.self_of_nhds, by simpa using hnear.gradient_eq⟩
  have heqf : (fun x => (ζ (e x) * f (e x)) *
      fderiv ℝ φ x (EuclideanSpace.single i 1)) =
      (fun x => f (e x) * fderiv ℝ φ x (EuclideanSpace.single i 1)) := by
    funext x
    by_cases hx : x ∈ tsupport φ
    · rw [(hone x hx).1, one_mul]
    · rw [fderiv_of_notMem_tsupport ℝ hx, zero_apply, mul_zero, mul_zero]
  have heqG : (fun x => φ x *
      ((fderiv ℝ e x).adjoint (ζ (e x) • G (e x) + f (e x) • gradient ζ (e x))) i) =
      (fun x => φ x * ((fderiv ℝ e x).adjoint (G (e x))) i) := by
    funext x
    by_cases hx : x ∈ tsupport φ
    · rw [(hone x hx).1, (hone x hx).2, one_smul, smul_zero, add_zero]
    · rw [image_eq_zero_of_notMem_tsupport hx, zero_mul, zero_mul]
  have htest := hchain.test_eq i φ hφ hcφ (subset_univ _)
  simp only [Measure.restrict_univ, Function.comp_def] at htest
  rw [heqf, heqG] at htest
  rw [setIntegral_eq_integral_of_forall_compl_eq_zero (fun x hx => ?_),
    setIntegral_eq_integral_of_forall_compl_eq_zero (fun x hx => ?_)]
  · exact htest
  · rw [image_eq_zero_of_notMem_tsupport (fun hx' => hx (hsφ hx')), zero_mul]
  · rw [fderiv_of_notMem_tsupport ℝ (fun hx' => hx (hsφ hx')), zero_apply, mul_zero]

end LiquidDrop

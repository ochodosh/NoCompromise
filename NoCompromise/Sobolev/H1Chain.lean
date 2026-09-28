import NoCompromise.Sobolev.H1Approximation
import NoCompromise.Sobolev.H1Calculus
import NoCompromise.Sobolev.Hilbert
import Mathlib.Analysis.InnerProductSpace.Adjoint

/-!
# Quantitative H¹ composition under bi-Lipschitz changes of variables

The whole-space chain rule follows from strong L² mollifier approximation. The
weak gradient is the adjoint derivative applied to the pulled-back weak gradient.
-/

noncomputable section

open MeasureTheory Filter Set InnerProductSpace
open scoped NNReal ENNReal Topology Gradient Convolution

namespace LiquidDrop

set_option maxSynthPendingDepth 8

/-- Lᵖ pullback with the exact inverse-Lipschitz volume distortion factor. -/
lemma memLp_comp_of_lipschitz_leftInverse {n : ℕ} {F : Type*} [NormedAddCommGroup F]
    {U V : Set (EuclideanSpace ℝ (Fin n))} (hU : MeasurableSet U)
    {Φ Ψ : EuclideanSpace ℝ (Fin n) → EuclideanSpace ℝ (Fin n)} {K : ℝ≥0}
    (hΦ : ContinuousOn Φ U) (hΨ : LipschitzOnWith K Ψ V)
    (hmaps : MapsTo Φ U V) (hinv : LeftInvOn Ψ Φ U)
    {p : ℝ≥0∞} {g : EuclideanSpace ℝ (Fin n) → F}
    (hg : MemLp g p (volume.restrict V)) :
    MemLp (g ∘ Φ) p (volume.restrict U) ∧
      eLpNorm (g ∘ Φ) p (volume.restrict U) ≤
        ((K : ℝ≥0∞) ^ n) ^ (1 / p).toReal * eLpNorm g p (volume.restrict V) := by
  have hmap := map_volume_restrict_le_of_lipschitz_leftInverse hU hΦ hΨ hmaps hinv
  have hm := hg.of_measure_le_smul (by finiteness : (K : ℝ≥0∞) ^ n ≠ ∞) hmap
  refine ⟨hm.comp_of_map (hΦ.aemeasurable hU), ?_⟩
  rw [← eLpNorm_map_measure hm.aestronglyMeasurable (hΦ.aemeasurable hU)]
  exact eLpNorm_le_of_measure_le_smul hmap

/-- The classical gradient chain rule in adjoint form holds almost everywhere. -/
lemma ae_gradient_comp_eq_adjoint {n : ℕ}
    {g : EuclideanSpace ℝ (Fin n) → ℝ} (hg : ContDiff ℝ 1 g)
    {Φ : EuclideanSpace ℝ (Fin n) → EuclideanSpace ℝ (Fin n)} {C : ℝ≥0}
    (hΦ : LipschitzWith C Φ) :
    ∀ᵐ x ∂volume, gradient (g ∘ Φ) x =
      (fderiv ℝ Φ x).adjoint (gradient g (Φ x)) := by
  have hh := ae_fderiv_comp_of_contDiffOn isOpen_univ isOpen_univ hg.contDiffOn
    hΦ.lipschitzOnWith (mapsTo_univ _ _)
  simp only [Measure.restrict_univ] at hh
  filter_upwards [hh] with x hx
  apply ext_inner_right ℝ
  intro y
  rw [inner_gradient_left, ContinuousLinearMap.adjoint_inner_left, inner_gradient_left,
    hx, ContinuousLinearMap.comp_apply]

/-- A Lipschitz derivative's adjoint acts pointwise with the same Lipschitz bound. -/
lemma norm_fderiv_adjoint_apply_le {n : ℕ}
    {Φ : EuclideanSpace ℝ (Fin n) → EuclideanSpace ℝ (Fin n)} {C : ℝ≥0}
    (hΦ : LipschitzWith C Φ) (x v : EuclideanSpace ℝ (Fin n)) :
    ‖(fderiv ℝ Φ x).adjoint v‖ ≤ C * ‖v‖ := by
  calc
    _ ≤ ‖(fderiv ℝ Φ x).adjoint‖ * ‖v‖ := ContinuousLinearMap.le_opNorm _ _
    _ = ‖fderiv ℝ Φ x‖ * ‖v‖ := by rw [LinearIsometryEquiv.norm_map]
    _ ≤ _ := mul_le_mul_of_nonneg_right (norm_fderiv_le_of_lipschitz ℝ hΦ) (norm_nonneg _)

/-- Multiplication by the measurable adjoint derivative preserves Lᵖ. -/
lemma memLp_fderiv_adjoint_apply {n : ℕ} {p : ℝ≥0∞}
    {μ : Measure (EuclideanSpace ℝ (Fin n))}
    {Φ : EuclideanSpace ℝ (Fin n) → EuclideanSpace ℝ (Fin n)} {C : ℝ≥0}
    (hΦ : LipschitzWith C Φ)
    {G : EuclideanSpace ℝ (Fin n) → EuclideanSpace ℝ (Fin n)}
    (hG : MemLp G p μ) :
    MemLp (fun x => (fderiv ℝ Φ x).adjoint (G x)) p μ ∧
      eLpNorm (fun x => (fderiv ℝ Φ x).adjoint (G x)) p μ ≤
        (C : ℝ≥0∞) * eLpNorm G p μ := by
  have hm : AEStronglyMeasurable (fun x => (fderiv ℝ Φ x).adjoint (G x)) μ := by
    exact (continuous_fst.clm_apply continuous_snd).comp_aestronglyMeasurable
      (((ContinuousLinearMap.adjoint.continuous.measurable.comp
        (measurable_fderiv ℝ Φ)).aestronglyMeasurable).prodMk hG.aestronglyMeasurable)
  have hb : ∀ᵐ x ∂μ, ‖(fderiv ℝ Φ x).adjoint (G x)‖ ≤ C * ‖G x‖ :=
    Eventually.of_forall (fun x => norm_fderiv_adjoint_apply_le hΦ x (G x))
  refine ⟨hG.of_le_mul hm hb, ?_⟩
  simpa only [ENNReal.ofReal_coe_nnreal] using
    eLpNorm_le_mul_eLpNorm_of_ae_le_mul hm hb p

/-- Whole-space L² pullback by a homeomorphism with Lipschitz inverse. -/
lemma memLp_two_comp_homeomorph {n : ℕ} {F : Type*} [NormedAddCommGroup F]
    (e : EuclideanSpace ℝ (Fin n) ≃ₜ EuclideanSpace ℝ (Fin n))
    {K : ℝ≥0} (he : LipschitzWith K e.symm)
    {g : EuclideanSpace ℝ (Fin n) → F} (hg : MemLp g 2 volume) :
    MemLp (g ∘ e) 2 volume ∧
      eLpNorm (g ∘ e) 2 volume ≤
        (K : ℝ≥0∞) ^ ((n : ℝ) / 2) * eLpNorm g 2 volume := by
  have h := memLp_comp_of_lipschitz_leftInverse (U := univ) (V := univ)
    MeasurableSet.univ e.continuous.continuousOn he.lipschitzOnWith (mapsTo_univ _ _)
    (fun x _ => e.symm_apply_apply x) (by simpa only [Measure.restrict_univ] using hg)
  simp only [Measure.restrict_univ] at h
  convert h using 2
  rw [← ENNReal.rpow_natCast, ← ENNReal.rpow_mul]
  congr 2
  norm_num
  ring

/-- Strong L² convergence of functions and gradient fields closes the H¹ graph. -/
lemma hasH1GradientOn_of_tendsto_eLpNorm {n : ℕ} {α : Type*} {l : Filter α} [l.NeBot]
    {U : Set (EuclideanSpace ℝ (Fin n))}
    {f : α → EuclideanSpace ℝ (Fin n) → ℝ}
    {G : α → EuclideanSpace ℝ (Fin n) → EuclideanSpace ℝ (Fin n)}
    {g : EuclideanSpace ℝ (Fin n) → ℝ}
    {H : EuclideanSpace ℝ (Fin n) → EuclideanSpace ℝ (Fin n)}
    (hf : ∀ a, HasH1GradientOn (f a) (G a) U)
    (hg : MemLp g 2 (volume.restrict U)) (hH : MemLp H 2 (volume.restrict U))
    (htf : Tendsto (fun a => eLpNorm (f a - g) 2 (volume.restrict U)) l (𝓝 0))
    (htG : Tendsto (fun a => eLpNorm (G a - H) 2 (volume.restrict U)) l (𝓝 0)) :
    HasH1GradientOn g H U := by
  have hh := hasH1GradientOn_of_tendsto_Lp
    (f := fun a => (hf a).memLp_function.toLp (f a))
    (G := fun a => (hf a).memLp_gradient.toLp (G a))
    (g := hg.toLp g) (H := hH.toLp H)
    (fun a => (hf a).congr_ae (hf a).memLp_function.coeFn_toLp.symm
      (hf a).memLp_gradient.coeFn_toLp.symm)
    ((Lp.tendsto_Lp_iff_tendsto_eLpNorm'' _ _ _ _).mpr htf)
    ((Lp.tendsto_Lp_iff_tendsto_eLpNorm'' _ _ _ _).mpr htG)
  exact hh.congr_ae hg.coeFn_toLp hH.coeFn_toLp

/-- The adjoint pullback of an L² field has the quantitative chain-rule bound. -/
lemma memLp_two_adjoint_comp_homeomorph {n : ℕ}
    (e : EuclideanSpace ℝ (Fin n) ≃ₜ EuclideanSpace ℝ (Fin n))
    {C K : ℝ≥0} (he : LipschitzWith C e) (hi : LipschitzWith K e.symm)
    {G : EuclideanSpace ℝ (Fin n) → EuclideanSpace ℝ (Fin n)}
    (hG : MemLp G 2 volume) :
    MemLp (fun x => (fderiv ℝ e x).adjoint (G (e x))) 2 volume ∧
      eLpNorm (fun x => (fderiv ℝ e x).adjoint (G (e x))) 2 volume ≤
        (C : ℝ≥0∞) * (K : ℝ≥0∞) ^ ((n : ℝ) / 2) * eLpNorm G 2 volume := by
  obtain ⟨hm, hb⟩ := memLp_two_comp_homeomorph e hi hG
  obtain ⟨hm', hb'⟩ := memLp_fderiv_adjoint_apply he hm
  refine ⟨hm', hb'.trans ?_⟩
  simpa only [mul_assoc] using mul_le_mul' (le_refl (C : ℝ≥0∞)) hb

/-- A smooth L² function with L² gradient satisfies the adjoint weak chain rule. -/
lemma hasH1GradientOn_smooth_comp_homeomorph {n : ℕ}
    (e : EuclideanSpace ℝ (Fin n) ≃ₜ EuclideanSpace ℝ (Fin n))
    {C K : ℝ≥0} (he : LipschitzWith C e) (hi : LipschitzWith K e.symm)
    {g : EuclideanSpace ℝ (Fin n) → ℝ} (hg : ContDiff ℝ 1 g)
    (hmg : MemLp g 2 volume) (hmG : MemLp (gradient g) 2 volume) :
    HasH1GradientOn (g ∘ e)
      (fun x => (fderiv ℝ e x).adjoint (gradient g (e x))) univ := by
  have hw := hasWeakGradientOn_comp_of_contDiffOn isOpen_univ isOpen_univ hg.contDiffOn
    he.lipschitzOnWith (mapsTo_univ _ _)
  have heq := ae_gradient_comp_eq_adjoint hg he
  have hm := (memLp_two_comp_homeomorph e hi hmg).1
  have hM := (memLp_two_adjoint_comp_homeomorph e he hi hmG).1
  refine ⟨hw.congr_ae EventuallyEq.rfl ?_, ?_, ?_⟩
  · simpa only [Measure.restrict_univ, Filter.EventuallyEq] using heq
  · simpa only [Measure.restrict_univ] using hm
  · simpa only [Measure.restrict_univ] using hM

/-- Whole-space H¹ is preserved under a globally bi-Lipschitz homeomorphism.
The weak gradient is the adjoint derivative applied to the original weak gradient. -/
theorem HasH1GradientOn.comp_homeomorph {n : ℕ}
    {f : EuclideanSpace ℝ (Fin n) → ℝ}
    {G : EuclideanSpace ℝ (Fin n) → EuclideanSpace ℝ (Fin n)}
    (hf : HasH1GradientOn f G univ)
    (e : EuclideanSpace ℝ (Fin n) ≃ₜ EuclideanSpace ℝ (Fin n))
    {C K : ℝ≥0} (he : LipschitzWith C e) (hi : LipschitzWith K e.symm) :
    HasH1GradientOn (f ∘ e) (fun x => (fderiv ℝ e x).adjoint (G (e x))) univ ∧
      eLpNorm (f ∘ e) 2 volume ≤
        (K : ℝ≥0∞) ^ ((n : ℝ) / 2) * eLpNorm f 2 volume ∧
      eLpNorm (fun x => (fderiv ℝ e x).adjoint (G (e x))) 2 volume ≤
        (C : ℝ≥0∞) * (K : ℝ≥0∞) ^ ((n : ℝ) / 2) * eLpNorm G 2 volume := by
  have hmf : MemLp f 2 volume := by simpa only [Measure.restrict_univ] using hf.memLp_function
  have hmG : MemLp G 2 volume := by simpa only [Measure.restrict_univ] using hf.memLp_gradient
  obtain ⟨hmf', hbf⟩ := memLp_two_comp_homeomorph e hi hmf
  obtain ⟨hmG', hbG⟩ := memLp_two_adjoint_comp_homeomorph e he hi hmG
  refine ⟨?_, hbf, hbG⟩
  let φ (j : ℕ) : ContDiffBump (0 : EuclideanSpace ℝ (Fin n)) :=
    ⟨(1 / ((j : ℝ) + 1)) / 2, 1 / ((j : ℝ) + 1), by positivity,
      half_lt_self (by positivity)⟩
  have hφlim : Tendsto (fun j => (φ j).rOut) atTop (𝓝 0) :=
    tendsto_one_div_add_atTop_nhds_zero_nat
  let g (j : ℕ) := (φ j).normed volume ⋆[ContinuousLinearMap.lsmul ℝ ℝ] f
  have hgs (j : ℕ) : ContDiff ℝ 1 (g j) := (hf.bump_convolution (φ j)).1.of_le (by simp)
  have hgH (j : ℕ) : HasH1GradientOn (g j) (gradient (g j)) univ := by
    have ha := hf.bump_convolution (φ j)
    exact ha.2.2.1.congr_ae EventuallyEq.rfl
      (Eventually.of_forall fun x => (ha.2.1 x).symm)
  have hgm (j : ℕ) : MemLp (g j) 2 volume := by
    simpa only [Measure.restrict_univ] using (hgH j).memLp_function
  have hgM (j : ℕ) : MemLp (gradient (g j)) 2 volume := by
    simpa only [Measure.restrict_univ] using (hgH j).memLp_gradient
  have hc (j : ℕ) := hasH1GradientOn_smooth_comp_homeomorph e he hi (hgs j) (hgm j) (hgM j)
  have hlim := hf.tendsto_bump_convolution hφlim
  apply hasH1GradientOn_of_tendsto_eLpNorm (l := atTop) hc
    (by simpa only [Measure.restrict_univ] using hmf')
    (by simpa only [Measure.restrict_univ] using hmG')
  · simp only [Measure.restrict_univ]
    have ht := ENNReal.Tendsto.const_mul (a := (K : ℝ≥0∞) ^ ((n : ℝ) / 2))
      hlim.1 (Or.inr (by finiteness))
    simp only [mul_zero] at ht
    apply tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds ht
      (fun _ => zero_le) (fun j => ?_)
    exact (memLp_two_comp_homeomorph e hi ((hgm j).sub hmf)).2
  · simp only [Measure.restrict_univ]
    have ht := ENNReal.Tendsto.const_mul
      (a := (C : ℝ≥0∞) * (K : ℝ≥0∞) ^ ((n : ℝ) / 2))
      hlim.2 (Or.inr (by finiteness))
    simp only [mul_zero] at ht
    apply tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds ht
      (fun _ => zero_le) (fun j => ?_)
    simpa only [Pi.sub_def, map_sub, mul_assoc, g] using
      (memLp_two_adjoint_comp_homeomorph e he hi ((hgM j).sub hmG)).2

/-- L² pullback on measurable source and target domains. -/
lemma memLp_two_comp_homeomorph_on {n : ℕ} {F : Type*} [NormedAddCommGroup F]
    {U V : Set (EuclideanSpace ℝ (Fin n))} (hU : MeasurableSet U)
    (e : EuclideanSpace ℝ (Fin n) ≃ₜ EuclideanSpace ℝ (Fin n))
    {K : ℝ≥0} (he : LipschitzWith K e.symm) (hmaps : MapsTo e U V)
    {g : EuclideanSpace ℝ (Fin n) → F} (hg : MemLp g 2 (volume.restrict V)) :
    MemLp (g ∘ e) 2 (volume.restrict U) ∧
      eLpNorm (g ∘ e) 2 (volume.restrict U) ≤
        (K : ℝ≥0∞) ^ ((n : ℝ) / 2) * eLpNorm g 2 (volume.restrict V) := by
  have h := memLp_comp_of_lipschitz_leftInverse hU e.continuous.continuousOn
    he.lipschitzOnWith hmaps (fun x _ => e.symm_apply_apply x) hg
  convert h using 2
  rw [← ENNReal.rpow_natCast, ← ENNReal.rpow_mul]
  congr 2
  norm_num
  ring

/-- The weak H¹ chain rule on arbitrary open domains mapped into one another. -/
theorem HasH1GradientOn.comp_homeomorph_on {n : ℕ}
    {U V : Set (EuclideanSpace ℝ (Fin n))} (hU : IsOpen U) (hV : IsOpen V)
    {f : EuclideanSpace ℝ (Fin n) → ℝ}
    {G : EuclideanSpace ℝ (Fin n) → EuclideanSpace ℝ (Fin n)}
    (hf : HasH1GradientOn f G V)
    (e : EuclideanSpace ℝ (Fin n) ≃ₜ EuclideanSpace ℝ (Fin n))
    {C K : ℝ≥0} (he : LipschitzWith C e) (hi : LipschitzWith K e.symm)
    (hmaps : MapsTo e U V) :
    HasH1GradientOn (f ∘ e) (fun x => (fderiv ℝ e x).adjoint (G (e x))) U ∧
      eLpNorm (f ∘ e) 2 (volume.restrict U) ≤
        (K : ℝ≥0∞) ^ ((n : ℝ) / 2) * eLpNorm f 2 (volume.restrict V) ∧
      eLpNorm (fun x => (fderiv ℝ e x).adjoint (G (e x))) 2 (volume.restrict U) ≤
        (C : ℝ≥0∞) * (K : ℝ≥0∞) ^ ((n : ℝ) / 2) *
          eLpNorm G 2 (volume.restrict V) := by
  obtain ⟨hmf, hbf⟩ := memLp_two_comp_homeomorph_on hU.measurableSet e hi hmaps
    hf.memLp_function
  obtain ⟨hmG, hbG⟩ := memLp_two_comp_homeomorph_on hU.measurableSet e hi hmaps
    hf.memLp_gradient
  obtain ⟨hmH, hbH⟩ := memLp_fderiv_adjoint_apply he hmG
  refine ⟨?_, hbf, hbH.trans ?_⟩
  swap
  · simpa only [mul_assoc] using mul_le_mul' (le_refl (C : ℝ≥0∞)) hbG
  apply hasH1GradientOn_of_memLp_test hmf hmH
  intro i φ hφ hcφ hsφ
  obtain ⟨ζ, hζ, hcζ, hsζ, hζone, hζb⟩ := exists_smooth_cutoff_one_near_compact
    (hcφ.image e.continuous) hV (by
      rintro _ ⟨x, hx, rfl⟩
      exact hmaps (hsφ hx))
  have hζ1 : ContDiff ℝ 1 ζ := hζ.of_le (by simp)
  have hcgrad : HasCompactSupport (gradient ζ) :=
    hcζ.of_isClosed_subset (isClosed_tsupport _) (tsupport_gradient_subset ζ)
  obtain ⟨B, hB⟩ := hcgrad.exists_bound_of_continuous (continuous_gradient_of_contDiff hζ1)
  have hζnorm (x) : ‖ζ x‖ ≤ 1 := by
    rw [Real.norm_eq_abs, abs_of_nonneg (hζb x).1]
    exact (hζb x).2
  have hcut := (hf.mul_compact_cutoff hV.measurableSet hζ1 hcζ hsζ hζnorm hB).1
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

/-- A real sum-of-L²-norms bound for the local bi-Lipschitz chain rule. -/
theorem HasH1GradientOn.comp_homeomorph_on_lpNorm {n : ℕ}
    {U V : Set (EuclideanSpace ℝ (Fin n))} (hU : IsOpen U) (hV : IsOpen V)
    {f : EuclideanSpace ℝ (Fin n) → ℝ}
    {G : EuclideanSpace ℝ (Fin n) → EuclideanSpace ℝ (Fin n)}
    (hf : HasH1GradientOn f G V)
    (e : EuclideanSpace ℝ (Fin n) ≃ₜ EuclideanSpace ℝ (Fin n))
    {C K : ℝ≥0} (he : LipschitzWith C e) (hi : LipschitzWith K e.symm)
    (hmaps : MapsTo e U V) :
    HasH1GradientOn (f ∘ e) (fun x => (fderiv ℝ e x).adjoint (G (e x))) U ∧
      lpNorm (f ∘ e) 2 (volume.restrict U) +
        lpNorm (fun x => (fderiv ℝ e x).adjoint (G (e x))) 2 (volume.restrict U) ≤
      max 1 (C : ℝ) * (K : ℝ) ^ ((n : ℝ) / 2) *
        (lpNorm f 2 (volume.restrict V) + lpNorm G 2 (volume.restrict V)) := by
  obtain ⟨hh, hbf, hbG⟩ := hf.comp_homeomorph_on hU hV e he hi hmaps
  have hff : eLpNorm f 2 (volume.restrict V) ≠ ∞ := hf.memLp_function.eLpNorm_ne_top
  have hfG : eLpNorm G 2 (volume.restrict V) ≠ ∞ := hf.memLp_gradient.eLpNorm_ne_top
  have hb1 : lpNorm (f ∘ e) 2 (volume.restrict U) ≤
      (K : ℝ) ^ ((n : ℝ) / 2) * lpNorm f 2 (volume.restrict V) := by
    have h := ENNReal.toReal_mono (by finiteness) hbf
    simpa only [ENNReal.toReal_mul, ← ENNReal.toReal_rpow, ENNReal.coe_toReal,
      toReal_eLpNorm, toReal_eLpNorm] using h
  have hb2 : lpNorm (fun x => (fderiv ℝ e x).adjoint (G (e x))) 2
      (volume.restrict U) ≤ (C : ℝ) * (K : ℝ) ^ ((n : ℝ) / 2) *
        lpNorm G 2 (volume.restrict V) := by
    have h := ENNReal.toReal_mono (by finiteness) hbG
    simpa only [ENNReal.toReal_mul, ← ENNReal.toReal_rpow, ENNReal.coe_toReal,
      toReal_eLpNorm, toReal_eLpNorm] using h
  refine ⟨hh, (add_le_add hb1 hb2).trans ?_⟩
  have hK : 0 ≤ (K : ℝ) ^ ((n : ℝ) / 2) := Real.rpow_nonneg K.coe_nonneg _
  have h1 : (K : ℝ) ^ ((n : ℝ) / 2) ≤
      max 1 (C : ℝ) * (K : ℝ) ^ ((n : ℝ) / 2) := by
    simpa only [one_mul] using mul_le_mul_of_nonneg_right (le_max_left 1 (C : ℝ)) hK
  have h2 := mul_le_mul_of_nonneg_right (le_max_right 1 (C : ℝ)) hK
  calc
    _ ≤ max 1 (C : ℝ) * (K : ℝ) ^ ((n : ℝ) / 2) * lpNorm f 2 (volume.restrict V) +
        max 1 (C : ℝ) * (K : ℝ) ^ ((n : ℝ) / 2) * lpNorm G 2 (volume.restrict V) :=
      add_le_add (mul_le_mul_of_nonneg_right h1 lpNorm_nonneg)
        (mul_le_mul_of_nonneg_right h2 lpNorm_nonneg)
    _ = _ := by ring

end LiquidDrop

import NoCompromise.BV.ZeroVariation

/-!
# Zero weak derivative on a real interval

The one-dimensional distributional constancy principle is obtained from the
proved BV zero-variation theorem, with the Euclidean one-coordinate space
identified isometrically with the real line.
-/

noncomputable section
open MeasureTheory Set Filter
open scoped Topology ENNReal
namespace LiquidDrop

/-- The real line as one-dimensional Euclidean space, with its exact norm. -/
def euclideanOneReal : EuclideanSpace ℝ (Fin 1) ≃ₗᵢ[ℝ] ℝ :=
  { (PiLp.equivOfUnique 2 ℝ (fun _ : Fin 1 => ℝ)).toLinearEquiv with
    norm_map' := fun x => by simp [EuclideanSpace.norm_eq, Real.sqrt_sq_eq_abs] }

@[simp] lemma euclideanOneReal_apply (x : EuclideanSpace ℝ (Fin 1)) :
    euclideanOneReal x = x 0 := rfl

@[simp] lemma euclideanOneReal_symm_apply (r : ℝ) (i : Fin 1) :
    euclideanOneReal.symm r i = r := rfl

lemma euclideanOneReal_measurePreserving : MeasurePreserving euclideanOneReal :=
  euclideanOneReal.measurePreserving

lemma locallyIntegrableOn_comp_euclideanOneReal {U : Set ℝ} (hU : IsOpen U)
    {f : ℝ → ℝ} (hf : LocallyIntegrableOn f U) :
    LocallyIntegrableOn (f ∘ euclideanOneReal) (euclideanOneReal ⁻¹' U) := by
  apply (locallyIntegrableOn_iff (hU.preimage euclideanOneReal.continuous).isLocallyClosed).mpr
  intro K hK hKc
  have hi : IntegrableOn f (euclideanOneReal '' K) :=
    hf.integrableOn_compact_subset (image_subset_iff.mpr hK)
      (hKc.image euclideanOneReal.continuous)
  have hp := euclideanOneReal_measurePreserving.integrableOn_comp_preimage
    euclideanOneReal.toHomeomorph.measurableEmbedding (s := euclideanOneReal '' K) (f := f)
  rw [euclideanOneReal.injective.preimage_image] at hp
  exact hp.mpr hi

lemma deriv_euclideanOneReal_conjugate
    {X : EuclideanSpace ℝ (Fin 1) → EuclideanSpace ℝ (Fin 1)}
    (hX : ContDiff ℝ 1 X) (x : EuclideanSpace ℝ (Fin 1)) :
    deriv (euclideanOneReal ∘ X ∘ euclideanOneReal.symm) (euclideanOneReal x) =
      divergenceN X x := by
  have hd := euclideanOneReal.toContinuousLinearEquiv.hasFDerivAt.comp _
    ((hX.differentiable one_ne_zero
      (euclideanOneReal.symm (euclideanOneReal x))).hasFDerivAt.comp (euclideanOneReal x)
      euclideanOneReal.symm.toContinuousLinearEquiv.hasFDerivAt)
  simp only [euclideanOneReal.symm_apply_apply] at hd
  have hd' := hd.hasDerivAt.deriv
  change deriv (euclideanOneReal ∘ X ∘ euclideanOneReal.symm) (euclideanOneReal x) =
    euclideanOneReal (fderiv ℝ X x (euclideanOneReal.symm 1)) at hd'
  rw [hd']
  have hone : euclideanOneReal.symm 1 = EuclideanSpace.single 0 1 := by
    ext i
    fin_cases i
    rfl
  rw [hone]
  simp [divergenceN]

/-- A locally integrable real function with zero distributional derivative on an open
connected set is almost everywhere constant there. -/
theorem ae_eq_const_of_integral_mul_deriv_eq_zero {U : Set ℝ}
    (hU : IsOpen U) (hcU : IsPreconnected U) {f : ℝ → ℝ}
    (hf : LocallyIntegrableOn f U)
    (hz : ∀ φ : ℝ → ℝ, ContDiff ℝ 1 φ → HasCompactSupport φ → tsupport φ ⊆ U →
      (∫ r in U, f r * deriv φ r) = 0) :
    ∃ c : ℝ, f =ᵐ[volume.restrict U] fun _ => c := by
  let V := euclideanOneReal ⁻¹' U
  have hV : IsOpen V := hU.preimage euclideanOneReal.continuous
  have hcV : IsPreconnected V := by
    have heq : V = euclideanOneReal.symm '' U :=
      (euclideanOneReal.symm.toEquiv.image_eq_preimage_symm U).symm
    rw [heq]
    exact hcU.image _ euclideanOneReal.symm.continuous.continuousOn
  have hv : variation (f ∘ euclideanOneReal) V = 0 := by
    apply le_antisymm _ bot_le
    unfold variation
    refine iSup_le fun X => iSup_le fun hX => ?_
    let φ : ℝ → ℝ := euclideanOneReal ∘ X ∘ euclideanOneReal.symm
    have hφ : ContDiff ℝ 1 φ := euclideanOneReal.toContinuousLinearEquiv.contDiff.comp
      (hX.1.comp euclideanOneReal.symm.toContinuousLinearEquiv.contDiff)
    have hcφ : HasCompactSupport φ :=
      (hX.2.1.comp_homeomorph euclideanOneReal.symm.toHomeomorph).comp_left
        euclideanOneReal.map_zero
    have hsφ : tsupport φ ⊆ U := by
      intro r hr
      have h1 := tsupport_comp_subset euclideanOneReal.map_zero
        (X ∘ euclideanOneReal.symm) hr
      have h2 := tsupport_comp_subset_preimage X euclideanOneReal.symm.continuous h1
      have h3 := hX.2.2.1 h2
      simpa only [V, mem_preimage, euclideanOneReal.apply_symm_apply] using h3
    have hi := hz φ hφ hcφ hsφ
    have hmp := euclideanOneReal_measurePreserving.restrict_preimage_emb
      euclideanOneReal.toHomeomorph.measurableEmbedding U
    have heq := hmp.integral_comp euclideanOneReal.toHomeomorph.measurableEmbedding
      (fun r => f r * deriv φ r)
    have hder (x : EuclideanSpace ℝ (Fin 1)) :
        deriv φ (euclideanOneReal x) = divergenceN X x :=
      deriv_euclideanOneReal_conjugate hX.1 x
    simp only [hder] at heq
    change (∫ x in V, (f ∘ euclideanOneReal) x * divergenceN X x) = _ at heq
    rw [heq, hi, ENNReal.ofReal_zero]
    exact le_rfl
  obtain ⟨c, hc⟩ := ae_eq_const_of_variation_eq_zero hV hcV
    (locallyIntegrableOn_comp_euclideanOneReal hU hf) hv
  refine ⟨c, ?_⟩
  have hmp := euclideanOneReal_measurePreserving.restrict_preimage_emb
    euclideanOneReal.toHomeomorph.measurableEmbedding U
  rw [← hmp.map_eq]
  exact euclideanOneReal.toHomeomorph.measurableEmbedding.ae_map_iff.mpr hc

/-- On the positive ray, a vanishing mean at the origin fixes the distributional constant. -/
theorem ae_eq_zero_of_integral_mul_deriv_eq_zero_of_average
    {f : ℝ → ℝ} (hf : LocallyIntegrableOn f (Ioi 0))
    (hz : ∀ φ : ℝ → ℝ, ContDiff ℝ 1 φ → HasCompactSupport φ → tsupport φ ⊆ Ioi 0 →
      (∫ r in Ioi 0, f r * deriv φ r) = 0)
    (havg : Tendsto (fun r : ℝ => r⁻¹ * ∫ t in Ioo 0 r, f t) (𝓝[>] 0) (𝓝 0)) :
    f =ᵐ[volume.restrict (Ioi 0)] fun _ => 0 := by
  obtain ⟨c, hc⟩ := ae_eq_const_of_integral_mul_deriv_eq_zero
    isOpen_Ioi isPreconnected_Ioi hf hz
  have heq (r : ℝ) (hr : 0 < r) : r⁻¹ * (∫ t in Ioo 0 r, f t) = c := by
    have hcr : f =ᵐ[volume.restrict (Ioo 0 r)] fun _ => c :=
      ae_restrict_of_ae_restrict_of_subset Ioo_subset_Ioi_self hc
    rw [integral_congr_ae hcr, setIntegral_const]
    simp only [measureReal_def, Real.volume_Ioo, sub_zero, ENNReal.toReal_ofReal hr.le,
      smul_eq_mul]
    field_simp
  have hpos : ∀ᶠ r : ℝ in 𝓝[>] 0, 0 < r := self_mem_nhdsWithin
  have hlim : Tendsto (fun r : ℝ => r⁻¹ * ∫ t in Ioo 0 r, f t) (𝓝[>] 0) (𝓝 c) :=
    tendsto_const_nhds.congr' (hpos.mono fun r hr => (heq r hr).symm)
  have hc0 : c = 0 := tendsto_nhds_unique hlim havg
  simpa only [hc0] using hc

end LiquidDrop

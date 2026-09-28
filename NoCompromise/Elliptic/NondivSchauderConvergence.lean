import NoCompromise.Elliptic.NondivSchauderDifference

/-!
# Strong convergence of genuine coordinate quotients

A C¹,α derivative gives the uniform Taylor remainder bound for every admissible
segment, hence uniform convergence of difference quotients to the actual
coordinate derivative. Finite-volume restrictions then give strong L² convergence.
-/

noncomputable section
open MeasureTheory Filter Metric Set InnerProductSpace
open scoped ENNReal Topology Gradient
namespace LiquidDrop
set_option maxSynthPendingDepth 8

/-- The actual first-order Taylor remainder, with a bound using only the derivative's
Hölder seminorm and the segment between the two points. -/
lemma nondiv_norm_segment_remainder_le {E F : Type*}
    [NormedAddCommGroup E] [NormedSpace ℝ E]
    [NormedAddCommGroup F] [NormedSpace ℝ F]
    {α : ℝ} (hα : 0 ≤ α) {f : E → F} {U : Set E}
    (hU : IsOpen U) (hf : HasC1HolderOn α f U) (x v : E)
    (hseg : ∀ t ∈ Icc (0 : ℝ) 1, x + t • v ∈ U) :
    ‖f (x + v) - f x - fderiv ℝ f x v‖ ≤
      holderSeminorm α (fderiv ℝ f) U * ‖v‖ ^ α * ‖v‖ := by
  have hx : x ∈ U := by simpa only [zero_smul, add_zero] using hseg 0 (by simp)
  have hder (t : ℝ) (ht : t ∈ Icc (0 : ℝ) 1) :
      HasDerivWithinAt (fun s : ℝ => f (x + s • v) - s • fderiv ℝ f x v)
        ((fderiv ℝ f (x + t • v) - fderiv ℝ f x) v) (Icc (0 : ℝ) 1) t := by
    simpa only [sub_apply, one_smul] using!
      ((nondiv_hasDerivAt_segment hU hf.contDiff x v (hseg t ht)).sub
        ((hasDerivAt_id t).smul_const (fderiv ℝ f x v))).hasDerivWithinAt
  have hb (t : ℝ) (ht : t ∈ Ico (0 : ℝ) 1) :
      ‖(fderiv ℝ f (x + t • v) - fderiv ℝ f x) v‖ ≤
        holderSeminorm α (fderiv ℝ f) U * ‖v‖ ^ α * ‖v‖ := by
    apply (ContinuousLinearMap.le_opNorm _ v).trans
    apply mul_le_mul_of_nonneg_right _ (norm_nonneg v)
    apply (hf.derivative_holder.nondiv_norm_sub_le (hseg t (Ico_subset_Icc_self ht)) hx).trans
    apply mul_le_mul_of_nonneg_left _ hf.derivative_holder.seminorm_nonneg
    apply Real.rpow_le_rpow (norm_nonneg _) _ hα
    simp only [add_sub_cancel_left, norm_smul, Real.norm_of_nonneg ht.1]
    simpa only [one_mul] using mul_le_mul_of_nonneg_right ht.2.le (norm_nonneg v)
  have h := norm_image_sub_le_of_norm_deriv_le_segment_01' hder hb
  simp only [one_smul, zero_smul, add_zero, sub_zero] at h
  convert h using 1
  congr 1
  abel

/-- Uniform approximation by coordinate difference quotients, including negative steps. -/
theorem nondiv_norm_coordinateDifferenceQuotient_sub_le {n : ℕ} {F : Type*}
    [NormedAddCommGroup F] [NormedSpace ℝ F]
    {α : ℝ} (hα : 0 ≤ α) {f : EuclideanSpace ℝ (Fin n) → F}
    {U : Set (EuclideanSpace ℝ (Fin n))} (hU : IsOpen U) (hf : HasC1HolderOn α f U)
    (i : Fin n) {h : ℝ} (hh : h ≠ 0) (x : EuclideanSpace ℝ (Fin n))
    (hseg : ∀ t ∈ Icc (0 : ℝ) 1, x + t • (h • EuclideanSpace.single i 1) ∈ U) :
    ‖coordinateDifferenceQuotient i h f x - fderiv ℝ f x (EuclideanSpace.single i 1)‖ ≤
      holderSeminorm α (fderiv ℝ f) U * ‖h‖ ^ α := by
  have hb := nondiv_norm_segment_remainder_le hα hU hf x
    (h • EuclideanSpace.single i 1) hseg
  have he : coordinateDifferenceQuotient i h f x - fderiv ℝ f x (EuclideanSpace.single i 1) =
      h⁻¹ • (f (x + h • EuclideanSpace.single i 1) - f x -
        fderiv ℝ f x (h • EuclideanSpace.single i 1)) := by
    simp only [coordinateDifferenceQuotient, smul_sub, map_smul, smul_smul,
      inv_mul_cancel₀ hh, one_smul]
  rw [he, norm_smul]
  apply (mul_le_mul_of_nonneg_left hb (norm_nonneg _)).trans_eq
  simp only [norm_smul, PiLp.norm_single, norm_one, mul_one, norm_inv]
  calc
    _ = (‖h‖⁻¹ * ‖h‖) * (holderSeminorm α (fderiv ℝ f) U * ‖h‖ ^ α) := by ring
    _ = _ := by rw [inv_mul_cancel₀ (norm_ne_zero_iff.mpr hh), one_mul]

/-- The same explicit modulus controls the actual extended L² norm on any measurable
finite-volume interior set. -/
lemma nondiv_eLpNorm_coordinateDifferenceQuotient_sub_le {n : ℕ} {F : Type*}
    [NormedAddCommGroup F] [NormedSpace ℝ F]
    {α : ℝ} (hα : 0 ≤ α) {f : EuclideanSpace ℝ (Fin n) → F}
    {U V : Set (EuclideanSpace ℝ (Fin n))} (hU : IsOpen U) (hV : MeasurableSet V)
    (hf : HasC1HolderOn α f U) (i : Fin n) {h : ℝ} (hh : h ≠ 0)
    (hseg : ∀ x ∈ V, ∀ t ∈ Icc (0 : ℝ) 1, x + t • (h • EuclideanSpace.single i 1) ∈ U) :
    eLpNorm (fun x => coordinateDifferenceQuotient i h f x -
      fderiv ℝ f x (EuclideanSpace.single i 1)) 2 (volume.restrict V) ≤
      volume V ^ (1 / 2 : ℝ) * ENNReal.ofReal (holderSeminorm α (fderiv ℝ f) U * ‖h‖ ^ α) := by
  have hb : ∀ᵐ x ∂volume.restrict V,
      ‖coordinateDifferenceQuotient i h f x - fderiv ℝ f x (EuclideanSpace.single i 1)‖ ≤
        holderSeminorm α (fderiv ℝ f) U * ‖h‖ ^ α := by
    filter_upwards [ae_restrict_mem hV] with x hx
    exact nondiv_norm_coordinateDifferenceQuotient_sub_le hα hU hf i hh x (hseg x hx)
  have hV0 : ∀ x ∈ V, x ∈ U := fun x hx => by
    simpa only [zero_smul, add_zero] using hseg x hx 0 ⟨le_rfl, zero_le_one⟩
  have hV1 : ∀ x ∈ V, x + h • EuclideanSpace.single i 1 ∈ U := fun x hx => by
    simpa only [one_smul] using hseg x hx 1 ⟨zero_le_one, le_rfl⟩
  have hm : AEStronglyMeasurable (fun x => coordinateDifferenceQuotient i h f x -
      fderiv ℝ f x (EuclideanSpace.single i 1)) (volume.restrict V) := by
    have hfc := hf.contDiff.continuousOn
    have hdc : ContinuousOn (fderiv ℝ f) U :=
      hf.contDiff.continuousOn_fderiv_of_isOpen hU le_rfl
    have hc : ContinuousOn (fun x => h⁻¹ • (f (x + h • EuclideanSpace.single i 1) - f x) -
        fderiv ℝ f x (EuclideanSpace.single i 1)) V :=
      (((hfc.comp (continuousOn_id.add continuousOn_const) hV1).sub
        (hfc.mono hV0)).const_smul _).sub ((hdc.mono hV0).clm_apply continuousOn_const)
    exact hc.aestronglyMeasurable hV
  simpa only [Measure.restrict_apply_univ, ENNReal.toReal_ofNat, one_div] using
    (eLpNorm_le_of_ae_bound (p := 2) hm hb)

/-- Strong L² convergence to the actual coordinate derivative, with no derivative
of order two or prior weak-gradient premise on that coordinate derivative. -/
theorem nondiv_tendsto_coordinateDifferenceQuotient_L2 {n : ℕ} {F : Type*}
    [NormedAddCommGroup F] [NormedSpace ℝ F]
    {α : ℝ} (hα : 0 < α) {f : EuclideanSpace ℝ (Fin n) → F}
    {U V : Set (EuclideanSpace ℝ (Fin n))} (hU : IsOpen U) (hV : MeasurableSet V)
    (hVfin : volume V ≠ ∞) (hf : HasC1HolderOn α f U)
    (i : Fin n) {h : ℕ → ℝ} (hh : ∀ j, h j ≠ 0) (ht : Tendsto h atTop (𝓝 0))
    (hseg : ∀ j x, x ∈ V → ∀ t ∈ Icc (0 : ℝ) 1,
      x + t • (h j • EuclideanSpace.single i 1) ∈ U) :
    Tendsto (fun j => eLpNorm (fun x => coordinateDifferenceQuotient i (h j) f x -
      fderiv ℝ f x (EuclideanSpace.single i 1)) 2 (volume.restrict V)) atTop (𝓝 0) := by
  have hpow : Tendsto (fun j => ‖h j‖ ^ α) atTop (𝓝 0) := by
    simpa only [norm_zero, Real.zero_rpow hα.ne', Function.comp_def] using!
      (Real.continuous_rpow_const hα.le).continuousAt.tendsto.comp ht.norm
  have hreal := hpow.const_mul (holderSeminorm α (fderiv ℝ f) U)
  have hof : Tendsto (fun j => ENNReal.ofReal
      (holderSeminorm α (fderiv ℝ f) U * ‖h j‖ ^ α)) atTop (𝓝 0) := by
    simpa only [mul_zero, ENNReal.ofReal_zero] using ENNReal.tendsto_ofReal hreal
  have hfin : volume V ^ (1 / 2 : ℝ) ≠ ∞ :=
    ENNReal.rpow_ne_top_of_nonneg (by norm_num) hVfin
  have hlim := ENNReal.Tendsto.const_mul hof (Or.inr hfin)
  simp only [mul_zero] at hlim
  apply tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds hlim (fun _ => bot_le)
  intro j
  exact nondiv_eLpNorm_coordinateDifferenceQuotient_sub_le hα.le hU hV hf i (hh j) (hseg j)

end LiquidDrop

import NoCompromise.Sobolev.W11TraceFlat

/-!
# Closure of the weak-gradient graph in L¹

Compact test pairings pass to the limit under actual local L¹ convergence of
the functions and gradient fields. This supplies the closure step for W¹,¹
chart approximation without using any boundary or BV structure theorem.
-/

noncomputable section
open MeasureTheory Set Filter
open scoped ENNReal Topology
namespace LiquidDrop

theorem hasWeakGradientOn_of_tendsto_locallyL1 {n : ℕ}
    {U : Set (EuclideanSpace ℝ (Fin n))} (hU : IsOpen U)
    {f : ℕ → EuclideanSpace ℝ (Fin n) → ℝ}
    {G : ℕ → EuclideanSpace ℝ (Fin n) → EuclideanSpace ℝ (Fin n)}
    {g : EuclideanSpace ℝ (Fin n) → ℝ}
    {H : EuclideanSpace ℝ (Fin n) → EuclideanSpace ℝ (Fin n)}
    (hf : ∀ j, HasWeakGradientOn (f j) (G j) U)
    (hg : LocallyIntegrableOn g U) (hH : LocallyIntegrableOn H U)
    (hcf : ∀ K, IsCompact K → K ⊆ U →
      Tendsto (fun j => ∫ x in K, ‖f j x - g x‖) atTop (𝓝 0))
    (hcG : ∀ K, IsCompact K → K ⊆ U →
      Tendsto (fun j => ∫ x in K, ‖G j x - H x‖) atTop (𝓝 0)) :
    HasWeakGradientOn g H U := by
  refine ⟨hg, hH, ?_⟩
  intro i φ hφ hcφ hsφ
  have hder : Continuous (fun x => fderiv ℝ φ x (EuclideanSpace.single i 1)) :=
    (hφ.continuous_fderiv one_ne_zero).clm_apply continuous_const
  have hleft (v : EuclideanSpace ℝ (Fin n) → ℝ) :
      (∫ x in U, v x * fderiv ℝ φ x (EuclideanSpace.single i 1)) =
        ∫ x in tsupport φ, v x * fderiv ℝ φ x (EuclideanSpace.single i 1) := by
    apply setIntegral_eq_of_subset_of_forall_sdiff_eq_zero hU.measurableSet hsφ
    intro x hx
    rw [fderiv_of_notMem_tsupport ℝ hx.2, zero_apply, mul_zero]
  have hright (V : EuclideanSpace ℝ (Fin n) → EuclideanSpace ℝ (Fin n)) :
      (∫ x in U, φ x * V x i) = ∫ x in tsupport φ, V x i * φ x := by
    rw [setIntegral_eq_of_subset_of_forall_sdiff_eq_zero hU.measurableSet hsφ
      (fun x hx => by rw [image_eq_zero_of_notMem_tsupport hx.2, zero_mul])]
    simp_rw [mul_comm]
  have htf := tendsto_integral_mul_of_l1_on_compact hcφ
    (fun j => (hf j).locallyIntegrable_function.integrableOn_compact_subset hsφ hcφ)
    (hg.integrableOn_compact_subset hsφ hcφ) hder.continuousOn
    (by simpa only [Real.norm_eq_abs] using hcf _ hcφ hsφ)
  have hcoord : Tendsto (fun j => ∫ x in tsupport φ, |G j x i - H x i|)
      atTop (𝓝 0) := by
    apply squeeze_zero (fun _ => integral_nonneg fun _ => abs_nonneg _)
      (fun j => ?_) (hcG _ hcφ hsφ)
    have hiG := (hf j).locallyIntegrable_gradient.integrableOn_compact_subset hsφ hcφ
    have hiH := hH.integrableOn_compact_subset hsφ hcφ
    apply integral_mono (hiG.eval_piLp i |>.sub (hiH.eval_piLp i)).abs (hiG.sub hiH).norm
    intro x
    simpa only [Real.norm_eq_abs, PiLp.sub_apply, Pi.sub_apply] using
      PiLp.norm_apply_le (G j x - H x) i
  have htG := tendsto_integral_mul_of_l1_on_compact hcφ
    (fun j => ((hf j).locallyIntegrable_gradient.integrableOn_compact_subset hsφ hcφ).eval_piLp i)
    ((hH.integrableOn_compact_subset hsφ hcφ).eval_piLp i) hφ.continuous.continuousOn hcoord
  have heq : (fun j => -(∫ x in tsupport φ, f j x *
      fderiv ℝ φ x (EuclideanSpace.single i 1))) =
      fun j => ∫ x in tsupport φ, G j x i * φ x := by
    funext j
    simpa only [hleft, hright] using (hf j).test_eq i φ hφ hcφ hsφ
  rw [hleft, hright]
  exact tendsto_nhds_unique (htf.neg.congr' (Eventually.of_forall fun j => congrFun heq j)) htG

theorem hasW11GradientOn_of_tendsto_L1 {n : ℕ}
    {U : Set (EuclideanSpace ℝ (Fin n))} (hU : IsOpen U)
    {f : ℕ → EuclideanSpace ℝ (Fin n) → ℝ}
    {G : ℕ → EuclideanSpace ℝ (Fin n) → EuclideanSpace ℝ (Fin n)}
    {g : EuclideanSpace ℝ (Fin n) → ℝ}
    {H : EuclideanSpace ℝ (Fin n) → EuclideanSpace ℝ (Fin n)}
    (hf : ∀ j, HasW11GradientOn (f j) (G j) U)
    (hg : IntegrableOn g U) (hH : IntegrableOn H U)
    (hcf : Tendsto (fun j => ∫ x in U, ‖f j x - g x‖) atTop (𝓝 0))
    (hcG : Tendsto (fun j => ∫ x in U, ‖G j x - H x‖) atTop (𝓝 0)) :
    HasW11GradientOn g H U := by
  refine ⟨hasWeakGradientOn_of_tendsto_locallyL1 hU
    (fun j => (hf j).toHasWeakGradientOn) hg.locallyIntegrableOn hH.locallyIntegrableOn ?_ ?_,
    hg, hH⟩
  · intro K _ hKU
    apply squeeze_zero (fun _ => integral_nonneg fun _ => norm_nonneg _)
      (fun j => ?_) hcf
    exact integral_mono_measure (Measure.restrict_mono hKU le_rfl)
      (Eventually.of_forall fun _ => norm_nonneg _)
      ((hf j).integrable_function.sub hg).norm
  · intro K _ hKU
    apply squeeze_zero (fun _ => integral_nonneg fun _ => norm_nonneg _)
      (fun j => ?_) hcG
    exact integral_mono_measure (Measure.restrict_mono hKU le_rfl)
      (Eventually.of_forall fun _ => norm_nonneg _)
      ((hf j).integrable_gradient.sub hH).norm

end LiquidDrop

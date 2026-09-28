import NoCompromise.Regularity.HeightCompactnessError

/-! # The distributional constant-normal identity in a small-excess limit -/

noncomputable section
open Set MeasureTheory Filter Metric
open scoped ENNReal Topology
namespace LiquidDrop

lemma abs_integral_compact_coordinate_error_le
    (μ : Measure AmbientSpace) [IsFiniteMeasureOnCompacts μ]
    {σ : AmbientSpace → AmbientSpace} (hσ : LocallyIntegrable σ μ) (ν : AmbientSpace)
    (φ : CompactlySupportedContinuousMap AmbientSpace ℝ) (i : Fin 3)
    {U : Set AmbientSpace} (hbU : Bornology.IsBounded U) (hs : tsupport φ ⊆ U) :
    |∫ x, φ x * (ν i - σ x i) ∂μ| ≤
      ‖φ.toBoundedContinuousFunction‖ * ∫ x in U, ‖σ x - ν‖ ∂μ := by
  have hd : LocallyIntegrable (fun x => ν - σ x) μ := continuous_const.locallyIntegrable.sub hσ
  have hiG := hd.integrable_smul_left_of_hasCompactSupport φ.continuous φ.hasCompactSupport
  have hi : Integrable (fun x => φ x * (ν i - σ x i)) μ := by
    simpa only [PiLp.smul_apply, PiLp.sub_apply, smul_eq_mul,
      CompactlySupportedContinuousMap.coe_toContinuousMap] using hiG.eval_piLp i
  have hin : IntegrableOn (fun x => ‖σ x - ν‖) U μ := by
    exact (((hσ.sub (show LocallyIntegrable (fun _ => ν) μ from
      continuous_const.locallyIntegrable)).integrableOn_isCompact
        hbU.isCompact_closure).mono_set subset_closure).norm
  have heq : (∫ x in U, φ x * (ν i - σ x i) ∂μ) = ∫ x, φ x * (ν i - σ x i) ∂μ := by
    apply setIntegral_eq_integral_of_forall_compl_eq_zero
    intro x hx
    rw [image_eq_zero_of_notMem_tsupport (fun hh => hx (hs hh)), zero_mul]
  rw [← heq, ← Real.norm_eq_abs]
  calc
    _ ≤ ∫ x in U, ‖φ x * (ν i - σ x i)‖ ∂μ := norm_integral_le_integral_norm _
    _ ≤ ∫ x in U, ‖φ.toBoundedContinuousFunction‖ * ‖σ x - ν‖ ∂μ := by
      apply integral_mono_ae hi.integrableOn.norm (hin.const_mul _)
      apply Eventually.of_forall
      intro x
      dsimp only
      rw [norm_mul]
      apply mul_le_mul (φ.toBoundedContinuousFunction.norm_coe_le_norm x) _
        (norm_nonneg _) (norm_nonneg _)
      simpa only [PiLp.sub_apply, norm_sub_rev] using PiLp.norm_apply_le (ν - σ x) i
    _ = _ := integral_const_mul _ _

lemma IsAmbientOutwardPerimeterPolar.coordinate_pairing_error
    {E : Set AmbientSpace} {μ : Measure AmbientSpace} {σ : AmbientSpace → AmbientSpace}
    (h : IsAmbientOutwardPerimeterPolar E μ σ) (ν : AmbientSpace)
    (i : Fin 3) (φ : CompactlySupportedContinuousMap AmbientSpace ℝ)
    (hφ : ContDiff ℝ 1 φ) :
    -(∫ x, E.indicator (fun _ => (1 : ℝ)) x *
      fderiv ℝ φ x (EuclideanSpace.single i 1)) - (-ν i) * (∫ x, φ x ∂μ) =
      ∫ x, φ x * (ν i - σ x i) ∂μ := by
  let := h.finiteOnCompacts
  have hiG := h.locallyIntegrable.neg.integrable_smul_left_of_hasCompactSupport
    φ.continuous φ.hasCompactSupport
  have hi : Integrable (fun x => φ x * (-σ x i)) μ := by
    simpa only [PiLp.smul_apply, PiLp.neg_apply, Pi.neg_apply, smul_eq_mul,
      CompactlySupportedContinuousMap.coe_toContinuousMap] using hiG.eval_piLp i
  have hc : Integrable (fun x => φ x * (-ν i)) μ :=
    φ.continuous.integrable_of_hasCompactSupport φ.hasCompactSupport |>.mul_const _
  rw [h.coordinate_eq i φ hφ, mul_comm (-ν i), ← integral_mul_const, ← integral_sub hi hc]
  apply integral_congr_ae
  exact Eventually.of_forall fun _ => by ring

theorem tendsto_coordinate_pairing_error_of_excess
    {E : ℕ → Set AmbientSpace} {ω : ℕ → ℝ}
    (hE : ∀ j, IsOmegaMinimal (E j) (ω j)) (hω : ∀ j, ω j ≤ 1)
    {U : Set AmbientSpace} (hbU : Bornology.IsBounded U) (ν : AmbientSpace)
    (he : Tendsto (fun j => normalExcessIntegral (E j) (hE j).locallyFinite
      (hE j).nullMeasurable U ν) atTop (𝓝 0))
    (i : Fin 3) (φ : CompactlySupportedContinuousMap AmbientSpace ℝ)
    (hφ : ContDiff ℝ 1 φ) (hs : tsupport φ ⊆ U) :
    Tendsto (fun j => -(∫ x, (E j).indicator (fun _ => (1 : ℝ)) x *
      fderiv ℝ φ x (EuclideanSpace.single i 1)) - (-ν i) *
        (∫ x, φ x ∂canonicalPerimeterMeasure (E j) (hE j).locallyFinite (hE j).nullMeasurable))
      atTop (𝓝 0) := by
  apply tendsto_zero_iff_norm_tendsto_zero.mpr
  apply squeeze_zero (fun _ => norm_nonneg _)
    (g := fun j => ‖φ.toBoundedContinuousFunction‖ *
      ∫ x in U, ‖reducedNormal (E j) (hE j).locallyFinite (hE j).nullMeasurable x - ν‖
        ∂canonicalPerimeterMeasure (E j) (hE j).locallyFinite (hE j).nullMeasurable)
  · intro j
    have hp : IsAmbientOutwardPerimeterPolar (E j)
        (canonicalPerimeterMeasure (E j) (hE j).locallyFinite (hE j).nullMeasurable)
        (reducedNormal (E j) (hE j).locallyFinite (hE j).nullMeasurable) := by
      rw [canonicalPerimeterMeasure_eq_reducedBoundary_area]
      exact reducedBoundary_outwardPerimeterPolar _ _ _
    let := hp.finiteOnCompacts
    rw [hp.coordinate_pairing_error ν i φ hφ, Real.norm_eq_abs]
    exact abs_integral_compact_coordinate_error_le _ hp.locallyIntegrable ν φ i hbU hs
  · simpa only [mul_zero] using
      (tendsto_integral_normal_error_of_excess hE hω hbU ν he).const_mul
        ‖φ.toBoundedContinuousFunction‖

end LiquidDrop

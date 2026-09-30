module

public import NoCompromise.Elliptic.CampanatoHolderSegment
public import NoCompromise.Elliptic.SobolevChainLocal

@[expose] public section

/-! The segment-average divergence identity follows from translation invariance,
Fubini, and the ordinary fundamental theorem of calculus on the test function.
The datum itself is only continuous; no derivative of it is assumed. -/

noncomputable section
open MeasureTheory Filter Metric Set InnerProductSpace
open scoped ENNReal NNReal Topology Gradient RealInnerProductSpace
namespace LiquidDrop
set_option maxSynthPendingDepth 8

lemma campanato_integral_segment_test_derivative {n : ℕ}
    {φ : EuclideanSpace ℝ (Fin n) → ℝ} (hφ : ContDiff ℝ 1 φ)
    (v y : EuclideanSpace ℝ (Fin n)) :
    (∫ t in Icc (0 : ℝ) 1, fderiv ℝ φ (y - t • v) v) = φ y - φ (y - v) := by
  have hd (t : ℝ) : HasDerivAt (fun s : ℝ => φ (y - s • v))
      (-fderiv ℝ φ (y - t • v) v) t := by
    have hp : HasDerivAt (fun s : ℝ => y - s • v) (-v) t := by
      simpa only [one_smul, id_eq, zero_sub] using!
        (hasDerivAt_const t y).sub ((hasDerivAt_id t).smul_const v)
    simpa only [map_neg, Function.comp_def] using!
      ((hφ.differentiable one_ne_zero (y - t • v)).hasFDerivAt.comp_hasDerivAt t hp)
  have hc : Continuous (fun t : ℝ => fderiv ℝ φ (y - t • v) v) :=
    ((hφ.continuous_fderiv one_ne_zero).comp
      (continuous_const.sub (continuous_id.smul continuous_const))).clm_apply continuous_const
  have ht := intervalIntegral.integral_eq_sub_of_hasDerivAt (fun t _ => hd t)
    (hc.neg.intervalIntegrable 0 1)
  rw [intervalIntegral.integral_neg, intervalIntegral.integral_of_le (by norm_num : (0 : ℝ) ≤ 1),
    ← integral_Icc_eq_integral_Ioc] at ht
  simp only [one_smul, zero_smul, sub_zero] at ht
  linarith

/-- Compact continuous data satisfy the exact directional test identity. -/
theorem campanatoSegmentAverage_integral_fderiv_global {n : ℕ}
    {g φ : EuclideanSpace ℝ (Fin n) → ℝ} (hg : Continuous g) (hcg : HasCompactSupport g)
    (hφ : ContDiff ℝ 1 φ) (hcφ : HasCompactSupport φ) (v : EuclideanSpace ℝ (Fin n)) :
    (∫ x, campanatoSegmentAverage g v x * fderiv ℝ φ x v) =
      -(∫ x, (g (x + v) - g x) * φ x) := by
  let D (x : EuclideanSpace ℝ (Fin n)) := fderiv ℝ φ x v
  have hD : Continuous D := (hφ.continuous_fderiv one_ne_zero).clm_apply continuous_const
  have hcD : HasCompactSupport D := hcφ.fderiv_apply ℝ v
  have hiD : Integrable D volume := hD.integrable_of_hasCompactSupport hcD
  have hig : Integrable g volume := hg.integrable_of_hasCompactSupport hcg
  obtain ⟨M, hM⟩ := hcg.exists_bound_of_continuous hg
  obtain ⟨B, hB⟩ := hcD.exists_bound_of_continuous hD
  let μ := volume.restrict (Icc (0 : ℝ) 1)
  let H (p : EuclideanSpace ℝ (Fin n) × ℝ) := g (p.1 + p.2 • v) * D p.1
  let K (p : EuclideanSpace ℝ (Fin n) × ℝ) := g p.1 * D (p.1 - p.2 • v)
  have hiH : Integrable H (volume.prod μ) := by
    apply ((hiD.norm.const_mul M).mul_prod (integrable_const (μ := μ) (1 : ℝ))).mono'
      ((hg.comp (continuous_fst.add (continuous_snd.smul continuous_const))).mul
        (hD.comp continuous_fst)).aestronglyMeasurable
    filter_upwards [] with p
    dsimp [H]
    rw [abs_mul, mul_one]
    exact mul_le_mul_of_nonneg_right (hM _) (abs_nonneg _)
  have hiK : Integrable K (volume.prod μ) := by
    apply (hig.norm.mul_prod (integrable_const (μ := μ) B)).mono'
      ((hg.comp continuous_fst).mul
        (hD.comp (continuous_fst.sub (continuous_snd.smul continuous_const)))).aestronglyMeasurable
    filter_upwards [] with p
    dsimp [K]
    rw [abs_mul]
    exact mul_le_mul_of_nonneg_left (hB _) (abs_nonneg _)
  have htranslate (t : ℝ) : (∫ x, H (x, t)) = ∫ y, K (y, t) := by
    simpa only [H, K, add_sub_cancel_right] using
      integral_add_right_eq_self (fun y => g y * D (y - t • v)) (t • v)
  have hgp : Integrable (fun x => g x * φ x) :=
    (hg.mul hφ.continuous).integrable_of_hasCompactSupport hcφ.mul_left
  have hgps : Integrable (fun x => g x * φ (x - v)) :=
    (hg.mul (hφ.continuous.comp (continuous_id.sub continuous_const)))
      |>.integrable_of_hasCompactSupport hcg.mul_right
  have hgsp : Integrable (fun x => g (x + v) * φ x) :=
    ((hg.comp (continuous_id.add continuous_const)).mul hφ.continuous)
      |>.integrable_of_hasCompactSupport hcφ.mul_left
  have ht : (∫ y, g y * φ (y - v)) = ∫ x, g (x + v) * φ x := by
    symm
    simpa only [add_sub_cancel_right] using
      integral_add_right_eq_self (fun y => g y * φ (y - v)) v
  calc
    _ = ∫ x, ∫ t, H (x, t) ∂μ := by
      apply integral_congr_ae
      exact Eventually.of_forall fun x => (integral_mul_const (D x) _).symm
    _ = ∫ t, (∫ x, H (x, t)) ∂μ := integral_integral_swap hiH
    _ = ∫ t, (∫ y, K (y, t)) ∂μ := by simp_rw [htranslate]
    _ = ∫ y, ∫ t, K (y, t) ∂μ := (integral_integral_swap hiK).symm
    _ = ∫ y, g y * (φ y - φ (y - v)) := by
      apply integral_congr_ae
      apply Eventually.of_forall
      intro y
      change (∫ t in Icc (0 : ℝ) 1, g y * D (y - t • v)) = _
      rw [integral_const_mul, campanato_integral_segment_test_derivative hφ v y]
    _ = (∫ y, g y * φ y) - ∫ y, g y * φ (y - v) := by
      simp_rw [mul_sub]
      exact integral_sub hgp hgps
    _ = -(∫ x, (g (x + v) - g x) * φ x) := by
      rw [ht]
      simp_rw [sub_mul]
      rw [integral_sub hgsp hgp]
      ring


/-- The genuine local distributional identity uses exactly the segment domain.
The datum need only be continuous on its original open domain. -/
theorem campanatoSegmentAverage_integral_fderiv {n : ℕ}
    {U : Set (EuclideanSpace ℝ (Fin n))} (hU : IsOpen U)
    {g φ : EuclideanSpace ℝ (Fin n) → ℝ} (hg : ContinuousOn g U)
    (hφ : ContDiff ℝ 1 φ) (hcφ : HasCompactSupport φ)
    (v : EuclideanSpace ℝ (Fin n)) (hsφ : tsupport φ ⊆ campanatoSegmentDomain U v) :
    (∫ x, campanatoSegmentAverage g v x * fderiv ℝ φ x v) =
      -(∫ x, (g (x + v) - g x) * φ x) := by
  let K := (fun p : EuclideanSpace ℝ (Fin n) × ℝ => p.1 + p.2 • v) ''
    (tsupport φ ×ˢ Icc (0 : ℝ) 1)
  have hK : IsCompact K := (hcφ.prod isCompact_Icc).image
    (continuous_fst.add (continuous_snd.smul continuous_const))
  have hKU : K ⊆ U := by
    rintro y ⟨⟨x, t⟩, ⟨hx, ht⟩, rfl⟩
    exact hsφ hx t ht
  obtain ⟨η, hη, hcη, hsη, hone, _⟩ := exists_smooth_cutoff_one_near_compact hK hU hKU
  let g' (x : EuclideanSpace ℝ (Fin n)) := η x * g x
  have hg' : Continuous g' := (sobolevChain_contDiff_cutoff hU
    (contDiffOn_zero.mpr hg) (hη.of_le (by simp)) hsη).continuous
  have hcg' : HasCompactSupport g' := hcη.mul_right
  have heq (x : EuclideanSpace ℝ (Fin n)) (hx : x ∈ tsupport φ)
      (t : ℝ) (ht : t ∈ Icc (0 : ℝ) 1) : g' (x + t • v) = g (x + t • v) := by
    have hk : x + t • v ∈ K := ⟨(x, t), ⟨hx, ht⟩, rfl⟩
    have hηx : η (x + t • v) = 1 :=
      (hone.filter_mono (nhds_le_nhdsSet hk)).self_of_nhds
    simp only [g', hηx, one_mul]
  have hleft (x) : campanatoSegmentAverage g' v x * fderiv ℝ φ x v =
      campanatoSegmentAverage g v x * fderiv ℝ φ x v := by
    by_cases hx : x ∈ tsupport φ
    · congr 1
      apply setIntegral_congr_fun measurableSet_Icc
      exact fun t ht => heq x hx t ht
    · rw [fderiv_of_notMem_tsupport ℝ hx]
      simp
  have hright (x) : (g' (x + v) - g' x) * φ x = (g (x + v) - g x) * φ x := by
    by_cases hx : x ∈ tsupport φ
    · have hzero := heq x hx 0 (by simp)
      have hone := heq x hx 1 (by simp)
      simpa only [zero_smul, one_smul, add_zero, hzero, hone] using
        congrArg (fun q : ℝ => q * φ x) (congrArg₂ (· - ·) hone hzero)
    · rw [image_eq_zero_of_notMem_tsupport hx]
      simp
  simpa only [hleft, hright] using
    campanatoSegmentAverage_integral_fderiv_global hg' hcg' hφ hcφ v

/-- The full scalar testing identity for the vector datum G_h, for either sign
of the nonzero step. The direction need not be a unit vector for this identity. -/
theorem campanatoSegmentField_distribution {n : ℕ}
    {U : Set (EuclideanSpace ℝ (Fin n))} (hU : IsOpen U)
    {g φ : EuclideanSpace ℝ (Fin n) → ℝ} (hg : ContinuousOn g U)
    (hφ : ContDiff ℝ 1 φ) (hcφ : HasCompactSupport φ)
    {h : ℝ} (hh : h ≠ 0) (e : EuclideanSpace ℝ (Fin n))
    (hsφ : tsupport φ ⊆ campanatoSegmentDomain U (h • e)) :
    (∫ x, inner ℝ (campanatoSegmentField g h e x) (gradient φ x)) =
      -(∫ x, ((g (x + h • e) - g x) / h) * φ x) := by
  have hid := campanatoSegmentAverage_integral_fderiv hU hg hφ hcφ (h • e) hsφ
  have hleft (x) : campanatoSegmentAverage g (h • e) x * fderiv ℝ φ x (h • e) =
      h * inner ℝ (campanatoSegmentField g h e x) (gradient φ x) := by
    rw [map_smul, smul_eq_mul, ← inner_gradient_left]
    dsimp only [campanatoSegmentField]
    rw [real_inner_smul_left, real_inner_comm e (gradient φ x)]
    ring
  simp_rw [hleft] at hid
  rw [integral_const_mul] at hid
  rw [show (fun x => ((g (x + h • e) - g x) / h) * φ x) =
      (fun x => h⁻¹ * ((g (x + h • e) - g x) * φ x)) by
    funext x; ring, integral_const_mul]
  apply (mul_left_cancel₀ hh)
  rw [mul_neg, ← mul_assoc, mul_inv_cancel₀ hh, one_mul]
  exact hid

end LiquidDrop

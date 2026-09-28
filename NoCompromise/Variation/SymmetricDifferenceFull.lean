import NoCompromise.Variation.WeightedFieldStability
import NoCompromise.Variation.ConstantTranslation
import NoCompromise.Variation.Volume
import NoCompromise.Variation.FreezingFlux

/-!
# Full symmetric-difference variation

For a Lebesgue-measurable set of globally locally finite perimeter, compactly
supported C¹ straight perturbations have the two-sided symmetric-difference
limit given by the absolute normal flux against the actual reduced-boundary
Hausdorff measure. The proof uses weighted field stability, finite smooth
freezing, and the established constant-translation formula. The partition sum
bound removes any dependence on the number of freezing regions.
-/

noncomputable section
open MeasureTheory Set Filter Function Metric
open scoped ENNReal NNReal Topology symmDiff
namespace LiquidDrop

/-- The pointwise indicator difference under the actual inverse straight map. -/
def straightIndicatorDifference (E : Set AmbientSpace)
    (X : AmbientSpace → AmbientSpace) (t : ℝ) (z : AmbientSpace) : ℝ :=
  |E.indicator (fun _ => (1 : ℝ)) (invFun (straightPerturbation X t) z) -
    E.indicator (fun _ => (1 : ℝ)) z|

lemma invFun_straightPerturbation_eq_symm
    {X : AmbientSpace → AmbientSpace} {L : ℝ≥0} (hX : LipschitzWith L X)
    {t : ℝ} (ht : |t| * L < 1) :
    invFun (straightPerturbation X t) = (straightPerturbationHomeomorph hX ht).symm :=
  invFun_eq_of_injective_of_rightInverse (straightPerturbation_bijective hX ht).1
    (straightPerturbationHomeomorph hX ht).apply_symm_apply

lemma indicator_comp_invFun_eq_image {A : Type*} [Nonempty A]
    {f : A → A} (hf : Bijective f) (E : Set A) (z : A) :
    E.indicator (fun _ => (1 : ℝ)) (invFun f z) =
      (f '' E).indicator (fun _ => (1 : ℝ)) z := by
  classical
  have he : z ∈ f '' E ↔ invFun f z ∈ E := by
    constructor
    · rintro ⟨x, hx, rfl⟩
      simpa only [leftInverse_invFun hf.1 x] using hx
    · intro hx
      exact ⟨invFun f z, hx, rightInverse_invFun hf.2 z⟩
  by_cases hz : invFun f z ∈ E
  · simp only [indicator_of_mem hz, indicator_of_mem (he.mpr hz)]
  · simp only [indicator_of_notMem hz, indicator_of_notMem (not_iff_not.mpr he |>.mpr hz)]

lemma straightIndicatorDifference_nonneg (E : Set AmbientSpace)
    (X : AmbientSpace → AmbientSpace) (t : ℝ) (z : AmbientSpace) :
    0 ≤ straightIndicatorDifference E X t z := abs_nonneg _

lemma straightIndicatorDifference_le_one (E : Set AmbientSpace)
    (X : AmbientSpace → AmbientSpace) (t : ℝ) (z : AmbientSpace) :
    straightIndicatorDifference E X t z ≤ 1 := by
  classical
  unfold straightIndicatorDifference
  by_cases h1 : invFun (straightPerturbation X t) z ∈ E <;>
    by_cases h2 : z ∈ E <;> simp [h1, h2]

lemma straightIndicatorDifference_eq_zero_of_notMem_tsupport
    {X : AmbientSpace → AmbientSpace} {L : ℝ≥0} (hX : LipschitzWith L X)
    {t : ℝ} (ht : |t| * L < 1) (E : Set AmbientSpace) {z : AmbientSpace}
    (hz : z ∉ tsupport X) : straightIndicatorDifference E X t z = 0 := by
  rw [straightIndicatorDifference, invFun_straightPerturbation_eq_symm hX ht,
    symm_straightPerturbationHomeomorph_eq_self_of_notMem_tsupport hX ht hz,
    sub_self, abs_zero]

lemma aestronglyMeasurable_straightIndicatorDifference
    {E : Set AmbientSpace} (hmE : NullMeasurableSet E volume)
    {X : AmbientSpace → AmbientSpace} {L : ℝ≥0}
    (hX : LipschitzWith L X) (hXC : ContDiff ℝ 1 X) {t : ℝ} (ht : |t| * L < 1) :
    AEStronglyMeasurable (straightIndicatorDifference E X t) volume := by
  have hmi := nullMeasurableSet_straightPerturbation_image
    (hXC.differentiable one_ne_zero) hX ht hmE
  have hme := ((locallyIntegrable_indicator_one hmi).aestronglyMeasurable.sub
    (locallyIntegrable_indicator_one hmE).aestronglyMeasurable).norm
  change AEStronglyMeasurable (fun z =>
    |(straightPerturbation X t '' E).indicator (fun _ => (1 : ℝ)) z -
      E.indicator (fun _ => (1 : ℝ)) z|) volume at hme
  change AEStronglyMeasurable (fun z =>
    |E.indicator (fun _ => (1 : ℝ)) (invFun (straightPerturbation X t) z) -
      E.indicator (fun _ => (1 : ℝ)) z|) volume
  simp_rw [indicator_comp_invFun_eq_image (straightPerturbation_bijective hX ht)]
  exact hme

lemma integrable_weighted_straightIndicatorDifference
    {E : Set AmbientSpace} (hmE : NullMeasurableSet E volume)
    {X : AmbientSpace → AmbientSpace} {L : ℝ≥0}
    (hX : LipschitzWith L X) (hXC : ContDiff ℝ 1 X) {t : ℝ} (ht : |t| * L < 1)
    {ζ : AmbientSpace → ℝ} (hζ : Continuous ζ) (hcζ : HasCompactSupport ζ) :
    Integrable (fun z => ζ z * straightIndicatorDifference E X t z) := by
  have hd := aestronglyMeasurable_straightIndicatorDifference hmE hX hXC ht
  apply (hζ.integrable_of_hasCompactSupport hcζ).norm.mono'
    (hζ.aestronglyMeasurable.mul hd)
  filter_upwards [] with z
  change ‖ζ z * straightIndicatorDifference E X t z‖ ≤ ‖ζ z‖
  rw [norm_mul, Real.norm_eq_abs, Real.norm_eq_abs,
    abs_of_nonneg (straightIndicatorDifference_nonneg E X t z)]
  simpa only [mul_one] using mul_le_mul_of_nonneg_left
    (straightIndicatorDifference_le_one E X t z) (abs_nonneg (ζ z))

lemma integral_straightIndicatorDifference_eq_symmDiff
    {E : Set AmbientSpace} (hmE : NullMeasurableSet E volume)
    {X : AmbientSpace → AmbientSpace} {L : ℝ≥0}
    (hX : LipschitzWith L X) (hXC : ContDiff ℝ 1 X) {t : ℝ} (ht : |t| * L < 1) :
    (∫ z, straightIndicatorDifference E X t z) =
      volume.real (E ∆ (straightPerturbation X t '' E)) := by
  classical
  have hmi := nullMeasurableSet_straightPerturbation_image
    (hXC.differentiable one_ne_zero) hX ht hmE
  have he (z : AmbientSpace) : straightIndicatorDifference E X t z =
      (E ∆ (straightPerturbation X t '' E)).indicator (fun _ => (1 : ℝ)) z := by
    rw [straightIndicatorDifference, indicator_comp_invFun_eq_image
      (straightPerturbation_bijective hX ht)]
    by_cases hzE : z ∈ E <;> by_cases hzF : z ∈ straightPerturbation X t '' E <;>
      simp [hzE, hzF, mem_symmDiff]
  simp_rw [he]
  rw [integral_indicator₀ (hmE.symmDiff hmi), setIntegral_const]
  simp

lemma eventually_weighted_straightIndicatorDifference_eq_constant_translation
    {Y : AmbientSpace → AmbientSpace} {L : ℝ≥0} (hY : LipschitzWith L Y)
    {a : AmbientSpace} {V : Set AmbientSpace} (hV : IsOpen V)
    (hYa : EqOn Y (fun _ => a) V) {ζ : AmbientSpace → ℝ}
    (hcζ : HasCompactSupport ζ) (hsζ : tsupport ζ ⊆ V) (E : Set AmbientSpace) :
    ∀ᶠ t : ℝ in 𝓝 0, (fun z => ζ z * straightIndicatorDifference E Y t z) =
      (fun z => ζ z * |E.indicator (fun _ => (1 : ℝ)) (z - t • a) -
        E.indicator (fun _ => (1 : ℝ)) z|) := by
  obtain ⟨δ, hδ, hδV⟩ := hcζ.exists_cthickening_subset_open hV hsζ
  have htL : ∀ᶠ t : ℝ in 𝓝 0, |t| * L < 1 := by
    have hh : Tendsto (fun t : ℝ => |t| * L) (𝓝 0) (𝓝 0) := by
      simpa using ((continuous_abs.tendsto 0).mul_const (L : ℝ))
    exact hh.eventually (gt_mem_nhds zero_lt_one)
  have hta : ∀ᶠ t : ℝ in 𝓝 0, |t| * ‖a‖ < δ := by
    have hh : Tendsto (fun t : ℝ => |t| * ‖a‖) (𝓝 0) (𝓝 0) := by
      simpa using ((continuous_abs.tendsto 0).mul_const ‖a‖)
    exact hh.eventually (gt_mem_nhds hδ)
  filter_upwards [htL, hta] with t htL hta
  funext z
  by_cases hz : z ∈ tsupport ζ
  · have hzV : z - t • a ∈ V := by
      apply hδV
      apply mem_cthickening_of_dist_le _ z δ (tsupport ζ) hz
      simpa only [dist_eq_norm, sub_sub_cancel_left, norm_neg, norm_smul, Real.norm_eq_abs]
        using hta.le
    have hsol : straightPerturbation Y t (z - t • a) = z := by
      rw [straightPerturbation, hYa hzV]
      exact sub_add_cancel _ _
    have hi : invFun (straightPerturbation Y t) z = z - t • a := by
      apply (straightPerturbation_bijective hY htL).1
      rw [rightInverse_invFun (straightPerturbation_bijective hY htL).2 z, hsol]
    simp only [straightIndicatorDifference, hi]
  · simp only [image_eq_zero_of_notMem_tsupport hz, zero_mul]

lemma HasLocallyFinitePerimeter.tendsto_weighted_cutoff_constant_field
    {E : Set AmbientSpace} (hE : HasLocallyFinitePerimeter E)
    (hmE : NullMeasurableSet E volume)
    {Y : AmbientSpace → AmbientSpace} {L : ℝ≥0} (hY : LipschitzWith L Y)
    {a : AmbientSpace} {V : Set AmbientSpace} (hV : IsOpen V)
    (hYa : EqOn Y (fun _ => a) V) {ζ : AmbientSpace → ℝ}
    (hζ : Continuous ζ) (hcζ : HasCompactSupport ζ) (hsζ : tsupport ζ ⊆ V) :
    Tendsto (fun t : ℝ => |t|⁻¹ * ∫ z, ζ z * straightIndicatorDifference E Y t z)
      (𝓝[≠] 0)
      (𝓝 (∫ z in reducedBoundary E hE hmE,
        ζ z * |inner ℝ a (reducedNormal E hE hmE z)| ∂hausdorffMeasure2 3)) := by
  apply (hE.tendsto_weighted_constant_translation hmE a hζ hcζ).congr'
  filter_upwards [(eventually_weighted_straightIndicatorDifference_eq_constant_translation
    hY hV hYa hcζ hsζ E).filter_mono nhdsWithin_le_nhds] with t ht
  rw [ht]

lemma integrable_weighted_binary_difference_ae {A : Type*} [MeasurableSpace A]
    {μ : Measure A} {ζ f g : A → ℝ} (hζ : Integrable ζ μ)
    (hf : AEStronglyMeasurable f μ) (hg : AEStronglyMeasurable g μ)
    (hbf : ∀ x, f x ∈ ({0, 1} : Set ℝ)) (hbg : ∀ x, g x ∈ ({0, 1} : Set ℝ)) :
    Integrable (fun x => ζ x * |f x - g x|) μ := by
  apply hζ.norm.mono'
    (hζ.aestronglyMeasurable.mul (continuous_abs.comp_aestronglyMeasurable (hf.sub hg)))
  filter_upwards [] with x
  change ‖ζ x * |f x - g x|‖ ≤ ‖ζ x‖
  rw [Real.norm_eq_abs, abs_mul, abs_abs]
  simpa only [mul_one, Real.norm_eq_abs] using
    mul_le_mul_of_nonneg_left (abs_sub_le_one_of_binary (hbf x) (hbg x)) (abs_nonneg (ζ x))

lemma aestronglyMeasurable_indicator_comp_straightInverse
    {E : Set AmbientSpace} (hmE : NullMeasurableSet E volume)
    {X : AmbientSpace → AmbientSpace} {L : ℝ≥0}
    (hX : LipschitzWith L X) (hXC : ContDiff ℝ 1 X) {t : ℝ} (ht : |t| * L < 1) :
    AEStronglyMeasurable (fun z => E.indicator (fun _ => (1 : ℝ))
      (invFun (straightPerturbation X t) z)) volume := by
  simp_rw [indicator_comp_invFun_eq_image (straightPerturbation_bijective hX ht)]
  exact (locallyIntegrable_indicator_one (nullMeasurableSet_straightPerturbation_image
    (hXC.differentiable one_ne_zero) hX ht hmE)).aestronglyMeasurable

lemma abs_integral_weighted_straightIndicatorDifference_sub_le
    {E : Set AmbientSpace} (hmE : NullMeasurableSet E volume)
    {X Y : AmbientSpace → AmbientSpace} {L : ℝ≥0}
    (hX : LipschitzWith L X) (hY : LipschitzWith L Y)
    (hXC : ContDiff ℝ 1 X) (hYC : ContDiff ℝ 1 Y) {t : ℝ} (ht : |t| * L < 1)
    {ζ : AmbientSpace → ℝ} (hζ : Continuous ζ) (hcζ : HasCompactSupport ζ)
    (hζ0 : ∀ z, 0 ≤ ζ z) :
    |(∫ z, ζ z * straightIndicatorDifference E X t z) -
      ∫ z, ζ z * straightIndicatorDifference E Y t z| ≤
      ∫ z, ζ z * |E.indicator (fun _ => (1 : ℝ)) (invFun (straightPerturbation X t) z) -
        E.indicator (fun _ => (1 : ℝ)) (invFun (straightPerturbation Y t) z)| := by
  have hix := integrable_weighted_straightIndicatorDifference hmE hX hXC ht hζ hcζ
  have hiy := integrable_weighted_straightIndicatorDifference hmE hY hYC ht hζ hcζ
  have hi := integrable_weighted_binary_difference_ae
    (hζ.integrable_of_hasCompactSupport hcζ)
    (aestronglyMeasurable_indicator_comp_straightInverse hmE hX hXC ht)
    (aestronglyMeasurable_indicator_comp_straightInverse hmE hY hYC ht)
    (fun z => by
      classical
      by_cases hz : invFun (straightPerturbation X t) z ∈ E <;> simp [hz])
    (fun z => by
      classical
      by_cases hz : invFun (straightPerturbation Y t) z ∈ E <;> simp [hz])
  rw [← integral_sub hix hiy]
  apply (abs_integral_le_integral_abs).trans
  apply integral_mono (hix.sub hiy).abs hi
  intro z
  change |ζ z * straightIndicatorDifference E X t z -
      ζ z * straightIndicatorDifference E Y t z| ≤ _
  rw [← mul_sub, abs_mul, abs_of_nonneg (hζ0 z)]
  apply mul_le_mul_of_nonneg_left _ (hζ0 z)
  unfold straightIndicatorDifference
  exact (abs_abs_sub_abs_le_abs_sub _ _).trans_eq (by congr 1; ring)


/-- One frozen cell approximates the normalized bulk difference by its constant
normal flux, with error controlled by its perimeter weight. -/
theorem FiniteFieldFreezing.eventually_abs_normalized_bulk_sub_flux_le
    {E : Set AmbientSpace} (hE : HasLocallyFinitePerimeter E)
    (hmE : NullMeasurableSet E volume) {X : AmbientSpace → AmbientSpace}
    {K A : Set AmbientSpace} {η : ℝ} {N : ℕ}
    (d : FiniteFieldFreezing X K A η N) (hXC : ContDiff ℝ 1 X)
    (hη : 0 ≤ η) (j : Fin N) {ε : ℝ} (hε : 0 < ε) :
    ∀ᶠ t : ℝ in 𝓝[≠] 0,
      |(|t|⁻¹ * ∫ z, d.weight j z * straightIndicatorDifference E X t z) -
        ∫ z in reducedBoundary E hE hmE,
          d.weight j z * |inner ℝ (d.constantVector j) (reducedNormal E hE hmE z)|
            ∂hausdorffMeasure2 3| ≤
        16 * η * (∫ z in reducedBoundary E hE hmE, d.weight j z ∂hausdorffMeasure2 3) + ε := by
  have hpolar := reducedBoundary_outwardPerimeterPolar E hE hmE
  have hs := hpolar.eventually_normalized_weighted_field_stability hmE
    (d.original_lipschitz j) (d.field_lipschitz j) hXC
    ((d.frozenField_contDiff j).of_le (by simp)) (d.weight_compact j)
    (d.open_region j) (d.compact_closure_region j) (d.weight_support j)
    hη (fun x hx => d.field_error_le j hx) (d.weight_lipschitz j) (d.weight_nonneg j)
    d.bound_nonneg d.original_bound (d.frozenField_bound j) (half_pos hε)
  have hv : (∫ z in d.region j, d.weight j z
      ∂(hausdorffMeasure2 3).restrict (reducedBoundary E hE hmE)) =
      ∫ z in reducedBoundary E hE hmE, d.weight j z ∂hausdorffMeasure2 3 :=
    setIntegral_eq_integral_of_forall_compl_eq_zero (fun z hz =>
      image_eq_zero_of_notMem_tsupport (fun hh => hz (d.weight_support j hh)))
  simp only [interpolatedInverse, interpolatedField_one, interpolatedField_zero, hv] at hs
  have hlim := hE.tendsto_weighted_cutoff_constant_field hmE (d.field_lipschitz j)
    (d.open_region j) (d.frozenField_eq_constant j) (d.weight_contDiff j).continuous
    (d.weight_compact j) (d.weight_support j)
  have he := (Metric.tendsto_nhds.mp hlim) (ε / 2) (half_pos hε)
  have ht : ∀ᶠ t : ℝ in 𝓝[≠] 0, |t| * d.fieldLip j < 1 := by
    have hh : Tendsto (fun t : ℝ => |t| * d.fieldLip j) (𝓝[≠] 0) (𝓝 0) := by
      simpa using ((continuous_abs.tendsto 0).mul_const (d.fieldLip j : ℝ)).mono_left
        (nhdsWithin_le_nhds (s := ({0} : Set ℝ)ᶜ))
    exact hh.eventually (gt_mem_nhds zero_lt_one)
  filter_upwards [hs, he, ht] with t hs he ht
  rw [setIntegral_eq_integral_of_forall_compl_eq_zero (fun z hz => by
    simp only [image_eq_zero_of_notMem_tsupport hz, zero_mul])] at hs
  have hc := abs_integral_weighted_straightIndicatorDifference_sub_le hmE
    (d.original_lipschitz j) (d.field_lipschitz j) hXC
    ((d.frozenField_contDiff j).of_le (by simp)) ht
    (d.weight_contDiff j).continuous (d.weight_compact j) (d.weight_nonneg j)
  have hn := mul_le_mul_of_nonneg_left hc (inv_nonneg.mpr (abs_nonneg t))
  rw [← abs_of_nonneg (inv_nonneg.mpr (abs_nonneg t)), ← abs_mul, mul_sub] at hn
  rw [Real.dist_eq] at he
  rw [abs_of_nonneg (inv_nonneg.mpr (abs_nonneg t))] at hn
  calc
    _ ≤ |(|t|⁻¹ * ∫ z, d.weight j z * straightIndicatorDifference E X t z) -
        (|t|⁻¹ * ∫ z, d.weight j z * straightIndicatorDifference E (d.frozenField j) t z)| +
        |(|t|⁻¹ * ∫ z, d.weight j z * straightIndicatorDifference E (d.frozenField j) t z) -
          ∫ z in reducedBoundary E hE hmE,
            d.weight j z * |inner ℝ (d.constantVector j) (reducedNormal E hE hmE z)|
              ∂hausdorffMeasure2 3| := abs_sub_le _ _ _
    _ ≤ (16 * η * (∫ z in reducedBoundary E hE hmE, d.weight j z ∂hausdorffMeasure2 3) +
          ε / 2) + ε / 2 := add_le_add (hn.trans hs) he.le
    _ = _ := by ring


/-- The partition is exact for the full bulk difference: outside the support of
`X`, its straight inverse fixes the point. -/
lemma FiniteFieldFreezing.integral_bulk_eq_sum
    {E : Set AmbientSpace} (hmE : NullMeasurableSet E volume)
    {X : AmbientSpace → AmbientSpace} {K A : Set AmbientSpace} {η : ℝ} {N : ℕ}
    (d : FiniteFieldFreezing X K A η N) (hXC : ContDiff ℝ 1 X)
    (hsX : tsupport X ⊆ K) {L : ℝ≥0} (hX : LipschitzWith L X)
    {t : ℝ} (ht : |t| * L < 1) :
    (∫ z, straightIndicatorDifference E X t z) =
      ∑ j, ∫ z, d.weight j z * straightIndicatorDifference E X t z := by
  classical
  have he (z : AmbientSpace) : straightIndicatorDifference E X t z =
      ∑ j, d.weight j z * straightIndicatorDifference E X t z := by
    rw [← Finset.sum_mul]
    by_cases hz : z ∈ K
    · rw [d.sum_eq_one z hz, one_mul]
    · rw [straightIndicatorDifference_eq_zero_of_notMem_tsupport hX ht E
        (fun hh => hz (hsX hh)), mul_zero]
  calc
    _ = ∫ z, ∑ j, d.weight j z * straightIndicatorDifference E X t z :=
      integral_congr_ae (Eventually.of_forall he)
    _ = _ := integral_finsetSum _ (fun j _ =>
      integrable_weighted_straightIndicatorDifference hmE hX hXC ht
        (d.weight_contDiff j).continuous (d.weight_compact j))

/-- Finite weighted stability and the exact constant-translation limits control
the full normalized bulk difference, with no overlap or cardinality factor. -/
theorem FiniteFieldFreezing.eventually_abs_normalized_total_bulk_sub_flux_le
    {E : Set AmbientSpace} (hE : HasLocallyFinitePerimeter E)
    (hmE : NullMeasurableSet E volume) {X : AmbientSpace → AmbientSpace}
    {K A : Set AmbientSpace} {η : ℝ} {N : ℕ}
    (d : FiniteFieldFreezing X K A η N) (hXC : ContDiff ℝ 1 X)
    (hcX : HasCompactSupport X) (hsX : tsupport X ⊆ K)
    (hη : 0 ≤ η) {ε : ℝ} (hε : 0 < ε) :
    ∀ᶠ t : ℝ in 𝓝[≠] 0,
      |(|t|⁻¹ * ∫ z, straightIndicatorDifference E X t z) -
        ∑ j, ∫ z in reducedBoundary E hE hmE,
          d.weight j z * |inner ℝ (d.constantVector j) (reducedNormal E hE hmE z)|
            ∂hausdorffMeasure2 3| ≤
        16 * η * (∑ j, ∫ z in reducedBoundary E hE hmE, d.weight j z ∂hausdorffMeasure2 3) + ε := by
  classical
  have hden : 0 < (N : ℝ) + 1 := by positivity
  have hp := eventually_all.mpr (fun j => d.eventually_abs_normalized_bulk_sub_flux_le
    hE hmE hXC hη j (div_pos hε hden))
  obtain ⟨L, hLX⟩ := ContDiff.lipschitzWith_of_hasCompactSupport hcX hXC one_ne_zero
  have ht : ∀ᶠ t : ℝ in 𝓝[≠] 0, |t| * L < 1 := by
    have hh : Tendsto (fun t : ℝ => |t| * L) (𝓝[≠] 0) (𝓝 0) := by
      simpa using ((continuous_abs.tendsto 0).mul_const (L : ℝ)).mono_left
        (nhdsWithin_le_nhds (s := ({0} : Set ℝ)ᶜ))
    exact hh.eventually (gt_mem_nhds zero_lt_one)
  filter_upwards [hp, ht] with t hp ht
  rw [d.integral_bulk_eq_sum hmE hXC hsX hLX ht, Finset.mul_sum, ← Finset.sum_sub_distrib]
  apply (Finset.abs_sum_le_sum_abs _ _).trans
  apply (Finset.sum_le_sum (fun j _ => hp j)).trans
  rw [Finset.sum_add_distrib, ← Finset.mul_sum]
  simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
  have hδ : 0 ≤ ε / ((N : ℝ) + 1) := (div_pos hε hden).le
  have hc : (N : ℝ) * (ε / ((N : ℝ) + 1)) ≤ ε := by
    calc
      _ ≤ ((N : ℝ) + 1) * (ε / ((N : ℝ) + 1)) := by nlinarith
      _ = ε := by field_simp
  linarith


/-- The inverse-indicator form of the full symmetric-difference limit. -/
theorem HasLocallyFinitePerimeter.tendsto_normalized_straightIndicatorDifference
    {E : Set AmbientSpace} (hE : HasLocallyFinitePerimeter E)
    (hmE : NullMeasurableSet E volume) {X : AmbientSpace → AmbientSpace}
    (hXC : ContDiff ℝ 1 X) (hcX : HasCompactSupport X) :
    Tendsto (fun t : ℝ => |t|⁻¹ * ∫ z, straightIndicatorDifference E X t z)
      (𝓝[≠] 0)
      (𝓝 (∫ z in reducedBoundary E hE hmE,
        |inner ℝ (X z) (reducedNormal E hE hmE z)| ∂hausdorffMeasure2 3)) := by
  classical
  have hpolar := reducedBoundary_outwardPerimeterPolar E hE hmE
  let μ := (hausdorffMeasure2 3).restrict (reducedBoundary E hE hmE)
  obtain ⟨R, hR⟩ := hcX.isBounded.subset_ball (0 : AmbientSpace)
  let A := ball (0 : AmbientSpace) R
  let B := μ.real A
  have hB : 0 ≤ B := ENNReal.toReal_nonneg
  apply Metric.tendsto_nhds.mpr
  intro ε hε
  let η := ε / (68 * (B + 1))
  have hη : 0 < η := div_pos hε (by positivity)
  obtain ⟨N, ⟨d⟩⟩ := exists_finiteFieldFreezing hcX isOpen_ball isBounded_ball hR hXC hcX hη
  have he := d.eventually_abs_normalized_total_bulk_sub_flux_le hE hmE hXC hcX
    (Subset.refl _) hη.le (half_pos hε)
  have hf := d.integral_flux_error_le hpolar hXC.continuous hcX (Subset.refl _) hη.le
  have hw := d.sum_integral_weight_le hpolar
  have hnum : 17 * η * B + ε / 2 < ε := by
    have hid : 68 * (B + 1) * η = ε := by
      dsimp [η]
      field_simp
    have hn : 0 ≤ η := hη.le
    nlinarith
  filter_upwards [he] with t ht
  rw [Real.dist_eq]
  calc
    _ ≤ |(|t|⁻¹ * ∫ z, straightIndicatorDifference E X t z) -
        ∑ j, ∫ z in reducedBoundary E hE hmE,
          d.weight j z * |inner ℝ (d.constantVector j) (reducedNormal E hE hmE z)|
            ∂hausdorffMeasure2 3| +
        |(∑ j, ∫ z in reducedBoundary E hE hmE,
          d.weight j z * |inner ℝ (d.constantVector j) (reducedNormal E hE hmE z)|
            ∂hausdorffMeasure2 3) -
          ∫ z in reducedBoundary E hE hmE,
            |inner ℝ (X z) (reducedNormal E hE hmE z)| ∂hausdorffMeasure2 3| := abs_sub_le _ _ _
    _ ≤ (16 * η * (∑ j, ∫ z in reducedBoundary E hE hmE,
          d.weight j z ∂hausdorffMeasure2 3) + ε / 2) + η * B := add_le_add ht hf
    _ ≤ 17 * η * B + ε / 2 := by
      have hm := mul_le_mul_of_nonneg_left hw (show 0 ≤ 16 * η by positivity)
      change 16 * η * (∑ j, ∫ z in reducedBoundary E hE hmE,
        d.weight j z ∂hausdorffMeasure2 3) ≤ 16 * η * B at hm
      linarith
    _ < ε := hnum

/-- Symmetric difference is supported where the compact perturbing field is
supported, since the straight map and its inverse fix every exterior point. -/
lemma symmDiff_straightPerturbation_subset_tsupport
    {X : AmbientSpace → AmbientSpace} {L : ℝ≥0} (hX : LipschitzWith L X)
    {t : ℝ} (ht : |t| * L < 1) (E : Set AmbientSpace) :
    E ∆ (straightPerturbation X t '' E) ⊆ tsupport X := by
  classical
  intro z hz
  by_contra hzX
  have hfix := straightPerturbation_eq_self_of_notMem_tsupport X t hzX
  have him : z ∈ straightPerturbation X t '' E ↔ z ∈ E := by
    constructor
    · rintro ⟨x, hx, hfx⟩
      have he : x = z := (straightPerturbation_bijective hX ht).1 (hfx.trans hfix.symm)
      exact he ▸ hx
    · intro hzE
      exact ⟨z, hzE, hfix⟩
  rcases mem_symmDiff.mp hz with hz | hz
  · exact hz.2 (him.mpr hz.1)
  · exact hz.2 (him.mp hz.1)

lemma eventually_measure_symmDiff_straightPerturbation_lt_top
    {X : AmbientSpace → AmbientSpace} (hXC : ContDiff ℝ 1 X)
    (hcX : HasCompactSupport X) (E : Set AmbientSpace) :
    ∀ᶠ t : ℝ in 𝓝 0, volume (E ∆ (straightPerturbation X t '' E)) < ∞ := by
  obtain ⟨L, hLX⟩ := ContDiff.lipschitzWith_of_hasCompactSupport hcX hXC one_ne_zero
  have hh : Tendsto (fun t : ℝ => |t| * L) (𝓝 0) (𝓝 0) := by
    simpa using ((continuous_abs.tendsto 0).mul_const (L : ℝ))
  filter_upwards [hh.eventually (gt_mem_nhds zero_lt_one)] with t ht
  exact (measure_mono (symmDiff_straightPerturbation_subset_tsupport hLX ht E)).trans_lt
    hcX.measure_lt_top

/-- The complete two-sided symmetric-difference variation formula for a globally
locally finite-perimeter, Lebesgue-measurable set and a compactly supported C¹
field. No finite-volume or finite-total-perimeter assumption is imposed. -/
theorem HasLocallyFinitePerimeter.tendsto_symmDiff_straightPerturbation
    {E : Set AmbientSpace} (hE : HasLocallyFinitePerimeter E)
    (hmE : NullMeasurableSet E volume) {X : AmbientSpace → AmbientSpace}
    (hXC : ContDiff ℝ 1 X) (hcX : HasCompactSupport X) :
    Tendsto (fun t : ℝ => volume.real (E ∆ (straightPerturbation X t '' E)) / |t|)
      (𝓝[≠] 0)
      (𝓝 (∫ z in reducedBoundary E hE hmE,
        |inner ℝ (X z) (reducedNormal E hE hmE z)| ∂hausdorffMeasure2 3)) := by
  apply (hE.tendsto_normalized_straightIndicatorDifference hmE hXC hcX).congr'
  obtain ⟨L, hLX⟩ := ContDiff.lipschitzWith_of_hasCompactSupport hcX hXC one_ne_zero
  have hh : Tendsto (fun t : ℝ => |t| * L) (𝓝[≠] 0) (𝓝 0) := by
    simpa using ((continuous_abs.tendsto 0).mul_const (L : ℝ)).mono_left
      (nhdsWithin_le_nhds (s := ({0} : Set ℝ)ᶜ))
  filter_upwards [hh.eventually (gt_mem_nhds zero_lt_one)] with t ht
  rw [integral_straightIndicatorDifference_eq_symmDiff hmE hLX hXC ht,
    div_eq_mul_inv, mul_comm]

end LiquidDrop

module

public import NoCompromise.CapacitaryK.MuPositive
public import NoCompromise.Measure.PositiveWeakStar

@[expose] public section

/-!
# The positive measure associated to the gradient length

We apply positive weak-star compactness to integration against the regularized
Laplacians, viewed as functionals on the open-subtype test space. Smooth cutoffs
and the localized Green identity give uniform bounds on each compact support.
-/

noncomputable section
open MeasureTheory Filter Set InnerProductSpace
open scoped Topology Gradient ContDiff RealInnerProductSpace CompactlySupported

namespace LiquidDrop.CapacitaryK

lemma continuousOn_gradNorm {U : Set E3} (hU : IsOpen U) {u : E3 → ℝ}
    (hu : ContDiffOn ℝ 3 u U) : ContinuousOn (gradNorm u) U := by
  intro x hx
  exact (gradient_length_continuousAt (hu.contDiffAt (hU.mem_nhds hx))).continuousWithinAt

lemma continuousOn_laplacianN_gradNormEps {U : Set E3} (hU : IsOpen U)
    {u : E3 → ℝ} (hu : ContDiffOn ℝ 3 u U) {ε : ℝ} (hε : ε ≠ 0) :
    ContinuousOn (laplacianN (gradNormEps ε u)) U := by
  intro x hx
  have hv := regularized_contDiffAt (hu.contDiffAt (hU.mem_nhds hx)) hε
  apply ContinuousAt.continuousWithinAt
  apply tendsto_finsetSum
  intro i _
  have hfirst : ContDiffAt ℝ 1 (poissonCoordinateDerivative i (gradNormEps ε u)) x :=
    (hv.fderiv_right (by norm_num)).clm_apply contDiffAt_const
  exact ((hfirst.fderiv_right (show (0 : ℕ∞ω) + 1 ≤ 1 by norm_num)).clm_apply
    (contDiffAt_const (c := basisVec i))).continuousAt

/-- The localized Green identity for the regularized gradient length. -/
lemma integral_gradNormEps_mul_laplacianN {U : Set E3} (hU : IsOpen U)
    {u : E3 → ℝ} (hu : ContDiffOn ℝ 3 u U) {ε : ℝ} (hε : ε ≠ 0)
    {φ : E3 → ℝ} (hφ : ContDiff ℝ (⊤ : ℕ∞) φ)
    (hcφ : HasCompactSupport φ) (hsφ : tsupport φ ⊆ U) :
    (∫ x, gradNormEps ε u x * laplacianN φ x) =
      ∫ x, φ x * laplacianN (gradNormEps ε u) x := by
  obtain ⟨χ, hχ, hcχ, hsχ, hone, _⟩ :=
    exists_smooth_cutoff_one_near_compact hcφ hU hsφ
  let v : E3 → ℝ := fun x => χ x * gradNormEps ε u x
  have hv : ContDiff ℝ 2 v := by
    apply contDiff_iff_contDiffAt.mpr
    intro x
    by_cases hx : x ∈ U
    · exact (hχ.of_le (by simp)).contDiffAt.mul
        (regularized_contDiffAt (hu.contDiffAt (hU.mem_nhds hx)) hε)
    · have hxt : x ∉ tsupport χ := fun ht => hx (hsχ ht)
      apply (contDiffAt_const (c := (0 : ℝ))).congr_of_eventuallyEq
      filter_upwards [(isClosed_tsupport χ).isOpen_compl.mem_nhds hxt] with y hy
      simp only [v, image_eq_zero_of_notMem_tsupport hy, zero_mul]
  have hcv : HasCompactSupport v := hcχ.mul_right
  have hnear (x : E3) (hx : x ∈ tsupport φ) : v =ᶠ[𝓝 x] gradNormEps ε u := by
    filter_upwards [hone.filter_mono (nhds_le_nhdsSet hx)] with y hy
    simp only [v, hy, one_mul]
  calc
    _ = ∫ x, v x * laplacianN φ x := by
      apply integral_congr_ae
      filter_upwards with x
      by_cases hx : x ∈ tsupport φ
      · rw [(hnear x hx).self_of_nhds]
      · have hz : laplacianN φ x = 0 := image_eq_zero_of_notMem_tsupport
          (fun ht => hx (laplacian_support φ ht))
        simp only [hz, mul_zero]
    _ = ∫ x, φ x * laplacianN v x := by
      rw [integral_mul_laplacianN (hφ.of_le (by simp)) (hv.of_le (by norm_num)) hcv,
        integral_mul_laplacianN hv (hφ.of_le (by simp)) hcφ]
      congr 1
      apply integral_congr_ae
      filter_upwards with x
      exact real_inner_comm _ _
    _ = _ := by
      apply integral_congr_ae
      filter_upwards with x
      by_cases hx : x ∈ tsupport φ
      · rw [laplacian_congr_near (hnear x hx)]
      · simp only [image_eq_zero_of_notMem_tsupport hx, zero_mul]

/-- Continuous functions on `U` may be integrated against ambient supported tests. -/
lemma integrable_supported_mul {U : Set E3} (hU : IsOpen U)
    {g f : E3 → ℝ} (hg : ContinuousOn g U) (hf : Continuous f)
    (hcf : HasCompactSupport f) (hsf : tsupport f ⊆ U) :
    Integrable (fun x => f x * g x) := by
  apply Continuous.integrable_of_hasCompactSupport _ hcf.mul_right
  exact (hf.continuousOn.mul hg).continuous_of_tsupport_subset hU
    (tsupport_mul_subset_left.trans hsf)

/-- Integration against a continuous density on the open domain. -/
def localDensityFunctional {U : Set E3} (hU : IsOpen U)
    (g : E3 → ℝ) (hg : ContinuousOn g U) : C_c(U, ℝ) →ₗ[ℝ] ℝ where
  toFun f := ∫ x, zeroExtendCC hU f x * g x
  map_add' f k := by
    simp only [map_add, CompactlySupportedContinuousMap.add_apply, add_mul]
    exact integral_add
      (integrable_supported_mul hU hg (zeroExtendCC hU f).continuous
        (zeroExtendCC hU f).hasCompactSupport (tsupport_zeroExtendCC_subset hU f))
      (integrable_supported_mul hU hg (zeroExtendCC hU k).continuous
        (zeroExtendCC hU k).hasCompactSupport (tsupport_zeroExtendCC_subset hU k))
  map_smul' c f := by
    simp only [map_smul, CompactlySupportedContinuousMap.smul_apply, smul_eq_mul,
      mul_assoc, integral_const_mul, RingHom.id_apply]

lemma localDensityFunctional_nonneg {U : Set E3} (hU : IsOpen U)
    {g : E3 → ℝ} (hg : ContinuousOn g U) (hg0 : ∀ x ∈ U, 0 ≤ g x)
    {f : C_c(U, ℝ)} (hf : 0 ≤ f) : 0 ≤ localDensityFunctional hU g hg f := by
  apply integral_nonneg
  intro x
  by_cases hx : x ∈ U
  · exact mul_nonneg
      (by rw [← Subtype.coe_mk x hx, zeroExtendCC_apply_coe]; exact hf ⟨x, hx⟩) (hg0 x hx)
  · change 0 ≤ zeroExtendFunction f x * g x
    simp [zeroExtendFunction_apply_notMem _ hx]

/-- Quantitative convergence of the distributional pairings. -/
lemma integral_gradNormEps_error {U : Set E3} (hU : IsOpen U) {u : E3 → ℝ}
    (hu : ContDiffOn ℝ 3 u U) (ε : ℝ)
    {φ : E3 → ℝ} (hφ : ContDiff ℝ (⊤ : ℕ∞) φ)
    (hcφ : HasCompactSupport φ) (hsφ : tsupport φ ⊆ U) :
    |(∫ x, gradNormEps ε u x * laplacianN φ x) -
      ∫ x, gradNorm u x * laplacianN φ x| ≤ |ε| * ∫ x, |laplacianN φ x| := by
  have hw := continuousOn_gradNorm hU hu
  have hiw := integrable_mul_laplacian hU hw (hφ.of_le (by simp)) hcφ hsφ
  have hiε := integrable_mul_laplacian hU ((hw.pow 2).add continuousOn_const).sqrt
    (hφ.of_le (by simp)) hcφ hsφ (f := gradNormEps ε u)
  have hiΔ : Integrable (fun x => |laplacianN φ x|) :=
    ((continuous_laplacianN (hφ.of_le (by simp))).integrable_of_hasCompactSupport
      (hcφ.of_isClosed_subset (isClosed_tsupport _) (laplacian_support φ))).abs
  rw [← integral_sub hiε hiw, ← integral_const_mul]
  rw [← Real.norm_eq_abs]
  apply norm_integral_le_of_norm_le (hiΔ.const_mul |ε|)
  filter_upwards with x
  rw [← sub_mul, Real.norm_eq_abs, abs_mul]
  exact mul_le_mul_of_nonneg_right (abs_gradNormEps_sub_gradNorm_le ε u x) (abs_nonneg _)

/-- A cutoff controls a positive density functional in the uniform norm. -/
lemma localDensityFunctional_bound {U : Set E3} (hU : IsOpen U)
    {g : E3 → ℝ} (hg : ContinuousOn g U) (hg0 : ∀ x ∈ U, 0 ≤ g x)
    {η : E3 → ℝ} (hη : Continuous η) (hcη : HasCompactSupport η)
    (hsη : tsupport η ⊆ U) (hη0 : ∀ x, 0 ≤ η x)
    (f : C_c(U, ℝ)) (hone : ∀ x ∈ tsupport (zeroExtendCC hU f), η x = 1) :
    |localDensityFunctional hU g hg f| ≤
      (∫ x, η x * g x) * ‖f.toBoundedContinuousFunction‖ := by
  have hi := integrable_supported_mul hU hg hη hcη hsη
  change |∫ x, zeroExtendCC hU f x * g x| ≤ _
  rw [← Real.norm_eq_abs, mul_comm, ← integral_const_mul]
  apply norm_integral_le_of_norm_le (hi.const_mul _)
  filter_upwards with x
  by_cases hx : x ∈ U
  · have hgx := hg0 x hx
    rw [Real.norm_eq_abs, abs_mul, abs_of_nonneg hgx, ← mul_assoc]
    apply mul_le_mul_of_nonneg_right _ hgx
    by_cases hxf : x ∈ tsupport (zeroExtendCC hU f)
    · rw [hone x hxf, mul_one]
      have hb := (zeroExtendCC hU f).toBoundedContinuousFunction.norm_coe_le_norm x
      simpa only [Real.norm_eq_abs,
        CompactlySupportedContinuousMap.toBoundedContinuousFunction_apply,
        norm_zeroExtendCC] using hb
    · rw [image_eq_zero_of_notMem_tsupport hxf, abs_zero]
      exact mul_nonneg (norm_nonneg _) (hη0 x)
  · have hf0 : zeroExtendCC hU f x = 0 :=
      image_eq_zero_of_notMem_tsupport (fun ht => hx (tsupport_zeroExtendCC_subset hU f ht))
    have hηx : η x = 0 := image_eq_zero_of_notMem_tsupport (fun ht => hx (hsη ht))
    simp only [hf0, hηx, zero_mul, mul_zero, norm_zero, le_refl]

/-- Uniform local bounds for the regularized positive density functionals. -/
lemma regularized_functionals_bounded {U : Set E3} (hU : IsOpen U) {u : E3 → ℝ}
    (hu : ContDiffOn ℝ 3 u U) (hΔ : ∀ x ∈ U, laplacianN u x = 0)
    (ε : ℕ → ℝ) (hε : ∀ j, ε j ≠ 0) (hε1 : ∀ j, |ε j| ≤ 1) :
    IsUniformlyLocallyBounded (fun j => localDensityFunctional hU
      (laplacianN (gradNormEps (ε j) u)) (continuousOn_laplacianN_gradNormEps hU hu (hε j))) := by
  intro K hK
  obtain ⟨η, hη, hcη, hsη, hone, hη01⟩ := exists_smooth_cutoff_one_near_compact
    (hK.image continuous_subtype_val) hU (by rintro _ ⟨x, _, rfl⟩; exact x.property)
  let C : ℝ := |∫ x, gradNorm u x * laplacianN η x| + ∫ x, |laplacianN η x|
  have hi0 : 0 ≤ ∫ x, |laplacianN η x| := integral_nonneg fun _ => abs_nonneg _
  refine ⟨C, add_nonneg (abs_nonneg _) hi0, ?_⟩
  intro j f hf
  have hg0 : ∀ x ∈ U, 0 ≤ laplacianN (gradNormEps (ε j) u) x := by
    intro x hx
    apply laplacianN_gradNormEps_nonneg (hε j) (hu.contDiffAt (hU.mem_nhds hx))
    filter_upwards [hU.mem_nhds hx] with y hy
    exact hΔ y hy
  have hb := localDensityFunctional_bound hU
    (continuousOn_laplacianN_gradNormEps hU hu (hε j)) hg0 hη.continuous hcη hsη
    (fun x => (hη01 x).1) f (by
      intro x hx
      rw [tsupport_zeroExtendCC] at hx
      obtain ⟨y, hy, rfl⟩ := hx
      exact (hone.filter_mono (nhds_le_nhdsSet
        (show (y : E3) ∈ Subtype.val '' K from ⟨y, hf hy, rfl⟩))).self_of_nhds)
  apply hb.trans
  apply mul_le_mul_of_nonneg_right _ (norm_nonneg _)
  rw [← integral_gradNormEps_mul_laplacianN hU hu (hε j) hη hcη hsη]
  have herr := (abs_le.mp (integral_gradNormEps_error hU hu (ε j) hη hcη hsη)).2
  have hsmall := mul_le_mul_of_nonneg_right (hε1 j) hi0
  have hw := le_abs_self (∫ x, gradNorm u x * laplacianN η x)
  dsimp [C]
  linarith

/-- The regularized pairings converge along any radii tending to zero. -/
lemma tendsto_integral_gradNormEps {U : Set E3} (hU : IsOpen U) {u : E3 → ℝ}
    (hu : ContDiffOn ℝ 3 u U) {ε : ℕ → ℝ} (hε : Tendsto ε atTop (𝓝 0))
    {φ : E3 → ℝ} (hφ : ContDiff ℝ (⊤ : ℕ∞) φ)
    (hcφ : HasCompactSupport φ) (hsφ : tsupport φ ⊆ U) :
    Tendsto (fun j => ∫ x, gradNormEps (ε j) u x * laplacianN φ x) atTop
      (𝓝 (∫ x, gradNorm u x * laplacianN φ x)) := by
  apply tendsto_iff_dist_tendsto_zero.mpr
  apply squeeze_zero (fun _ => dist_nonneg)
    (fun j => by simpa only [Real.dist_eq] using integral_gradNormEps_error hU hu (ε j) hφ hcφ hsφ)
  simpa only [abs_zero, zero_mul] using hε.abs.mul_const (∫ x, |laplacianN φ x|)

/-- `prop:K-mu`: on an open set `U` where `u` is `C³` and harmonic, the distribution `Δw`,
`w = |∇u|`, is a positive Radon measure: there is a measure `μ` on `ℝ³`, carried by `U` and finite
on compact subsets of `U`, with `∫ w Δφ = ∫ φ dμ` for every smooth compactly supported `φ` with
`tsupport φ ⊆ U`. -/
theorem K_mu_measure {U : Set E3} (hU : IsOpen U) {u : E3 → ℝ}
    (hu : ContDiffOn ℝ 3 u U) (hΔ : ∀ x ∈ U, laplacianN u x = 0) :
    ∃ μ : Measure E3, μ Uᶜ = 0 ∧ (∀ K : Set E3, IsCompact K → K ⊆ U → μ K < ⊤) ∧
      ∀ φ : E3 → ℝ, ContDiff ℝ (⊤ : ℕ∞) φ → HasCompactSupport φ → tsupport φ ⊆ U →
        ∫ x, gradNorm u x * laplacianN φ x = ∫ x, φ x ∂μ := by
  let : LocallyCompactSpace U := hU.locallyCompactSpace
  let ε : ℕ → ℝ := fun j => 1 / ((j : ℝ) + 1)
  have hεpos (j : ℕ) : 0 < ε j := by dsimp [ε]; positivity
  have hε (j : ℕ) : ε j ≠ 0 := ne_of_gt (hεpos j)
  have hε1 (j : ℕ) : |ε j| ≤ 1 := by
    rw [abs_of_pos (hεpos j)]
    dsimp [ε]
    exact (div_le_one (by positivity)).mpr (by linarith [Nat.cast_nonneg (α := ℝ) j])
  have hεlim : Tendsto ε atTop (𝓝 0) := tendsto_one_div_add_atTop_nhds_zero_nat
  let L (j : ℕ) := localDensityFunctional hU (laplacianN (gradNormEps (ε j) u))
    (continuousOn_laplacianN_gradNormEps hU hu (hε j))
  have hpos (j : ℕ) (f : C_c(U, ℝ)) (hf : 0 ≤ f) : 0 ≤ L j f := by
    apply localDensityFunctional_nonneg hU _ _ hf
    intro x hx
    apply laplacianN_gradNormEps_nonneg (hε j) (hu.contDiffAt (hU.mem_nhds hx))
    filter_upwards [hU.mem_nhds hx] with y hy
    exact hΔ y hy
  obtain ⟨ν, σ, hσ, _, hνfin, ht⟩ := exists_subseq_positive_riesz L
    (regularized_functionals_bounded hU hu hΔ ε hε hε1) hpos
  let : IsFiniteMeasureOnCompacts ν := hνfin
  refine ⟨ν.map (Subtype.val : U → E3), ?_, ?_, ?_⟩
  · rw [Measure.map_apply measurable_subtype_coe hU.measurableSet.compl]
    have he : (Subtype.val : U → E3) ⁻¹' Uᶜ = ∅ := by
      ext x
      simp only [mem_preimage, mem_compl_iff, mem_empty_iff_false, iff_false]
      exact not_not.mpr x.property
    rw [he, measure_empty]
  · intro K hK hKU
    rw [Measure.map_apply measurable_subtype_coe hK.measurableSet]
    exact (Topology.IsInducing.subtypeVal.isCompact_preimage' hK
      (by simpa only [Subtype.range_coe] using hKU)).measure_lt_top
  · intro φ hφ hcφ hsφ
    let f : C_c(E3, ℝ) := ⟨⟨φ, hφ.continuous⟩, hcφ⟩
    let fU : C_c(U, ℝ) := restrictSupportedCC ⟨f, hsφ⟩
    have hL (j : ℕ) : L j fU = ∫ x, gradNormEps (ε j) u x * laplacianN φ x := by
      change (∫ x, zeroExtendCC hU (restrictSupportedCC ⟨f, hsφ⟩) x *
        laplacianN (gradNormEps (ε j) u) x) = _
      rw [zeroExtendCC_restrictSupportedCC]
      exact (integral_gradNormEps_mul_laplacianN hU hu (hε j) hφ hcφ hsφ).symm
    have htφ : Tendsto (fun j => L (σ j) fU) atTop
        (𝓝 (∫ x, gradNorm u x * laplacianN φ x)) := by
      simp only [hL]
      exact (tendsto_integral_gradNormEps hU hu hεlim hφ hcφ hsφ).comp hσ.tendsto_atTop
    have heq := tendsto_nhds_unique htφ (ht fU)
    rw [(MeasurableEmbedding.subtype_coe hU.measurableSet).integral_map]
    exact heq

end LiquidDrop.CapacitaryK

import NoCompromise.Surface.TotalCurvature
import NoCompromise.Surface.TotalCurvatureIndexBridge
import NoCompromise.Surface.TotalCurvatureIndexTangent
import NoCompromise.Area.RectifiableFormula

/-!
# The total curvature equals the average index sum (blueprint chapter 14)

`thm:total-curvature-index` (`total_curvature_index`): for a compact smooth embedded surface
`S ⊆ ℝ³` with a unit normal field `n`,

  `∫_S κ dH² = ∫_{S²} ι_y(n) dH²(y)`, both sides finite.

The proof follows the blueprint. The Gauss map is replaced by its smooth Lipschitz extension `N`
(`exists_gaussMap_extension`), which is again a unit normal field with the same curvature and the
same index sums (`gaussCurvature_congr_of_eqOn`, `gaussIndexSum_congr_of_eqOn`).

* `S` is countably `H²`-rectifiable with finite area (`Surface/TotalCurvatureIndexBridge.lean`),
  so the chartwise area formula `CountablyH2Rectifiable.area_formula_rect_chartwise` applies to
  `N` on `S`.
* At almost every chart point the chart tangent plane is the tangent plane of `S`
  (`ae_range_fderiv_eq_tangentPlane`, `Surface/TotalCurvatureIndexTangent.lean`), and there the
  chartwise Jacobian of `N` is `|κ|` (`chartTangentialJacobian_normal_eq_abs_gaussCurvature`,
  from lem:gauss-jacobian).
* The curvature is the continuous function `gaussDensity N = det (orientedDifferential N id N)`
  on `S` (conv:gauss-orientation), so the weights `1_{κ > 0}`, `1_{κ < 0}`, `1_{κ = 0}` are Borel.
  The weight `1_{κ = 0}` shows that almost every `y` is a regular value; the other two give
  `∫ κ⁺` and `∫ κ⁻` as integrals of the fibre counts, which are a.e.-measurable
  (`aemeasurable_fiber_tsum_chartwise`) and vanish off `S²`.
* At a regular value `ι_y(n)` is the difference of the two fibre counts
  (`gaussIndexSum_eq_toReal_sub`).

Neither connectedness nor the particular normal of prop:orientation-parity is used.
`total_curvature_index_integrable_and_eq` is the exact shape of the named hypothesis
`h_total_curvature_index`.
-/

noncomputable section
open MeasureTheory Set Function Filter InnerProductSpace
open scoped ENNReal NNReal Topology
namespace LiquidDrop
set_option maxSynthPendingDepth 8

local notation "E2" => EuclideanSpace ℝ (Fin 2)

/-- Weighted fibre sums over a set with a chartwise piece decomposition are a.e.-measurable
for `H²`. -/
theorem aemeasurable_fiber_tsum_chartwise {S : Set E₃} {Φ : E₃ → E₃} {LΦ : ℝ≥0}
    (hΦ : LipschitzWith LΦ Φ)
    (f : ℕ → E2 → E₃) (L : ℕ → ℝ≥0) (A : ℕ → Set E2)
    (hf : ∀ i, LipschitzWith (L i) (f i)) (hA : ∀ i, IsUniformDifferentiabilityPiece (f i) (A i))
    (hinj : ∀ i, InjOn (f i) (A i))
    (hAS : ∀ i, f i '' A i ⊆ S) (hd : Pairwise (Disjoint on fun i => f i '' A i))
    (hn : hausdorffMeasure2 3 (S \ ⋃ i, f i '' A i) = 0)
    {q : E₃ → ℝ≥0∞} (hq : Measurable q) :
    AEMeasurable (fun y => ∑' x : ↥(S ∩ Φ ⁻¹' {y}), q x) (hausdorffMeasure2 3) := by
  have hfm (i : ℕ) : Measurable (f i) := (hf i).continuous.measurable
  have hCS : (⋃ i, f i '' A i) ⊆ S := iUnion_subset hAS
  have hnullΦ : hausdorffMeasure2 3 (Φ '' (S \ ⋃ i, f i '' A i)) = 0 :=
    hausdorffMeasure2_image_null_of_lipschitz hΦ hn
  have hmeas : AEMeasurable (fun y => ∑' i, areaMultiplicity (Φ ∘ f i) (A i) (q ∘ f i) y)
      (hausdorffMeasure2 3) :=
    AEMeasurable.tsum fun i => aemeasurable_areaMultiplicity_lipschitz_planar
      (hΦ.comp (hf i)) (hA i).1 (hq.comp (hfm i))
  refine hmeas.congr ?_
  filter_upwards [(measure_eq_zero_iff_ae_notMem).mp hnullΦ] with y hy
  rw [← areaMultiplicity_eq_tsum_fiber, areaMultiplicity_inter_of_notMem_image_sdiff q hy,
    inter_eq_right.mpr hCS, areaMultiplicity_iUnion Φ (fun i => f i '' A i) hd q y]
  exact tsum_congr fun i => (areaMultiplicity_image_of_injOn (hinj i) q y).symm

/-- At a chart point whose chart tangent plane is the tangent plane of `S`, the chartwise
tangential Jacobian of a unit normal field is `|κ|` (lem:gauss-jacobian). -/
theorem chartTangentialJacobian_normal_eq_abs_gaussCurvature {S : Set E₃} {N : E₃ → E₃}
    (hS : IsSmoothEmbeddedSurface S) (hN : IsUnitNormalField S N) (hNd : Differentiable ℝ N)
    {f : ℕ → E2 → E₃} {A : ℕ → Set E2}
    (hinj : ∀ i, InjOn (f i) (A i)) (hd : Pairwise (Disjoint on fun i => f i '' A i))
    {i : ℕ} {z : E2} (hz : z ∈ A i) (hfz : f i z ∈ S) (hdiff : DifferentiableAt ℝ (f i) z)
    (hK : Injective (fderiv ℝ (f i) z))
    (hT : LinearMap.range (fderiv ℝ (f i) z : E2 →ₗ[ℝ] E₃) = tangentPlane S (f i z)) :
    chartTangentialJacobian N f A (f i z) = |gaussCurvature S N (f i z)| := by
  obtain ⟨e⟩ := exists_range_plane_isometry (fderiv ℝ (f i) z) hK
  rw [chartTangentialJacobian_eq_jacobian2Linear N hinj hd hz hK e,
    chartTangentialMap_eq_fderiv_comp_subtypeL hdiff hK (hNd _)]
  let ι : E2 →ₗᵢ[ℝ] E₃ := (fderiv ℝ (f i) z).range.subtypeₗᵢ.comp e.toLinearIsometry
  have hι : LinearMap.range ι.toLinearMap = tangentPlane S (f i z) := by
    rw [← hT]
    ext w
    constructor
    · rintro ⟨v, rfl⟩
      exact (e v).2
    · intro hw
      exact ⟨e.symm ⟨w, hw⟩, by simp [ι]⟩
  rw [← jacobian2Linear_normal_eq_abs_gaussCurvature hS hN hfz ι hι]
  rfl

/-- The curvature density `p ↦ det (orientedDifferential N id N p)`; on `S` it is the Gauss
curvature (`det_orientedDifferential_gaussMap`). -/
def gaussDensity (N : E₃ → E₃) (p : E₃) : ℝ :=
  LinearMap.det (orientedDifferential N (fun y => y) N p : E₃ →ₗ[ℝ] E₃)

lemma continuous_gaussDensity {N : E₃ → E₃} (hN : ContDiff ℝ (⊤ : ℕ∞) N) :
    Continuous (gaussDensity N) := by
  have hc : Continuous fun p => orientedDifferential N (fun y => y) N p := by
    have hN0 : Continuous N := hN.continuous
    have hN1 : Continuous (fderiv ℝ N) := hN.continuous_fderiv (by simp)
    have hsr : Continuous fun p => (innerSL ℝ (N p)).smulRight (N p) :=
      ((ContinuousLinearMap.smulRightL ℝ E₃ E₃).continuous₂.comp
        (((innerSL ℝ : E₃ →L[ℝ] E₃ →L[ℝ] ℝ).continuous.comp hN0).prodMk hN0) :)
    unfold orientedDifferential
    exact (hN1.clm_comp (continuous_const.sub hsr)).add hsr
  exact ContinuousLinearMap.continuous_det.comp hc

/-- Pointwise: the sign of a real number is the difference of the two sign weights. -/
lemma intSign_eq_toReal_sub (r : ℝ) :
    ((SignType.sign r : ℤ) : ℝ) =
      (if 0 < r then (1 : ℝ≥0∞) else 0).toReal - (if r < 0 then (1 : ℝ≥0∞) else 0).toReal := by
  rcases lt_trichotomy r 0 with h | h | h
  · simp [h, h.not_gt, sign_neg h]
  · simp [h]
  · simp [h, h.not_gt, sign_pos h]


/-- At a regular value, the index sum of the Gauss map is the difference of the numbers of fibre
points of positive and of negative curvature. -/
lemma gaussIndexSum_eq_toReal_sub {S : Set E₃} {N : E₃ → E₃}
    (hS : IsSmoothEmbeddedSurface S) (hc : IsCompact S) (hN : IsUnitNormalField S N) {y : E₃}
    (hy : IsSurfaceRegularValue S (Metric.sphere (0 : E₃) 1) N y) :
    (gaussIndexSum S N y : ℝ) =
      (∑' x : ↥(S ∩ N ⁻¹' {y}), if 0 < gaussDensity N x then (1 : ℝ≥0∞) else 0).toReal -
      (∑' x : ↥(S ∩ N ⁻¹' {y}), if gaussDensity N x < 0 then (1 : ℝ≥0∞) else 0).toReal := by
  classical
  have hfin := finite_gaussMap_fiber hS hc hN hy
  have hfin' : (S ∩ N ⁻¹' {y}).Finite := hfin
  have htsum (q : E₃ → ℝ≥0∞) (hq : ∀ x, q x ≠ ⊤) :
      (∑' x : ↥(S ∩ N ⁻¹' {y}), q x).toReal = ∑ x ∈ hfin.toFinset, (q x).toReal := by
    rw [← hfin'.coe_toFinset, Finset.tsum_subtype', ENNReal.toReal_sum (fun x _ => hq x)]
    rfl
  rw [htsum (fun x => if 0 < gaussDensity N x then 1 else 0) (fun x => by split_ifs <;> simp),
    htsum (fun x => if gaussDensity N x < 0 then 1 else 0) (fun x => by split_ifs <;> simp),
    ← Finset.sum_sub_distrib]
  unfold gaussIndexSum indexSum
  split_ifs with h0
  swap
  · exact absurd ⟨hy, hfin⟩ h0
  push_cast
  apply Finset.sum_congr rfl
  intro p _
  exact intSign_eq_toReal_sub _


/-- thm:total-curvature-index for a unit normal field that is globally smooth and Lipschitz
(such as the extension of `exists_gaussMap_extension`). -/
theorem total_curvature_index_of_lipschitz {S : Set E₃} {N : E₃ → E₃}
    (hS : IsSmoothEmbeddedSurface S) (hc : IsCompact S) (hN : IsUnitNormalField S N)
    (hNs : ContDiff ℝ (⊤ : ℕ∞) N) {LN : ℝ≥0} (hNL : LipschitzWith LN N) :
    (∀ᵐ y ∂(hausdorffMeasure2 3).restrict (Metric.sphere (0 : E₃) 1),
      IsSurfaceRegularValue S (Metric.sphere (0 : E₃) 1) N y) ∧
    Integrable (gaussCurvature S N) ((hausdorffMeasure2 3).restrict S) ∧
      Integrable (fun y => (gaussIndexSum S N y : ℝ))
          ((hausdorffMeasure2 3).restrict (Metric.sphere (0 : E₃) 1)) ∧
        ∫ x in S, gaussCurvature S N x ∂(hausdorffMeasure2 3) =
          ∫ y in Metric.sphere (0 : E₃) 1, (gaussIndexSum S N y : ℝ) ∂(hausdorffMeasure2 3) := by
  classical
  set μ := hausdorffMeasure2 3 with hμ
  set S2 := Metric.sphere (0 : E₃) 1 with hS2
  set κ := gaussDensity N with hκdef
  have hSm : MeasurableSet S := hc.isClosed.measurableSet
  have hNd : Differentiable ℝ N := hNs.differentiable (by simp)
  have hκc : Continuous κ := continuous_gaussDensity hNs
  have hκm : Measurable κ := hκc.measurable
  have hκS : ∀ x ∈ S, κ x = gaussCurvature S N x := fun x hx =>
    det_orientedDifferential_gaussMap hS hN hx
  obtain ⟨f, L, A, hf, hA, hinj, hrank, hAS, hd, hnull, hformula⟩ :=
    (hS.countablyH2Rectifiable_of_isCompact hc).area_formula_rect_chartwise
  -- The chartwise Jacobian of `N` is `|κ|` almost everywhere on `S`.
  have hJ : ∀ᵐ x ∂μ.restrict S, chartTangentialJacobian N f A x = |κ x| := by
    have hbad (i : ℕ) : μ (f i '' {z | ¬(z ∈ A i → DifferentiableAt ℝ (f i) z →
        Injective (fderiv ℝ (f i) z) →
          LinearMap.range (fderiv ℝ (f i) z : E2 →ₗ[ℝ] E₃) = tangentPlane S (f i z))}) = 0 := by
      apply hausdorffMeasure2_image_null_of_lipschitz (hf i)
      rw [hausdorffMeasure2_plane]
      exact ae_iff.mp ((ae_restrict_iff' (hA i).1).mp
        (ae_range_fderiv_eq_tangentPlane hS (hA i).1.nullMeasurableSet
          fun z hz => hAS i ⟨z, hz, rfl⟩))
    have hB : μ ((S \ ⋃ i, f i '' A i) ∪ ⋃ i, f i '' {z | ¬(z ∈ A i →
        DifferentiableAt ℝ (f i) z → Injective (fderiv ℝ (f i) z) →
          LinearMap.range (fderiv ℝ (f i) z : E2 →ₗ[ℝ] E₃) = tangentPlane S (f i z))}) = 0 :=
      measure_union_null hnull (measure_iUnion_null hbad)
    rw [ae_restrict_iff' hSm, ae_iff]
    refine measure_mono_null ?_ hB
    intro x hx
    by_contra hxB
    apply hx
    intro hxS
    have hcov : x ∈ ⋃ i, f i '' A i := by
      by_contra h
      exact hxB (Or.inl ⟨hxS, h⟩)
    obtain ⟨i, z, hz, rfl⟩ := mem_iUnion.mp hcov
    have hgood : DifferentiableAt ℝ (f i) z → Injective (fderiv ℝ (f i) z) →
        LinearMap.range (fderiv ℝ (f i) z : E2 →ₗ[ℝ] E₃) = tangentPlane S (f i z) := by
      by_contra h
      exact hxB (Or.inr (mem_iUnion.mpr ⟨i, z, fun h' => h (h' hz), rfl⟩))
    rw [chartTangentialJacobian_normal_eq_abs_gaussCurvature hS hN hNd hinj hd hz hxS
      (hrank i hz).1 (hrank i hz).2 (hgood (hrank i hz).1 (hrank i hz).2), hκS _ hxS]
  -- The area formula for the Gauss map with a Borel weight.
  have harea : ∀ q : E₃ → ℝ≥0∞, Measurable q →
      ∫⁻ x in S, q x * ENNReal.ofReal |κ x| ∂μ = ∫⁻ y, ∑' x : ↥(S ∩ N ⁻¹' {y}), q x ∂μ := by
    intro q hq
    rw [← hformula N LN hNL q hq]
    apply lintegral_congr_ae
    filter_upwards [hJ] with x hx
    rw [hx]
  have hmeasF : ∀ q : E₃ → ℝ≥0∞, Measurable q →
      AEMeasurable (fun y => ∑' x : ↥(S ∩ N ⁻¹' {y}), q x) μ := fun q hq =>
    aemeasurable_fiber_tsum_chartwise hNL f L A hf hA hinj hAS hd hnull hq
  have hsupp : ∀ q : E₃ → ℝ≥0∞,
      support (fun y => ∑' x : ↥(S ∩ N ⁻¹' {y}), q x) ⊆ S2 := by
    intro q y hy
    by_contra hyS
    apply hy
    apply ENNReal.tsum_eq_zero.mpr
    rintro ⟨p, hp, hpy⟩
    exact absurd (show y ∈ S2 by
      rw [← mem_singleton_iff.mp hpy, hS2, mem_sphere_zero_iff_norm]
      exact (hN.2 p hp).1) hyS
  -- The three weights.
  set qp : E₃ → ℝ≥0∞ := fun x => if 0 < κ x then 1 else 0 with hqp
  set qn : E₃ → ℝ≥0∞ := fun x => if κ x < 0 then 1 else 0 with hqn
  set q0 : E₃ → ℝ≥0∞ := fun x => if κ x = 0 then 1 else 0 with hq0
  have hqpm : Measurable qp :=
    Measurable.ite (measurableSet_lt measurable_const hκm) measurable_const measurable_const
  have hqnm : Measurable qn :=
    Measurable.ite (measurableSet_lt hκm measurable_const) measurable_const measurable_const
  have hq0m : Measurable q0 :=
    Measurable.ite (measurableSet_eq_fun hκm measurable_const) measurable_const measurable_const
  -- Almost every point is a regular value (the equidimensional Sard statement for `N`).
  have hreg : ∀ᵐ y ∂μ, IsSurfaceRegularValue S S2 N y := by
    have h0 : ∫⁻ y, ∑' x : ↥(S ∩ N ⁻¹' {y}), q0 x ∂μ = 0 := by
      rw [← harea q0 hq0m]
      refine (lintegral_congr fun x => ?_).trans lintegral_zero
      by_cases h : κ x = 0 <;> simp [hq0, h]
    filter_upwards [(lintegral_eq_zero_iff' (hmeasF q0 hq0m)).mp h0] with y hy
    have hy' : ∑' x : ↥(S ∩ N ⁻¹' {y}), q0 x = 0 := hy
    rw [isSurfaceRegularValue_normal_iff hS hN]
    intro p hp hpy
    have hz := ENNReal.tsum_eq_zero.mp hy' ⟨p, hp, hpy⟩
    rw [← hκS p hp]
    intro hk
    simp [hq0, hk] at hz
  -- Integrability of the curvature on `S`.
  have hfinS : μ S < ⊤ := hS.hausdorffMeasure2_lt_top_of_isCompact hc
  have : IsFiniteMeasure (μ.restrict S) := isFiniteMeasure_restrict.mpr hfinS.ne
  obtain ⟨C, hC⟩ := hc.exists_bound_of_continuousOn hκc.continuousOn
  have hκint : Integrable κ (μ.restrict S) :=
    Integrable.of_bound hκc.aestronglyMeasurable C ((ae_restrict_iff' hSm).mpr (ae_of_all _ hC))
  -- Positive and negative parts.
  have hpos : ∫⁻ x in S, qp x * ENNReal.ofReal |κ x| ∂μ =
      ∫⁻ x in S, ENNReal.ofReal (κ x) ∂μ := by
    apply lintegral_congr
    intro x
    by_cases h : 0 < κ x
    · simp [hqp, h, abs_of_pos h]
    · simp [hqp, h, ENNReal.ofReal_of_nonpos (not_lt.mp h)]
  have hneg : ∫⁻ x in S, qn x * ENNReal.ofReal |κ x| ∂μ =
      ∫⁻ x in S, ENNReal.ofReal (-κ x) ∂μ := by
    apply lintegral_congr
    intro x
    by_cases h : κ x < 0
    · simp [hqn, h, abs_of_neg h]
    · simp [hqn, h, ENNReal.ofReal_of_nonpos (neg_nonpos.mpr (not_lt.mp h))]
  have hLp : ∫⁻ y in S2, ∑' x : ↥(S ∩ N ⁻¹' {y}), qp x ∂μ =
      ∫⁻ x in S, ENNReal.ofReal (κ x) ∂μ := by
    rw [setLIntegral_eq_of_support_subset (hsupp qp), ← harea qp hqpm, hpos]
  have hLn : ∫⁻ y in S2, ∑' x : ↥(S ∩ N ⁻¹' {y}), qn x ∂μ =
      ∫⁻ x in S, ENNReal.ofReal (-κ x) ∂μ := by
    rw [setLIntegral_eq_of_support_subset (hsupp qn), ← harea qn hqnm, hneg]
  have hLp_ne : ∫⁻ y in S2, ∑' x : ↥(S ∩ N ⁻¹' {y}), qp x ∂μ ≠ ⊤ := by
    rw [hLp]
    exact hκint.lintegral_lt_top.ne
  have hLn_ne : ∫⁻ y in S2, ∑' x : ↥(S ∩ N ⁻¹' {y}), qn x ∂μ ≠ ⊤ := by
    rw [hLn]
    exact hκint.neg.lintegral_lt_top.ne
  have hNpm := (hmeasF qp hqpm).restrict (s := S2)
  have hNnm := (hmeasF qn hqnm).restrict (s := S2)
  have hIp := integrable_toReal_of_lintegral_ne_top hNpm hLp_ne
  have hIn := integrable_toReal_of_lintegral_ne_top hNnm hLn_ne
  have hιae : (fun y => (gaussIndexSum S N y : ℝ)) =ᵐ[μ.restrict S2] fun y =>
      (∑' x : ↥(S ∩ N ⁻¹' {y}), qp x).toReal - (∑' x : ↥(S ∩ N ⁻¹' {y}), qn x).toReal := by
    filter_upwards [ae_restrict_of_ae hreg] with y hy
    exact gaussIndexSum_eq_toReal_sub hS hc hN hy
  refine ⟨ae_restrict_of_ae hreg, hκint.congr ?_, (hIp.sub hIn).congr hιae.symm, ?_⟩
  · filter_upwards [ae_restrict_mem hSm] with x hx
    exact hκS x hx
  rw [integral_congr_ae hιae, integral_sub hIp hIn, integral_toReal hNpm (ae_lt_top' hNpm hLp_ne),
    integral_toReal hNnm (ae_lt_top' hNnm hLn_ne), hLp, hLn,
    ← integral_eq_lintegral_pos_part_sub_lintegral_neg_part hκint]
  exact setIntegral_congr_fun hSm fun x hx => (hκS x hx).symm


/-- Two unit normal fields agreeing on `S` have the same Gauss curvature on `S`. -/
lemma gaussCurvature_congr_of_eqOn {S : Set E₃} {n m : E₃ → E₃}
    (hn : IsUnitNormalField S n) (hm : IsUnitNormalField S m) (h : EqOn n m S) {p : E₃}
    (hp : p ∈ S) : gaussCurvature S n p = gaussCurvature S m p := by
  unfold gaussCurvature
  rw [tangentShapeOperator_congr ((hn.contDiffAt hp).differentiableAt (by simp))
    ((hm.contDiffAt hp).differentiableAt (by simp)) (eventuallyEq_of_mem self_mem_nhdsWithin h)]

lemma isSurfaceRegularValue_congr_of_eqOn {S : Set E₃} {n m : E₃ → E₃}
    (hS : IsSmoothEmbeddedSurface S) (hn : IsUnitNormalField S n) (hm : IsUnitNormalField S m)
    (h : EqOn n m S) (y : E₃) :
    IsSurfaceRegularValue S (Metric.sphere (0 : E₃) 1) n y ↔
      IsSurfaceRegularValue S (Metric.sphere (0 : E₃) 1) m y := by
  rw [isSurfaceRegularValue_normal_iff hS hn, isSurfaceRegularValue_normal_iff hS hm]
  refine forall₂_congr fun p hp => ?_
  rw [h hp, gaussCurvature_congr_of_eqOn hn hm h hp]

/-- Two unit normal fields agreeing on `S` have the same Gauss-map index sums. -/
lemma gaussIndexSum_congr_of_eqOn {S : Set E₃} {n m : E₃ → E₃}
    (hS : IsSmoothEmbeddedSurface S) (hn : IsUnitNormalField S n) (hm : IsUnitNormalField S m)
    (h : EqOn n m S) (y : E₃) : gaussIndexSum S n y = gaussIndexSum S m y := by
  classical
  have hset : {p ∈ S | n p = y} = {p ∈ S | m p = y} := by
    ext p
    exact and_congr_right fun hp => by rw [h hp]
  have hreg := isSurfaceRegularValue_congr_of_eqOn hS hn hm h y
  unfold gaussIndexSum indexSum
  split_ifs with h0 h1 h1
  · apply Finset.sum_congr (by ext p; simp only [Set.Finite.mem_toFinset, hset])
    intro p hp
    have hpS : p ∈ S := (h1.2.mem_toFinset.mp hp).1
    rw [localSign_gaussMap hS hn hpS, localSign_gaussMap hS hm hpS,
      gaussCurvature_congr_of_eqOn hn hm h hpS]
  · exact absurd ⟨hreg.mp h0.1, hset ▸ h0.2⟩ h1
  · exact absurd ⟨hreg.mpr h1.1, hset.symm ▸ h1.2⟩ h0
  · rfl

/-- **thm:total-curvature-index.** For a compact smooth embedded surface `S ⊆ ℝ³` with a unit
normal field `n`, the Gauss curvature is `H²`-integrable on `S`, the index sum `y ↦ ι_y(n)` is
`H²`-integrable on `S²`, and `∫_S κ dH² = ∫_{S²} ι_y(n) dH²(y)`. Neither connectedness nor the
particular normal of prop:orientation-parity is needed. -/
theorem total_curvature_index {S : Set E₃} {n : E₃ → E₃}
    (hS : IsSmoothEmbeddedSurface S) (hc : IsCompact S) (hn : IsUnitNormalField S n) :
    Integrable (gaussCurvature S n) ((hausdorffMeasure2 3).restrict S) ∧
      Integrable (fun y => (gaussIndexSum S n y : ℝ))
          ((hausdorffMeasure2 3).restrict (Metric.sphere (0 : E₃) 1)) ∧
        ∫ x in S, gaussCurvature S n x ∂(hausdorffMeasure2 3) =
          ∫ y in Metric.sphere (0 : E₃) 1, (gaussIndexSum S n y : ℝ) ∂(hausdorffMeasure2 3) := by
  obtain ⟨N, hNs, ⟨LN, hNL⟩, hNS, -⟩ := exists_gaussMap_extension hS hc hn
  have hN : IsUnitNormalField S N :=
    ⟨⟨univ, isOpen_univ, subset_univ _, hNs.contDiffOn⟩, fun p hp => by
      rw [hNS p hp]
      exact hn.2 p hp⟩
  have hNn : EqOn N n S := fun p hp => hNS p hp
  obtain ⟨-, h1, h2, h3⟩ := total_curvature_index_of_lipschitz hS hc hN hNs hNL
  have hSm : MeasurableSet S := hc.isClosed.measurableSet
  have hκ : EqOn (gaussCurvature S N) (gaussCurvature S n) S := fun p hp =>
    gaussCurvature_congr_of_eqOn hN hn hNn hp
  have hι : (fun y => (gaussIndexSum S N y : ℝ)) = fun y => (gaussIndexSum S n y : ℝ) :=
    funext fun y => by rw [gaussIndexSum_congr_of_eqOn hS hN hn hNn y]
  refine ⟨h1.congr ?_, hι ▸ h2, ?_⟩
  · filter_upwards [ae_restrict_mem hSm] with x hx
    exact hκ hx
  rw [← setIntegral_congr_fun hSm hκ, h3, hι]

/-- thm:total-curvature-index in the form of the named hypothesis `h_total_curvature_index` of
`total_curvature_le_of_total_curvature_index` and `total_curvature_le_of_merge_disjoint`. -/
theorem total_curvature_index_integrable_and_eq {S : Set E₃} {n : E₃ → E₃}
    (hS : IsSmoothEmbeddedSurface S) (hc : IsCompact S) (hn : IsUnitNormalField S n) :
    Integrable (fun y => (gaussIndexSum S n y : ℝ))
          ((hausdorffMeasure2 3).restrict (Metric.sphere (0 : E₃) 1)) ∧
        ∫ x in S, gaussCurvature S n x ∂(hausdorffMeasure2 3) =
          ∫ y in Metric.sphere (0 : E₃) 1, (gaussIndexSum S n y : ℝ) ∂(hausdorffMeasure2 3) :=
  (total_curvature_index hS hc hn).2

/-- The almost-everywhere regularity of the Gauss map of a compact smooth embedded surface, in the
form of the named hypothesis `h_sard_charts` (cor:sard-charts for the embedded model). This is an
independent proof, as a by-product of the area formula: the weight `1_{κ = 0}` has zero area
integral, so almost no fibre meets `{κ = 0}`. -/
theorem ae_isSurfaceRegularValue_gaussMap_of_areaFormula {S : Set E₃} {n : E₃ → E₃}
    (hS : IsSmoothEmbeddedSurface S) (hc : IsCompact S) (hn : IsUnitNormalField S n) :
    ∀ᵐ y ∂(hausdorffMeasure2 3).restrict (Metric.sphere (0 : E₃) 1),
      IsSurfaceRegularValue S (Metric.sphere (0 : E₃) 1) n y := by
  obtain ⟨N, hNs, ⟨LN, hNL⟩, hNS, -⟩ := exists_gaussMap_extension hS hc hn
  have hN : IsUnitNormalField S N :=
    ⟨⟨univ, isOpen_univ, subset_univ _, hNs.contDiffOn⟩, fun p hp => by
      rw [hNS p hp]
      exact hn.2 p hp⟩
  filter_upwards [(total_curvature_index_of_lipschitz hS hc hN hNs hNL).1] with y hy
  exact (isSurfaceRegularValue_congr_of_eqOn hS hN hn (fun p hp => hNS p hp) y).mp hy


end LiquidDrop

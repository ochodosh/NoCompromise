module

public import NoCompromise.Area.C1GraphAlgebra
public import NoCompromise.Measure.FinitePartition
public import Mathlib.Analysis.Calculus.ContDiff.RCLike
public import Mathlib.MeasureTheory.Constructions.Polish.Basic
public import Mathlib.MeasureTheory.Measure.Real
public import Mathlib.MeasureTheory.Measure.WithDensity

@[expose] public section

/-!
# Area of C¹ graphs in arbitrary dimension

Normalized Hausdorff measure is compared locally with the linear graph map.
Finite compact partitions sum the local errors, which tend to zero. This proof
uses only linear image measure and Lipschitz Hausdorff distortion.
-/

noncomputable section
open MeasureTheory Set Module Filter Function Metric
open scoped ENNReal NNReal Topology Gradient
namespace LiquidDrop
set_option maxSynthPendingDepth 8

/-- Lipschitz distortion for normalized `d`-dimensional Hausdorff measure. -/
lemma normalizedHausdorffMeasure_image_le_of_lipschitzOn (d : ℕ) {n m : ℕ}
    {f : EuclideanSpace ℝ (Fin n) → EuclideanSpace ℝ (Fin m)}
    {B : Set (EuclideanSpace ℝ (Fin n))} {K : ℝ≥0}
    (hf : LipschitzOnWith K f B) :
    Measure.euclideanHausdorffMeasure d (f '' B) ≤
      (K : ℝ≥0∞) ^ d * Measure.euclideanHausdorffMeasure d B := by
  simp_rw [Measure.euclideanHausdorffMeasure_def]
  simp only [Measure.smul_apply, ENNReal.smul_def, smul_eq_mul]
  calc
    _ ≤ _ := mul_le_mul' le_rfl (hf.hausdorffMeasure_image_le (d := (d : ℝ)) (by positivity))
    _ = _ := by rw [ENNReal.rpow_natCast]; ac_rfl

/-- Comparing two parametrizations by their relative upper and lower stretches. -/
lemma normalizedHausdorffMeasure_image_bounds_of_relative_stretch {k m : ℕ}
    (L : EuclideanSpace ℝ (Fin k) →L[ℝ] EuclideanSpace ℝ (Fin m))
    (hL : Function.Injective L)
    {h : EuclideanSpace ℝ (Fin k) → EuclideanSpace ℝ (Fin m)}
    {B : Set (EuclideanSpace ℝ (Fin k))} (hh : InjOn h B)
    {a b : ℝ} (ha : 0 ≤ a) (hb : 0 < b)
    (hst : ∀ x ∈ B, ∀ y ∈ B,
      b * ‖L (x - y)‖ ≤ ‖h x - h y‖ ∧ ‖h x - h y‖ ≤ a * ‖L (x - y)‖) :
    ENNReal.ofReal (b ^ k) * Measure.euclideanHausdorffMeasure k (L '' B) ≤
      Measure.euclideanHausdorffMeasure k (h '' B) ∧
    Measure.euclideanHausdorffMeasure k (h '' B) ≤
      ENNReal.ofReal (a ^ k) * Measure.euclideanHausdorffMeasure k (L '' B) := by
  have hLin : InjOn L B := hL.injOn
  have hq : LipschitzOnWith (Real.toNNReal a)
      (h ∘ Function.invFunOn L B) (L '' B) := by
    apply LipschitzOnWith.of_dist_le_mul
    rintro _ ⟨x, hx, rfl⟩ _ ⟨y, hy, rfl⟩
    simpa only [Function.comp_apply, hLin.leftInvOn_invFunOn hx,
      hLin.leftInvOn_invFunOn hy, dist_eq_norm, Real.coe_toNNReal _ ha, ← L.map_sub]
      using (hst x hx y hy).2
  have hp : LipschitzOnWith (Real.toNNReal (1 / b))
      (L ∘ Function.invFunOn h B) (h '' B) := by
    apply LipschitzOnWith.of_dist_le_mul
    rintro _ ⟨x, hx, rfl⟩ _ ⟨y, hy, rfl⟩
    simp only [Function.comp_apply, hh.leftInvOn_invFunOn hx,
      hh.leftInvOn_invFunOn hy, dist_eq_norm, Real.coe_toNNReal _ (by positivity : 0 ≤ 1 / b),
      ← L.map_sub]
    rw [div_mul_eq_mul_div, one_mul]
    exact (le_div_iff₀ hb).2 (by simpa only [mul_comm] using (hst x hx y hy).1)
  have hqi : (h ∘ Function.invFunOn L B) '' (L '' B) = h '' B := by
    simp only [Function.comp_def]
    rw [← Set.image_image h (Function.invFunOn L B), hLin.invFunOn_image Subset.rfl]
  have hpi : (L ∘ Function.invFunOn h B) '' (h '' B) = L '' B := by
    simp only [Function.comp_def]
    rw [← Set.image_image L (Function.invFunOn h B), hh.invFunOn_image Subset.rfl]
  have hupper := normalizedHausdorffMeasure_image_le_of_lipschitzOn k hq
  have hlower := normalizedHausdorffMeasure_image_le_of_lipschitzOn k hp
  rw [hqi] at hupper
  rw [hpi] at hlower
  change _ ≤ ENNReal.ofReal a ^ k * _ at hupper
  change _ ≤ ENNReal.ofReal (1 / b) ^ k * _ at hlower
  refine ⟨?_, ?_⟩
  · rw [ENNReal.ofReal_pow hb.le]
    calc
      _ ≤ ENNReal.ofReal b ^ k *
          (ENNReal.ofReal (1 / b) ^ k * Measure.euclideanHausdorffMeasure k (h '' B)) :=
        mul_le_mul' le_rfl hlower
      _ = _ := by
        rw [← mul_assoc, ← mul_pow, ← ENNReal.ofReal_mul hb.le,
          mul_one_div_cancel hb.ne', ENNReal.ofReal_one, one_pow, one_mul]
  · simpa only [ENNReal.ofReal_pow ha] using hupper


/-- The graph Jacobian, expressed algebraically using the total derivative. -/
def graphJacobianN {k : ℕ} (f : EuclideanSpace ℝ (Fin k) → ℝ)
    (x : EuclideanSpace ℝ (Fin k)) : ℝ := (fderiv ℝ (graphMapN f) x).normDet

lemma graphJacobianN_nonneg {k : ℕ} (f : EuclideanSpace ℝ (Fin k) → ℝ)
    (x : EuclideanSpace ℝ (Fin k)) : 0 ≤ graphJacobianN f x :=
  (fderiv ℝ (graphMapN f) x).normDet_nonneg

lemma measurable_graphJacobianN {k : ℕ} (f : EuclideanSpace ℝ (Fin k) → ℝ) :
    Measurable (graphJacobianN f) :=
  continuous_normDet_euclidean.measurable.comp (measurable_fderiv ℝ (graphMapN f))

lemma continuousOn_graphJacobianN {k : ℕ} {U : Set (EuclideanSpace ℝ (Fin k))}
    (hU : IsOpen U) {f : EuclideanSpace ℝ (Fin k) → ℝ} (hf : ContDiffOn ℝ 1 f U) :
    ContinuousOn (graphJacobianN f) U :=
  continuous_normDet_euclidean.comp_continuousOn
    ((contDiffOn_graphMapN hf).continuousOn_fderiv_of_isOpen hU le_rfl)

lemma graphJacobianN_eq {k : ℕ} {f : EuclideanSpace ℝ (Fin k) → ℝ}
    {x : EuclideanSpace ℝ (Fin k)} (hf : DifferentiableAt ℝ f x) :
    graphJacobianN f x = Real.sqrt (1 + ‖gradient f x‖ ^ 2) :=
  normDet_fderiv_graphMapN hf

/-- A small perturbation of a graph tangent map has multiplicatively close area. -/
lemma graph_area_bounds_of_remainder {k : ℕ} (p : EuclideanSpace ℝ (Fin k))
    {f : EuclideanSpace ℝ (Fin k) → ℝ} {B : Set (EuclideanSpace ℝ (Fin k))}
    {ε : ℝ} (hε : 0 ≤ ε) (hεone : ε < 1)
    (hrem : ∀ x ∈ B, ∀ y ∈ B,
      ‖graphMapN f x - graphMapN f y - graphTangentN p (x - y)‖ ≤ ε * ‖x - y‖) :
    ENNReal.ofReal ((1 - ε) ^ k * (graphTangentN p).normDet) * volume B ≤
      Measure.euclideanHausdorffMeasure k (graphMapN f '' B) ∧
    Measure.euclideanHausdorffMeasure k (graphMapN f '' B) ≤
      ENNReal.ofReal ((1 + ε) ^ k * (graphTangentN p).normDet) * volume B := by
  have hst (x) (hx : x ∈ B) (y) (hy : y ∈ B) :
      (1 - ε) * ‖graphTangentN p (x - y)‖ ≤ ‖graphMapN f x - graphMapN f y‖ ∧
      ‖graphMapN f x - graphMapN f y‖ ≤ (1 + ε) * ‖graphTangentN p (x - y)‖ := by
    have he := (hrem x hx y hy).trans
      (mul_le_mul_of_nonneg_left (norm_le_graphTangentN p (x - y)) hε)
    have hl := norm_sub_le (graphMapN f x - graphMapN f y)
      (graphMapN f x - graphMapN f y - graphTangentN p (x - y))
    have hi : graphMapN f x - graphMapN f y -
        (graphMapN f x - graphMapN f y - graphTangentN p (x - y)) =
        graphTangentN p (x - y) := by abel
    rw [hi] at hl
    have hu := norm_sub_le (graphMapN f x - graphMapN f y - graphTangentN p (x - y))
      (-graphTangentN p (x - y))
    simp only [sub_neg_eq_add, sub_add_cancel, norm_neg] at hu
    constructor <;> nlinarith
  have hb := normalizedHausdorffMeasure_image_bounds_of_relative_stretch
    (graphTangentN p) (graphTangentN_injective p) (graphMapN_injective f).injOn
    (by linarith : 0 ≤ 1 + ε) (by linarith : 0 < 1 - ε) hst
  rw [normalizedHausdorffMeasure_image_linear_injective _ (graphTangentN_injective p)] at hb
  simpa only [ENNReal.ofReal_mul (pow_nonneg (by linarith : 0 ≤ 1 - ε) k),
    ENNReal.ofReal_mul (pow_nonneg (by linarith : 0 ≤ 1 + ε) k), mul_assoc] using hb

/-- A C¹ graph has its explicit graph tangent as strict derivative. -/
lemma hasStrictFDerivAt_graphMapN {k : ℕ} {U : Set (EuclideanSpace ℝ (Fin k))}
    (hU : IsOpen U) {f : EuclideanSpace ℝ (Fin k) → ℝ} (hf : ContDiffOn ℝ 1 f U)
    {x : EuclideanSpace ℝ (Fin k)} (hx : x ∈ U) :
    HasStrictFDerivAt (graphMapN f) (graphTangentN (gradient f x)) x := by
  have hdiff : DifferentiableAt ℝ f x :=
    (hf.differentiableOn (by norm_num) x hx).differentiableAt (hU.mem_nhds hx)
  exact ((contDiffOn_graphMapN hf).contDiffAt (hU.mem_nhds hx)).hasStrictFDerivAt'
    (hasFDerivAt_graphMapN hdiff) (by norm_num)

/-- Strict differentiability gives a pairwise remainder bound in an open ball. -/
lemma exists_graph_remainder_ball {k : ℕ} {U : Set (EuclideanSpace ℝ (Fin k))}
    (hU : IsOpen U) {f : EuclideanSpace ℝ (Fin k) → ℝ} (hf : ContDiffOn ℝ 1 f U)
    {x : EuclideanSpace ℝ (Fin k)} (hx : x ∈ U) {ε : ℝ} (hε : 0 < ε) :
    ∃ r > 0, ball x r ⊆ U ∧ ∀ y ∈ ball x r, ∀ z ∈ ball x r,
      ‖graphMapN f y - graphMapN f z - graphTangentN (gradient f x) (y - z)‖ ≤
        ε * ‖y - z‖ := by
  have hstrict := hasStrictFDerivAt_graphMapN hU hf hx
  obtain ⟨V, hV, W, hW, hbound⟩ := mem_nhds_prod_iff.mp (hstrict.isLittleO.bound hε)
  obtain ⟨r, hr, hball⟩ := Metric.mem_nhds_iff.mp
    (inter_mem (inter_mem hV hW) (hU.mem_nhds hx))
  refine ⟨r, hr, fun y hy => (hball hy).2, ?_⟩
  intro y hy z hz
  exact @hbound (y, z) ⟨(hball hy).1.1, (hball hz).1.2⟩

/-- The multiplicative stretch errors tend to zero in every fixed dimension. -/
lemma exists_graph_stretch_error (k : ℕ) (J : ℝ) {η : ℝ} (hη : 0 < η) :
    ∃ ε : ℝ, 0 < ε ∧ ε < 1 ∧
      J - η ≤ (1 - ε) ^ k * J ∧ (1 + ε) ^ k * J ≤ J + η := by
  have hlow : ContinuousAt (fun t : ℝ => (1 - t) ^ k * J) 0 := by fun_prop
  have hupp : ContinuousAt (fun t : ℝ => (1 + t) ^ k * J) 0 := by fun_prop
  have he : ∀ᶠ t : ℝ in 𝓝 0,
      J - η < (1 - t) ^ k * J ∧ (1 + t) ^ k * J < J + η := by
    exact (hlow.eventually (eventually_gt_nhds (by simpa using hη))).and
      (hupp.eventually (eventually_lt_nhds (by simpa using hη)))
  obtain ⟨r, hr, hb⟩ := Metric.mem_nhds_iff.mp he
  let ε := min (r / 2) (1 / 2)
  have hε : 0 < ε := lt_min (by positivity) (by norm_num)
  have hεr : ε < r := lt_of_le_of_lt (min_le_left _ _) (by linarith)
  have hεone : ε < 1 := lt_of_le_of_lt (min_le_right _ _) (by norm_num)
  have h := hb (show ε ∈ ball (0 : ℝ) r by
    simpa only [mem_ball, Real.dist_eq, sub_zero, abs_of_pos hε] using hεr)
  exact ⟨ε, hε, hεone, h.1.le, h.2.le⟩

/-- On a sufficiently small neighborhood, area and the Jacobian integral have
arbitrarily small relative error for every Borel subset of a fixed compact carrier. -/
lemma exists_local_graph_area_error {k : ℕ} {U K : Set (EuclideanSpace ℝ (Fin k))}
    (hU : IsOpen U) (hK : IsCompact K) (hKU : K ⊆ U)
    {f : EuclideanSpace ℝ (Fin k) → ℝ} (hf : ContDiffOn ℝ 1 f U)
    {x : EuclideanSpace ℝ (Fin k)} (hx : x ∈ K) {η : ℝ} (hη : 0 < η) :
    ∃ V : Set (EuclideanSpace ℝ (Fin k)), IsOpen V ∧ x ∈ V ∧
      ∀ B : Set (EuclideanSpace ℝ (Fin k)), MeasurableSet B → B ⊆ K → B ⊆ V →
        Measure.euclideanHausdorffMeasure k (graphMapN f '' B) < ∞ ∧
        |(Measure.euclideanHausdorffMeasure k).real (graphMapN f '' B) -
          ∫ y in B, graphJacobianN f y| ≤ η * volume.real B := by
  have hdiff := hf.differentiableOn (by norm_num) x (hKU hx) |>.differentiableAt
    (hU.mem_nhds (hKU hx))
  have hJ : (graphTangentN (gradient f x)).normDet = graphJacobianN f x := by
    rw [graphJacobianN, fderiv_graphMapN hdiff]
  obtain ⟨ε, hε, hεone, hl, hu⟩ := exists_graph_stretch_error k (graphJacobianN f x)
    (show 0 < η / 2 by positivity)
  obtain ⟨r, hr, hrU, hrem⟩ := exists_graph_remainder_ball hU hf (hKU hx) hε
  have hc := (continuousOn_graphJacobianN hU hf).continuousAt (hU.mem_nhds (hKU hx))
  obtain ⟨s, hs, hos⟩ := Metric.continuousAt_iff.mp hc (η / 2) (by positivity)
  refine ⟨ball x r ∩ ball x s, isOpen_ball.inter isOpen_ball,
    ⟨mem_ball_self hr, mem_ball_self hs⟩, ?_⟩
  intro B hB hBK hBV
  have hv : volume B < ∞ := (measure_mono hBK).trans_lt hK.measure_lt_top
  have hi : IntegrableOn (graphJacobianN f) B :=
    ((continuousOn_graphJacobianN hU hf).mono hKU |>.integrableOn_compact hK).mono_set hBK
  obtain ⟨hlo, hup⟩ := graph_area_bounds_of_remainder (gradient f x) hε.le hεone
    (fun y hy z hz => hrem y (hBV hy).1 z (hBV hz).1)
  rw [hJ] at hlo hup
  have hfin := hup.trans_lt (ENNReal.mul_lt_top ENNReal.ofReal_lt_top hv)
  refine ⟨hfin, ?_⟩
  have hlow : (graphJacobianN f x - η / 2) * volume.real B ≤
      (Measure.euclideanHausdorffMeasure k).real (graphMapN f '' B) := by
    have ht := ENNReal.toReal_mono hfin.ne hlo
    simp only [ENNReal.toReal_mul, ENNReal.toReal_ofReal'] at ht
    exact (mul_le_mul_of_nonneg_right
      (hl.trans (le_max_left _ _)) ENNReal.toReal_nonneg).trans ht
  have hupp : (Measure.euclideanHausdorffMeasure k).real (graphMapN f '' B) ≤
      (graphJacobianN f x + η / 2) * volume.real B := by
    have ht := ENNReal.toReal_mono (ENNReal.mul_lt_top ENNReal.ofReal_lt_top hv).ne hup
    have hn : 0 ≤ (1 + ε) ^ k * graphJacobianN f x :=
      mul_nonneg (pow_nonneg (by positivity) _) (graphJacobianN_nonneg f x)
    simp only [ENNReal.toReal_mul, ENNReal.toReal_ofReal hn] at ht
    exact ht.trans (mul_le_mul_of_nonneg_right hu measureReal_nonneg)
  have hosc (y) (hy : y ∈ B) : |graphJacobianN f y - graphJacobianN f x| ≤ η / 2 := by
    simpa only [Real.dist_eq] using (hos (hBV hy).2).le
  have hil : (graphJacobianN f x - η / 2) * volume.real B ≤
      ∫ y in B, graphJacobianN f y := by
    have h := integral_mono_ae
      (integrableOn_const (C := graphJacobianN f x - η / 2) hv.ne) hi (by
        filter_upwards [ae_restrict_mem hB] with y hy
        linarith [(abs_le.mp (hosc y hy)).1])
    simpa only [integral_const, smul_eq_mul, mul_comm, measureReal_restrict_apply_univ] using h
  have hiu : (∫ y in B, graphJacobianN f y) ≤
      (graphJacobianN f x + η / 2) * volume.real B := by
    have h := integral_mono_ae hi
      (integrableOn_const (C := graphJacobianN f x + η / 2) hv.ne) (by
        filter_upwards [ae_restrict_mem hB] with y hy
        linarith [(abs_le.mp (hosc y hy)).2])
    simpa only [integral_const, smul_eq_mul, mul_comm, measureReal_restrict_apply_univ] using h
  apply abs_le.mpr
  constructor <;> nlinarith

/-- Compactness upgrades the local estimates to a finite measurable partition. -/
lemma exists_graph_area_error_partition {k : ℕ} {U K A : Set (EuclideanSpace ℝ (Fin k))}
    (hU : IsOpen U) (hK : IsCompact K) (hKU : K ⊆ U)
    {f : EuclideanSpace ℝ (Fin k) → ℝ} (hf : ContDiffOn ℝ 1 f U)
    (hA : MeasurableSet A) (hAK : A ⊆ K) {η : ℝ} (hη : 0 < η) :
    ∃ (l : ℕ) (B : Fin l → Set (EuclideanSpace ℝ (Fin k))),
      (∀ i, MeasurableSet (B i)) ∧ Pairwise (Disjoint on B) ∧ (⋃ i, B i) = A ∧
      (∀ i, B i ⊆ A) ∧
      (∀ i, Measure.euclideanHausdorffMeasure k (graphMapN f '' B i) < ∞) ∧
      ∀ i, |(Measure.euclideanHausdorffMeasure k).real (graphMapN f '' B i) -
        ∫ y in B i, graphJacobianN f y| ≤ η * volume.real (B i) := by
  classical
  have hlocal (x : K) := exists_local_graph_area_error hU hK hKU hf x.property hη
  choose V hVo hVx hVerr using hlocal
  obtain ⟨δ, hδ, hcover⟩ := lebesgue_number_lemma_of_metric hK hVo
    (fun x hx => mem_iUnion.mpr ⟨⟨x, hx⟩, hVx ⟨x, hx⟩⟩)
  obtain ⟨l, B, c, hm, hd, hc, hBA, hbase, hdiam⟩ :=
    exists_finite_measurable_partition_of_compact_subset hK hA hAK
      (show 0 < δ / 2 by positivity)
  have herr (i : Fin l) :
      Measure.euclideanHausdorffMeasure k (graphMapN f '' B i) < ∞ ∧
      |(Measure.euclideanHausdorffMeasure k).real (graphMapN f '' B i) -
        ∫ y in B i, graphJacobianN f y| ≤ η * volume.real (B i) := by
    obtain ⟨j, hj⟩ := hcover (c i) (c i).property
    apply hVerr j (B i) (hm i) ((hBA i).trans hAK)
    intro y hy
    apply hj
    rw [mem_ball, dist_eq_norm]
    exact (hbase i y hy).trans_lt (by linarith)
  exact ⟨l, B, hm, hd, hc, hBA, fun i => (herr i).1, fun i => (herr i).2⟩

lemma graph_image_measure_lt_top_of_compact {k : ℕ}
    {U K A : Set (EuclideanSpace ℝ (Fin k))} (hU : IsOpen U) (hK : IsCompact K)
    (hKU : K ⊆ U) {f : EuclideanSpace ℝ (Fin k) → ℝ} (hf : ContDiffOn ℝ 1 f U)
    (hA : MeasurableSet A) (hAK : A ⊆ K) :
    Measure.euclideanHausdorffMeasure k (graphMapN f '' A) < ∞ := by
  obtain ⟨l, B, hm, hd, hc, hBA, hfin, herr⟩ :=
    exists_graph_area_error_partition hU hK hKU hf hA hAK (by norm_num : (0 : ℝ) < 1)
  rw [← hc, image_iUnion]
  exact (measure_iUnion_fintype_le _ _).trans_lt (ENNReal.sum_lt_top.mpr fun i _ => hfin i)

/-- Exact real area on every Borel subset of a compact graph patch. -/
theorem graph_image_measureReal_eq_integral_of_compact {k : ℕ}
    {U K A : Set (EuclideanSpace ℝ (Fin k))} (hU : IsOpen U) (hK : IsCompact K)
    (hKU : K ⊆ U) {f : EuclideanSpace ℝ (Fin k) → ℝ} (hf : ContDiffOn ℝ 1 f U)
    (hA : MeasurableSet A) (hAK : A ⊆ K) :
    (Measure.euclideanHausdorffMeasure k).real (graphMapN f '' A) =
      ∫ y in A, graphJacobianN f y := by
  have he (η : ℝ) (hη : 0 < η) :
      |(Measure.euclideanHausdorffMeasure k).real (graphMapN f '' A) -
        ∫ y in A, graphJacobianN f y| ≤ η * volume.real A := by
    obtain ⟨l, B, hm, hd, hc, hBA, hfin, herr⟩ :=
      exists_graph_area_error_partition hU hK hKU hf hA hAK hη
    have hmimage (i) : MeasurableSet (graphMapN f '' B i) :=
      (hm i).image_of_continuousOn_injOn
        ((continuousOn_graphMapN hf.continuousOn).mono ((hBA i).trans (hAK.trans hKU)))
        (graphMapN_injective f).injOn
    have hi (i) : IntegrableOn (graphJacobianN f) (B i) :=
      ((continuousOn_graphJacobianN hU hf).mono hKU |>.integrableOn_compact hK).mono_set
        ((hBA i).trans hAK)
    have himage : Pairwise (Disjoint on fun i => graphMapN f '' B i) := by
      intro i j hij
      exact (hd hij).image (graphMapN_injective f).injOn (subset_univ _) (subset_univ _)
    have ha : (Measure.euclideanHausdorffMeasure k).real (graphMapN f '' A) =
        ∑ i, (Measure.euclideanHausdorffMeasure k).real (graphMapN f '' B i) := by
      rw [← hc, image_iUnion]
      exact measureReal_iUnion_fintype himage hmimage (fun i => (hfin i).ne)
    have hint : (∫ y in A, graphJacobianN f y) = ∑ i, ∫ y in B i, graphJacobianN f y := by
      rw [← hc]
      exact integral_iUnion_fintype hm hd hi
    have hv : volume.real A = ∑ i, volume.real (B i) := by
      rw [← hc]
      exact measureReal_iUnion_fintype hd hm
        (fun i => ((measure_mono ((hBA i).trans hAK)).trans_lt hK.measure_lt_top).ne)
    rw [ha, hint, ← Finset.sum_sub_distrib]
    calc
      _ ≤ ∑ i, |(Measure.euclideanHausdorffMeasure k).real (graphMapN f '' B i) -
          ∫ y in B i, graphJacobianN f y| := Finset.abs_sum_le_sum_abs _ _
      _ ≤ ∑ i, η * volume.real (B i) := Finset.sum_le_sum fun i _ => herr i
      _ = _ := by rw [← Finset.mul_sum, ← hv]
  have ht : Tendsto (fun j : ℕ => (1 : ℝ) / (j + 1) * volume.real A) atTop (𝓝 0) := by
    simpa only [zero_mul] using tendsto_one_div_add_atTop_nhds_zero_nat.mul_const (volume.real A)
  have hz : |(Measure.euclideanHausdorffMeasure k).real (graphMapN f '' A) -
      ∫ y in A, graphJacobianN f y| ≤ 0 :=
    ge_of_tendsto ht (Eventually.of_forall fun (j : ℕ) =>
      he ((1 : ℝ) / ((j : ℝ) + 1)) (by positivity))
  exact sub_eq_zero.mp (abs_eq_zero.mp (le_antisymm hz (abs_nonneg _)))

/-- Unweighted normalized Hausdorff area on a compact graph patch. -/
theorem graph_image_measure_eq_lintegral_of_compact {k : ℕ}
    {U K A : Set (EuclideanSpace ℝ (Fin k))} (hU : IsOpen U) (hK : IsCompact K)
    (hKU : K ⊆ U) {f : EuclideanSpace ℝ (Fin k) → ℝ} (hf : ContDiffOn ℝ 1 f U)
    (hA : MeasurableSet A) (hAK : A ⊆ K) :
    Measure.euclideanHausdorffMeasure k (graphMapN f '' A) =
      ∫⁻ y in A, ENNReal.ofReal (graphJacobianN f y) := by
  have hi : IntegrableOn (graphJacobianN f) A :=
    ((continuousOn_graphJacobianN hU hf).mono hKU |>.integrableOn_compact hK).mono_set hAK
  rw [← ofReal_integral_eq_lintegral_ofReal hi
    (ae_of_all _ fun x => graphJacobianN_nonneg f x),
    ← graph_image_measureReal_eq_integral_of_compact hU hK hKU hf hA hAK]
  exact (ENNReal.ofReal_toReal
    (graph_image_measure_lt_top_of_compact hU hK hKU hf hA hAK).ne).symm


end LiquidDrop

module

public import NoCompromise.Area.GoodPieces
public import NoCompromise.Measure.FinitePartition
public import Mathlib.MeasureTheory.Measure.Real
public import Mathlib.MeasureTheory.Measure.WithDensity

@[expose] public section

/-!
# The area measure on an injective uniform piece

Finite measurable partitions sum the local almost-linear errors. Sending the
common error to zero identifies image area with the integral of the Gram
Jacobian. On injective Borel pieces, Jacobian-weighted volume therefore pushes
forward exactly to the restricted normalized Hausdorff area measure.
-/

noncomputable section
open MeasureTheory Set Module Filter Function
open scoped ENNReal NNReal Topology
namespace LiquidDrop
set_option maxSynthPendingDepth 8
namespace UniformDifferentiabilityCarrier
variable {m : ℕ} {f : EuclideanSpace ℝ (Fin 2) → EuclideanSpace ℝ (Fin m)}

lemma image_measure_lt_top (d : UniformDifferentiabilityCarrier f) :
    hausdorffMeasure2 m (f '' d.carrier) < ∞ := by
  obtain ⟨r, hr, hsmall⟩ := d.exists_injective_scale
  obtain ⟨t, ht⟩ := d.exists_finite_patch_cover hr
  have hsub : f '' d.carrier ⊆ ⋃ c ∈ t, f '' d.patch c r := by
    intro y hy
    obtain ⟨x, hx, rfl⟩ := hy
    obtain ⟨c, hc, hxc⟩ := mem_iUnion₂.mp (ht hx)
    exact mem_iUnion₂.mpr ⟨c, hc, x, hxc, rfl⟩
  apply (measure_mono hsub).trans_lt
  apply (measure_biUnion_finset_le t (fun c => f '' d.patch c r)).trans_lt
  apply ENNReal.sum_lt_top.mpr
  intro c hc
  have hb := (d.local_area_bounds (d.patch_subset c r) c.property hsmall
    (fun _ hx _ hy => d.patch_diameter_le c r hx hy) (fun x hx => ?_)).2
  · exact hb.trans_lt (ENNReal.mul_lt_top ENNReal.ofReal_lt_top
      (d.isCompact_patch c r).measure_lt_top)
  · have h := Metric.mem_closedBall.mp hx.2
    have hr0 : (0 : ℝ) ≤ r := r.coe_nonneg
    exact_mod_cast (show ‖x - (c : EuclideanSpace ℝ (Fin 2))‖ ≤ (r : ℝ) by
      rw [← dist_eq_norm]
      linarith)

lemma image_subset_measure_lt_top (d : UniformDifferentiabilityCarrier f)
    {A : Set (EuclideanSpace ℝ (Fin 2))} (hAK : A ⊆ d.carrier) :
    hausdorffMeasure2 m (f '' A) < ∞ :=
  (measure_mono (image_mono hAK)).trans_lt d.image_measure_lt_top

lemma integrableOn_jacobian (d : UniformDifferentiabilityCarrier f)
    {A : Set (EuclideanSpace ℝ (Fin 2))} (hA : MeasurableSet A) (hAK : A ⊆ d.carrier) :
    IntegrableOn (jacobian2 f) A := by
  have hfin : volume A ≠ ∞ := ((measure_mono hAK).trans_lt d.isCompact.measure_lt_top).ne
  apply (integrableOn_const (μ := volume) (C := (d.bound : ℝ) ^ 2) hfin).mono'
  · exact (measurable_jacobian2 f).aestronglyMeasurable.restrict
  · filter_upwards [ae_restrict_mem hA] with x hx
    rw [Real.norm_eq_abs, abs_of_nonneg (jacobian2_nonneg f x)]
    exact d.jacobian_le_sq_bound (hAK hx)

/-- The local area bounds expressed as inequalities of finite real measures. -/
lemma local_area_real_bounds (d : UniformDifferentiabilityCarrier f)
    {B : Set (EuclideanSpace ℝ (Fin 2))} (hBK : B ⊆ d.carrier)
    {x₀ : EuclideanSpace ℝ (Fin 2)} (hx₀ : x₀ ∈ d.carrier) {r : ℝ≥0}
    (hr : 4 * (d.modulus r : ℝ) < 1 / (d.bound : ℝ))
    (hdiam : ∀ x ∈ B, ∀ y ∈ B, ‖x - y‖₊ ≤ r)
    (hbase : ∀ x ∈ B, ‖x - x₀‖₊ ≤ r) :
    (jacobian2 f x₀ - 6 * d.bound * (d.modulus r : ℝ)) * volume.real B ≤
      (hausdorffMeasure2 m).real (f '' B) ∧
    (hausdorffMeasure2 m).real (f '' B) ≤
      (jacobian2 f x₀ + 6 * d.bound * (d.modulus r : ℝ)) * volume.real B := by
  obtain ⟨hl, hu⟩ := d.local_area_bounds hBK hx₀ hr hdiam hbase
  have hvol : volume B < ∞ := (measure_mono hBK).trans_lt d.isCompact.measure_lt_top
  constructor
  · have ht := ENNReal.toReal_mono (d.image_subset_measure_lt_top hBK).ne hl
    simp only [ENNReal.toReal_mul, ENNReal.toReal_ofReal'] at ht
    exact (mul_le_mul_of_nonneg_right (le_max_left _ _) ENNReal.toReal_nonneg).trans ht
  · have ht := ENNReal.toReal_mono
      (ENNReal.mul_lt_top ENNReal.ofReal_lt_top hvol).ne hu
    have hn : 0 ≤ jacobian2 f x₀ + 6 * d.bound * (d.modulus r : ℝ) := by
      exact add_nonneg (jacobian2_nonneg f x₀) (by positivity)
    simpa only [ENNReal.toReal_mul, ENNReal.toReal_ofReal hn, Measure.real] using ht

/-- On a small patch the area error is controlled by the modulus and Jacobian oscillation. -/
lemma local_area_integral_error (d : UniformDifferentiabilityCarrier f)
    {B : Set (EuclideanSpace ℝ (Fin 2))} (hB : MeasurableSet B) (hBK : B ⊆ d.carrier)
    {x₀ : EuclideanSpace ℝ (Fin 2)} (hx₀ : x₀ ∈ d.carrier) {r : ℝ≥0}
    (hr : 4 * (d.modulus r : ℝ) < 1 / (d.bound : ℝ))
    (hdiam : ∀ x ∈ B, ∀ y ∈ B, ‖x - y‖₊ ≤ r)
    (hbase : ∀ x ∈ B, ‖x - x₀‖₊ ≤ r) {δ : ℝ}
    (hosc : ∀ x ∈ B, |jacobian2 f x - jacobian2 f x₀| ≤ δ) :
    |(hausdorffMeasure2 m).real (f '' B) - ∫ x in B, jacobian2 f x| ≤
      (6 * d.bound * (d.modulus r : ℝ) + δ) * volume.real B := by
  have hfin : volume B ≠ ∞ := ((measure_mono hBK).trans_lt d.isCompact.measure_lt_top).ne
  have hi := d.integrableOn_jacobian hB hBK
  have hlow : (jacobian2 f x₀ - δ) * volume.real B ≤ ∫ x in B, jacobian2 f x := by
    have h := integral_mono_ae (integrableOn_const (C := jacobian2 f x₀ - δ) hfin) hi
      (by filter_upwards [ae_restrict_mem hB] with x hx; linarith [(abs_le.mp (hosc x hx)).1])
    simpa only [integral_const, smul_eq_mul, mul_comm, measureReal_restrict_apply_univ] using h
  have hupp : (∫ x in B, jacobian2 f x) ≤ (jacobian2 f x₀ + δ) * volume.real B := by
    have h := integral_mono_ae hi (integrableOn_const (C := jacobian2 f x₀ + δ) hfin)
      (by filter_upwards [ae_restrict_mem hB] with x hx; linarith [(abs_le.mp (hosc x hx)).2])
    simpa only [integral_const, smul_eq_mul, mul_comm, measureReal_restrict_apply_univ] using h
  obtain ⟨ha, hb⟩ := d.local_area_real_bounds hBK hx₀ hr hdiam hbase
  apply abs_le.mpr
  constructor <;> nlinarith

/-- Every prescribed relative area error holds uniformly on sufficiently small carrier pieces. -/
lemma exists_uniform_area_integral_error_scale (d : UniformDifferentiabilityCarrier f)
    {ε : ℝ} (hε : 0 < ε) :
    ∃ r : ℝ≥0, 0 < r ∧ ∀ (B : Set (EuclideanSpace ℝ (Fin 2))),
      MeasurableSet B → B ⊆ d.carrier →
      ∀ (x₀ : EuclideanSpace ℝ (Fin 2)), x₀ ∈ d.carrier →
      (∀ x ∈ B, ∀ y ∈ B, ‖x - y‖₊ ≤ r) →
      (∀ x ∈ B, ‖x - x₀‖₊ ≤ r) →
      |(hausdorffMeasure2 m).real (f '' B) - ∫ x in B, jacobian2 f x| ≤
        ε * volume.real B := by
  have hN := d.bound_pos
  obtain ⟨r₀, hr₀, hω₀⟩ := d.exists_pos_modulus_lt
    (show 0 < min ((1 / (d.bound : ℝ)) / 4) (ε / (12 * d.bound)) by positivity)
  obtain ⟨δ, hδ, hj⟩ := Metric.uniformContinuousOn_iff.mp
    d.uniformContinuousOn_jacobian (ε / 2) (by positivity)
  let r : ℝ≥0 := min r₀ ⟨δ / 2, by positivity⟩
  have hr : 0 < r := lt_min hr₀ (by change 0 < δ / 2; positivity)
  have hrr₀ : r ≤ r₀ := min_le_left _ _
  have hrδ : (r : ℝ) < δ := by
    have h : (r : ℝ) ≤ δ / 2 := by exact_mod_cast (min_le_right r₀ (⟨δ / 2, by positivity⟩ : ℝ≥0))
    linarith
  have hω : (d.modulus r : ℝ) ≤ d.modulus r₀ := by exact_mod_cast d.monotone_modulus hrr₀
  have hsmall : 4 * (d.modulus r : ℝ) < 1 / (d.bound : ℝ) := by
    have h := (lt_div_iff₀ (by norm_num : (0 : ℝ) < 4)).mp
      (hω₀.trans_le (min_le_left _ _))
    linarith
  have he : 6 * (d.bound : ℝ) * (d.modulus r : ℝ) ≤ ε / 2 := by
    have h := (lt_div_iff₀ (by positivity : (0 : ℝ) < 12 * d.bound)).mp
      (hω₀.trans_le (min_le_right _ _))
    nlinarith
  refine ⟨r, hr, ?_⟩
  intro B hB hBK x₀ hx₀ hdiam hbase
  have hos : ∀ x ∈ B, |jacobian2 f x - jacobian2 f x₀| ≤ ε / 2 := by
    intro x hx
    have hdist : dist x x₀ < δ := by
      rw [dist_eq_norm]
      exact (show ‖x - x₀‖ ≤ (r : ℝ) by exact_mod_cast hbase x hx).trans_lt hrδ
    simpa only [Real.dist_eq] using (hj x (hBK hx) x₀ hx₀ hdist).le
  exact (d.local_area_integral_error hB hBK hx₀ hsmall hdiam hbase hos).trans
    (mul_le_mul_of_nonneg_right (by linarith) measureReal_nonneg)

/-- On an injective piece, finite disjoint partitions let the local area errors be summed. -/
lemma area_integral_error_le_of_partition (d : UniformDifferentiabilityCarrier f)
    {A : Set (EuclideanSpace ℝ (Fin 2))} (hAK : A ⊆ d.carrier) (hinj : InjOn f A)
    {k : ℕ} {B : Fin k → Set (EuclideanSpace ℝ (Fin 2))}
    (hm : ∀ i, MeasurableSet (B i)) (hd : Pairwise (Disjoint on B))
    (hc : (⋃ i, B i) = A) (hBA : ∀ i, B i ⊆ A) {ε : ℝ}
    (he : ∀ i, |(hausdorffMeasure2 m).real (f '' B i) - ∫ x in B i, jacobian2 f x| ≤
      ε * volume.real (B i)) :
    |(hausdorffMeasure2 m).real (f '' A) - ∫ x in A, jacobian2 f x| ≤
      ε * volume.real A := by
  have hBK (i) := (hBA i).trans hAK
  have hmimage (i) : MeasurableSet (f '' B i) :=
    IsUniformDifferentiabilityPiece.measurableSet_image ⟨hm i, d, hBK i⟩
  have himage : Pairwise (Disjoint on fun i => f '' B i) := by
    intro i j hij
    apply Set.disjoint_left.mpr
    rintro y ⟨x, hx, hxy⟩ ⟨z, hz, hzy⟩
    have heq : x = z := hinj (hBA i hx) (hBA j hz) (hxy.trans hzy.symm)
    subst z
    exact Set.disjoint_left.mp (hd hij) hx hz
  have ha : (hausdorffMeasure2 m).real (f '' A) =
      ∑ i, (hausdorffMeasure2 m).real (f '' B i) := by
    rw [← hc, image_iUnion]
    exact measureReal_iUnion_fintype himage hmimage
      (fun i => (d.image_subset_measure_lt_top (hBK i)).ne)
  have hi : (∫ x in A, jacobian2 f x) = ∑ i, ∫ x in B i, jacobian2 f x := by
    rw [← hc]
    exact integral_iUnion_fintype hm hd (fun i => d.integrableOn_jacobian (hm i) (hBK i))
  have hv : volume.real A = ∑ i, volume.real (B i) := by
    rw [← hc]
    exact measureReal_iUnion_fintype hd hm
      (fun i => ((measure_mono (hBK i)).trans_lt d.isCompact.measure_lt_top).ne)
  rw [ha, hi, ← Finset.sum_sub_distrib]
  calc
    _ ≤ ∑ i, |(hausdorffMeasure2 m).real (f '' B i) - ∫ x in B i, jacobian2 f x| :=
      Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ i, ε * volume.real (B i) := Finset.sum_le_sum fun i _ => he i
    _ = _ := by rw [← Finset.mul_sum, ← hv]

/-- Exact real area on an injective Borel subset of a uniform carrier. -/
theorem image_measureReal_eq_integral (d : UniformDifferentiabilityCarrier f)
    {A : Set (EuclideanSpace ℝ (Fin 2))} (hA : MeasurableSet A)
    (hAK : A ⊆ d.carrier) (hinj : InjOn f A) :
    (hausdorffMeasure2 m).real (f '' A) = ∫ x in A, jacobian2 f x := by
  have he (ε : ℝ) (hε : 0 < ε) :
      |(hausdorffMeasure2 m).real (f '' A) - ∫ x in A, jacobian2 f x| ≤
        ε * volume.real A := by
    obtain ⟨r, hr, hbound⟩ := d.exists_uniform_area_integral_error_scale hε
    obtain ⟨k, B, c, hm, hd, hc, hBA, hbase, hdiam⟩ :=
      exists_finite_measurable_partition_of_compact_subset d.isCompact hA hAK
        (show (0 : ℝ) < r by exact_mod_cast hr)
    apply d.area_integral_error_le_of_partition hAK hinj hm hd hc hBA
    intro i
    apply hbound (B i) (hm i) ((hBA i).trans hAK) (c i) (c i).property
    · intro x hx y hy
      exact_mod_cast hdiam i x hx y hy
    · intro x hx
      exact_mod_cast hbase i x hx
  have ht : Tendsto (fun j : ℕ => (1 : ℝ) / (j + 1) * volume.real A) atTop (𝓝 0) := by
    simpa only [zero_mul] using tendsto_one_div_add_atTop_nhds_zero_nat.mul_const (volume.real A)
  have hz : |(hausdorffMeasure2 m).real (f '' A) - ∫ x in A, jacobian2 f x| ≤ 0 :=
    ge_of_tendsto ht (Eventually.of_forall fun (j : ℕ) =>
      he ((1 : ℝ) / ((j : ℝ) + 1)) (by positivity))
  exact sub_eq_zero.mp (abs_eq_zero.mp (le_antisymm hz (abs_nonneg _)))

/-- The unweighted area identity on an injective uniform piece. -/
theorem image_measure_eq_lintegral_jacobian (d : UniformDifferentiabilityCarrier f)
    {A : Set (EuclideanSpace ℝ (Fin 2))} (hA : MeasurableSet A)
    (hAK : A ⊆ d.carrier) (hinj : InjOn f A) :
    hausdorffMeasure2 m (f '' A) = ∫⁻ x in A, ENNReal.ofReal (jacobian2 f x) := by
  rw [← ofReal_integral_eq_lintegral_ofReal (d.integrableOn_jacobian hA hAK)
    (ae_of_all _ fun x => jacobian2_nonneg f x), ← d.image_measureReal_eq_integral hA hAK hinj]
  exact (ENNReal.ofReal_toReal (d.image_subset_measure_lt_top hAK).ne).symm

/-- On an injective carrier subset, the Jacobian-weighted volume pushes forward to surface area. -/
theorem map_withDensity_jacobian_restrict (d : UniformDifferentiabilityCarrier f)
    (hfm : Measurable f) {A : Set (EuclideanSpace ℝ (Fin 2))} (hA : MeasurableSet A)
    (hAK : A ⊆ d.carrier) (hinj : InjOn f A) :
    Measure.map f ((volume.restrict A).withDensity (fun x => ENNReal.ofReal (jacobian2 f x))) =
      (hausdorffMeasure2 m).restrict (f '' A) := by
  ext T hT
  rw [Measure.map_apply hfm hT, withDensity_apply _ (hfm hT), Measure.restrict_apply hT,
    Measure.restrict_restrict (hfm hT)]
  rw [← d.image_measure_eq_lintegral_jacobian ((hfm hT).inter hA)
    (inter_subset_right.trans hAK) (hinj.mono inter_subset_right)]
  congr 1
  ext y
  simp only [mem_image, mem_inter_iff, mem_preimage]
  aesop

/-- The weighted area identity for weights pulled back from the target. -/
theorem lintegral_comp_mul_jacobian (d : UniformDifferentiabilityCarrier f)
    (hfm : Measurable f) {A : Set (EuclideanSpace ℝ (Fin 2))} (hA : MeasurableSet A)
    (hAK : A ⊆ d.carrier) (hinj : InjOn f A)
    {q : EuclideanSpace ℝ (Fin m) → ℝ≥0∞} (hq : Measurable q) :
    (∫⁻ x in A, q (f x) * ENNReal.ofReal (jacobian2 f x)) =
      ∫⁻ y in f '' A, q y ∂hausdorffMeasure2 m := by
  rw [← d.map_withDensity_jacobian_restrict hfm hA hAK hinj,
    lintegral_map hq hfm]
  rw [lintegral_withDensity_eq_lintegral_mul (volume.restrict A)
    (g := fun x => q (f x)) (measurable_jacobian2 f).ennreal_ofReal (hq.comp hfm)]
  simp only [Pi.mul_apply, mul_comm]

end UniformDifferentiabilityCarrier
end LiquidDrop

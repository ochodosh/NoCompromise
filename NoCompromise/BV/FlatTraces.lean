import NoCompromise.BV.Traces

/-!
# Integrable BV traces on flat interfaces

One-dimensional essential traces define the actual normal traces. Their
measurability follows from one-sided averages, and line slicing controls their
integrals by the ambient BV norm.
-/

noncomputable section
open MeasureTheory Filter Set Metric
open scoped ENNReal Topology
namespace LiquidDrop
set_option maxSynthPendingDepth 8

/-- Real normal-line coordinates, with the tangential coordinate first. -/
def realLineCoordinates (n : ℕ) :
    (EuclideanSpace ℝ (Fin n) × ℝ) ≃ₜ EuclideanSpace ℝ (Fin (n + 1)) :=
  (Homeomorph.prodComm _ _).trans (euclideanLastEquiv n).symm.toHomeomorph

@[simp] lemma realLineCoordinates_apply {n : ℕ} (p : EuclideanSpace ℝ (Fin n) × ℝ) :
    realLineCoordinates n p = graphAppendN p.1 p.2 := rfl

lemma realLineCoordinates_measurePreserving (n : ℕ) :
    MeasurePreserving (realLineCoordinates n) (volume.prod volume) volume :=
  ((euclideanLastEquiv_measurePreserving n).symm
    (euclideanLastEquiv n).toHomeomorph.toMeasurableEquiv).comp Measure.measurePreserving_swap

/-- The trace from below on a coordinate hyperplane. -/
def flatBVLeftTrace {n : ℕ} (f : EuclideanSpace ℝ (Fin (n + 1)) → ℝ) (a : ℝ)
    (x : EuclideanSpace ℝ (Fin n)) : ℝ := bvLeftTrace (fun t => f (graphAppendN x t)) a

/-- The trace from above on a coordinate hyperplane. -/
def flatBVRightTrace {n : ℕ} (f : EuclideanSpace ℝ (Fin (n + 1)) → ℝ) (a : ℝ)
    (x : EuclideanSpace ℝ (Fin n)) : ℝ := bvRightTrace (fun t => f (graphAppendN x t)) a

lemma HasBVLeftTrace.tendsto_mean {f : ℝ → ℝ} {a L : ℝ}
    (h : HasBVLeftTrace f a L) (hi : LocallyIntegrable f volume) :
    Tendsto (fun r : ℝ => r⁻¹ * ∫ t in Ioo (a - r) a, f t) (𝓝[>] 0) (𝓝 L) := by
  apply tendsto_iff_norm_sub_tendsto_zero.mpr
  simp only [Real.norm_eq_abs]
  apply squeeze_zero' (Eventually.of_forall fun _ => abs_nonneg _)
    _ (h.tendsto_mean_abs_sub hi)
  filter_upwards [self_mem_nhdsWithin] with r hr
  change 0 < r at hr
  have hif := (hi.integrableOn_isCompact (isCompact_Icc (a := a - r) (b := a))).mono_set
    Ioo_subset_Icc_self
  have hc : IntegrableOn (fun _ : ℝ => L) (Ioo (a - r) a) volume :=
    integrableOn_const measure_Ioo_lt_top.ne
  have he : r⁻¹ * (∫ t in Ioo (a - r) a, f t) - L =
      r⁻¹ * ∫ t in Ioo (a - r) a, f t - L := by
    rw [integral_sub hif hc, setIntegral_const, Measure.real, Real.volume_Ioo,
      ENNReal.toReal_ofReal (show 0 ≤ a - (a - r) by linarith [hr])]
    simp only [smul_eq_mul]
    field_simp [hr.ne']
    ring
  rw [he, abs_mul, abs_of_pos (inv_pos.mpr hr)]
  exact mul_le_mul_of_nonneg_left abs_integral_le_integral_abs (inv_nonneg.mpr hr.le)

lemma HasBVRightTrace.tendsto_mean {f : ℝ → ℝ} {a L : ℝ}
    (h : HasBVRightTrace f a L) (hi : LocallyIntegrable f volume) :
    Tendsto (fun r : ℝ => r⁻¹ * ∫ t in Ioo a (a + r), f t) (𝓝[>] 0) (𝓝 L) := by
  apply tendsto_iff_norm_sub_tendsto_zero.mpr
  simp only [Real.norm_eq_abs]
  apply squeeze_zero' (Eventually.of_forall fun _ => abs_nonneg _)
    _ (h.tendsto_mean_abs_sub hi)
  filter_upwards [self_mem_nhdsWithin] with r hr
  change 0 < r at hr
  have hif := (hi.integrableOn_isCompact (isCompact_Icc (a := a) (b := a + r))).mono_set
    Ioo_subset_Icc_self
  have hc : IntegrableOn (fun _ : ℝ => L) (Ioo a (a + r)) volume :=
    integrableOn_const measure_Ioo_lt_top.ne
  have he : r⁻¹ * (∫ t in Ioo a (a + r), f t) - L =
      r⁻¹ * ∫ t in Ioo a (a + r), f t - L := by
    rw [integral_sub hif hc, setIntegral_const, Measure.real, Real.volume_Ioo,
      ENNReal.toReal_ofReal (show 0 ≤ a + r - a by linarith [hr])]
    simp only [smul_eq_mul]
    field_simp [hr.ne']
    ring
  rw [he, abs_mul, abs_of_pos (inv_pos.mpr hr)]
  exact mul_le_mul_of_nonneg_left abs_integral_le_integral_abs (inv_nonneg.mpr hr.le)

lemma aestronglyMeasurable_realLine_integral {n : ℕ}
    {f : EuclideanSpace ℝ (Fin (n + 1)) → ℝ} (hf : AEStronglyMeasurable f volume)
    (S : Set ℝ) :
    AEStronglyMeasurable (fun x : EuclideanSpace ℝ (Fin n) =>
      ∫ t in S, f (graphAppendN x t)) volume := by
  have hm := hf.comp_quasiMeasurePreserving
    (realLineCoordinates_measurePreserving n).quasiMeasurePreserving
  exact (hm.mono_measure (Measure.prod_mono le_rfl Measure.restrict_le_self)).integral_prod_right'

/-- The actual trace from below is measurable as the almost-everywhere limit of normal averages. -/
theorem IsBVOn.aestronglyMeasurable_flatBVLeftTrace {n : ℕ}
    {f : EuclideanSpace ℝ (Fin (n + 1)) → ℝ} (hf : IsBVOn f univ) (a : ℝ) :
    AEStronglyMeasurable (flatBVLeftTrace f a) volume := by
  have hi := integrableOn_univ.mp hf.1
  have hprod := ((realLineCoordinates_measurePreserving n).integrable_comp
    hi.aestronglyMeasurable).mpr hi
  apply aestronglyMeasurable_of_tendsto_ae (𝓝[>] (0 : ℝ))
    (f := fun r x => r⁻¹ * ∫ t in Ioo (a - r) a, f (graphAppendN x t))
  · intro r
    exact (aestronglyMeasurable_realLine_integral hi.aestronglyMeasurable _).const_mul _
  · filter_upwards [hf.ae_lineSlice_and_lintegral_variation_le.1, hprod.prod_right_ae]
      with x hx hix
    have hl := isLocallyBVOn_of_variation_lt_top isOpen_univ hx.1.locallyIntegrableOn hx.2
    have hl' : IsLocallyBVOn ((fun t : ℝ => f (graphAppendN x t)) ∘ euclideanOneReal) univ := hl
    exact (hl'.hasBVLeftTrace a).tendsto_mean hix.locallyIntegrable

/-- The actual trace from above is measurable as the almost-everywhere limit of normal averages. -/
theorem IsBVOn.aestronglyMeasurable_flatBVRightTrace {n : ℕ}
    {f : EuclideanSpace ℝ (Fin (n + 1)) → ℝ} (hf : IsBVOn f univ) (a : ℝ) :
    AEStronglyMeasurable (flatBVRightTrace f a) volume := by
  have hi := integrableOn_univ.mp hf.1
  have hprod := ((realLineCoordinates_measurePreserving n).integrable_comp
    hi.aestronglyMeasurable).mpr hi
  apply aestronglyMeasurable_of_tendsto_ae (𝓝[>] (0 : ℝ))
    (f := fun r x => r⁻¹ * ∫ t in Ioo a (a + r), f (graphAppendN x t))
  · intro r
    exact (aestronglyMeasurable_realLine_integral hi.aestronglyMeasurable _).const_mul _
  · filter_upwards [hf.ae_lineSlice_and_lintegral_variation_le.1, hprod.prod_right_ae]
      with x hx hix
    have hl := isLocallyBVOn_of_variation_lt_top isOpen_univ hx.1.locallyIntegrableOn hx.2
    have hl' : IsLocallyBVOn ((fun t : ℝ => f (graphAppendN x t)) ∘ euclideanOneReal) univ := hl
    exact (hl'.hasBVRightTrace a).tendsto_mean hix.locallyIntegrable

lemma lintegral_of_line_trace_bound {n : ℕ}
    {f : EuclideanSpace ℝ (Fin (n + 1)) → ℝ} (hf : IsBVOn f univ)
    {T : EuclideanSpace ℝ (Fin n) → ℝ}
    (hT : ∀ᵐ x : EuclideanSpace ℝ (Fin n),
      |T x| ≤ (∫ t : ℝ, |f (graphAppendN x t)|) +
        2 * (variation (lineSlice f x) univ).toReal) :
    (∫⁻ x, ENNReal.ofReal |T x|) ≤
      ENNReal.ofReal (∫ z, |f z|) + 2 * variation f univ := by
  have hi := (integrableOn_univ.mp hf.1).abs
  have hp := realLineCoordinates_measurePreserving n
  have hip := (hp.integrable_comp hi.aestronglyMeasurable).mpr hi
  let I : EuclideanSpace ℝ (Fin n) → ℝ := fun x => ∫ t : ℝ, |f (graphAppendN x t)|
  have hIi : Integrable I volume := hip.integral_prod_left
  have hIn (x) : 0 ≤ I x := integral_nonneg fun _ => abs_nonneg _
  have hI : (∫⁻ x, ENNReal.ofReal (I x)) = ENNReal.ofReal (∫ z, |f z|) := by
    rw [← ofReal_integral_eq_lintegral_ofReal hIi (ae_of_all _ hIn)]
    congr 1
    calc
      _ = ∫ p : EuclideanSpace ℝ (Fin n) × ℝ, |f (realLineCoordinates n p)| :=
        (integral_prod _ hip).symm
      _ = _ := by
        simpa only [] using!
          hp.integral_comp (realLineCoordinates n).measurableEmbedding (fun z => |f z|)
  calc
    _ ≤ ∫⁻ x, ENNReal.ofReal (I x) + 2 * variation (lineSlice f x) univ := by
      apply lintegral_mono_ae
      filter_upwards [hT] with x hx
      apply (ENNReal.ofReal_le_ofReal hx).trans
      rw [ENNReal.ofReal_add (hIn x) (by positivity), ENNReal.ofReal_mul (by norm_num)]
      norm_num only [ENNReal.ofReal_ofNat]
      gcongr
      exact ENNReal.ofReal_toReal_le
    _ = ENNReal.ofReal (∫ z, |f z|) +
        2 * ∫⁻ x, variation (lineSlice f x) univ := by
      rw [lintegral_add_left' hIi.aestronglyMeasurable.aemeasurable.ennreal_ofReal,
        hI, lintegral_const_mul' _ _ (by norm_num)]
    _ ≤ _ := by
      gcongr
      exact hf.ae_lineSlice_and_lintegral_variation_le.2

/-- Both traces on every flat interface have finite `L¹` norm controlled by the ambient BV norm. -/
theorem IsBVOn.integrable_flatBVTraces {n : ℕ}
    {f : EuclideanSpace ℝ (Fin (n + 1)) → ℝ} (hf : IsBVOn f univ) (a : ℝ) :
    Integrable (flatBVLeftTrace f a) volume ∧ Integrable (flatBVRightTrace f a) volume ∧
    (∫⁻ x, ENNReal.ofReal |flatBVLeftTrace f a x|) ≤
      ENNReal.ofReal (∫ z, |f z|) + 2 * variation f univ ∧
    (∫⁻ x, ENNReal.ofReal |flatBVRightTrace f a x|) ≤
      ENNReal.ofReal (∫ z, |f z|) + 2 * variation f univ := by
  have hb : ∀ᵐ x : EuclideanSpace ℝ (Fin n),
      |flatBVLeftTrace f a x| ≤ (∫ t : ℝ, |f (graphAppendN x t)|) +
        2 * (variation (lineSlice f x) univ).toReal ∧
      |flatBVRightTrace f a x| ≤ (∫ t : ℝ, |f (graphAppendN x t)|) +
        2 * (variation (lineSlice f x) univ).toReal := by
    filter_upwards [hf.ae_lineSlice_and_lintegral_variation_le.1] with x hx
    have hx' : IsBVOn ((fun t : ℝ => f (graphAppendN x t)) ∘ euclideanOneReal) univ := hx
    exact hx'.lineTrace_abs_le a
  have hL := lintegral_of_line_trace_bound hf (hb.mono fun _ hx => hx.1)
  have hR := lintegral_of_line_trace_bound hf (hb.mono fun _ hx => hx.2)
  have hfin : ENNReal.ofReal (∫ z, |f z|) + 2 * variation f univ < ∞ := by
    exact ENNReal.add_lt_top.mpr ⟨ENNReal.ofReal_lt_top,
      ENNReal.mul_lt_top (by norm_num) hf.2⟩
  refine ⟨⟨hf.aestronglyMeasurable_flatBVLeftTrace a, ?_⟩,
    ⟨hf.aestronglyMeasurable_flatBVRightTrace a, ?_⟩, hL, hR⟩
  · simpa only [HasFiniteIntegral, Real.enorm_eq_ofReal_abs] using hL.trans_lt hfin
  · simpa only [HasFiniteIntegral, Real.enorm_eq_ofReal_abs] using hR.trans_lt hfin

lemma IsLocallyBVOn.exists_isBVOn_eq_on_flat_slab {n : ℕ}
    {f : EuclideanSpace ℝ (Fin (n + 1)) → ℝ} (hf : IsLocallyBVOn f univ)
    {K : Set (EuclideanSpace ℝ (Fin n))} (hK : IsCompact K) (a : ℝ) :
    ∃ g : EuclideanSpace ℝ (Fin (n + 1)) → ℝ, IsBVOn g univ ∧
      ∀ x ∈ K, ∀ t ∈ Ioo (a - 1) (a + 1), g (graphAppendN x t) = f (graphAppendN x t) := by
  have hc : IsCompact (realLineCoordinates n '' (K ×ˢ Icc (a - 1) (a + 1))) :=
    (hK.prod isCompact_Icc).image (realLineCoordinates n).continuous
  obtain ⟨R, hR, hsR⟩ := hc.isBounded.exists_pos_norm_lt
  let κ : ContDiffBump (0 : EuclideanSpace ℝ (Fin (n + 1))) :=
    ⟨R, R + 1, hR, by linarith⟩
  refine ⟨fun z => κ z * f z,
    hf.isBVOn_mul_compact_factor isOpen_univ κ.contDiff κ.hasCompactSupport (subset_univ _), ?_⟩
  intro x hx t ht
  have hz : graphAppendN x t ∈ realLineCoordinates n '' (K ×ˢ Icc (a - 1) (a + 1)) :=
    ⟨(x, t), ⟨hx, Ioo_subset_Icc_self ht⟩, rfl⟩
  have hb : graphAppendN x t ∈ closedBall 0 κ.rIn := by
    simpa only [mem_closedBall, dist_zero_right] using (hsR _ hz).le
  change κ (graphAppendN x t) * f (graphAppendN x t) = f (graphAppendN x t)
  rw [κ.one_of_mem_closedBall hb, one_mul]

/-- Compact localization gives both `L¹` traces for a locally BV ambient function. -/
theorem IsLocallyBVOn.integrableOn_flatBVTraces {n : ℕ}
    {f : EuclideanSpace ℝ (Fin (n + 1)) → ℝ} (hf : IsLocallyBVOn f univ)
    {K : Set (EuclideanSpace ℝ (Fin n))} (hK : IsCompact K) (a : ℝ) :
    IntegrableOn (flatBVLeftTrace f a) K volume ∧
      IntegrableOn (flatBVRightTrace f a) K volume := by
  obtain ⟨g, hg, hgf⟩ := hf.exists_isBVOn_eq_on_flat_slab hK a
  have hgl := isLocallyBVOn_of_variation_lt_top isOpen_univ hg.1.locallyIntegrableOn hg.2
  have he : ∀ᵐ x ∂volume.restrict K,
      flatBVLeftTrace g a x = flatBVLeftTrace f a x ∧
        flatBVRightTrace g a x = flatBVRightTrace f a x := by
    filter_upwards [ae_restrict_of_ae hgl.ae_line_oneSided_traces,
      ae_restrict_mem hK.measurableSet] with x hx hxK
    have hnear : (fun t => g (graphAppendN x t)) =ᶠ[𝓝 a]
        (fun t => f (graphAppendN x t)) := by
      filter_upwards [isOpen_Ioo.mem_nhds
        (show a ∈ Ioo (a - 1) (a + 1) from ⟨by linarith, by linarith⟩)] with t ht
      exact hgf x hxK t ht
    have hL : HasBVLeftTrace (fun t => f (graphAppendN x t)) a (flatBVLeftTrace g a x) :=
      (hx a).1.congr' (hnear.filter_mono (inf_le_left.trans nhdsWithin_le_nhds))
    have hR : HasBVRightTrace (fun t => f (graphAppendN x t)) a (flatBVRightTrace g a x) :=
      (hx a).2.congr' (hnear.filter_mono (inf_le_left.trans nhdsWithin_le_nhds))
    exact ⟨hL.eq_bvLeftTrace.symm, hR.eq_bvRightTrace.symm⟩
  exact ⟨(hg.integrable_flatBVTraces a).1.integrableOn.congr (he.mono fun _ hx => hx.1),
    (hg.integrable_flatBVTraces a).2.1.integrableOn.congr (he.mono fun _ hx => hx.2)⟩

theorem IsLocallyBVOn.locallyIntegrable_flatBVLeftTrace {n : ℕ}
    {f : EuclideanSpace ℝ (Fin (n + 1)) → ℝ} (hf : IsLocallyBVOn f univ) (a : ℝ) :
    LocallyIntegrable (flatBVLeftTrace f a) volume :=
  locallyIntegrable_iff.mpr fun _ hK => (hf.integrableOn_flatBVTraces hK a).1

theorem IsLocallyBVOn.locallyIntegrable_flatBVRightTrace {n : ℕ}
    {f : EuclideanSpace ℝ (Fin (n + 1)) → ℝ} (hf : IsLocallyBVOn f univ) (a : ℝ) :
    LocallyIntegrable (flatBVRightTrace f a) volume :=
  locallyIntegrable_iff.mpr fun _ hK => (hf.integrableOn_flatBVTraces hK a).2

end LiquidDrop

import NoCompromise.BV.JumpMeasure
import NoCompromise.BV.LineSlicing
import Mathlib.MeasureTheory.Integral.Average

/-!
# One-sided BV traces

The one-dimensional traces are intrinsic essential one-sided limits. Their
existence follows from the actual local classical BV representatives; in
particular no choice of values on a Lebesgue-null set affects the trace.
-/

noncomputable section
open MeasureTheory Filter Set Metric
open scoped ENNReal Topology
namespace LiquidDrop
set_option maxSynthPendingDepth 8

/-- Essential approach to a real point from the left. -/
def bvTraceLeftFilter (a : ℝ) : Filter ℝ := (𝓝[<] a) ⊓ ae volume

/-- Essential approach to a real point from the right. -/
def bvTraceRightFilter (a : ℝ) : Filter ℝ := (𝓝[>] a) ⊓ ae volume

instance bvTraceLeftFilter_neBot (a : ℝ) : (bvTraceLeftFilter a).NeBot := by
  apply Filter.inf_neBot_iff.mpr
  intro S hS T hT
  obtain ⟨b, hba, hb⟩ := mem_nhdsLT_iff_exists_Ioo_subset.mp hS
  have hp : volume (Ioo b a) ≠ 0 := by
    rw [Real.volume_Ioo]
    exact ne_of_gt (ENNReal.ofReal_pos.mpr (sub_pos.mpr hba))
  obtain ⟨t, ht, hTt⟩ := Measure.exists_mem_of_measure_ne_zero_of_ae hp
    (ae_restrict_of_ae hT)
  exact ⟨t, hb ht, hTt⟩

instance bvTraceRightFilter_neBot (a : ℝ) : (bvTraceRightFilter a).NeBot := by
  apply Filter.inf_neBot_iff.mpr
  intro S hS T hT
  obtain ⟨b, hab, hb⟩ := mem_nhdsGT_iff_exists_Ioo_subset.mp hS
  have hp : volume (Ioo a b) ≠ 0 := by
    rw [Real.volume_Ioo]
    exact ne_of_gt (ENNReal.ofReal_pos.mpr (sub_pos.mpr hab))
  obtain ⟨t, ht, hTt⟩ := Measure.exists_mem_of_measure_ne_zero_of_ae hp
    (ae_restrict_of_ae hT)
  exact ⟨t, hb ht, hTt⟩

/-- The trace seen from the left, disregarding arbitrary null-set values. -/
def HasBVLeftTrace (f : ℝ → ℝ) (a L : ℝ) : Prop :=
  Tendsto f (bvTraceLeftFilter a) (𝓝 L)

/-- The trace seen from the right, disregarding arbitrary null-set values. -/
def HasBVRightTrace (f : ℝ → ℝ) (a L : ℝ) : Prop :=
  Tendsto f (bvTraceRightFilter a) (𝓝 L)

/-- The unique left trace where it exists, and zero otherwise. -/
def bvLeftTrace (f : ℝ → ℝ) (a : ℝ) : ℝ := by
  classical
  exact if h : ∃ L, HasBVLeftTrace f a L then h.choose else 0

/-- The unique right trace where it exists, and zero otherwise. -/
def bvRightTrace (f : ℝ → ℝ) (a : ℝ) : ℝ := by
  classical
  exact if h : ∃ L, HasBVRightTrace f a L then h.choose else 0

lemma HasBVLeftTrace.unique {f : ℝ → ℝ} {a L M : ℝ}
    (hL : HasBVLeftTrace f a L) (hM : HasBVLeftTrace f a M) : L = M :=
  tendsto_nhds_unique hL hM

lemma HasBVRightTrace.unique {f : ℝ → ℝ} {a L M : ℝ}
    (hL : HasBVRightTrace f a L) (hM : HasBVRightTrace f a M) : L = M :=
  tendsto_nhds_unique hL hM

lemma HasBVLeftTrace.eq_bvLeftTrace {f : ℝ → ℝ} {a L : ℝ}
    (h : HasBVLeftTrace f a L) : bvLeftTrace f a = L := by
  rw [bvLeftTrace, dite_eq_left ⟨L, h⟩]
  exact (Exists.choose_spec (show ∃ M, HasBVLeftTrace f a M from ⟨L, h⟩)).unique h

lemma HasBVRightTrace.eq_bvRightTrace {f : ℝ → ℝ} {a L : ℝ}
    (h : HasBVRightTrace f a L) : bvRightTrace f a = L := by
  rw [bvRightTrace, dite_eq_left ⟨L, h⟩]
  exact (Exists.choose_spec (show ∃ M, HasBVRightTrace f a M from ⟨L, h⟩)).unique h

lemma HasBVLeftTrace.congr_ae {f g : ℝ → ℝ} {a L : ℝ}
    (h : HasBVLeftTrace f a L) (he : f =ᵐ[volume] g) : HasBVLeftTrace g a L :=
  h.congr' (he.filter_mono inf_le_right)

lemma HasBVRightTrace.congr_ae {f g : ℝ → ℝ} {a L : ℝ}
    (h : HasBVRightTrace f a L) (he : f =ᵐ[volume] g) : HasBVRightTrace g a L :=
  h.congr' (he.filter_mono inf_le_right)

lemma eventuallyEq_bvTraceLeftFilter_of_ae_eq_near {f g : ℝ → ℝ} {a : ℝ}
    {U : Set ℝ} (hU : U ∈ 𝓝 a) (he : f =ᵐ[volume.restrict U] g) :
    f =ᶠ[bvTraceLeftFilter a] g := by
  have hnear : ∀ᶠ x in bvTraceLeftFilter a, x ∈ U :=
    Filter.Eventually.filter_mono (inf_le_left.trans nhdsWithin_le_nhds) hU
  have hae : ∀ᵐ x : ℝ, x ∈ U → f x = g x := ae_imp_of_ae_restrict he
  filter_upwards [hnear, hae.filter_mono inf_le_right] with x hx heq
  exact heq hx

lemma eventuallyEq_bvTraceRightFilter_of_ae_eq_near {f g : ℝ → ℝ} {a : ℝ}
    {U : Set ℝ} (hU : U ∈ 𝓝 a) (he : f =ᵐ[volume.restrict U] g) :
    f =ᶠ[bvTraceRightFilter a] g := by
  have hnear : ∀ᶠ x in bvTraceRightFilter a, x ∈ U :=
    Filter.Eventually.filter_mono (inf_le_left.trans nhdsWithin_le_nhds) hU
  have hae : ∀ᵐ x : ℝ, x ∈ U → f x = g x := ae_imp_of_ae_restrict he
  filter_upwards [hnear, hae.filter_mono inf_le_right] with x hx heq
  exact heq hx

/-- Every locally distributionally BV real function has both genuine traces at every point. -/
theorem IsLocallyBVOn.exists_oneSided_traces {f : ℝ → ℝ}
    (hf : IsLocallyBVOn (f ∘ euclideanOneReal) univ) (a : ℝ) :
    ∃ L M : ℝ, HasBVLeftTrace f a L ∧ HasBVRightTrace f a M := by
  obtain ⟨g, hg, _, he⟩ := hf.exists_boundedVariationOn_representative_Ioo (a - 1) (a + 1)
  have he' : f =ᵐ[volume.restrict (Ioo (a - 1) (a + 1))] g := by
    simpa only [Function.comp_def, euclideanOneReal.apply_symm_apply] using he
  have hU : Ioo (a - 1) (a + 1) ∈ 𝓝 a :=
    isOpen_Ioo.mem_nhds ⟨by linarith, by linarith⟩
  refine ⟨Function.leftLim g a, Function.rightLim g a, ?_, ?_⟩
  · exact ((hg.tendsto_leftLim a).mono_left inf_le_left).congr'
      (eventuallyEq_bvTraceLeftFilter_of_ae_eq_near hU he').symm
  · exact ((hg.tendsto_rightLim a).mono_left inf_le_left).congr'
      (eventuallyEq_bvTraceRightFilter_of_ae_eq_near hU he').symm

theorem IsLocallyBVOn.hasBVLeftTrace {f : ℝ → ℝ}
    (hf : IsLocallyBVOn (f ∘ euclideanOneReal) univ) (a : ℝ) :
    HasBVLeftTrace f a (bvLeftTrace f a) := by
  obtain ⟨L, _, hL, _⟩ := hf.exists_oneSided_traces a
  rwa [hL.eq_bvLeftTrace]

theorem IsLocallyBVOn.hasBVRightTrace {f : ℝ → ℝ}
    (hf : IsLocallyBVOn (f ∘ euclideanOneReal) univ) (a : ℝ) :
    HasBVRightTrace f a (bvRightTrace f a) := by
  obtain ⟨_, M, _, hM⟩ := hf.exists_oneSided_traces a
  rwa [hM.eq_bvRightTrace]

lemma HasBVLeftTrace.mem_closed {f : ℝ → ℝ} {a L : ℝ} {S : Set ℝ}
    (h : HasBVLeftTrace f a L) (hS : IsClosed S) (hf : ∀ᵐ t : ℝ, f t ∈ S) : L ∈ S :=
  hS.mem_of_tendsto h (hf.filter_mono inf_le_right)

lemma HasBVRightTrace.mem_closed {f : ℝ → ℝ} {a L : ℝ} {S : Set ℝ}
    (h : HasBVRightTrace f a L) (hS : IsClosed S) (hf : ∀ᵐ t : ℝ, f t ∈ S) : L ∈ S :=
  hS.mem_of_tendsto h (hf.filter_mono inf_le_right)

/-- The discrepancy between the two traces is exactly the signed derivative atom. -/
theorem IsRealBVPolar.bvRightTrace_sub_bvLeftTrace {f σ : ℝ → ℝ} {μ : Measure ℝ}
    (h : IsRealBVPolar f μ σ)
    (hf : IsLocallyBVOn (f ∘ euclideanOneReal) univ) (a : ℝ) :
    bvRightTrace f a - bvLeftTrace f a = μ.real {a} * σ a := by
  obtain ⟨g, hg, hc, he⟩ := hf.exists_boundedVariationOn_representative_Ioo (a - 1) (a + 1)
  have he' : f =ᵐ[volume.restrict (Ioo (a - 1) (a + 1))] g := by
    simpa only [Function.comp_def, euclideanOneReal.apply_symm_apply] using he
  have ha : a ∈ Ioo (a - 1) (a + 1) := ⟨by linarith, by linarith⟩
  have hL : HasBVLeftTrace f a (g a) :=
    ((hc a).mono Iio_subset_Iic_self |>.tendsto.mono_left inf_le_left).congr'
      (eventuallyEq_bvTraceLeftFilter_of_ae_eq_near (isOpen_Ioo.mem_nhds ha) he').symm
  have hR : HasBVRightTrace f a (Function.rightLim g a) :=
    ((hg.tendsto_rightLim a).mono_left inf_le_left).congr'
      (eventuallyEq_bvTraceRightFilter_of_ae_eq_near (isOpen_Ioo.mem_nhds ha) he').symm
  rw [hL.eq_bvLeftTrace, hR.eq_bvRightTrace]
  exact h.oneDimensionalJump_eq_atom he' hc ha

/-- At a point without a derivative atom the interior and exterior line traces agree. -/
theorem IsRealBVPolar.bvRightTrace_eq_bvLeftTrace_of_no_atom
    {f σ : ℝ → ℝ} {μ : Measure ℝ} (h : IsRealBVPolar f μ σ)
    (hf : IsLocallyBVOn (f ∘ euclideanOneReal) univ) {a : ℝ} (ha : μ {a} = 0) :
    bvRightTrace f a = bvLeftTrace f a := by
  have he := h.bvRightTrace_sub_bvLeftTrace hf a
  rw [Measure.real, ha, ENNReal.toReal_zero, zero_mul] at he
  exact sub_eq_zero.mp he

/-- Actual scalar traces exist on almost every normal line of a locally BV function. -/
theorem IsLocallyBVOn.ae_line_oneSided_traces {n : ℕ}
    {f : EuclideanSpace ℝ (Fin (n + 1)) → ℝ} (hf : IsLocallyBVOn f univ) :
    ∀ᵐ x : EuclideanSpace ℝ (Fin n), ∀ a : ℝ,
      HasBVLeftTrace (fun t => f (graphAppendN x t)) a
        (bvLeftTrace (fun t => f (graphAppendN x t)) a) ∧
      HasBVRightTrace (fun t => f (graphAppendN x t)) a
        (bvRightTrace (fun t => f (graphAppendN x t)) a) := by
  filter_upwards [hf.ae_lineSlice] with x hx
  have hx' : IsLocallyBVOn ((fun t => f (graphAppendN x t)) ∘ euclideanOneReal) univ := hx
  exact fun a => ⟨hx'.hasBVLeftTrace a, hx'.hasBVRightTrace a⟩

/-- The essential left trace has the usual one-sided `L¹` mean interpretation. -/
theorem HasBVLeftTrace.tendsto_mean_abs_sub {f : ℝ → ℝ} {a L : ℝ}
    (h : HasBVLeftTrace f a L) (hi : LocallyIntegrable f volume) :
    Tendsto (fun r : ℝ => r⁻¹ * ∫ t in Ioo (a - r) a, |f t - L|)
      (𝓝[>] 0) (𝓝 0) := by
  apply Metric.tendsto_nhds.mpr
  intro ε hε
  have he := (Metric.tendsto_nhds.mp h) (ε / 2) (by positivity)
  obtain ⟨S, hS, T, hT, hST⟩ := Filter.eventually_inf.mp he
  obtain ⟨b, hba, hb⟩ := mem_nhdsLT_iff_exists_Ioo_subset.mp hS
  filter_upwards [Ioo_mem_nhdsGT (sub_pos.mpr hba)] with r hr
  have hc : IntegrableOn (fun _ : ℝ => L) (Ioo (a - r) a) volume :=
    integrableOn_const (measure_Ioo_lt_top.ne)
  have hi' : IntegrableOn (fun t => |f t - L|) (Ioo (a - r) a) volume := by
    simpa only [Real.norm_eq_abs, Pi.sub_apply] using!
      ((hi.integrableOn_isCompact isCompact_Icc).mono_set Ioo_subset_Icc_self |>.sub hc).norm
  have hle : (∫ t in Ioo (a - r) a, |f t - L|) ≤ r * (ε / 2) := by
    calc
      _ ≤ ∫ _t : ℝ in Ioo (a - r) a, ε / 2 := by
        apply integral_mono_ae hi' (integrableOn_const measure_Ioo_lt_top.ne)
        filter_upwards [ae_restrict_of_ae hT, ae_restrict_mem measurableSet_Ioo]
          with t ht htr
        have htb : t ∈ S := hb ⟨by linarith [hr.2, htr.1], htr.2⟩
        simpa only [Real.dist_eq] using (hST t ⟨htb, ht⟩).le
      _ = _ := by
        rw [setIntegral_const, Measure.real, Real.volume_Ioo, ENNReal.toReal_ofReal]
        · simp only [smul_eq_mul]; ring
        · linarith [hr.1]
  have hn : 0 ≤ r⁻¹ * ∫ t in Ioo (a - r) a, |f t - L| :=
    mul_nonneg (inv_nonneg.mpr hr.1.le) (integral_nonneg fun _ => abs_nonneg _)
  rw [Real.dist_eq, sub_zero, abs_of_nonneg hn]
  calc
    _ ≤ r⁻¹ * (r * (ε / 2)) := mul_le_mul_of_nonneg_left hle (inv_nonneg.mpr hr.1.le)
    _ = ε / 2 := by rw [← mul_assoc, inv_mul_cancel₀ hr.1.ne', one_mul]
    _ < ε := by linarith

/-- The essential right trace has the usual one-sided `L¹` mean interpretation. -/
theorem HasBVRightTrace.tendsto_mean_abs_sub {f : ℝ → ℝ} {a L : ℝ}
    (h : HasBVRightTrace f a L) (hi : LocallyIntegrable f volume) :
    Tendsto (fun r : ℝ => r⁻¹ * ∫ t in Ioo a (a + r), |f t - L|)
      (𝓝[>] 0) (𝓝 0) := by
  apply Metric.tendsto_nhds.mpr
  intro ε hε
  have he := (Metric.tendsto_nhds.mp h) (ε / 2) (by positivity)
  obtain ⟨S, hS, T, hT, hST⟩ := Filter.eventually_inf.mp he
  obtain ⟨b, hab, hb⟩ := mem_nhdsGT_iff_exists_Ioo_subset.mp hS
  filter_upwards [Ioo_mem_nhdsGT (sub_pos.mpr hab)] with r hr
  have hc : IntegrableOn (fun _ : ℝ => L) (Ioo a (a + r)) volume :=
    integrableOn_const (measure_Ioo_lt_top.ne)
  have hi' : IntegrableOn (fun t => |f t - L|) (Ioo a (a + r)) volume := by
    simpa only [Real.norm_eq_abs, Pi.sub_apply] using!
      ((hi.integrableOn_isCompact isCompact_Icc).mono_set Ioo_subset_Icc_self |>.sub hc).norm
  have hle : (∫ t in Ioo a (a + r), |f t - L|) ≤ r * (ε / 2) := by
    calc
      _ ≤ ∫ _t : ℝ in Ioo a (a + r), ε / 2 := by
        apply integral_mono_ae hi' (integrableOn_const measure_Ioo_lt_top.ne)
        filter_upwards [ae_restrict_of_ae hT, ae_restrict_mem measurableSet_Ioo]
          with t ht htr
        have htb : t ∈ S := hb ⟨htr.1, by linarith [hr.2, htr.2]⟩
        simpa only [Real.dist_eq] using (hST t ⟨htb, ht⟩).le
      _ = _ := by
        rw [setIntegral_const, Measure.real, Real.volume_Ioo, ENNReal.toReal_ofReal]
        · simp only [smul_eq_mul]; ring
        · linarith [hr.1]
  have hn : 0 ≤ r⁻¹ * ∫ t in Ioo a (a + r), |f t - L| :=
    mul_nonneg (inv_nonneg.mpr hr.1.le) (integral_nonneg fun _ => abs_nonneg _)
  rw [Real.dist_eq, sub_zero, abs_of_nonneg hn]
  calc
    _ ≤ r⁻¹ * (r * (ε / 2)) := mul_le_mul_of_nonneg_left hle (inv_nonneg.mpr hr.1.le)
    _ = ε / 2 := by rw [← mul_assoc, inv_mul_cancel₀ hr.1.ne', one_mul]
    _ < ε := by linarith


/-- Fubini and the fundamental theorem of calculus retain the left endpoint trace term. -/
lemma integral_Iio_cumulative_mul_deriv {α : Type*} [MeasurableSpace α]
    (μ : Measure α) [SFinite μ] {w g : α → ℝ} (hw : Integrable w μ) (hg : Measurable g)
    {ψ : ℝ → ℝ} (hψ : ContDiff ℝ 1 ψ) (hcψ : HasCompactSupport ψ) (a : ℝ) :
    (∫ r in Iio a, (∫ x in {x | g x < r}, w x ∂μ) * deriv ψ r) =
      ψ a * (∫ x in {x | g x < a}, w x ∂μ) - ∫ x in {x | g x < a}, ψ (g x) * w x ∂μ := by
  classical
  let S : Set (ℝ × α) := {p | g p.2 < p.1 ∧ p.1 < a}
  have hS : MeasurableSet S :=
    (measurableSet_lt (hg.comp measurable_snd) measurable_fst).inter
      (measurableSet_lt measurable_fst measurable_const)
  let F : ℝ × α → ℝ := S.indicator (fun p => deriv ψ p.1 * w p.2)
  have hiψ : Integrable (deriv ψ) :=
    (hψ.continuous_deriv le_rfl).integrable_of_hasCompactSupport hcψ.deriv
  have hiF : Integrable F (volume.prod μ) := (hiψ.mul_prod hw).indicator hS
  have hleft (r : ℝ) : (∫ x, F (r, x) ∂μ) =
      (Iio a).indicator (fun r => (∫ x in {x | g x < r}, w x ∂μ) * deriv ψ r) r := by
    by_cases hr : r < a
    · rw [indicator_of_mem (show r ∈ Iio a from hr), ← integral_mul_const,
        ← integral_indicator (measurableSet_lt hg measurable_const)]
      apply integral_congr_ae
      exact ae_of_all _ fun x => by
        by_cases hx : g x < r <;> simp [F, S, Set.indicator, hr, hx, mul_comm]
    · simp [F, S, hr]
  have hright (x : α) : (∫ r : ℝ, F (r, x)) =
      {x | g x < a}.indicator (fun x => (ψ a - ψ (g x)) * w x) x := by
    by_cases hx : g x < a
    · rw [indicator_of_mem (show x ∈ {x | g x < a} from hx)]
      calc
        _ = ∫ r in Ioo (g x) a, deriv ψ r * w x := by
          rw [← integral_indicator measurableSet_Ioo]
          apply integral_congr_ae
          exact ae_of_all _ fun r => by rfl
        _ = (∫ r in Ioo (g x) a, deriv ψ r) * w x := integral_mul_const _ _
        _ = _ := by
          rw [← integral_Ioc_eq_integral_Ioo, ← intervalIntegral.integral_of_le hx.le]
          congr 1
          exact intervalIntegral.integral_eq_sub_of_hasDerivAt
            (fun t _ => (hψ.differentiable one_ne_zero t).hasDerivAt)
            ((hψ.continuous_deriv le_rfl).intervalIntegrable _ _)
    · rw [indicator_of_notMem (show x ∉ {x | g x < a} from hx)]
      have hz : F ∘ (fun r => (r, x)) = fun _ => 0 := by
        funext r
        have hn : ¬ (g x < r ∧ r < a) := fun h => hx (h.1.trans h.2)
        simp [F, S, hn]
      simpa only [Function.comp_def, integral_zero] using congrArg (fun f : ℝ → ℝ => ∫ r, f r) hz
  have hbound := (hcψ.isCompact_range hψ.continuous).isBounded
  obtain ⟨C, hC⟩ := hbound.exists_norm_le
  have hip : Integrable (fun x => ψ (g x) * w x) μ :=
    hw.bdd_mul (hψ.continuous.measurable.comp hg).aestronglyMeasurable
      (ae_of_all _ fun x => hC _ (mem_range_self _))
  calc
    _ = ∫ r : ℝ, ∫ x, F (r, x) ∂μ := by
      rw [← integral_indicator measurableSet_Iio]
      exact integral_congr_ae (ae_of_all _ fun r => (hleft r).symm)
    _ = ∫ x, (∫ r : ℝ, F (r, x)) ∂μ := integral_integral_swap (f := fun r x => F (r, x)) hiF
    _ = ∫ x in {x | g x < a}, (ψ a - ψ (g x)) * w x ∂μ := by
      simp_rw [hright]
      exact integral_indicator (measurableSet_lt hg measurable_const)
    _ = _ := by
      simp only [sub_mul]
      rw [integral_sub (hw.const_mul _).integrableOn hip.integrableOn, integral_const_mul]

lemma IsRealBVPolar.locallyIntegrable_polar {f σ : ℝ → ℝ} {μ : Measure ℝ}
    (h : IsRealBVPolar f μ σ) : LocallyIntegrable σ μ := by
  let := h.finiteOnCompacts
  apply locallyIntegrable_iff.mpr
  intro K hK
  let : IsFiniteMeasure (μ.restrict K) := ⟨by
    rw [Measure.restrict_apply_univ]
    exact hK.measure_lt_top⟩
  apply Integrable.of_bound h.measurable.aestronglyMeasurable.restrict 1
  exact (ae_restrict_of_ae h.norm_ae).mono fun t ht => by
    simpa only [Real.norm_eq_abs] using ht.le

/-- A local cumulative representative computes both intrinsic traces, including atoms. -/
lemma IsRealBVPolar.exists_cumulative_with_traces {f σ : ℝ → ℝ} {μ : Measure ℝ}
    (h : IsRealBVPolar f μ σ) {l u a : ℝ} (ha : a ∈ Ioo l u) :
    ∃ c : ℝ,
      f =ᵐ[volume.restrict (Ioo l u)]
        (fun t => (∫ s in Iio t, σ s ∂μ.restrict (Icc l u)) + c) ∧
      bvLeftTrace f a = (∫ s in Iio a, σ s ∂μ.restrict (Icc l u)) + c ∧
      bvRightTrace f a = (∫ s in Iic a, σ s ∂μ.restrict (Icc l u)) + c := by
  have hi := h.locallyIntegrable_polar.integrableOn_isCompact (isCompact_Icc (a := l) (b := u))
  obtain ⟨c, hc⟩ := h.exists_cumulative_ae_eq_Ioo l u
  have hL : HasBVLeftTrace f a ((∫ s in Iio a, σ s ∂μ.restrict (Icc l u)) + c) :=
    (((continuousWithinAt_integral_sublevel_left hi measurable_id a).add_const c).mono
      Iio_subset_Iic_self |>.tendsto.mono_left inf_le_left).congr'
      (eventuallyEq_bvTraceLeftFilter_of_ae_eq_near (isOpen_Ioo.mem_nhds ha) hc).symm
  have hR : HasBVRightTrace f a ((∫ s in Iic a, σ s ∂μ.restrict (Icc l u)) + c) :=
    (((tendsto_integral_sublevel_right hi measurable_id a).add_const c).mono_left
      inf_le_left).congr'
      (eventuallyEq_bvTraceRightFilter_of_ae_eq_near (isOpen_Ioo.mem_nhds ha) hc).symm
  exact ⟨c, hc, hL.eq_bvLeftTrace, hR.eq_bvRightTrace⟩

/-- The actual left half-line integration-by-parts identity for an arbitrary local BV polar. -/
theorem IsRealBVPolar.integral_Iio_mul_deriv {f σ : ℝ → ℝ} {μ : Measure ℝ}
    (h : IsRealBVPolar f μ σ) {ψ : ℝ → ℝ}
    (hψ : ContDiff ℝ 1 ψ) (hcψ : HasCompactSupport ψ) (a : ℝ) :
    (∫ t in Iio a, f t * deriv ψ t) =
      ψ a * bvLeftTrace f a - ∫ t in Iio a, ψ t * σ t ∂μ := by
  let := h.finiteOnCompacts
  obtain ⟨R, hR, hsR⟩ := (hcψ.union (isCompact_singleton (x := a))).isBounded.exists_pos_norm_lt
  have hsψ : tsupport ψ ⊆ Ioo (-R) R := by
    intro t ht
    have htR := hsR t (Or.inl ht)
    simpa only [Real.norm_eq_abs, abs_lt, mem_Ioo] using htR
  have ha : a ∈ Ioo (-R) R := by
    have haR := hsR a (Or.inr (mem_singleton a))
    simpa only [Real.norm_eq_abs, abs_lt, mem_Ioo] using haR
  obtain ⟨c, hfc, hL, _⟩ := h.exists_cumulative_with_traces ha
  let ν := μ.restrict (Icc (-R) R)
  let F : ℝ → ℝ := fun t => ∫ s in Iio t, σ s ∂ν
  have hiσ : Integrable σ ν :=
    h.locallyIntegrable_polar.integrableOn_isCompact isCompact_Icc
  have hiF : LocallyIntegrable F volume :=
    locallyIntegrable_of_boundedVariationOn_real
      (boundedVariationOn_integral_sublevel hiσ measurable_id)
  have hiD : Integrable (deriv ψ) volume :=
    (hψ.continuous_deriv le_rfl).integrable_of_hasCompactSupport hcψ.deriv
  have hiFD : Integrable (fun t => F t * deriv ψ t) volume := by
    simpa only [smul_eq_mul] using hiF.integrable_smul_right_of_hasCompactSupport
      (hψ.continuous_deriv le_rfl) hcψ.deriv
  have he : (fun t => f t * deriv ψ t) =ᵐ[volume]
      (fun t => (F t + c) * deriv ψ t) := by
    have hAE := ae_imp_of_ae_restrict hfc
    filter_upwards [hAE] with t ht
    by_cases htR : t ∈ Ioo (-R) R
    · rw [ht htR]
    · have hz : deriv ψ t = 0 :=
        deriv_of_notMem_tsupport (fun htψ => htR (hsψ htψ))
      rw [hz, mul_zero, mul_zero]
  have hp : (∫ t in Iio a, ψ t * σ t ∂ν) = ∫ t in Iio a, ψ t * σ t ∂μ := by
    rw [show ν = μ.restrict (Icc (-R) R) from rfl,
      Measure.restrict_restrict measurableSet_Iio,
      inter_comm, ← Measure.restrict_restrict measurableSet_Icc]
    apply setIntegral_eq_integral_of_forall_compl_eq_zero
    intro t ht
    have hz : ψ t = 0 := image_eq_zero_of_notMem_tsupport
      (fun htψ => ht (Ioo_subset_Icc_self (hsψ htψ)))
    rw [hz, zero_mul]
  calc
    _ = ∫ t in Iio a, (F t + c) * deriv ψ t :=
      integral_congr_ae (ae_restrict_of_ae he)
    _ = (∫ t in Iio a, F t * deriv ψ t) + c * ∫ t in Iio a, deriv ψ t := by
      simp only [add_mul]
      rw [integral_add hiFD.integrableOn (hiD.const_mul c).integrableOn,
        integral_const_mul]
    _ = ψ a * F a - (∫ t in Iio a, ψ t * σ t ∂ν) + c * ψ a := by
      have hcut : (∫ t in Iio a, F t * deriv ψ t) =
          ψ a * F a - ∫ t in Iio a, ψ t * σ t ∂ν :=
        integral_Iio_cumulative_mul_deriv ν hiσ measurable_id hψ hcψ a
      rw [hcut, ← integral_Iic_eq_integral_Iio (μ := volume) (f := deriv ψ),
        hcψ.integral_Iic_deriv_eq hψ]
    _ = _ := by rw [hp, hL]; dsimp only [F, ν]; ring

/-- A quantitative local trace bound, with an explicit compact derivative-mass term. -/
theorem IsRealBVPolar.trace_abs_le {f σ : ℝ → ℝ} {μ : Measure ℝ}
    (h : IsRealBVPolar f μ σ) (a : ℝ) :
    |bvLeftTrace f a| ≤ (∫ t in Ioo a (a + 1), |f t|) +
        2 * μ.real (Icc (a - 1) (a + 2)) ∧
    |bvRightTrace f a| ≤ (∫ t in Ioo a (a + 1), |f t|) +
        2 * μ.real (Icc (a - 1) (a + 2)) := by
  let := h.finiteOnCompacts
  let ν := μ.restrict (Icc (a - 1) (a + 2))
  let M := μ.real (Icc (a - 1) (a + 2))
  let : IsFiniteMeasure ν := ⟨by
    rw [show ν = μ.restrict (Icc (a - 1) (a + 2)) from rfl,
      Measure.restrict_apply_univ]
    exact isCompact_Icc.measure_lt_top⟩
  have hbound (S : Set ℝ) : |∫ t in S, σ t ∂ν| ≤ M := by
    have hh := norm_integral_le_of_norm_le_const (μ := ν.restrict S)
      ((ae_restrict_of_ae (ae_restrict_of_ae h.norm_ae)).mono fun t ht =>
        show ‖σ t‖ ≤ (1 : ℝ) by simpa only [Real.norm_eq_abs] using ht.le)
    have hm : (ν.restrict S).real univ ≤ M := by
      simpa only [Measure.real, Measure.restrict_apply_univ, ν, M] using
        (measureReal_mono (μ := ν) (subset_univ S))
    have hh' : |∫ t in S, σ t ∂ν| ≤ (ν.restrict S).real univ := by
      simpa only [Real.norm_eq_abs, one_mul] using hh
    exact hh'.trans hm
  obtain ⟨c, hfc, hL, hR⟩ := h.exists_cumulative_with_traces
    (show a ∈ Ioo (a - 1) (a + 2) from ⟨by linarith, by linarith⟩)
  have hi : IntegrableOn (fun t => |f t|) (Ioo a (a + 1)) volume :=
    ((h.locallyIntegrable.integrableOn_isCompact isCompact_Icc).mono_set
      Ioo_subset_Icc_self).abs
  have hestimate (v : ℝ) (hv : |v| ≤ M) :
      |v + c| ≤ (∫ t in Ioo a (a + 1), |f t|) + 2 * M := by
    have hp : ∀ᵐ t ∂volume.restrict (Ioo a (a + 1)), |v + c| ≤ |f t| + 2 * M := by
      have hsub : Ioo a (a + 1) ⊆ Ioo (a - 1) (a + 2) :=
        fun t ht => ⟨by linarith [ht.1], by linarith [ht.2]⟩
      filter_upwards [ae_restrict_of_ae_restrict_of_subset hsub hfc] with t ht
      have hc : |c| ≤ |f t| + M := by
        have he : c = f t - ∫ s in Iio t, σ s ∂ν := by rw [ht]; dsimp [ν]; ring
        rw [he]
        exact (abs_sub _ _).trans (add_le_add_right (hbound (Iio t)) _)
      exact (abs_add_le _ _).trans (by linarith)
    have hint := integral_mono_ae (integrableOn_const (C := |v + c|) measure_Ioo_lt_top.ne)
      (hi.add (integrableOn_const (C := 2 * M) measure_Ioo_lt_top.ne)) hp
    simp only [Pi.add_apply] at hint
    rw [integral_add hi (integrableOn_const measure_Ioo_lt_top.ne)] at hint
    simpa only [setIntegral_const, Measure.real, Real.volume_Ioo, add_sub_cancel_left,
      ENNReal.toReal_ofReal zero_le_one, smul_eq_mul, one_mul] using hint
  rw [hL, hR]
  exact ⟨hestimate _ (hbound (Iio a)), hestimate _ (hbound (Iic a))⟩

/-- The cumulative polar representation alone identifies the two traces and their jump. -/
lemma IsRealBVPolar.trace_jump {f σ : ℝ → ℝ} {μ : Measure ℝ}
    (h : IsRealBVPolar f μ σ) (a : ℝ) :
    bvRightTrace f a - bvLeftTrace f a = μ.real {a} * σ a := by
  have ha : a ∈ Ioo (a - 1) (a + 1) := ⟨by linarith, by linarith⟩
  obtain ⟨c, hfc, hL, hR⟩ := h.exists_cumulative_with_traces ha
  have hi := h.locallyIntegrable_polar.integrableOn_isCompact
    (isCompact_Icc (a := a - 1) (b := a + 1))
  let g : ℝ → ℝ := fun t => (∫ s in Iio t, σ s ∂μ.restrict (Icc (a - 1) (a + 1))) + c
  have hc (t : ℝ) : ContinuousWithinAt g (Iic t) t :=
    (continuousWithinAt_integral_sublevel_left hi measurable_id t).add_const c
  have hr : Function.rightLim g a =
      (∫ s in Iic a, σ s ∂μ.restrict (Icc (a - 1) (a + 1))) + c :=
    rightLim_eq_of_tendsto ((tendsto_integral_sublevel_right hi measurable_id a).add_const c)
  have hj := h.oneDimensionalJump_eq_atom hfc hc ha
  rw [oneDimensionalJump, hr] at hj
  rw [hL, hR]
  exact hj

/-- The right half-line formula uses the exterior trace and the opposite endpoint sign. -/
theorem IsRealBVPolar.integral_Ioi_mul_deriv {f σ : ℝ → ℝ} {μ : Measure ℝ}
    (h : IsRealBVPolar f μ σ) {ψ : ℝ → ℝ}
    (hψ : ContDiff ℝ 1 ψ) (hcψ : HasCompactSupport ψ) (a : ℝ) :
    (∫ t in Ioi a, f t * deriv ψ t) =
      -(ψ a * bvRightTrace f a) - ∫ t in Ioi a, ψ t * σ t ∂μ := by
  let := h.finiteOnCompacts
  have hi : Integrable (fun t => f t * deriv ψ t) volume := by
    simpa only [smul_eq_mul] using h.locallyIntegrable.integrable_smul_right_of_hasCompactSupport
      (hψ.continuous_deriv le_rfl) hcψ.deriv
  have hp : Integrable (fun t => ψ t * σ t) μ := by
    simpa only [smul_eq_mul, mul_comm] using
      h.locallyIntegrable_polar.integrable_smul_right_of_hasCompactSupport hψ.continuous hcψ
  have hv := intervalIntegral.integral_Iic_add_Ioi (b := a) hi.integrableOn hi.integrableOn
  rw [integral_Iic_eq_integral_Iio] at hv
  have hm := intervalIntegral.integral_Iic_add_Ioi (b := a) hp.integrableOn hp.integrableOn
  have hs : Disjoint (Iio a) ({a} : Set ℝ) := by
    rw [disjoint_singleton_right]
    exact lt_irrefl a
  have he : Iio a ∪ ({a} : Set ℝ) = Iic a := by
    ext t
    simp only [mem_union, mem_Iio, mem_singleton_iff, mem_Iic]
    exact le_iff_lt_or_eq.symm
  have hatom := setIntegral_union hs (measurableSet_singleton a)
    hp.integrableOn hp.integrableOn
  rw [he, integral_singleton, smul_eq_mul] at hatom
  have hL := h.integral_Iio_mul_deriv hψ hcψ a
  have htot := h.test_eq ψ hψ hcψ
  have hj := congrArg (fun z : ℝ => ψ a * z) (h.trace_jump a)
  rw [mul_sub] at hj
  nlinarith

/-- Cutting an arbitrary scalar BV function on an interval produces its two endpoint traces. -/
theorem IsRealBVPolar.integral_Ioo_mul_deriv {f σ : ℝ → ℝ} {μ : Measure ℝ}
    (h : IsRealBVPolar f μ σ) {ψ : ℝ → ℝ}
    (hψ : ContDiff ℝ 1 ψ) (hcψ : HasCompactSupport ψ) {a b : ℝ} (hab : a < b) :
    (∫ t in Ioo a b, f t * deriv ψ t) =
      ψ b * bvLeftTrace f b - ψ a * bvRightTrace f a -
        ∫ t in Ioo a b, ψ t * σ t ∂μ := by
  let := h.finiteOnCompacts
  have hi : Integrable (fun t => f t * deriv ψ t) volume := by
    simpa only [smul_eq_mul] using h.locallyIntegrable.integrable_smul_right_of_hasCompactSupport
      (hψ.continuous_deriv le_rfl) hcψ.deriv
  have hp : Integrable (fun t => ψ t * σ t) μ := by
    simpa only [smul_eq_mul, mul_comm] using
      h.locallyIntegrable_polar.integrable_smul_right_of_hasCompactSupport hψ.continuous hcψ
  have hs : Disjoint (Iic a) (Ioo a b) := by
    exact disjoint_left.mpr fun t ht hu => (not_lt_of_ge ht) hu.1
  have he : Iic a ∪ Ioo a b = Iio b := by
    ext t
    simp only [mem_union, mem_Iic, mem_Ioo, mem_Iio]
    constructor
    · rintro (ht | ht)
      · exact ht.trans_lt hab
      · exact ht.2
    · intro ht
      by_cases hta : t ≤ a
      · exact Or.inl hta
      · exact Or.inr ⟨lt_of_not_ge hta, ht⟩
  have hv := setIntegral_union (μ := volume) hs measurableSet_Ioo hi.integrableOn hi.integrableOn
  rw [he, integral_Iic_eq_integral_Iio] at hv
  have hm := setIntegral_union (μ := μ) hs measurableSet_Ioo hp.integrableOn hp.integrableOn
  rw [he] at hm
  have hall := intervalIntegral.integral_Iic_add_Ioi (b := a) hp.integrableOn hp.integrableOn
  have hvall := intervalIntegral.integral_Iic_add_Ioi (b := a) hi.integrableOn hi.integrableOn
  rw [integral_Iic_eq_integral_Iio] at hvall
  have hleft := h.integral_Iio_mul_deriv hψ hcψ b
  have hright := h.integral_Ioi_mul_deriv hψ hcψ a
  have htot := h.test_eq ψ hψ hcψ
  linarith

/-- A line trace is bounded by the global `L¹` norm and twice the genuine BV variation. -/
theorem IsBVOn.lineTrace_abs_le {f : ℝ → ℝ}
    (hf : IsBVOn (f ∘ euclideanOneReal) univ) (a : ℝ) :
    |bvLeftTrace f a| ≤ (∫ t, |f t|) + 2 * (variation (f ∘ euclideanOneReal) univ).toReal ∧
    |bvRightTrace f a| ≤ (∫ t, |f t|) + 2 * (variation (f ∘ euclideanOneReal) univ).toReal := by
  have hl := isLocallyBVOn_of_variation_lt_top isOpen_univ hf.1.locallyIntegrableOn hf.2
  obtain ⟨μ, σ, h⟩ := exists_real_bv_polar hl
  have hmass : μ univ = variation (f ∘ euclideanOneReal) univ := by
    simpa only [preimage_univ] using h.open_eq univ isOpen_univ
  have hfin : μ univ ≠ ∞ := by rw [hmass]; exact hf.2.ne
  have hif : Integrable f volume := by
    have hi := integrableOn_univ.mp hf.1
    have hh := (euclideanOneReal.symm.measurePreserving.integrable_comp
      hi.aestronglyMeasurable).mpr hi
    simpa only [Function.comp_def, euclideanOneReal.apply_symm_apply] using hh
  have hle : (∫ t in Ioo a (a + 1), |f t|) + 2 * μ.real (Icc (a - 1) (a + 2)) ≤
      (∫ t, |f t|) + 2 * (variation (f ∘ euclideanOneReal) univ).toReal := by
    apply add_le_add
    · exact setIntegral_le_integral hif.abs (ae_of_all _ fun _ => abs_nonneg _)
    · apply mul_le_mul_of_nonneg_left _ (by norm_num)
      have hm := measureReal_mono (μ := μ) (subset_univ (Icc (a - 1) (a + 2))) hfin
      simpa only [Measure.real, hmass] using hm
  exact ⟨(h.trace_abs_le a).1.trans hle, (h.trace_abs_le a).2.trans hle⟩

end LiquidDrop

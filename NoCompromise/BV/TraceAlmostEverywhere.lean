module

public import NoCompromise.BV.FlatTraces
public import NoCompromise.BV.LineDistribution
public import Mathlib.Topology.EMetricSpace.VariationOnFromTo

@[expose] public section

/-!
# Almost every flat trace is the original slice

Normal averages provide joint measurability of the actual essential traces.
This justifies changing the order of the almost-everywhere quantifiers in the
line-slicing argument, without presuming that arbitrary separately measurable
functions are jointly measurable.
-/

noncomputable section
open MeasureTheory Filter Set Metric
open scoped ENNReal Topology
namespace LiquidDrop
set_option maxSynthPendingDepth 8

/-- Both genuine one-sided traces coincide with the original function at almost
all real points. -/
theorem IsLocallyBVOn.bvTraces_ae_eq {f : ℝ → ℝ}
    (hf : IsLocallyBVOn (f ∘ euclideanOneReal) univ) :
    ∀ᵐ a : ℝ, bvLeftTrace f a = f a ∧ bvRightTrace f a = f a := by
  have hlocal (k : ℕ) : ∀ᵐ a ∂volume.restrict (Ioo (-(k : ℝ)) k),
      bvLeftTrace f a = f a ∧ bvRightTrace f a = f a := by
    obtain ⟨g, hg, _, he⟩ := hf.exists_boundedVariationOn_representative_Ioo (-(k : ℝ)) k
    have he' : f =ᵐ[volume.restrict (Ioo (-(k : ℝ)) k)] g := by
      simpa only [Function.comp_def, euclideanOneReal.apply_symm_apply] using he
    filter_upwards [he', ae_restrict_mem measurableSet_Ioo,
      ae_restrict_of_ae (hg.countable_not_continuousAt.ae_notMem volume)] with a hea ha hca
    have hcont : ContinuousAt g a := by simpa only [mem_ofPred_eq, not_not] using hca
    have hl : HasBVLeftTrace f a (g a) :=
      (hcont.tendsto.mono_left (inf_le_left.trans nhdsWithin_le_nhds)).congr'
        (eventuallyEq_bvTraceLeftFilter_of_ae_eq_near
          (isOpen_Ioo.mem_nhds ha) he').symm
    have hr : HasBVRightTrace f a (g a) :=
      (hcont.tendsto.mono_left (inf_le_left.trans nhdsWithin_le_nhds)).congr'
        (eventuallyEq_bvTraceRightFilter_of_ae_eq_near
          (isOpen_Ioo.mem_nhds ha) he').symm
    exact ⟨hl.eq_bvLeftTrace.trans hea.symm, hr.eq_bvRightTrace.trans hea.symm⟩
  have hall : ∀ᵐ a : ℝ, ∀ k : ℕ, a ∈ Ioo (-(k : ℝ)) k →
      bvLeftTrace f a = f a ∧ bvRightTrace f a = f a :=
    ae_all_iff.mpr fun k => ae_imp_of_ae_restrict (hlocal k)
  filter_upwards [hall] with a ha
  obtain ⟨k, hk⟩ := exists_nat_gt |a|
  exact ha k ⟨by linarith [neg_abs_le a], by linarith [le_abs_self a]⟩

/-- Moving one-sided normal averages are jointly measurable in base point and height. -/
lemma measurable_flat_left_average {n : ℕ}
    {f : EuclideanSpace ℝ (Fin (n + 1)) → ℝ} (hf : Measurable f) (r : ℝ) :
    Measurable (fun p : EuclideanSpace ℝ (Fin n) × ℝ =>
      r⁻¹ * ∫ t in Ioo (p.2 - r) p.2, f (graphAppendN p.1 t)) := by
  let S : Set ((EuclideanSpace ℝ (Fin n) × ℝ) × ℝ) :=
    {q | q.1.2 - r < q.2 ∧ q.2 < q.1.2}
  have hS : MeasurableSet S :=
    (measurableSet_lt (measurable_snd.comp measurable_fst |>.sub_const r)
      measurable_snd).inter
      (measurableSet_lt measurable_snd (measurable_snd.comp measurable_fst))
  have hq : Measurable (fun q : (EuclideanSpace ℝ (Fin n) × ℝ) × ℝ =>
      f (graphAppendN q.1.1 q.2)) :=
    hf.comp ((realLineCoordinates n).continuous.measurable.comp
      ((measurable_fst.comp measurable_fst).prodMk measurable_snd))
  have hi := (hq.indicator hS).stronglyMeasurable.integral_prod_right' (ν := volume) |>.measurable
  convert hi.const_mul r⁻¹ using 1
  ext p
  congr 1
  rw [← integral_indicator measurableSet_Ioo]
  apply integral_congr_ae
  exact ae_of_all _ fun t => by simp [S, Set.indicator]

lemma measurable_flat_right_average {n : ℕ}
    {f : EuclideanSpace ℝ (Fin (n + 1)) → ℝ} (hf : Measurable f) (r : ℝ) :
    Measurable (fun p : EuclideanSpace ℝ (Fin n) × ℝ =>
      r⁻¹ * ∫ t in Ioo p.2 (p.2 + r), f (graphAppendN p.1 t)) := by
  let S : Set ((EuclideanSpace ℝ (Fin n) × ℝ) × ℝ) :=
    {q | q.1.2 < q.2 ∧ q.2 < q.1.2 + r}
  have hS : MeasurableSet S :=
    (measurableSet_lt (measurable_snd.comp measurable_fst) measurable_snd).inter
      (measurableSet_lt measurable_snd
        (measurable_snd.comp measurable_fst |>.add_const r))
  have hq : Measurable (fun q : (EuclideanSpace ℝ (Fin n) × ℝ) × ℝ =>
      f (graphAppendN q.1.1 q.2)) :=
    hf.comp ((realLineCoordinates n).continuous.measurable.comp
      ((measurable_fst.comp measurable_fst).prodMk measurable_snd))
  have hi := (hq.indicator hS).stronglyMeasurable.integral_prod_right' (ν := volume) |>.measurable
  convert hi.const_mul r⁻¹ using 1
  ext p
  congr 1
  rw [← integral_indicator measurableSet_Ioo]
  apply integral_congr_ae
  exact ae_of_all _ fun t => by simp [S, Set.indicator]

/-- The actual left and right traces are jointly almost-everywhere measurable. -/
theorem IsLocallyBVOn.aestronglyMeasurable_flatBVTraces_joint {n : ℕ}
    {f : EuclideanSpace ℝ (Fin (n + 1)) → ℝ}
    (hf : IsLocallyBVOn f univ) (hmf : Measurable f) :
    AEStronglyMeasurable (fun p : EuclideanSpace ℝ (Fin n) × ℝ =>
      flatBVLeftTrace f p.2 p.1) (volume.prod volume) ∧
    AEStronglyMeasurable (fun p : EuclideanSpace ℝ (Fin n) × ℝ =>
      flatBVRightTrace f p.2 p.1) (volume.prod volume) := by
  have hs : ∀ᵐ p : EuclideanSpace ℝ (Fin n) × ℝ ∂volume.prod volume,
      IsLocallyBVOn ((fun t : ℝ => f (graphAppendN p.1 t)) ∘ euclideanOneReal) univ :=
    Measure.quasiMeasurePreserving_fst.ae hf.ae_lineSlice
  have hi : ∀ᵐ p : EuclideanSpace ℝ (Fin n) × ℝ ∂volume.prod volume,
      LocallyIntegrable (fun t : ℝ => f (graphAppendN p.1 t)) volume := by
    filter_upwards [hs] with p hp
    obtain ⟨μ, σ, h⟩ := exists_real_bv_polar hp
    exact h.locallyIntegrable
  constructor
  · apply aestronglyMeasurable_of_tendsto_ae (𝓝[>] (0 : ℝ))
      (f := fun r p => r⁻¹ * ∫ t in Ioo (p.2 - r) p.2, f (graphAppendN p.1 t))
    · exact fun r => (measurable_flat_left_average hmf r).aestronglyMeasurable
    · filter_upwards [hs, hi] with p hp hip
      exact (hp.hasBVLeftTrace p.2).tendsto_mean hip
  · apply aestronglyMeasurable_of_tendsto_ae (𝓝[>] (0 : ℝ))
      (f := fun r p => r⁻¹ * ∫ t in Ioo p.2 (p.2 + r), f (graphAppendN p.1 t))
    · exact fun r => (measurable_flat_right_average hmf r).aestronglyMeasurable
    · filter_upwards [hs, hi] with p hp hip
      exact (hp.hasBVRightTrace p.2).tendsto_mean hip

/-- Fubini for equality of jointly almost-everywhere measurable real functions. -/
lemma ae_eq_prod_of_ae_ae_eq {A B : Type*} [MeasurableSpace A] [MeasurableSpace B]
    {μ : Measure A} {ρ : Measure B} [SFinite μ] [SFinite ρ]
    {f g : A × B → ℝ} (hf : AEMeasurable f (μ.prod ρ))
    (hg : AEMeasurable g (μ.prod ρ))
    (he : ∀ᵐ x ∂μ, ∀ᵐ y ∂ρ, f (x, y) = g (x, y)) : f =ᵐ[μ.prod ρ] g := by
  have hm : hf.mk f =ᵐ[μ.prod ρ] hg.mk g := by
    apply (Measure.ae_prod_iff_ae_ae
      (measurableSet_eq_fun hf.measurable_mk hg.measurable_mk)).mpr
    filter_upwards [he, Measure.ae_ae_of_ae_prod hf.ae_eq_mk,
      Measure.ae_ae_of_ae_prod hg.ae_eq_mk] with x hx hfx hgx
    filter_upwards [hx, hfx, hgx] with y hxy hfxy hgxy
    exact hfxy.symm.trans (hxy.trans hgxy)
  exact hf.ae_eq_mk.trans (hm.trans hg.ae_eq_mk.symm)

/-- Almost every flat interface sees the actual measurable representative from
both sides, with one common exceptional set of heights. -/
theorem IsLocallyBVOn.ae_flatBVTraces_eq {n : ℕ}
    {f : EuclideanSpace ℝ (Fin (n + 1)) → ℝ}
    (hf : IsLocallyBVOn f univ) (hmf : Measurable f) :
    ∀ᵐ a : ℝ, ∀ᵐ x : EuclideanSpace ℝ (Fin n),
      flatBVLeftTrace f a x = f (graphAppendN x a) ∧
      flatBVRightTrace f a x = f (graphAppendN x a) := by
  have hboth : ∀ᵐ x : EuclideanSpace ℝ (Fin n), ∀ᵐ a : ℝ,
      flatBVLeftTrace f a x = f (graphAppendN x a) ∧
      flatBVRightTrace f a x = f (graphAppendN x a) := by
    filter_upwards [hf.ae_lineSlice] with x hx
    exact (show IsLocallyBVOn
      ((fun a => f (graphAppendN x a)) ∘ euclideanOneReal) univ from hx).bvTraces_ae_eq
  have hm := hf.aestronglyMeasurable_flatBVTraces_joint hmf
  have hmf' : Measurable (fun p : EuclideanSpace ℝ (Fin n) × ℝ =>
      f (graphAppendN p.1 p.2)) := hmf.comp (realLineCoordinates n).continuous.measurable
  have hl := ae_eq_prod_of_ae_ae_eq hm.1.aemeasurable hmf'.aemeasurable
    (hboth.mono fun _ hx => hx.mono fun _ ha => ha.1)
  have hr := ae_eq_prod_of_ae_ae_eq hm.2.aemeasurable hmf'.aemeasurable
    (hboth.mono fun _ hx => hx.mono fun _ ha => ha.2)
  exact Measure.ae_ae_of_ae_prod
    (Measure.measurePreserving_swap.quasiMeasurePreserving.ae (hl.and hr))

/-- Ambient almost-everywhere equality preserves both traces on almost every
normal line, simultaneously at every height. -/
theorem IsLocallyBVOn.ae_all_flatBVTraces_congr {n : ℕ}
    {f g : EuclideanSpace ℝ (Fin (n + 1)) → ℝ}
    (hf : IsLocallyBVOn f univ) (he : f =ᵐ[volume] g) :
    ∀ᵐ x : EuclideanSpace ℝ (Fin n), ∀ a : ℝ,
      flatBVLeftTrace f a x = flatBVLeftTrace g a x ∧
      flatBVRightTrace f a x = flatBVRightTrace g a x := by
  have hep := (realLineCoordinates_measurePreserving n).quasiMeasurePreserving.ae_eq_comp he
  filter_upwards [hf.ae_line_oneSided_traces, Measure.ae_ae_of_ae_prod hep] with x hx hex
  intro a
  exact ⟨((hx a).1.congr_ae hex).eq_bvLeftTrace.symm,
    ((hx a).2.congr_ae hex).eq_bvRightTrace.symm⟩

/-- Almost every flat trace of a locally BV function equals any Borel
representative of that function on the plane. -/
theorem IsLocallyBVOn.ae_flatBVTraces_eq_of_ae {n : ℕ}
    {f g : EuclideanSpace ℝ (Fin (n + 1)) → ℝ}
    (hf : IsLocallyBVOn f univ) (hg : Measurable g) (he : f =ᵐ[volume] g) :
    ∀ᵐ a : ℝ, ∀ᵐ x : EuclideanSpace ℝ (Fin n),
      flatBVLeftTrace f a x = g (graphAppendN x a) ∧
      flatBVRightTrace f a x = g (graphAppendN x a) := by
  have hgbv : IsLocallyBVOn g univ := hf.congr_ae (by simpa only [Measure.restrict_univ] using he)
  have htrace := hf.ae_all_flatBVTraces_congr he
  filter_upwards [hgbv.ae_flatBVTraces_eq hg] with a ha
  filter_upwards [ha, htrace] with x hx htx
  exact ⟨(htx a).1.trans hx.1, (htx a).2.trans hx.2⟩

end LiquidDrop

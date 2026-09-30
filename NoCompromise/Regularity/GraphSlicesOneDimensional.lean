module

public import NoCompromise.BV.JumpDisintegration

@[expose] public section

/-! # The actual signed jump count between cleared binary phases -/

noncomputable section
open Set MeasureTheory Filter Metric
open scoped ENNReal Topology
namespace LiquidDrop
set_option maxSynthPendingDepth 8

/-- The cumulative representation gives the fundamental theorem on an interior
half-open interval, with no continuity of the original BV function assumed. -/
lemma IsRealBVPolar.integral_Ico_eq_sub
    {f g σ : ℝ → ℝ} {μ : Measure ℝ} {a b α β : ℝ}
    (h : IsRealBVPolar f μ σ)
    (hfg : f =ᵐ[volume.restrict (Ioo a b)] g)
    (hc : ∀ t, ContinuousWithinAt g (Iic t) t)
    (hα : α ∈ Ioo a b) (hβ : β ∈ Ioo a b) (hαβ : α ≤ β) :
    (∫ t in Ico α β, σ t ∂μ) = g β - g α := by
  let := h.finiteOnCompacts
  let : IsFiniteMeasure (μ.restrict (Icc a b)) := ⟨by
    rw [Measure.restrict_apply_univ]
    exact isCompact_Icc.measure_lt_top⟩
  have hi : Integrable σ (μ.restrict (Icc a b)) :=
    Integrable.of_bound h.measurable.aestronglyMeasurable.restrict 1
      ((ae_restrict_of_ae h.norm_ae).mono fun t ht => by
        simpa only [Real.norm_eq_abs] using ht.le)
  obtain ⟨c, he⟩ := h.exists_cumulative_eqOn_Ioo a b hfg hc
  have hd := setIntegral_sdiff (μ := μ.restrict (Icc a b))
    (s := Iio β) (t := Iio α) measurableSet_Iio hi.integrableOn
    (fun _ ht => ht.trans_le hαβ)
  have hs : Iio β \ Iio α = Ico α β := by
    ext t
    simp only [Set.mem_sdiff, mem_Iio, mem_Ico, not_lt]
    tauto
  rw [hs, Measure.restrict_restrict measurableSet_Ico,
    inter_eq_left.mpr (show Ico α β ⊆ Icc a b from fun t ht =>
      ⟨hα.1.le.trans ht.1, ht.2.le.trans hβ.2.le⟩)] at hd
  rw [he hβ, he hα]
  linarith

/-- A left-continuous representative has the actual constant value throughout
an open interval on which the original function is almost everywhere constant. -/
lemma IsBinaryBVRepresentativeOn.eqOn_of_ae_const
    {f g : ℝ → ℝ} {a b l u c : ℝ}
    (hg : IsBinaryBVRepresentativeOn f g a b)
    (hsub : Ioo l u ⊆ Ioo a b)
    (hf : f =ᵐ[volume.restrict (Ioo l u)] fun _ => c) :
    EqOn g (fun _ => c) (Ioo l u) := by
  apply eqOn_Ioo_of_left_continuous_ae_eq (fun t _ => hg.leftContinuous t)
    (fun _ _ => continuousWithinAt_const)
  have he : f =ᵐ[volume.restrict (Ioo l u)] g :=
    ae_mono (Measure.restrict_mono hsub le_rfl) hg.ae_eq
  exact he.symm.trans hf

/-- Genuine lower-one and upper-zero phase bands force total derivative -1,
equivalently outward oriented jump count +1, on the intervening interval. -/
theorem IsBinaryBVRepresentativeOn.oriented_jump_count
    {f g σ : ℝ → ℝ} {μ : Measure ℝ} {a b l u α β : ℝ}
    (hg : IsBinaryBVRepresentativeOn f g a b) (hμ : IsRealBVPolar f μ σ)
    (hl : l ≤ b) (hu : a ≤ u)
    (hα : α ∈ Ioo a l) (hβ : β ∈ Ioo u b) (hαβ : α < β)
    (hL : f =ᵐ[volume.restrict (Ioo a l)] fun _ => 1)
    (hU : f =ᵐ[volume.restrict (Ioo u b)] fun _ => 0) :
    {t ∈ Ioo α β | oneDimensionalJump g t ≠ 0}.Finite ∧
      (∫ t in Ioo α β, σ t ∂μ) = -1 ∧
      -(∑ᶠ t : ℝ, (Ioo α β).indicator (oneDimensionalJump g) t) = 1 := by
  have hα' : α ∈ Ioo a b := ⟨hα.1, hα.2.trans_le hl⟩
  have hβ' : β ∈ Ioo a b := ⟨hu.trans_lt hβ.1, hβ.2⟩
  have hsub : Icc α β ⊆ Ioo a b := fun t ht =>
    ⟨hα'.1.trans_le ht.1, ht.2.trans_lt hβ'.2⟩
  have heα : g α = 1 := hg.eqOn_of_ae_const
    (fun _ ht => ⟨ht.1, ht.2.trans_le hl⟩) hL hα
  have heβ : g β = 0 := hg.eqOn_of_ae_const
    (fun _ ht => ⟨hu.trans_lt ht.1, ht.2⟩) hU hβ
  have hz : μ {α} = 0 := measure_mono_null (singleton_subset_iff.mpr hα)
    (hμ.measure_eq_zero_of_ae_const isOpen_Ioo hL)
  have hi := hμ.integral_Ico_eq_sub hg.ae_eq hg.leftContinuous hα' hβ' hαβ.le
  rw [integral_Ico_eq_integral_Ioo' hz, heα, heβ] at hi
  norm_num at hi
  refine ⟨((hg.finite_jumps isCompact_Icc hsub).subset fun t ht =>
    ⟨Ioo_subset_Icc_self ht.1, ht.2⟩), hi, ?_⟩
  rw [← hg.setIntegral_eq_finsum_jumps hμ isCompact_Icc hsub
    measurableSet_Ioo Ioo_subset_Icc_self, hi]
  norm_num

end LiquidDrop

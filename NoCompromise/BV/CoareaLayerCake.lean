module

public import NoCompromise.BV.StrictApprox
public import Mathlib.MeasureTheory.Integral.Layercake
public import Mathlib.MeasureTheory.Function.ConvergenceInMeasure

@[expose] public section

/-!
# Layer-cake distances and almost-everywhere convergence of superlevels

The L1 distance equals the integral of the distances of the strict superlevel
indicators. Vanishing integrable errors therefore give a common subsequence
with L1 convergence of superlevels for almost every level.
-/

noncomputable section
open MeasureTheory Filter Set
open scoped ENNReal Topology
namespace LiquidDrop
set_option maxSynthPendingDepth 8

/-- The actual real-valued indicator of the strict superlevel set. -/
def superlevelIndicator {α : Type*} (f : α → ℝ) (t : ℝ) : α → ℝ :=
  {x | t < f x}.indicator (fun _ => 1)

lemma superlevelIndicator_apply {α : Type*} (f : α → ℝ) (t : ℝ) (x : α) :
    superlevelIndicator f t x = if t < f x then 1 else 0 := by
  classical
  simp only [superlevelIndicator, indicator_apply, mem_ofPred_eq]

lemma ofReal_abs_superlevel_difference (a b t : ℝ) :
    ENNReal.ofReal |(if t < a then (1 : ℝ) else 0) - (if t < b then 1 else 0)| =
      (Ico (min a b) (max a b)).indicator (fun _ => (1 : ℝ≥0∞)) t := by
  classical
  rcases le_total a b with hab | hba
  · rw [min_eq_left hab, max_eq_right hab]
    by_cases hta : t < a <;> by_cases htb : t < b <;>
      simp only [hta, htb, ↓reduceIte, indicator_apply, mem_Ico]
    all_goals split_ifs <;> norm_num at * <;> linarith
  · rw [min_eq_right hba, max_eq_left hba]
    by_cases hta : t < a <;> by_cases htb : t < b <;>
      simp only [hta, htb, ↓reduceIte, indicator_apply, mem_Ico]
    all_goals split_ifs <;> norm_num at * <;> linarith

/-- The length between two real values is the total difference of their level indicators. -/
theorem lintegral_abs_superlevel_difference (a b : ℝ) :
    (∫⁻ t : ℝ, ENNReal.ofReal
      |(if t < a then (1 : ℝ) else 0) - (if t < b then 1 else 0)|) =
        ENNReal.ofReal |a - b| := by
  simp_rw [ofReal_abs_superlevel_difference]
  rw [lintegral_indicator measurableSet_Ico]
  simp [Real.volume_Ico, max_sub_min_eq_abs, abs_sub_comm]

/-- Joint measurability of strict superlevel indicators. -/
lemma measurable_superlevelIndicator_uncurry {α : Type*} [MeasurableSpace α]
    {f : α → ℝ} (hf : Measurable f) :
    Measurable (fun p : ℝ × α => superlevelIndicator f p.1 p.2) := by
  simpa only [superlevelIndicator_apply, Function.comp_def] using
    measurable_const.ite (measurableSet_lt measurable_fst (hf.comp measurable_snd)) measurable_const

/-- Tonelli's level-set formula for the L¹ distance, with infinite values allowed. -/
theorem lintegral_superlevel_l1_distance {α : Type*} [MeasurableSpace α]
    {μ : Measure α} [SFinite μ] {f g : α → ℝ} (hf : Measurable f) (hg : Measurable g) :
    (∫⁻ t : ℝ, ∫⁻ x, ENNReal.ofReal
      |superlevelIndicator f t x - superlevelIndicator g t x| ∂μ) =
        ∫⁻ x, ENNReal.ofReal |f x - g x| ∂μ := by
  have hm : Measurable (fun p : ℝ × α => ENNReal.ofReal
      |superlevelIndicator f p.1 p.2 - superlevelIndicator g p.1 p.2|) :=
    by simpa only [Real.norm_eq_abs, Pi.sub_apply] using
      ((measurable_superlevelIndicator_uncurry hf).sub
        (measurable_superlevelIndicator_uncurry hg)).norm.ennreal_ofReal
  rw [lintegral_lintegral_swap hm.aemeasurable]
  apply lintegral_congr
  intro x
  simp only [superlevelIndicator_apply]
  exact lintegral_abs_superlevel_difference (f x) (g x)

/-- Scalar AE changes do not change any level-set L¹ distance. -/
lemma superlevel_l1_distance_congr_ae {α : Type*} [MeasurableSpace α]
    {μ : Measure α} {f f' g g' : α → ℝ}
    (hf : f =ᵐ[μ] f') (hg : g =ᵐ[μ] g') (t : ℝ) :
    (∫⁻ x, ENNReal.ofReal |superlevelIndicator f t x - superlevelIndicator g t x| ∂μ) =
      ∫⁻ x, ENNReal.ofReal |superlevelIndicator f' t x - superlevelIndicator g' t x| ∂μ := by
  apply lintegral_congr_ae
  filter_upwards [hf, hg] with x hx hy
  simp only [superlevelIndicator_apply, hx, hy]

/-- The distance of the superlevel indicators is measurable in the level,
even for merely AE-measurable input representatives. -/
lemma measurable_superlevel_l1_distance {α : Type*} [MeasurableSpace α]
    {μ : Measure α} [SFinite μ] {f g : α → ℝ} (hf : AEMeasurable f μ)
    (hg : AEMeasurable g μ) : Measurable (fun t : ℝ =>
      ∫⁻ x, ENNReal.ofReal |superlevelIndicator f t x - superlevelIndicator g t x| ∂μ) := by
  have heq := funext (superlevel_l1_distance_congr_ae hf.ae_eq_mk hg.ae_eq_mk)
  rw [heq]
  apply Measurable.lintegral_prod_right' (f := fun p : ℝ × α =>
    ENNReal.ofReal |superlevelIndicator (hf.mk f) p.1 p.2 -
      superlevelIndicator (hg.mk g) p.1 p.2|)
  simpa only [Real.norm_eq_abs, Pi.sub_apply] using
    ((measurable_superlevelIndicator_uncurry hf.measurable_mk).sub
      (measurable_superlevelIndicator_uncurry hg.measurable_mk)).norm.ennreal_ofReal

/-- Tonelli's level-set L¹ identity for AE-measurable representatives. -/
theorem lintegral_superlevel_l1_distance_ae {α : Type*} [MeasurableSpace α]
    {μ : Measure α} [SFinite μ] {f g : α → ℝ} (hf : AEMeasurable f μ)
    (hg : AEMeasurable g μ) :
    (∫⁻ t : ℝ, ∫⁻ x, ENNReal.ofReal
      |superlevelIndicator f t x - superlevelIndicator g t x| ∂μ) =
        ∫⁻ x, ENNReal.ofReal |f x - g x| ∂μ := by
  calc
    _ = ∫⁻ t : ℝ, ∫⁻ x, ENNReal.ofReal
        |superlevelIndicator (hf.mk f) t x - superlevelIndicator (hg.mk g) t x| ∂μ :=
      lintegral_congr (superlevel_l1_distance_congr_ae hf.ae_eq_mk hg.ae_eq_mk)
    _ = ∫⁻ x, ENNReal.ofReal |hf.mk f x - hg.mk g x| ∂μ :=
      lintegral_superlevel_l1_distance hf.measurable_mk hg.measurable_mk
    _ = _ := by
      apply lintegral_congr_ae
      filter_upwards [hf.ae_eq_mk, hg.ae_eq_mk] with x hx hy
      rw [hx, hy]

/-- A sequence of finite-integral nonnegative extended-valued functions whose
integrals vanish admits a subsequence tending to zero almost everywhere. -/
theorem exists_subseq_ae_tendsto_zero_of_lintegral {α : Type*} [MeasurableSpace α]
    {μ : Measure α} {s : ℕ → α → ℝ≥0∞} (hs : ∀ j, AEMeasurable (s j) μ)
    (hfin : ∀ j, (∫⁻ x, s j x ∂μ) < ∞)
    (ht : Tendsto (fun j => ∫⁻ x, s j x ∂μ) atTop (𝓝 0)) :
    ∃ σ : ℕ → ℕ, StrictMono σ ∧
      ∀ᵐ x ∂μ, Tendsto (fun j => s (σ j) x) atTop (𝓝 0) := by
  let q (j : ℕ) (x : α) : ℝ := (s j x).toReal
  have hq (j) : AEStronglyMeasurable (q j) μ := (hs j).ennreal_toReal.aestronglyMeasurable
  have hfinite (j) : ∀ᵐ x ∂μ, s j x < ∞ := ae_lt_top' (hs j) (hfin j).ne
  have heq (j) : eLpNorm (q j) 1 μ = ∫⁻ x, s j x ∂μ := by
    rw [eLpNorm_one_eq_lintegral_enorm (hq j)]
    apply lintegral_congr_ae
    filter_upwards [hfinite j] with x hx
    simp only [q, Real.enorm_eq_ofReal ENNReal.toReal_nonneg, ENNReal.ofReal_toReal hx.ne]
  have htq : Tendsto (fun j => eLpNorm (q j - 0) 1 μ) atTop (𝓝 0) := by
    simpa only [sub_zero, heq] using ht
  obtain ⟨σ, hσ, hconv⟩ := (tendstoInMeasure_of_tendsto_eLpNorm (by norm_num :
    (1 : ℝ≥0∞) ≠ 0) htq).exists_seq_tendsto_ae
  refine ⟨σ, hσ, ?_⟩
  filter_upwards [hconv, ae_all_iff.mpr hfinite] with x hx hfx
  have h := ENNReal.continuous_ofReal.continuousAt.tendsto.comp hx
  simpa only [q, ENNReal.ofReal_toReal (hfx _).ne, Pi.zero_apply,
    ENNReal.ofReal_zero, Function.comp_def] using h

/-- L¹ convergence of errors yields convergence of superlevel indicators for
almost every level along a single strictly increasing subsequence. -/
theorem exists_subseq_superlevel_l1_of_l1_errors {α : Type*} [MeasurableSpace α]
    {μ : Measure α} [SFinite μ] {f : ℕ → α → ℝ} {g : α → ℝ}
    (hf : ∀ j, AEMeasurable (f j) μ) (hg : AEMeasurable g μ)
    (hi : ∀ j, Integrable (fun x => f j x - g x) μ)
    (ht : Tendsto (fun j => ∫⁻ x, ENNReal.ofReal |f j x - g x| ∂μ) atTop (𝓝 0)) :
    ∃ σ : ℕ → ℕ, StrictMono σ ∧ ∀ᵐ t : ℝ ∂volume,
      Tendsto (fun j => ∫⁻ x, ENNReal.ofReal
        |superlevelIndicator (f (σ j)) t x - superlevelIndicator g t x| ∂μ)
        atTop (𝓝 0) := by
  apply exists_subseq_ae_tendsto_zero_of_lintegral
    (fun j => (measurable_superlevel_l1_distance (hf j) hg).aemeasurable)
  · intro j
    rw [lintegral_superlevel_l1_distance_ae (hf j) hg]
    simpa only [hasFiniteIntegral_iff_norm, Real.norm_eq_abs] using (hi j).hasFiniteIntegral
  · simpa only [lintegral_superlevel_l1_distance_ae (hf _) hg] using ht

end LiquidDrop

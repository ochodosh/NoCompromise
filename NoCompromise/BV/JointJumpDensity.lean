import NoCompromise.BV.JumpProduct
import Mathlib.MeasureTheory.Constructions.Polish.Basic

/-!
# A jointly Borel density for binary slice derivatives

Shrinking right-minus-left averages recover the canonical jump at every
interior point of a binary BV representative. Consequently their Borel limit
agrees with each slice polar density almost everywhere, and has absolute value
one for the product measure constructed from the actual slice measures.
-/

noncomputable section
open MeasureTheory Filter Set Metric
open scoped ENNReal Topology
namespace LiquidDrop

/-- Right-minus-left normalized averages, with the integration interval fixed. -/
def lineAverageDifference {α : Type*} (F : α × ℝ → ℝ) (r : ℝ) (p : α × ℝ) : ℝ :=
  (∫ s in Ioo (0 : ℝ) 1, F (p.1, p.2 + r * s)) -
    ∫ s in Ioo (0 : ℝ) 1, F (p.1, p.2 - r * s)

lemma measurable_lineAverageDifference {α : Type*} [MeasurableSpace α]
    {F : α × ℝ → ℝ} (hF : Measurable F) (r : ℝ) :
    Measurable (lineAverageDifference F r) := by
  have hr : StronglyMeasurable (fun p : (α × ℝ) × ℝ =>
      F (p.1.1, p.1.2 + r * p.2)) :=
    (hF.comp ((measurable_fst.comp measurable_fst).prodMk
      ((measurable_snd.comp measurable_fst).add
        (measurable_const.mul measurable_snd)))).stronglyMeasurable
  have hl : StronglyMeasurable (fun p : (α × ℝ) × ℝ =>
      F (p.1.1, p.1.2 - r * p.2)) :=
    (hF.comp ((measurable_fst.comp measurable_fst).prodMk
      ((measurable_snd.comp measurable_fst).sub
        (measurable_const.mul measurable_snd)))).stronglyMeasurable
  exact (hr.integral_prod_right' (ν := volume.restrict (Ioo (0 : ℝ) 1))).measurable.sub
    (hl.integral_prod_right' (ν := volume.restrict (Ioo (0 : ℝ) 1))).measurable

/-- A jointly Borel choice of jump density, obtained from shrinking one-sided averages. -/
def jointJumpDensity {α : Type*} (F : α × ℝ → ℝ) (p : α × ℝ) : ℝ :=
  limUnder atTop (fun k : ℕ => lineAverageDifference F ((k + 1 : ℝ)⁻¹) p)

lemma measurable_jointJumpDensity {α : Type*} [MeasurableSpace α]
    {F : α × ℝ → ℝ} (hF : Measurable F) : Measurable (jointJumpDensity F) :=
  (StronglyMeasurable.limUnder (fun k : ℕ =>
    (measurable_lineAverageDifference hF ((k + 1 : ℝ)⁻¹)).stronglyMeasurable)).measurable

lemma integral_affine_eq_const_of_ae {f : ℝ → ℝ} {a b t r c : ℝ}
    (hr : r ≠ 0) (hf : f =ᵐ[volume.restrict (Ioo a b)] (fun _ => c))
    (hm : MapsTo (fun s => t + r * s) (Ioo (0 : ℝ) 1) (Ioo a b)) :
    (∫ s in Ioo (0 : ℝ) 1, f (t + r * s)) = c := by
  have hp : Measure.QuasiMeasurePreserving (fun s : ℝ => t + r * s) volume volume := by
    simpa only [Function.comp_def, smul_eq_mul] using
      (quasiMeasurePreserving_add_left volume t).comp
        (Measure.quasiMeasurePreserving_smul volume hr)
  have hfa : ∀ᵐ y ∂volume, y ∈ Ioo a b → f y = c :=
    (ae_restrict_iff' measurableSet_Ioo).mp hf
  have he : (fun s => f (t + r * s)) =ᵐ[volume.restrict (Ioo (0 : ℝ) 1)] (fun _ => c) := by
    filter_upwards [ae_restrict_of_ae (hp.ae hfa), ae_restrict_mem measurableSet_Ioo]
      with s hs hsI
    exact hs (hm hsI)
  rw [integral_congr_ae he]
  simp

lemma IsBinaryBVRepresentativeOn.exists_ae_const_left {f g : ℝ → ℝ} {a b t : ℝ}
    (h : IsBinaryBVRepresentativeOn f g a b) (ht : t ∈ Ioo a b) :
    ∃ δ > 0, f =ᵐ[volume.restrict (Ioo (t - δ) t)] (fun _ => g t) := by
  have hnear : ∀ᶠ y in 𝓝[<] t, y ∈ Ioo a b :=
    mem_nhdsWithin_of_mem_nhds (isOpen_Ioo.mem_nhds ht)
  have heq := eventually_eq_of_tendsto_binary
    (hnear.mono fun y hy => h.binary y hy)
    ((h.leftContinuous t).mono Iio_subset_Iic_self)
  obtain ⟨δ, hδ, hgood⟩ := Metric.mem_nhdsWithin_iff.mp (hnear.and heq)
  have hside (y : ℝ) (hy : y ∈ Ioo (t - δ) t) : y ∈ Ioo a b ∧ g y = g t := by
    apply hgood
    refine ⟨?_, hy.2⟩
    rw [mem_ball, Real.dist_eq, abs_of_neg (sub_neg.mpr hy.2)]
    linarith [hy.1]
  refine ⟨δ, hδ, ?_⟩
  filter_upwards [ae_restrict_of_ae_restrict_of_subset
    (fun y hy => (hside y hy).1) h.ae_eq, ae_restrict_mem measurableSet_Ioo] with y hfy hy
  exact hfy.trans (hside y hy).2

lemma IsBinaryBVRepresentativeOn.exists_ae_const_right {f g : ℝ → ℝ} {a b t : ℝ}
    (h : IsBinaryBVRepresentativeOn f g a b) (ht : t ∈ Ioo a b) :
    ∃ δ > 0, f =ᵐ[volume.restrict (Ioo t (t + δ))] (fun _ => Function.rightLim g t) := by
  have hnear : ∀ᶠ y in 𝓝[>] t, y ∈ Ioo a b :=
    mem_nhdsWithin_of_mem_nhds (isOpen_Ioo.mem_nhds ht)
  have heq := eventually_eq_of_tendsto_binary
    (hnear.mono fun y hy => h.binary y hy) (h.boundedVariation.tendsto_rightLim t)
  obtain ⟨δ, hδ, hgood⟩ := Metric.mem_nhdsWithin_iff.mp (hnear.and heq)
  have hside (y : ℝ) (hy : y ∈ Ioo t (t + δ)) :
      y ∈ Ioo a b ∧ g y = Function.rightLim g t := by
    apply hgood
    refine ⟨?_, hy.1⟩
    rw [mem_ball, Real.dist_eq, abs_of_pos (sub_pos.mpr hy.1)]
    linarith [hy.2]
  refine ⟨δ, hδ, ?_⟩
  filter_upwards [ae_restrict_of_ae_restrict_of_subset
    (fun y hy => (hside y hy).1) h.ae_eq, ae_restrict_mem measurableSet_Ioo] with y hfy hy
  exact hfy.trans (hside y hy).2

/-- On a good binary BV slice the difference of one-sided averages is eventually
exactly its jump, not merely convergent to it. -/
lemma IsBinaryBVRepresentativeOn.averageDifference_eventually_eq_jump {α : Type*}
    {F : α × ℝ → ℝ} {x : α} {g : ℝ → ℝ} {a b t : ℝ}
    (h : IsBinaryBVRepresentativeOn (fun s => F (x, s)) g a b) (ht : t ∈ Ioo a b) :
    ∃ δ > 0, ∀ r : ℝ, 0 < r → r < δ →
      lineAverageDifference F r (x, t) = oneDimensionalJump g t := by
  obtain ⟨δl, hδl, hl⟩ := h.exists_ae_const_left ht
  obtain ⟨δr, hδr, hr⟩ := h.exists_ae_const_right ht
  refine ⟨min δl δr, lt_min hδl hδr, fun r hr0 hrδ => ?_⟩
  have hright : (∫ s in Ioo (0 : ℝ) 1, F (x, t + r * s)) = Function.rightLim g t := by
    apply integral_affine_eq_const_of_ae hr0.ne' hr
    intro s hs
    have hspos : 0 < r * s := mul_pos hr0 hs.1
    have hslt : r * s < r := by nlinarith [hs.2]
    exact ⟨by linarith, by linarith [hrδ.trans_le (min_le_right δl δr)]⟩
  have hleft : (∫ s in Ioo (0 : ℝ) 1, F (x, t - r * s)) = g t := by
    have he := integral_affine_eq_const_of_ae (neg_ne_zero.mpr hr0.ne') hl
      (show MapsTo (fun s => t + (-r) * s) (Ioo (0 : ℝ) 1) (Ioo (t - δl) t) from by
        intro s hs
        have hspos : 0 < r * s := mul_pos hr0 hs.1
        have hslt : r * s < r := by nlinarith [hs.2]
        constructor <;> nlinarith [hrδ.trans_le (min_le_left δl δr)])
    simpa only [neg_mul, sub_eq_add_neg] using he
  exact congrArg₂ Sub.sub hright hleft

lemma IsBinaryBVRepresentativeOn.jointJumpDensity_eq {α : Type*}
    {F : α × ℝ → ℝ} {x : α} {g : ℝ → ℝ} {a b t : ℝ}
    (h : IsBinaryBVRepresentativeOn (fun s => F (x, s)) g a b) (ht : t ∈ Ioo a b) :
    jointJumpDensity F (x, t) = oneDimensionalJump g t := by
  obtain ⟨δ, hδ, hd⟩ := h.averageDifference_eventually_eq_jump ht
  have hz : Tendsto (fun k : ℕ => ((k + 1 : ℝ)⁻¹)) atTop (𝓝 0) := by
    exact tendsto_inv_atTop_zero.comp
      (tendsto_atTop_add_const_right atTop 1 tendsto_natCast_atTop_atTop)
  have he : (fun k : ℕ => lineAverageDifference F ((k + 1 : ℝ)⁻¹) (x, t))
      =ᶠ[atTop] (fun _ => oneDimensionalJump g t) := by
    filter_upwards [hz.eventually (Iio_mem_nhds hδ)] with k hk
    exact hd _ (by positivity) hk
  exact (tendsto_const_nhds.congr' he.symm).limUnder_eq

lemma IsBinaryBVRepresentativeOn.rightLim_binary {f g : ℝ → ℝ} {a b t : ℝ}
    (h : IsBinaryBVRepresentativeOn f g a b) (ht : t ∈ Ioo a b) :
    Function.rightLim g t ∈ ({0, 1} : Set ℝ) := by
  have hnear : ∀ᶠ y in 𝓝[>] t, y ∈ Ioo a b :=
    mem_nhdsWithin_of_mem_nhds (isOpen_Ioo.mem_nhds ht)
  have hb := hnear.mono fun y hy => h.binary y hy
  have heq := eventually_eq_of_tendsto_binary hb (h.boundedVariation.tendsto_rightLim t)
  obtain ⟨y, hy, he⟩ := (hb.and heq).exists
  exact he ▸ hy

lemma IsBinaryBVRepresentativeOn.abs_jump_eq_one {f g : ℝ → ℝ} {a b t : ℝ}
    (h : IsBinaryBVRepresentativeOn f g a b) (ht : t ∈ Ioo a b)
    (hj : oneDimensionalJump g t ≠ 0) : |oneDimensionalJump g t| = 1 := by
  have hl := h.binary t ht
  have hr := h.rightLim_binary ht
  simp only [mem_insert_iff, mem_singleton_iff] at hl hr
  rcases hl with hl | hl <;> rcases hr with hr | hr <;>
    simp_all [oneDimensionalJump]

/-- The jointly Borel density agrees almost everywhere with the actual polar
sign on each interval carrying a canonical binary representative. -/
lemma IsBinaryBVRepresentativeOn.jointJumpDensity_eq_polar_ae {α : Type*}
    {F : α × ℝ → ℝ} {x : α} {g σ : ℝ → ℝ} {μ : Measure ℝ} {a b : ℝ}
    (h : IsBinaryBVRepresentativeOn (fun s => F (x, s)) g a b)
    (hμ : IsRealBVPolar (fun s => F (x, s)) μ σ) :
    (fun t => jointJumpDensity F (x, t)) =ᵐ[μ.restrict (Ioo a b)] σ := by
  filter_upwards [hμ.ae_mem_jumps_on_binary_region isOpen_Ioo h.ae_eq
    h.boundedVariation h.leftContinuous h.binary,
    ae_restrict_of_ae hμ.norm_ae, ae_restrict_mem measurableSet_Ioo] with t hj hσ ht
  have ha := hμ.oneDimensionalJump_eq_atom h.ae_eq h.leftContinuous ht
  have hab := congrArg abs ha
  rw [h.abs_jump_eq_one ht hj, abs_mul, abs_of_nonneg (measureReal_nonneg), hσ,
    mul_one] at hab
  rw [h.jointJumpDensity_eq ht, ha, ← hab, one_mul]

lemma jointJumpDensity_eq_polar_ae {α : Type*}
    {F : α × ℝ → ℝ} {x : α} {σ : ℝ → ℝ} {μ : Measure ℝ}
    (hμ : IsRealBVPolar (fun s => F (x, s)) μ σ)
    (hg : ∀ a b, ∃ g, IsBinaryBVRepresentativeOn (fun s => F (x, s)) g a b) :
    (fun t => jointJumpDensity F (x, t)) =ᵐ[μ] σ := by
  have he (k : ℕ) : ∀ᵐ t ∂μ, t ∈ Ioo (-(k : ℝ)) k →
      jointJumpDensity F (x, t) = σ t := by
    obtain ⟨g, hg⟩ := hg (-(k : ℝ)) k
    exact (ae_restrict_iff' measurableSet_Ioo).mp (hg.jointJumpDensity_eq_polar_ae hμ)
  filter_upwards [ae_all_iff.mpr he] with t ht
  obtain ⟨k, hk⟩ := exists_nat_gt |t|
  exact ht k ⟨by linarith [(abs_lt.mp hk).1], (abs_lt.mp hk).2⟩

/-- Almost-everywhere statements for a Borel predicate pass between the product
measure and its actual one-dimensional slice measures. -/
lemma ae_sliceProductMeasure_iff {α β : Type*} [MeasurableSpace α]
    (ν : Measure α) [MetricSpace β] [ProperSpace β] [SecondCountableTopology β]
    [MeasurableSpace β] [BorelSpace β] (c : β) (κ : α → Measure β)
    (hfin : ∀ᵐ x ∂ν, IsFiniteMeasureOnCompacts (κ x))
    (hκ : ∀ A : Set β, MeasurableSet A → AEMeasurable (fun x => κ x A) ν)
    {p : α × β → Prop} (hp : MeasurableSet {z | p z}) :
    (∀ᵐ z ∂sliceProductMeasure ν c κ hfin hκ, p z) ↔
      ∀ᵐ x ∂ν, ∀ᵐ t ∂κ x, p (x, t) := by
  rw [ae_iff]
  change sliceProductMeasure ν c κ hfin hκ {z | p z}ᶜ = 0 ↔ _
  rw [sliceProductMeasure_apply _ _ _ _ _ hp.compl,
    lintegral_eq_zero_iff' (aemeasurable_measure_prod_section c hfin hκ _ hp.compl)]
  change (∀ᵐ x ∂ν, κ x {t | ¬ p (x, t)} = 0) ↔ _
  exact Filter.eventually_congr (Eventually.of_forall fun _ => ae_iff.symm)

lemma ae_abs_jointJumpDensity_eq_one {α : Type*} [MeasurableSpace α]
    {ν : Measure α} {F : α × ℝ → ℝ} (hF : Measurable F)
    {κ : α → Measure ℝ} {σ : α → ℝ → ℝ}
    (hp : ∀ᵐ x ∂ν, IsRealBVPolar (fun t => F (x, t)) (κ x) (σ x))
    (hg : ∀ᵐ x ∂ν, ∀ a b, ∃ g,
      IsBinaryBVRepresentativeOn (fun t => F (x, t)) g a b)
    (hκ : ∀ A : Set ℝ, MeasurableSet A → AEMeasurable (fun x => κ x A) ν) :
    ∀ᵐ z ∂sliceProductMeasure ν 0 κ (hp.mono fun _ h => h.finiteOnCompacts) hκ,
      |jointJumpDensity F z| = 1 := by
  apply (ae_sliceProductMeasure_iff ν 0 κ _ hκ
    (measurableSet_eq_fun
      (by simpa only [Real.norm_eq_abs] using (measurable_jointJumpDensity hF).norm)
      measurable_const)).mpr
  filter_upwards [hp, hg] with x hx hgx
  filter_upwards [jointJumpDensity_eq_polar_ae hx hgx, hx.norm_ae] with t ht hn
  rw [ht, hn]

end LiquidDrop

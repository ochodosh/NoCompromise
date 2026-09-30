module

public import NoCompromise.Variation.FieldStability
public import NoCompromise.DeGiorgi.PolarDifferentiation
public import Mathlib.MeasureTheory.Integral.Layercake
public import Mathlib.MeasureTheory.Measure.WithDensity

@[expose] public section

/-!
# Weighted stability and finite partitions

Layer-cake integration lifts field stability on superlevel sets to a weighted
estimate for the actual perimeter measure. A Lipschitz weight contributes a
quadratic-in-time correction. After division by `|t|`, the eventual error bound
is `16 M` times the integral of the weight against perimeter, so summing a finite
partition introduces no factor depending on its size.

Compact containment and global bounds on the two fields ensure the required
inverse trajectories remain in the comparison neighborhood for all sufficiently
small positive and negative times. The original set needs only Lebesgue
measurability; no joint kernel or variation-measurability premise is assumed.
-/

noncomputable section
open MeasureTheory Set Filter
open scoped ENNReal NNReal Topology
namespace LiquidDrop

/-- Layer-cake lifting of superlevel-set estimates to a weighted integral. -/
lemma lintegral_weight_mul_le_of_superlevel_bound
    {A : Type*} [MeasurableSpace A] {μ ν : Measure A}
    {w : A → ℝ≥0∞} (hw : AEMeasurable w μ)
    {ζ : A → ℝ} (hζ : Measurable ζ) (hζ0 : ∀ x, 0 ≤ ζ x)
    {δ : ℝ} (hδ : 0 ≤ δ) {C : ℝ≥0∞} (hC : C ≠ ∞)
    (hb : ∀ r > 0, (∫⁻ x in {x | r < ζ x}, w x ∂μ) ≤
      C * ν {x | r < ζ x + δ}) :
    (∫⁻ x, ENNReal.ofReal (ζ x) * w x ∂μ) ≤
      C * ∫⁻ x, ENNReal.ofReal (ζ x + δ) ∂ν := by
  have he := lintegral_eq_lintegral_meas_lt (μ.withDensity w)
    (Eventually.of_forall hζ0) hζ.aemeasurable
  rw [lintegral_withDensity_eq_lintegral_mul₀ hw hζ.ennreal_ofReal.aemeasurable] at he
  have he' := lintegral_eq_lintegral_meas_lt ν
    (Eventually.of_forall (fun x => add_nonneg (hζ0 x) hδ)) (hζ.add_const δ).aemeasurable
  calc
    _ = ∫⁻ r in Ioi (0 : ℝ), (μ.withDensity w) {x | r < ζ x} := by
      simpa only [Pi.mul_apply, mul_comm] using he
    _ ≤ ∫⁻ r in Ioi (0 : ℝ), C * ν {x | r < ζ x + δ} := by
      apply lintegral_mono_ae
      filter_upwards [ae_restrict_mem measurableSet_Ioi] with r hr
      rw [withDensity_apply _ (measurableSet_lt measurable_const hζ)]
      exact hb r hr
    _ = C * ∫⁻ r in Ioi (0 : ℝ), ν {x | r < ζ x + δ} :=
      lintegral_const_mul' _ _ hC
    _ = _ := congrArg (C * ·) he'.symm

/-- Weighted stability for the actual perimeter measure. The radius-independent
error is the amount by which the weight changes along inverse trajectories. -/
theorem IsAmbientOutwardPerimeterPolar.weighted_field_stability
    {E : Set AmbientSpace} {μ : Measure AmbientSpace} {ν : AmbientSpace → AmbientSpace}
    (hpolar : IsAmbientOutwardPerimeterPolar E μ ν) (hmE : NullMeasurableSet E volume)
    {X Y : AmbientSpace → AmbientSpace} {L : ℝ≥0}
    (hX : LipschitzWith L X) (hY : LipschitzWith L Y)
    (hXC : ContDiff ℝ 1 X) (hYC : ContDiff ℝ 1 Y) {t : ℝ}
    (ht : |t| * L < 1 / 2) {K V : Set AmbientSpace}
    (hK : MeasurableSet K) (hV : IsOpen V) (hcV : IsCompact (closure V))
    (hpath : ∀ s ∈ Icc (0 : ℝ) 1, MapsTo (interpolatedInverse X Y t s) K V)
    {M : ℝ} (hM : 0 ≤ M) (hbound : ∀ x ∈ V, ‖X x - Y x‖ ≤ M)
    {ζ : AmbientSpace → ℝ} (hζ : Continuous ζ) (hζ0 : ∀ x, 0 ≤ ζ x)
    {δ : ℝ} (hδ : 0 ≤ δ)
    (hweight : ∀ s ∈ Icc (0 : ℝ) 1, ∀ z ∈ K,
      ζ z ≤ ζ (interpolatedInverse X Y t s z) + δ) :
    (∫⁻ z in K, ENNReal.ofReal (ζ z) *
      ‖E.indicator (fun _ => (1 : ℝ)) (interpolatedInverse X Y t 1 z) -
        E.indicator (fun _ => (1 : ℝ)) (interpolatedInverse X Y t 0 z)‖ₑ) ≤
      ENNReal.ofReal (16 * |t| * M) *
        ((∫⁻ x in V, ENNReal.ofReal (ζ x) ∂μ) + ENNReal.ofReal δ * μ V) := by
  let := hpolar.finiteOnCompacts
  let u : AmbientSpace → ℝ := E.indicator (fun _ => (1 : ℝ))
  have hiV : IntegrableOn u V :=
    ((locallyIntegrable_indicator_one hmE).integrableOn_isCompact hcV).mono_set subset_closure
  have hμV : μ V < ∞ := (measure_mono (s := V) subset_closure).trans_lt hcV.measure_lt_top
  have ht1 : |t| * L < 1 := lt_trans ht (by norm_num)
  have hiq (s : ℝ) (hs : s ∈ Icc 0 1) :=
    integrableOn_comp_interpolatedInverse hX hY ht1 hs hK (hpath s hs) hiV
  let w : AmbientSpace → ℝ≥0∞ := fun z =>
    ‖u (interpolatedInverse X Y t 1 z) - u (interpolatedInverse X Y t 0 z)‖ₑ
  have hw : AEMeasurable w (volume.restrict K) :=
    ((hiq 1 (by simp)).sub (hiq 0 (by simp))).aestronglyMeasurable.enorm
  have hl := lintegral_weight_mul_le_of_superlevel_bound hw hζ.measurable hζ0 hδ
    (C := ENNReal.ofReal (16 * |t| * M)) ENNReal.ofReal_ne_top
    (ν := μ.restrict V) ?_
  · refine hl.trans_eq ?_
    congr 1
    simp_rw [ENNReal.ofReal_add (hζ0 _) hδ]
    rw [lintegral_add_left hζ.measurable.ennreal_ofReal,
      lintegral_const, Measure.restrict_apply_univ]
  · intro r hr
    let W : Set AmbientSpace := V ∩ {x | r < ζ x + δ}
    have hW : IsOpen W := hV.inter (isOpen_lt continuous_const (hζ.add continuous_const))
    have hWV : W ⊆ V := inter_subset_left
    have huW : IsBVOn u W := by
      refine ⟨hiV.mono_set hWV, ?_⟩
      change perimeterIn E W < ∞
      rw [← hpolar.open_eq W hW]
      exact (measure_mono hWV).trans_lt hμV
    have hpathW : ∀ s ∈ Icc (0 : ℝ) 1,
        MapsTo (interpolatedInverse X Y t s) (K ∩ {x | r < ζ x}) W := by
      intro s hs z hz
      refine ⟨hpath s hs hz.1, ?_⟩
      exact hz.2.trans_le (hweight s hs z hz.1)
    have hb := lintegral_field_stability hX hY hXC hYC ht
      (hK.inter (measurableSet_lt measurable_const hζ.measurable)) hW huW hpathW hM
      (fun x hx => hbound x hx.1)
    change (∫⁻ z in K ∩ {x | r < ζ x}, w z) ≤
      ENNReal.ofReal (16 * |t| * M) * perimeterIn E W at hb
    rw [← hpolar.open_eq W hW] at hb
    rw [Measure.restrict_restrict (measurableSet_lt measurable_const hζ.measurable),
      Measure.restrict_apply (measurableSet_lt measurable_const (hζ.measurable.add_const δ))]
    simpa only [W, inter_comm] using hb

/-- Bounded fields give a uniform displacement bound along every interpolated inverse. -/
lemma norm_interpolatedInverse_sub_self_le
    {X Y : AmbientSpace → AmbientSpace} {L : ℝ≥0}
    (hX : LipschitzWith L X) (hY : LipschitzWith L Y) {t s : ℝ}
    (ht : |t| * L < 1) (hs : s ∈ Icc 0 1) (z : AmbientSpace)
    {B : ℝ} (hBX : ∀ x, ‖X x‖ ≤ B) (hBY : ∀ x, ‖Y x‖ ≤ B) :
    ‖interpolatedInverse X Y t s z - z‖ ≤ |t| * B := by
  let q := interpolatedInverse X Y t s z
  have he : q + t • interpolatedField X Y s q = z :=
    Function.rightInverse_invFun (straightPerturbation_bijective
      (lipschitzWith_interpolatedField_Icc hX hY hs) ht).2 z
  have hn : ‖interpolatedField X Y s q‖ ≤ B := by
    calc
      _ ≤ ‖(1 - s) • Y q‖ + ‖s • X q‖ := norm_add_le _ _
      _ = (1 - s) * ‖Y q‖ + s * ‖X q‖ := by
        simp only [norm_smul, Real.norm_eq_abs, abs_of_nonneg hs.1,
          abs_of_nonneg (sub_nonneg.mpr hs.2)]
      _ ≤ (1 - s) * B + s * B := add_le_add
        (mul_le_mul_of_nonneg_left (hBY q) (sub_nonneg.mpr hs.2))
        (mul_le_mul_of_nonneg_left (hBX q) hs.1)
      _ = B := by ring
  have heq : q - z = -(t • interpolatedField X Y s q) := by
    calc
      _ = q - (q + t • interpolatedField X Y s q) := congrArg (q - ·) he.symm
      _ = _ := by abel
  change ‖q - z‖ ≤ _
  rw [heq, norm_neg, norm_smul, Real.norm_eq_abs]
  exact mul_le_mul_of_nonneg_left hn (abs_nonneg t)

/-- A Lipschitz weight changes by at most its Lipschitz constant times displacement. -/
lemma weight_interpolatedInverse_le
    {X Y : AmbientSpace → AmbientSpace} {L : ℝ≥0}
    (hX : LipschitzWith L X) (hY : LipschitzWith L Y) {t s : ℝ}
    (ht : |t| * L < 1) (hs : s ∈ Icc 0 1) (z : AmbientSpace)
    {B : ℝ} (hBX : ∀ x, ‖X x‖ ≤ B) (hBY : ∀ x, ‖Y x‖ ≤ B)
    {ζ : AmbientSpace → ℝ} {Q : ℝ≥0} (hζ : LipschitzWith Q ζ) :
    ζ z ≤ ζ (interpolatedInverse X Y t s z) + Q * |t| * B := by
  have hn := norm_interpolatedInverse_sub_self_le hX hY ht hs z hBX hBY
  have hl := hζ.norm_sub_le z (interpolatedInverse X Y t s z)
  rw [Real.norm_eq_abs, norm_sub_rev z] at hl
  have h := (le_abs_self (ζ z - ζ (interpolatedInverse X Y t s z))).trans hl
  have h' := mul_le_mul_of_nonneg_left hn Q.coe_nonneg
  nlinarith

/-- In the weighted estimate a Lipschitz weight has a quadratic-in-time correction. -/
theorem IsAmbientOutwardPerimeterPolar.weighted_field_stability_lipschitz
    {E : Set AmbientSpace} {μ : Measure AmbientSpace} {ν : AmbientSpace → AmbientSpace}
    (hpolar : IsAmbientOutwardPerimeterPolar E μ ν) (hmE : NullMeasurableSet E volume)
    {X Y : AmbientSpace → AmbientSpace} {L : ℝ≥0}
    (hX : LipschitzWith L X) (hY : LipschitzWith L Y)
    (hXC : ContDiff ℝ 1 X) (hYC : ContDiff ℝ 1 Y) {t : ℝ}
    (ht : |t| * L < 1 / 2) {K V : Set AmbientSpace}
    (hK : MeasurableSet K) (hV : IsOpen V) (hcV : IsCompact (closure V))
    (hpath : ∀ s ∈ Icc (0 : ℝ) 1, MapsTo (interpolatedInverse X Y t s) K V)
    {M : ℝ} (hM : 0 ≤ M) (hbound : ∀ x ∈ V, ‖X x - Y x‖ ≤ M)
    {ζ : AmbientSpace → ℝ} {Q : ℝ≥0} (hζ : LipschitzWith Q ζ) (hζ0 : ∀ x, 0 ≤ ζ x)
    {B : ℝ} (hB : 0 ≤ B) (hBX : ∀ x, ‖X x‖ ≤ B) (hBY : ∀ x, ‖Y x‖ ≤ B) :
    (∫⁻ z in K, ENNReal.ofReal (ζ z) *
      ‖E.indicator (fun _ => (1 : ℝ)) (interpolatedInverse X Y t 1 z) -
        E.indicator (fun _ => (1 : ℝ)) (interpolatedInverse X Y t 0 z)‖ₑ) ≤
      ENNReal.ofReal (16 * |t| * M) *
        ((∫⁻ x in V, ENNReal.ofReal (ζ x) ∂μ) + ENNReal.ofReal (Q * |t| * B) * μ V) :=
  hpolar.weighted_field_stability hmE hX hY hXC hYC ht hK hV hcV hpath hM hbound
    hζ.continuous hζ0 (by positivity) (fun s hs z _ =>
      weight_interpolatedInverse_le hX hY (lt_trans ht (by norm_num)) hs z hBX hBY hζ)

/-- Compact containment guarantees the required inverse-image condition for all
sufficiently small times, uniformly over the whole interpolation interval. -/
lemma eventually_interpolatedInverse_mapsTo
    {X Y : AmbientSpace → AmbientSpace} {L : ℝ≥0}
    (hX : LipschitzWith L X) (hY : LipschitzWith L Y)
    {K V : Set AmbientSpace} (hK : IsCompact K) (hV : IsOpen V) (hKV : K ⊆ V)
    {B : ℝ} (hBX : ∀ x, ‖X x‖ ≤ B) (hBY : ∀ x, ‖Y x‖ ≤ B) :
    ∀ᶠ t : ℝ in 𝓝 0, |t| * L < 1 / 2 ∧
      ∀ s ∈ Icc (0 : ℝ) 1, MapsTo (interpolatedInverse X Y t s) K V := by
  obtain ⟨δ, hδ, hδV⟩ := hK.exists_cthickening_subset_open hV hKV
  have hsmall : ∀ᶠ t : ℝ in 𝓝 0, |t| * L < 1 / 2 := by
    have hh : Tendsto (fun t : ℝ => |t| * L) (𝓝 0) (𝓝 0) := by
      simpa using (continuous_abs.continuousAt.tendsto (x := (0 : ℝ))).mul_const (L : ℝ)
    exact hh.eventually (gt_mem_nhds (by norm_num))
  have hdist : ∀ᶠ t : ℝ in 𝓝 0, |t| * B < δ := by
    have hh : Tendsto (fun t : ℝ => |t| * B) (𝓝 0) (𝓝 0) := by
      simpa using (continuous_abs.continuousAt.tendsto (x := (0 : ℝ))).mul_const B
    exact hh.eventually (gt_mem_nhds hδ)
  filter_upwards [hsmall, hdist] with t ht htd
  refine ⟨ht, fun s hs z hz => hδV ?_⟩
  apply Metric.mem_cthickening_of_dist_le _ z δ K hz
  rw [dist_eq_norm]
  exact (norm_interpolatedInverse_sub_self_le hX hY (lt_trans ht (by norm_num))
    hs z hBX hBY).trans htd.le

/-- Real integral form of the weighted bound, with a quadratic-in-time remainder. -/
theorem IsAmbientOutwardPerimeterPolar.integral_weighted_field_stability_lipschitz
    {E : Set AmbientSpace} {μ : Measure AmbientSpace} {ν : AmbientSpace → AmbientSpace}
    (hpolar : IsAmbientOutwardPerimeterPolar E μ ν) (hmE : NullMeasurableSet E volume)
    {X Y : AmbientSpace → AmbientSpace} {L : ℝ≥0}
    (hX : LipschitzWith L X) (hY : LipschitzWith L Y)
    (hXC : ContDiff ℝ 1 X) (hYC : ContDiff ℝ 1 Y) {t : ℝ}
    (ht : |t| * L < 1 / 2) {K V : Set AmbientSpace}
    (hK : MeasurableSet K) (hV : IsOpen V) (hcV : IsCompact (closure V))
    (hpath : ∀ s ∈ Icc (0 : ℝ) 1, MapsTo (interpolatedInverse X Y t s) K V)
    {M : ℝ} (hM : 0 ≤ M) (hbound : ∀ x ∈ V, ‖X x - Y x‖ ≤ M)
    {ζ : AmbientSpace → ℝ} {Q : ℝ≥0} (hζ : LipschitzWith Q ζ) (hζ0 : ∀ x, 0 ≤ ζ x)
    {B : ℝ} (hB : 0 ≤ B) (hBX : ∀ x, ‖X x‖ ≤ B) (hBY : ∀ x, ‖Y x‖ ≤ B) :
    (∫ z in K, ζ z * |E.indicator (fun _ => (1 : ℝ)) (interpolatedInverse X Y t 1 z) -
        E.indicator (fun _ => (1 : ℝ)) (interpolatedInverse X Y t 0 z)|) ≤
      (16 * |t| * M) * ((∫ x in V, ζ x ∂μ) + (Q * |t| * B) * μ.real V) := by
  let := hpolar.finiteOnCompacts
  have hiζ : IntegrableOn ζ V μ :=
    (hζ.continuous.continuousOn.integrableOn_compact hcV).mono_set subset_closure
  have hμV : μ V ≠ ∞ := ((measure_mono (s := V) subset_closure).trans_lt hcV.measure_lt_top).ne
  let u : AmbientSpace → ℝ := E.indicator (fun _ => (1 : ℝ))
  have hiV : IntegrableOn u V :=
    ((locallyIntegrable_indicator_one hmE).integrableOn_isCompact hcV).mono_set subset_closure
  have hiq (s : ℝ) (hs : s ∈ Icc 0 1) := integrableOn_comp_interpolatedInverse
    hX hY (lt_trans ht (by norm_num)) hs hK (hpath s hs) hiV
  let d : AmbientSpace → ℝ := fun z => u (interpolatedInverse X Y t 1 z) -
    u (interpolatedInverse X Y t 0 z)
  have hd : AEStronglyMeasurable d (volume.restrict K) :=
    ((hiq 1 (by simp)).sub (hiq 0 (by simp))).aestronglyMeasurable
  have heq : (∫ z in K, ζ z * |d z|) =
      (∫⁻ z in K, ENNReal.ofReal (ζ z) * ‖d z‖ₑ).toReal := by
    rw [integral_eq_lintegral_of_nonneg_ae
      (Eventually.of_forall (fun z => mul_nonneg (hζ0 z) (abs_nonneg _)))
      (hζ.continuous.aestronglyMeasurable.mul (continuous_abs.comp_aestronglyMeasurable hd))]
    congr 1
    apply lintegral_congr
    intro z
    rw [ENNReal.ofReal_mul (hζ0 z), ← Real.norm_eq_abs, ofReal_norm]
  have h := hpolar.weighted_field_stability_lipschitz hmE hX hY hXC hYC ht hK hV hcV
    hpath hM hbound hζ hζ0 hB hBX hBY
  rw [← ofReal_integral_eq_lintegral_ofReal hiζ (Eventually.of_forall hζ0)] at h
  have hreal := ENNReal.toReal_mono (by finiteness) h
  rw [heq]
  simpa only [ENNReal.toReal_mul, ENNReal.toReal_add ENNReal.ofReal_ne_top
    (ENNReal.mul_ne_top ENNReal.ofReal_ne_top hμV),
    ENNReal.toReal_ofReal (by positivity : 0 ≤ 16 * |t| * M),
    ENNReal.toReal_ofReal (by positivity : 0 ≤ (Q : ℝ) * |t| * B),
    ENNReal.toReal_ofReal (integral_nonneg hζ0), Measure.real, d, u] using hreal

/-- The normalized weighted replacement error has an eventual bound with no
factor depending on the number of partition pieces. -/
theorem IsAmbientOutwardPerimeterPolar.eventually_normalized_weighted_field_stability
    {E : Set AmbientSpace} {μ : Measure AmbientSpace} {ν : AmbientSpace → AmbientSpace}
    (hpolar : IsAmbientOutwardPerimeterPolar E μ ν) (hmE : NullMeasurableSet E volume)
    {X Y : AmbientSpace → AmbientSpace} {L : ℝ≥0}
    (hX : LipschitzWith L X) (hY : LipschitzWith L Y)
    (hXC : ContDiff ℝ 1 X) (hYC : ContDiff ℝ 1 Y)
    {K V : Set AmbientSpace} (hK : IsCompact K)
    (hV : IsOpen V) (hcV : IsCompact (closure V)) (hKV : K ⊆ V)
    {M : ℝ} (hM : 0 ≤ M) (hbound : ∀ x ∈ V, ‖X x - Y x‖ ≤ M)
    {ζ : AmbientSpace → ℝ} {Q : ℝ≥0} (hζ : LipschitzWith Q ζ) (hζ0 : ∀ x, 0 ≤ ζ x)
    {B : ℝ} (hB : 0 ≤ B) (hBX : ∀ x, ‖X x‖ ≤ B) (hBY : ∀ x, ‖Y x‖ ≤ B)
    {ε : ℝ} (hε : 0 < ε) :
    ∀ᶠ t : ℝ in 𝓝[≠] 0,
      |t|⁻¹ * (∫ z in K, ζ z *
        |E.indicator (fun _ => (1 : ℝ)) (interpolatedInverse X Y t 1 z) -
          E.indicator (fun _ => (1 : ℝ)) (interpolatedInverse X Y t 0 z)|) ≤
        16 * M * (∫ x in V, ζ x ∂μ) + ε := by
  have hg : ∀ᶠ t : ℝ in 𝓝[≠] 0, |t| * L < 1 / 2 ∧
      ∀ s ∈ Icc (0 : ℝ) 1, MapsTo (interpolatedInverse X Y t s) K V :=
    (eventually_interpolatedInverse_mapsTo hX hY hK hV hKV hBX hBY).filter_mono
      nhdsWithin_le_nhds
  have hlim : Tendsto (fun t : ℝ => 16 * M *
      ((∫ x in V, ζ x ∂μ) + (Q * |t| * B) * μ.real V))
      (𝓝[≠] 0) (𝓝 (16 * M * ∫ x in V, ζ x ∂μ)) := by
    have hc : Continuous (fun t : ℝ => 16 * M *
      ((∫ x in V, ζ x ∂μ) + (Q * |t| * B) * μ.real V)) := by fun_prop
    simpa using (hc.tendsto 0).mono_left
      (nhdsWithin_le_nhds (s := ({0} : Set ℝ)ᶜ))
  have he := hlim.eventually (gt_mem_nhds (lt_add_of_pos_right _ hε))
  filter_upwards [hg, he, self_mem_nhdsWithin] with t ht hte ht0
  have htn : t ≠ 0 := ht0
  have hb := hpolar.integral_weighted_field_stability_lipschitz hmE hX hY hXC hYC
    ht.1 hK.measurableSet hV hcV ht.2 hM hbound hζ hζ0 hB hBX hBY
  have hmul := mul_le_mul_of_nonneg_left hb (inv_nonneg.mpr (abs_nonneg t))
  have heq : |t|⁻¹ * ((16 * |t| * M) *
      ((∫ x in V, ζ x ∂μ) + (Q * |t| * B) * μ.real V)) =
      16 * M * ((∫ x in V, ζ x ∂μ) + (Q * |t| * B) * μ.real V) := by
    field_simp [abs_ne_zero.mpr htn]
  exact (hmul.trans_eq heq).trans hte.le

end LiquidDrop

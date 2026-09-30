module

public import NoCompromise.Sobolev.H1Approximation
public import NoCompromise.Sobolev.H1Algebra
public import NoCompromise.Sobolev.H1Reflection
public import NoCompromise.Sobolev.H1Chain
public import NoCompromise.Sobolev.WeakCompactness

@[expose] public section

/-!
# H¹ difference quotients

Translation and difference-quotient estimates use the actual weak gradient.
All local estimates state the needed domain clearance explicitly.
-/

noncomputable section

open MeasureTheory Filter Metric Set InnerProductSpace
open scoped NNReal ENNReal Topology Gradient Convolution

namespace LiquidDrop

set_option maxSynthPendingDepth 8

/-- Forward difference quotient in one coordinate direction. The value at `h = 0`
is set to zero by the ordinary field convention. -/
def coordinateDifferenceQuotient {n : ℕ} {F : Type*} [AddCommGroup F] [Module ℝ F]
    (i : Fin n) (h : ℝ) (f : EuclideanSpace ℝ (Fin n) → F)
    (x : EuclideanSpace ℝ (Fin n)) : F :=
  h⁻¹ • (f (x + h • EuclideanSpace.single i 1) - f x)

/-- Jensen upgrades the segment gradient bound to the square of the norm. -/
lemma norm_sub_sq_le_integral_gradient_segment {n : ℕ}
    {U : Set (EuclideanSpace ℝ (Fin n))} (hU : IsOpen U)
    {f : EuclideanSpace ℝ (Fin n) → ℝ} (hf : ContDiffOn ℝ 1 f U)
    (x h : EuclideanSpace ℝ (Fin n))
    (hseg : ∀ t ∈ Icc (0 : ℝ) 1, x + t • h ∈ U) :
    ‖f (x + h) - f x‖ ^ 2 ≤
      ‖h‖ ^ 2 * ∫ t in Icc (0 : ℝ) 1, ‖gradient f (x + t • h)‖ ^ 2 := by
  let g : ℝ → ℝ := fun t => ‖gradient f (x + t • h)‖
  have hcg : ContinuousOn g (Icc (0 : ℝ) 1) :=
    (continuousOn_gradient_of_contDiffOn hU hf).norm.comp
      (continuous_const.add (continuous_id.smul continuous_const)).continuousOn hseg
  have hig : IntegrableOn g (Icc (0 : ℝ) 1) := hcg.integrableOn_compact isCompact_Icc
  have hig2 : IntegrableOn (fun t => g t ^ 2) (Icc (0 : ℝ) 1) :=
    (hcg.pow 2).integrableOn_compact isCompact_Icc
  have hgn (t : ℝ) : 0 ≤ g t := norm_nonneg _
  have hline := enorm_sub_le_lintegral_gradient_segment hU hf x h hseg
  simp only [← ofReal_norm, ← ENNReal.ofReal_mul (norm_nonneg h)] at hline
  rw [← ofReal_integral_eq_lintegral_ofReal (hig.const_mul ‖h‖)
    (Eventually.of_forall fun t => mul_nonneg (norm_nonneg h) (hgn t)),
    integral_const_mul] at hline
  have hreal : ‖f (x + h) - f x‖ ≤ ‖h‖ * ∫ t in Icc (0 : ℝ) 1, g t :=
    (ENNReal.ofReal_le_ofReal_iff (mul_nonneg (norm_nonneg h)
      (integral_nonneg hgn))).mp hline
  have hj := norm_integral_smul_sq_le_of_probability_kernel
    (μ := volume.restrict (Icc (0 : ℝ) 1)) (k := fun _ => (1 : ℝ)) (f := g)
    measurable_const (integrableOn_const (by simp)) (fun _ => by norm_num)
    (by simp) (by simpa only [one_smul, IntegrableOn] using hig)
    (by simpa only [one_mul, Real.norm_of_nonneg (hgn _), IntegrableOn] using hig2)
  simp only [one_smul, one_mul, Real.norm_of_nonneg (hgn _),
    Real.norm_of_nonneg (integral_nonneg hgn)] at hj
  calc
    _ ≤ (‖h‖ * ∫ t in Icc (0 : ℝ) 1, g t) ^ 2 :=
      (sq_le_sq₀ (norm_nonneg _)
        (mul_nonneg (norm_nonneg h) (integral_nonneg hgn))).mpr hreal
    _ = ‖h‖ ^ 2 * (∫ t in Icc (0 : ℝ) 1, g t) ^ 2 := mul_pow _ _ _
    _ ≤ _ := mul_le_mul_of_nonneg_left hj (sq_nonneg _)

/-- Smooth squared translation estimate on any measurable set whose displacement
segments stay in the open differentiability domain. -/
theorem lintegral_translation_sub_sq_le_of_contDiffOn {n : ℕ}
    {U Q : Set (EuclideanSpace ℝ (Fin n))} (hU : IsOpen U) (hQ : MeasurableSet Q)
    {f : EuclideanSpace ℝ (Fin n) → ℝ} (hf : ContDiffOn ℝ 1 f U)
    (h : EuclideanSpace ℝ (Fin n))
    (hseg : ∀ x ∈ Q, ∀ t ∈ Icc (0 : ℝ) 1, x + t • h ∈ U) :
    (∫⁻ x in Q, ENNReal.ofReal (‖f (x + h) - f x‖ ^ 2)) ≤
      ENNReal.ofReal (‖h‖ ^ 2) * ∫⁻ x in U, ENNReal.ofReal (‖gradient f x‖ ^ 2) := by
  classical
  let G := U.indicator (fun x => ENNReal.ofReal (‖gradient f x‖ ^ 2))
  have hG : Measurable G :=
    (ENNReal.continuous_ofReal.comp_continuousOn
      ((continuousOn_gradient_of_contDiffOn hU hf).norm.pow 2)).measurable_piecewise
      continuousOn_const hU.measurableSet
  have hm : Measurable (fun p : EuclideanSpace ℝ (Fin n) × ℝ =>
      ENNReal.ofReal (‖h‖ ^ 2) * G (p.1 + p.2 • h)) :=
    measurable_const.mul (hG.comp ((continuous_fst.add
      (continuous_snd.smul continuous_const)).measurable))
  calc
    _ ≤ ∫⁻ x in Q, ∫⁻ t in Icc (0 : ℝ) 1,
        ENNReal.ofReal (‖h‖ ^ 2) * G (x + t • h) := by
      apply lintegral_mono_ae
      filter_upwards [ae_restrict_mem hQ] with x hx
      have hi : IntegrableOn (fun t => ‖gradient f (x + t • h)‖ ^ 2) (Icc (0 : ℝ) 1) :=
        (((continuousOn_gradient_of_contDiffOn hU hf).norm.pow 2).comp
          (continuous_const.add (continuous_id.smul continuous_const)).continuousOn
          (hseg x hx)).integrableOn_compact isCompact_Icc
      have hb := ENNReal.ofReal_le_ofReal
        (norm_sub_sq_le_integral_gradient_segment hU hf x h (hseg x hx))
      rw [ENNReal.ofReal_mul (sq_nonneg _), ofReal_integral_eq_lintegral_ofReal hi
        (Eventually.of_forall fun _ => sq_nonneg _),
        ← lintegral_const_mul' _ _ ENNReal.ofReal_ne_top] at hb
      apply hb.trans_eq
      apply lintegral_congr_ae
      filter_upwards [ae_restrict_mem measurableSet_Icc] with t ht
      simp only [G, indicator_of_mem (hseg x hx t ht)]
    _ = ∫⁻ t in Icc (0 : ℝ) 1, ∫⁻ x in Q,
        ENNReal.ofReal (‖h‖ ^ 2) * G (x + t • h) :=
      lintegral_lintegral_swap hm.aemeasurable
    _ ≤ ∫⁻ _t in Icc (0 : ℝ) 1, ENNReal.ofReal (‖h‖ ^ 2) * ∫⁻ y, G y := by
      apply lintegral_mono
      intro t
      calc
        _ ≤ ∫⁻ x, ENNReal.ofReal (‖h‖ ^ 2) * G (x + t • h) :=
          lintegral_mono' Measure.restrict_le_self le_rfl
        _ = _ := by
          rw [lintegral_const_mul' _ _ ENNReal.ofReal_ne_top, lintegral_add_right_eq_self]
    _ = _ := by
      rw [setLIntegral_const]
      simp only [Real.volume_Icc, sub_zero, ENNReal.ofReal_one, mul_one]
      rw [lintegral_indicator hU.measurableSet]

/-- Translation into a measurable region preserves Lᵖ membership and does not
increase the norm when the integration region is restricted. -/
lemma memLp_translate_restrict_and_eLpNorm_le {n : ℕ} {F : Type*}
    [NormedAddCommGroup F] {U Q : Set (EuclideanSpace ℝ (Fin n))}
    (hU : MeasurableSet U) {p : ℝ≥0∞} {f : EuclideanSpace ℝ (Fin n) → F}
    (hf : MemLp f p (volume.restrict U)) (h : EuclideanSpace ℝ (Fin n))
    (hmap : ∀ x ∈ Q, x + h ∈ U) :
    MemLp (fun x => f (x + h)) p (volume.restrict Q) ∧
      eLpNorm (fun x => f (x + h)) p (volume.restrict Q) ≤
        eLpNorm f p (volume.restrict U) := by
  have hp := (measurePreserving_add_right volume h).restrict_preimage hU
  have hm := hf.comp_measurePreserving hp
  refine ⟨hm.mono_measure (Measure.restrict_mono hmap le_rfl), ?_⟩
  exact (eLpNorm_mono_measure _ (Measure.restrict_mono hmap le_rfl)).trans_eq
    (eLpNorm_comp_measurePreserving hf.aestronglyMeasurable hp)

/-- Ordinary L² translation bound for a smooth function with square-integrable
function and gradient, on nested regions containing the displacement segments. -/
theorem lpNorm_translation_sub_le_of_contDiffOn {n : ℕ}
    {U Q : Set (EuclideanSpace ℝ (Fin n))} (hU : IsOpen U) (hQ : MeasurableSet Q)
    {f : EuclideanSpace ℝ (Fin n) → ℝ} (hf : ContDiffOn ℝ 1 f U)
    (hmf : MemLp f 2 (volume.restrict U))
    (hmG : MemLp (gradient f) 2 (volume.restrict U))
    (h : EuclideanSpace ℝ (Fin n))
    (hseg : ∀ x ∈ Q, ∀ t ∈ Icc (0 : ℝ) 1, x + t • h ∈ U) :
    lpNorm (fun x => f (x + h) - f x) 2 (volume.restrict Q) ≤
      ‖h‖ * lpNorm (gradient f) 2 (volume.restrict U) := by
  have hQU : Q ⊆ U := fun x hx => by simpa using hseg x hx 0 (by simp)
  have hmap : ∀ x ∈ Q, x + h ∈ U := fun x hx => by simpa using hseg x hx 1 (by simp)
  have hmd : MemLp (fun x => f (x + h) - f x) 2 (volume.restrict Q) :=
    (memLp_translate_restrict_and_eLpNorm_le hU.measurableSet hmf h hmap).1.sub
      (hmf.mono_measure (Measure.restrict_mono hQU le_rfl))
  have hiD := (memLp_two_iff_integrable_sq_norm hmd.aestronglyMeasurable).mp hmd
  have hiG := (memLp_two_iff_integrable_sq_norm hmG.aestronglyMeasurable).mp hmG
  have hb := lintegral_translation_sub_sq_le_of_contDiffOn hU hQ hf h hseg
  rw [← ofReal_integral_eq_lintegral_ofReal hiD
      (Eventually.of_forall fun _ => sq_nonneg _),
    ← ofReal_integral_eq_lintegral_ofReal hiG
      (Eventually.of_forall fun _ => sq_nonneg _),
    ← ENNReal.ofReal_mul (sq_nonneg _)] at hb
  have hb' := (ENNReal.ofReal_le_ofReal_iff (mul_nonneg (sq_nonneg _)
    (integral_nonneg fun _ => sq_nonneg _))).mp hb
  rw [← lpNorm_two_sq_eq_integral_norm_sq hmd,
    ← lpNorm_two_sq_eq_integral_norm_sq hmG] at hb'
  have hn : 0 ≤ ‖h‖ * lpNorm (gradient f) 2 (volume.restrict U) :=
    mul_nonneg (norm_nonneg _) lpNorm_nonneg
  nlinarith [lpNorm_nonneg (f := fun x => f (x + h) - f x) (p := 2)
    (μ := volume.restrict Q)]

/-- Sharp local H¹ translation estimate. A fixed positive neighborhood of the
intermediate region lies in the original domain, and every displacement segment
from the integration region stays in that intermediate region. -/
theorem HasH1GradientOn.lpNorm_translation_sub_le {n : ℕ}
    {U V Q : Set (EuclideanSpace ℝ (Fin n))}
    (hU : IsOpen U) (hV : IsOpen V) (hQ : MeasurableSet Q)
    {f : EuclideanSpace ℝ (Fin n) → ℝ}
    {G : EuclideanSpace ℝ (Fin n) → EuclideanSpace ℝ (Fin n)}
    (hf : HasH1GradientOn f G U) {δ : ℝ} (hδ : 0 < δ)
    (hclear : ∀ x ∈ V, closedBall x δ ⊆ U)
    (h : EuclideanSpace ℝ (Fin n))
    (hseg : ∀ x ∈ Q, ∀ t ∈ Icc (0 : ℝ) 1, x + t • h ∈ V) :
    lpNorm (fun x => f (x + h) - f x) 2 (volume.restrict Q) ≤
      ‖h‖ * lpNorm G 2 (volume.restrict U) := by
  have hVU : V ⊆ U := fun x hx => hclear x hx (mem_closedBall_self hδ.le)
  have hQV : Q ⊆ V := fun x hx => by simpa using hseg x hx 0 (by simp)
  have hmap : ∀ x ∈ Q, x + h ∈ V := fun x hx => by simpa using hseg x hx 1 (by simp)
  let φ (j : ℕ) : ContDiffBump (0 : EuclideanSpace ℝ (Fin n)) :=
    ⟨(δ / ((j : ℝ) + 1)) / 2, δ / ((j : ℝ) + 1), by positivity,
      half_lt_self (by positivity)⟩
  have hφδ (j) : (φ j).rOut ≤ δ :=
    div_le_self hδ.le (by linarith [Nat.cast_nonneg (α := ℝ) j])
  have hφlim : Tendsto (fun j => (φ j).rOut) atTop (𝓝 0) := by
    simpa only [mul_one_div, mul_zero] using
      (tendsto_one_div_add_atTop_nhds_zero_nat (𝕜 := ℝ)).const_mul δ
  have hs (j : ℕ) : ∀ x ∈ V, tsupport (fun y => (φ j).normed volume (x - y)) ⊆ U := by
    intro x hx y hy
    have ht := tsupport_comp_subset_preimage ((φ j).normed volume)
      (continuous_const.sub continuous_id) hy
    have hd : ‖x - y‖ ≤ (φ j).rOut := by
      simpa only [ContDiffBump.tsupport_normed_eq, mem_preimage, mem_closedBall,
        dist_zero_right, Pi.sub_apply, id_eq] using ht
    apply hclear x hx
    rw [mem_closedBall, dist_comm, dist_eq_norm]
    exact hd.trans (hφδ j)
  let u (j : ℕ) := (φ j).normed volume ⋆[ContinuousLinearMap.lsmul ℝ ℝ] U.indicator f
  have hu (j) := hf.bump_convolution_indicator hU hV (φ j) (hs j)
  have hmF : MemLp (U.indicator f) 2 volume :=
    (memLp_indicator_iff_restrict hU.measurableSet).mpr hf.memLp_function
  have hmu (j) : MemLp (u j) 2 volume :=
    (memLp_two_convolution_probability_kernel (φ j).continuous_normed
      (φ j).hasCompactSupport_normed (φ j).nonneg_normed (φ j).integral_normed hmF).1
  have hmD (j) : MemLp (fun x => u j (x + h) - u j x) 2 (volume.restrict Q) :=
    (((hmu j).comp_measurePreserving (measurePreserving_add_right volume h)).sub
      (hmu j)).mono_measure Measure.restrict_le_self
  have hbd (j) : eLpNorm (fun x => u j (x + h) - u j x) 2 (volume.restrict Q) ≤
      ENNReal.ofReal (‖h‖ * lpNorm G 2 (volume.restrict U)) := by
    have hbg : lpNorm (gradient (u j)) 2 (volume.restrict V) ≤
        lpNorm G 2 (volume.restrict U) := by
      have hh := ENNReal.toReal_mono hf.memLp_gradient.eLpNorm_ne_top (hu j).2.2.2.2
      simpa only [toReal_eLpNorm,
        toReal_eLpNorm] using hh
    rw [← ofReal_lpNorm (hmD j)]
    apply ENNReal.ofReal_le_ofReal
    exact (lpNorm_translation_sub_le_of_contDiffOn hV hQ
      ((hu j).1.of_le (by simp)).contDiffOn (hu j).2.2.1.memLp_function
      (hu j).2.2.1.memLp_gradient h hseg).trans
        (mul_le_mul_of_nonneg_left hbg (norm_nonneg _))
  have ht : Tendsto (fun j => eLpNorm (u j - U.indicator f) 2 volume) atTop (𝓝 0) :=
    tendsto_eLpNorm_bump_convolution_sub hmF hφlim
  obtain ⟨σ, _, hae⟩ := (tendstoInMeasure_of_tendsto_eLpNorm
    (by norm_num : (2 : ℝ≥0∞) ≠ 0) ht).exists_seq_tendsto_ae
  have haeD : ∀ᵐ x ∂volume.restrict Q,
      Tendsto (fun j => u (σ j) (x + h) - u (σ j) x) atTop (𝓝 (f (x + h) - f x)) := by
    have haeT := (measurePreserving_add_right volume h).quasiMeasurePreserving.ae hae
    filter_upwards [ae_restrict_of_ae hae, ae_restrict_of_ae haeT, ae_restrict_mem hQ]
      with x hx hxT hxQ
    simpa only [indicator_of_mem (hVU (hQV hxQ)),
      indicator_of_mem (hVU (hmap x hxQ))] using hxT.sub hx
  have hmDf : MemLp (fun x => f (x + h) - f x) 2 (volume.restrict Q) :=
    (memLp_translate_restrict_and_eLpNorm_le hU.measurableSet hf.memLp_function h
      (fun x hx => hVU (hmap x hx))).1.sub
      (hf.memLp_function.mono_measure (Measure.restrict_mono (hQV.trans hVU) le_rfl))
  have hb := Lp.eLpNorm_le_of_ae_tendsto (Eventually.of_forall fun j => hbd (σ j))
    (fun j => (hmD (σ j)).aestronglyMeasurable) hmDf.aestronglyMeasurable haeD
  have hbr := ENNReal.toReal_mono ENNReal.ofReal_ne_top hb
  simpa only [toReal_eLpNorm,
    ENNReal.toReal_ofReal (mul_nonneg (norm_nonneg _) lpNorm_nonneg)] using hbr

/-- Whole-space H¹ translation bound, with constant one. -/
theorem HasH1GradientOn.lpNorm_translation_sub_le_global {n : ℕ}
    {f : EuclideanSpace ℝ (Fin n) → ℝ}
    {G : EuclideanSpace ℝ (Fin n) → EuclideanSpace ℝ (Fin n)}
    (hf : HasH1GradientOn f G univ) (h : EuclideanSpace ℝ (Fin n)) :
    lpNorm (fun x => f (x + h) - f x) 2 volume ≤ ‖h‖ * lpNorm G 2 volume := by
  simpa only [Measure.restrict_univ] using hf.lpNorm_translation_sub_le
    isOpen_univ isOpen_univ MeasurableSet.univ zero_lt_one
    (fun _ _ => subset_univ _) h (fun _ _ _ _ => mem_univ _)

/-- Coordinate difference quotients of an Lᵖ function remain in Lᵖ whenever both
sampled points stay in the original region. -/
lemma memLp_coordinateDifferenceQuotient {n : ℕ} {F : Type*}
    [NormedAddCommGroup F] [NormedSpace ℝ F]
    {U Q : Set (EuclideanSpace ℝ (Fin n))} (hU : MeasurableSet U) (hQU : Q ⊆ U)
    {p : ℝ≥0∞} {f : EuclideanSpace ℝ (Fin n) → F}
    (hf : MemLp f p (volume.restrict U)) (i : Fin n) (h : ℝ)
    (hmap : ∀ x ∈ Q, x + h • EuclideanSpace.single i 1 ∈ U) :
    MemLp (coordinateDifferenceQuotient i h f) p (volume.restrict Q) :=
  ((memLp_translate_restrict_and_eLpNorm_le hU hf _ hmap).1.sub
    (hf.mono_measure (Measure.restrict_mono hQU le_rfl))).const_smul h⁻¹

/-- The local L² coordinate difference quotient is bounded by the original weak
 gradient, uniformly in every nonzero step satisfying the stated clearance. -/
theorem HasH1GradientOn.lpNorm_coordinateDifferenceQuotient_le {n : ℕ}
    {U V Q : Set (EuclideanSpace ℝ (Fin n))}
    (hU : IsOpen U) (hV : IsOpen V) (hQ : MeasurableSet Q)
    {f : EuclideanSpace ℝ (Fin n) → ℝ}
    {G : EuclideanSpace ℝ (Fin n) → EuclideanSpace ℝ (Fin n)}
    (hf : HasH1GradientOn f G U) {δ : ℝ} (hδ : 0 < δ)
    (hclear : ∀ x ∈ V, closedBall x δ ⊆ U)
    (i : Fin n) {h : ℝ} (hh : h ≠ 0)
    (hseg : ∀ x ∈ Q, ∀ t ∈ Icc (0 : ℝ) 1,
      x + t • (h • EuclideanSpace.single i 1) ∈ V) :
    lpNorm (coordinateDifferenceQuotient i h f) 2 (volume.restrict Q) ≤
      lpNorm G 2 (volume.restrict U) := by
  change lpNorm (h⁻¹ • (fun x => f (x + h • EuclideanSpace.single i 1) - f x))
    2 (volume.restrict Q) ≤ _
  rw [lpNorm_const_smul]
  have hb := mul_le_mul_of_nonneg_left
    (hf.lpNorm_translation_sub_le hU hV hQ hδ hclear _ hseg) (norm_nonneg h⁻¹)
  simpa only [coe_nnnorm, norm_smul, PiLp.norm_single, norm_one, mul_one,
    norm_inv, ← mul_assoc, inv_mul_cancel₀ (norm_ne_zero_iff.mpr hh), one_mul] using hb

/-- Whole-space uniform L² difference-quotient bound. -/
theorem HasH1GradientOn.lpNorm_coordinateDifferenceQuotient_le_global {n : ℕ}
    {f : EuclideanSpace ℝ (Fin n) → ℝ}
    {G : EuclideanSpace ℝ (Fin n) → EuclideanSpace ℝ (Fin n)}
    (hf : HasH1GradientOn f G univ) (i : Fin n) {h : ℝ} (hh : h ≠ 0) :
    lpNorm (coordinateDifferenceQuotient i h f) 2 volume ≤ lpNorm G 2 volume := by
  simpa only [Measure.restrict_univ] using hf.lpNorm_coordinateDifferenceQuotient_le
    isOpen_univ isOpen_univ MeasurableSet.univ zero_lt_one
    (fun _ _ => subset_univ _) i hh (fun _ _ _ _ => mem_univ _)

/-- Translation commutes with the genuine weak gradient on open subdomains. -/
theorem HasH1GradientOn.translate {n : ℕ}
    {U V : Set (EuclideanSpace ℝ (Fin n))} (hU : IsOpen U) (hV : IsOpen V)
    {f : EuclideanSpace ℝ (Fin n) → ℝ}
    {G : EuclideanSpace ℝ (Fin n) → EuclideanSpace ℝ (Fin n)}
    (hf : HasH1GradientOn f G U) (h : EuclideanSpace ℝ (Fin n))
    (hmap : ∀ x ∈ V, x + h ∈ U) :
    HasH1GradientOn (fun x => f (x + h)) (fun x => G (x + h)) V := by
  have hi : LipschitzWith 1 (Homeomorph.addRight h).symm := by
    simpa only [Homeomorph.addRight_symm, Homeomorph.coe_addRight] using
      (isometry_add_right (-h)).lipschitzWith
  have ht := (hf.comp_homeomorph_on hV hU (Homeomorph.addRight h)
    (isometry_add_right h).lipschitzWith hi hmap).1
  simpa only [Homeomorph.coe_addRight, Function.comp_def, fderiv_add_const,
    fderiv_fun_id, ContinuousLinearMap.adjoint_id, ContinuousLinearMap.id_apply] using ht

/-- Difference quotients commute with weak differentiation. -/
theorem HasH1GradientOn.coordinateDifferenceQuotient {n : ℕ}
    {U V : Set (EuclideanSpace ℝ (Fin n))} (hU : IsOpen U) (hV : IsOpen V) (hVU : V ⊆ U)
    {f : EuclideanSpace ℝ (Fin n) → ℝ}
    {G : EuclideanSpace ℝ (Fin n) → EuclideanSpace ℝ (Fin n)}
    (hf : HasH1GradientOn f G U) (i : Fin n) (h : ℝ)
    (hmap : ∀ x ∈ V, x + h • EuclideanSpace.single i 1 ∈ U) :
    HasH1GradientOn (coordinateDifferenceQuotient i h f)
      (coordinateDifferenceQuotient i h G) V :=
  ((hf.translate hU hV _ hmap).sub (hf.mono hVU)).const_mul h⁻¹

/-- Discrete integration by parts for L² functions on the whole space. The
backward difference uses the signed step `-h`, so the identity carries a minus sign. -/
theorem integral_coordinateDifferenceQuotient_mul {n : ℕ}
    {f g : EuclideanSpace ℝ (Fin n) → ℝ} (hf : MemLp f 2 volume) (hg : MemLp g 2 volume)
    (i : Fin n) (h : ℝ) :
    (∫ x, coordinateDifferenceQuotient i h f x * g x) =
      -(∫ x, f x * coordinateDifferenceQuotient i (-h) g x) := by
  let a := h • EuclideanSpace.single i (1 : ℝ)
  have hfg : Integrable (fun x => f x * g x) := hf.integrable_mul hg
  have htfg : Integrable (fun x => f (x + a) * g x) :=
    (hf.comp_measurePreserving (measurePreserving_add_right volume a)).integrable_mul hg
  have hftg : Integrable (fun x => f x * g (x - a)) :=
    hf.integrable_mul (hg.comp_measurePreserving (measurePreserving_sub_right volume a))
  have hshift : (∫ x, f (x + a) * g x) = ∫ x, f x * g (x - a) := by
    rw [← integral_add_right_eq_self (fun x => f x * g (x - a)) a]
    simp only [add_sub_cancel_right]
  have heL : (fun x => coordinateDifferenceQuotient i h f x * g x) =
      fun x => h⁻¹ * (f (x + a) * g x - f x * g x) := by
    funext x
    simp only [coordinateDifferenceQuotient, smul_eq_mul, a]
    ring
  have heR : (fun x => f x * coordinateDifferenceQuotient i (-h) g x) =
      fun x => -(h⁻¹) * (f x * g (x - a) - f x * g x) := by
    funext x
    simp only [coordinateDifferenceQuotient, smul_eq_mul, a, neg_smul, neg_inv,
      sub_eq_add_neg]
    ring
  rw [heL, heR, integral_const_mul, integral_const_mul, integral_sub htfg hfg,
    integral_sub hftg hfg, hshift]
  ring

/-- A scalar Lipschitz function has uniformly bounded coordinate difference quotients. -/
lemma norm_coordinateDifferenceQuotient_le_of_lipschitz {n : ℕ}
    {f : EuclideanSpace ℝ (Fin n) → ℝ} {C : ℝ≥0} (hf : LipschitzWith C f)
    (i : Fin n) (h : ℝ) (x : EuclideanSpace ℝ (Fin n)) :
    ‖coordinateDifferenceQuotient i h f x‖ ≤ C := by
  by_cases hh : h = 0
  · simp [coordinateDifferenceQuotient, hh]
  · calc
      _ = ‖h⁻¹‖ * ‖f (x + h • EuclideanSpace.single i 1) - f x‖ := norm_smul _ _
      _ ≤ ‖h⁻¹‖ * (C * ‖(x + h • EuclideanSpace.single i 1) - x‖) :=
        mul_le_mul_of_nonneg_left (hf.norm_sub_le _ _) (norm_nonneg _)
      _ = C := by
        simp only [add_sub_cancel_left, norm_smul, PiLp.norm_single, norm_one, mul_one,
          norm_inv]
        rw [mul_left_comm, inv_mul_cancel₀ (norm_ne_zero_iff.mpr hh), mul_one]

/-- At a differentiability point, coordinate difference quotients converge to the
corresponding classical derivative as the signed nonzero step tends to zero. -/
lemma tendsto_coordinateDifferenceQuotient_of_differentiableAt {n : ℕ}
    {f : EuclideanSpace ℝ (Fin n) → ℝ} {x : EuclideanSpace ℝ (Fin n)}
    (hf : DifferentiableAt ℝ f x) (i : Fin n) :
    Tendsto (fun h : ℝ => coordinateDifferenceQuotient i h f x) (𝓝[≠] 0)
      (𝓝 (fderiv ℝ f x (EuclideanSpace.single i 1))) := by
  have hp : HasDerivAt (fun t : ℝ => x + t • EuclideanSpace.single i (1 : ℝ))
      (EuclideanSpace.single i 1) 0 := by
    simpa only [one_smul, id_eq] using
      ((hasDerivAt_id (0 : ℝ)).smul_const (EuclideanSpace.single i (1 : ℝ))).const_add x
  have hfd : HasFDerivAt f (fderiv ℝ f x)
      (x + (0 : ℝ) • EuclideanSpace.single i 1) := by simpa using hf.hasFDerivAt
  have hd := (hfd.comp_hasDerivAt 0 hp).tendsto_slope_zero
  simpa only [Function.comp_def, slope_def_module, sub_zero, zero_smul, add_zero, zero_add,
    coordinateDifferenceQuotient] using hd

/-- Difference quotients of a compact C¹ test converge in pairing with every
locally integrable function; the test support supplies one common compact bound. -/
theorem tendsto_integral_mul_coordinateDifferenceQuotient_test {n : ℕ}
    {f φ : EuclideanSpace ℝ (Fin n) → ℝ} (hf : LocallyIntegrable f)
    (hφ : ContDiff ℝ 1 φ) (hcφ : HasCompactSupport φ) (i : Fin n) :
    Tendsto (fun h : ℝ => ∫ x, f x * coordinateDifferenceQuotient i h φ x) (𝓝[≠] 0)
      (𝓝 (∫ x, f x * fderiv ℝ φ x (EuclideanSpace.single i 1))) := by
  obtain ⟨C, hC⟩ := ContDiff.lipschitzWith_of_hasCompactSupport hcφ hφ one_ne_zero
  let K := cthickening 1 (tsupport φ)
  have hK : IsCompact K := hcφ.cthickening
  have hm (h : ℝ) : Continuous (coordinateDifferenceQuotient i h φ) := by
    unfold coordinateDifferenceQuotient
    exact (continuous_const (y := h⁻¹)).smul
      ((hφ.continuous.comp (continuous_id.add continuous_const)).sub hφ.continuous)
  apply tendsto_integral_filter_of_dominated_convergence
    (K.indicator (fun x => (C : ℝ) * ‖f x‖))
  · exact Eventually.of_forall fun h => hf.aestronglyMeasurable.mul (hm h).aestronglyMeasurable
  · have hh : ∀ᶠ h : ℝ in 𝓝[≠] 0, ‖h‖ ≤ 1 := by
      have hball : ∀ᶠ h : ℝ in 𝓝[≠] 0, h ∈ ball 0 1 :=
        mem_nhdsWithin_of_mem_nhds (ball_mem_nhds (0 : ℝ) zero_lt_one)
      exact hball.mono fun h ht => (show ‖h‖ < 1 by
        simpa only [mem_ball, dist_zero_right] using ht).le
    filter_upwards [hh] with h hh
    exact Eventually.of_forall fun x => by
      by_cases hx : x ∈ K
      · rw [indicator_of_mem hx, norm_mul]
        exact (mul_le_mul_of_nonneg_left
          (norm_coordinateDifferenceQuotient_le_of_lipschitz hC i h x) (norm_nonneg _)).trans_eq
          (mul_comm _ _)
      · have hxφ : x ∉ tsupport φ := fun hs => hx (self_subset_cthickening _ hs)
        have hxhφ : x + h • EuclideanSpace.single i (1 : ℝ) ∉ tsupport φ := by
          intro hs
          apply hx
          apply mem_cthickening_of_dist_le _ _ 1 (tsupport φ) hs
          simpa only [dist_eq_norm, sub_add_cancel_left, norm_neg, norm_smul,
            PiLp.norm_single, norm_one, mul_one] using hh
        simp only [coordinateDifferenceQuotient, image_eq_zero_of_notMem_tsupport hxφ,
          image_eq_zero_of_notMem_tsupport hxhφ, sub_self, smul_zero, mul_zero, norm_zero,
          indicator_of_notMem hx]
        exact le_rfl
  · rw [integrable_indicator_iff hK.measurableSet]
    exact (hf.integrableOn_isCompact hK).norm.const_mul C
  · exact Eventually.of_forall fun x => tendsto_const_nhds.mul
      (tendsto_coordinateDifferenceQuotient_of_differentiableAt
        (hφ.differentiable one_ne_zero x) i)

/-- A uniform L² bound along any sequence of nonzero coordinate steps tending to
zero produces an L² weak coordinate derivative on the open region. The source
function is global L²; the bound and the resulting derivative are local to `U`. -/
theorem exists_weak_coordinateDerivative_of_differenceQuotient_bound {n : ℕ}
    {U : Set (EuclideanSpace ℝ (Fin n))} (_hU : IsOpen U)
    {f : EuclideanSpace ℝ (Fin n) → ℝ} (hf : MemLp f 2 volume)
    (i : Fin n) {h : ℕ → ℝ} (hh : ∀ j, h j ≠ 0)
    (ht : Tendsto h atTop (𝓝 0)) {C : ℝ}
    (hb : ∀ j, lpNorm (coordinateDifferenceQuotient i (h j) f)
      2 (volume.restrict U) ≤ C) :
    ∃ g : EuclideanSpace ℝ (Fin n) → ℝ, MemLp g 2 (volume.restrict U) ∧
      lpNorm g 2 (volume.restrict U) ≤ C ∧
      ∀ φ : EuclideanSpace ℝ (Fin n) → ℝ, ContDiff ℝ 1 φ → HasCompactSupport φ →
        tsupport φ ⊆ U →
        -(∫ x in U, f x * fderiv ℝ φ x (EuclideanSpace.single i 1)) =
          ∫ x in U, φ x * g x := by
  have hm (j : ℕ) : MemLp (coordinateDifferenceQuotient i (h j) f)
      2 (volume.restrict U) :=
    (((hf.comp_measurePreserving (measurePreserving_add_right volume
      (h j • EuclideanSpace.single i 1))).sub hf).const_smul (h j)⁻¹).mono_measure
        Measure.restrict_le_self
  let u (j : ℕ) : Lp ℝ 2 (volume.restrict U) := (hm j).toLp _
  have hbu (j) : ‖u j‖ ≤ C := by
    change ‖(hm j).toLp _‖ ≤ C
    rw [Lp.norm_toLp, toReal_eLpNorm]
    exact hb j
  obtain ⟨g, σ, hσ, hgb, hweak⟩ := exists_subseq_weakly_tendsto_of_hilbert_bound u hbu
  refine ⟨g, Lp.memLp g, ?_, ?_⟩
  · simpa only [Lp.norm_def, toReal_eLpNorm] using hgb
  · intro φ hφ hcφ hsφ
    have hmφ : MemLp φ 2 (volume.restrict U) :=
      hφ.continuous.memLp_of_hasCompactSupport hcφ
    let ℓ : Lp ℝ 2 (volume.restrict U) →L[ℝ] ℝ := innerSL ℝ (hmφ.toLp φ)
    have hpair (j : ℕ) : ℓ (u j) =
        ∫ x in U, φ x * coordinateDifferenceQuotient i (h j) f x := by
      change inner ℝ (hmφ.toLp φ) ((hm j).toLp _) = _
      rw [L2.inner_def]
      apply integral_congr_ae
      filter_upwards [hmφ.coeFn_toLp, (hm j).coeFn_toLp] with x hx hy
      rw [hx, hy, Real.inner_apply]
    have hpairg : ℓ g = ∫ x in U, φ x * g x := by
      change inner ℝ (hmφ.toLp φ) g = _
      rw [L2.inner_def]
      apply integral_congr_ae
      filter_upwards [hmφ.coeFn_toLp] with x hx
      rw [hx, Real.inner_apply]
    have htest (j : ℕ) : ℓ (u j) =
        -(∫ x, f x * coordinateDifferenceQuotient i (-(h j)) φ x) := by
      rw [hpair, setIntegral_eq_integral_of_forall_compl_eq_zero
        (fun x hx => by rw [image_eq_zero_of_notMem_tsupport (fun hs => hx (hsφ hs)), zero_mul])]
      have hφglobal : MemLp φ 2 volume := hφ.continuous.memLp_of_hasCompactSupport hcφ
      simpa only [mul_comm] using integral_coordinateDifferenceQuotient_mul hf hφglobal i (h j)
    have hstep : Tendsto (fun j => -(h (σ j))) atTop (𝓝[≠] (0 : ℝ)) := by
      apply tendsto_nhdsWithin_iff.mpr
      refine ⟨?_, Eventually.of_forall fun j => ?_⟩
      · simpa using (ht.comp hσ.tendsto_atTop).neg
      · simpa only [mem_compl_iff, mem_singleton_iff, neg_eq_zero] using hh (σ j)
    have hlim := ((tendsto_integral_mul_coordinateDifferenceQuotient_test
      (hf.locallyIntegrable (by norm_num)) hφ hcφ i).comp hstep).neg
    have heq : ℓ g = -(∫ x, f x * fderiv ℝ φ x (EuclideanSpace.single i 1)) := by
      apply tendsto_nhds_unique (hweak ℓ)
      simpa only [Function.comp_def, htest] using hlim
    rw [hpairg] at heq
    rw [setIntegral_eq_integral_of_forall_compl_eq_zero
      (fun x hx => by rw [fderiv_of_notMem_tsupport ℝ
        (fun hs => hx (hsφ hs)), zero_apply, mul_zero])]
    exact heq.symm

/-- Uniform L² bounds for all coordinate difference quotients imply the genuine
H¹ weak-gradient relation. The construction retains each coordinate bound and
their sum bounds the full gradient norm. -/
theorem exists_hasH1GradientOn_of_differenceQuotient_bounds {n : ℕ}
    {U : Set (EuclideanSpace ℝ (Fin n))} (hU : IsOpen U)
    {f : EuclideanSpace ℝ (Fin n) → ℝ} (hf : MemLp f 2 volume)
    {h : ℕ → ℝ} (hh : ∀ j, h j ≠ 0) (ht : Tendsto h atTop (𝓝 0))
    {C : Fin n → ℝ}
    (hb : ∀ i j, lpNorm (coordinateDifferenceQuotient i (h j) f)
      2 (volume.restrict U) ≤ C i) :
    ∃ G : EuclideanSpace ℝ (Fin n) → EuclideanSpace ℝ (Fin n),
      HasH1GradientOn f G U ∧
      (∀ i, lpNorm (fun x => G x i) 2 (volume.restrict U) ≤ C i) ∧
      lpNorm G 2 (volume.restrict U) ≤ ∑ i, C i := by
  classical
  choose g hg hgb htest using fun i =>
    exists_weak_coordinateDerivative_of_differenceQuotient_bound hU hf i hh ht (hb i)
  let v (i : Fin n) (x : EuclideanSpace ℝ (Fin n)) : EuclideanSpace ℝ (Fin n) :=
    g i x • EuclideanSpace.single i 1
  let G (x : EuclideanSpace ℝ (Fin n)) : EuclideanSpace ℝ (Fin n) := ∑ i, v i x
  have hvi (i : Fin n) : MemLp (v i) 2 (volume.restrict U) := by
    exact ((ContinuousLinearMap.id ℝ ℝ).smulRight
      (EuclideanSpace.single i 1)).comp_memLp' (hg i)
  have hG : MemLp G 2 (volume.restrict U) := by
    simpa only [Finset.mem_univ, forall_const] using
      (memLp_finsetSum Finset.univ (fun i _ => hvi i))
  have hcoord (x : EuclideanSpace ℝ (Fin n)) (i : Fin n) : G x i = g i x := by
    simp [G, v, Pi.single_apply]
  refine ⟨G, hasH1GradientOn_of_memLp_test
    (hf.mono_measure Measure.restrict_le_self) hG ?_, ?_, ?_⟩
  · intro i φ hφ hcφ hsφ
    simpa only [hcoord] using htest i φ hφ hcφ hsφ
  · intro i
    simpa only [hcoord] using hgb i
  · have hvnorm (i : Fin n) : lpNorm (v i) 2 (volume.restrict U) =
        lpNorm (g i) 2 (volume.restrict U) := by
      rw [← toReal_eLpNorm, ← toReal_eLpNorm]
      congr 1
      apply eLpNorm_congr_norm_ae (hvi i).aestronglyMeasurable (hg i).aestronglyMeasurable
      exact Eventually.of_forall fun x => by simp [v, norm_smul, PiLp.norm_single]
    have hsum := lpNorm_sum_le (s := Finset.univ) (f := v)
      (fun i _ => hvi i) (by norm_num : (1 : ℝ≥0∞) ≤ 2)
    have hsum' : lpNorm G 2 (volume.restrict U) ≤ ∑ i, lpNorm (v i) 2 (volume.restrict U) := by
      have he : G = ∑ i, v i := by ext x; simp [G]
      rw [he]
      exact hsum
    exact hsum'.trans (Finset.sum_le_sum fun i _ => (hvnorm i).trans_le (hgb i))

/-- Local L² difference-quotient characterization using zero extension only as an
auxiliary representative. Every sampled point is explicitly required to lie in
the larger region, so the resulting weak gradient belongs to the original function. -/
theorem exists_hasH1GradientOn_of_local_differenceQuotient_bounds {n : ℕ}
    {U V : Set (EuclideanSpace ℝ (Fin n))} (hU : MeasurableSet U) (hV : IsOpen V)
    (hVU : V ⊆ U) {f : EuclideanSpace ℝ (Fin n) → ℝ}
    (hf : MemLp f 2 (volume.restrict U))
    {h : ℕ → ℝ} (hh : ∀ j, h j ≠ 0) (ht : Tendsto h atTop (𝓝 0))
    (hmap : ∀ (i : Fin n) j x, x ∈ V → x + h j • EuclideanSpace.single i 1 ∈ U)
    {C : Fin n → ℝ}
    (hb : ∀ i j, lpNorm (coordinateDifferenceQuotient i (h j) f)
      2 (volume.restrict V) ≤ C i) :
    ∃ G : EuclideanSpace ℝ (Fin n) → EuclideanSpace ℝ (Fin n),
      HasH1GradientOn f G V ∧
      (∀ i, lpNorm (fun x => G x i) 2 (volume.restrict V) ≤ C i) ∧
      lpNorm G 2 (volume.restrict V) ≤ ∑ i, C i := by
  have hmF : MemLp (U.indicator f) 2 volume := (memLp_indicator_iff_restrict hU).mpr hf
  have he (i : Fin n) (j : ℕ) :
      coordinateDifferenceQuotient i (h j) (U.indicator f) =ᵐ[volume.restrict V]
        coordinateDifferenceQuotient i (h j) f := by
    filter_upwards [ae_restrict_mem hV.measurableSet] with x hx
    simp only [coordinateDifferenceQuotient, indicator_of_mem (hVU hx),
      indicator_of_mem (hmap i j x hx)]
  have hbF (i : Fin n) (j : ℕ) :
      lpNorm (coordinateDifferenceQuotient i (h j) (U.indicator f))
        2 (volume.restrict V) ≤ C i := by
    have hmf := memLp_coordinateDifferenceQuotient hU hVU hf i (h j) (hmap i j)
    have hmFj := hmf.ae_eq (he i j).symm
    rw [← toReal_eLpNorm, eLpNorm_congr_ae (he i j), toReal_eLpNorm]
    exact hb i j
  obtain ⟨G, hG, hcoord, hnorm⟩ :=
    exists_hasH1GradientOn_of_differenceQuotient_bounds hV hmF hh ht hbF
  refine ⟨G, hG.congr_ae ?_ EventuallyEq.rfl, hcoord, hnorm⟩
  filter_upwards [ae_restrict_mem hV.measurableSet] with x hx
  exact indicator_of_mem (hVU hx) f

/-- Local discrete integration by parts. The support of the test and its forward
translate lie in the source region; no global L² premise on the source is imposed. -/
theorem setIntegral_coordinateDifferenceQuotient_mul {n : ℕ}
    {U : Set (EuclideanSpace ℝ (Fin n))} (hU : MeasurableSet U)
    {f φ : EuclideanSpace ℝ (Fin n) → ℝ} (hf : MemLp f 2 (volume.restrict U))
    (hφ : MemLp φ 2 volume) (hsφ : Function.support φ ⊆ U) (i : Fin n) (h : ℝ)
    (hmap : ∀ x ∈ Function.support φ, x + h • EuclideanSpace.single i 1 ∈ U) :
    (∫ x in U, coordinateDifferenceQuotient i h f x * φ x) =
      -(∫ x in U, f x * coordinateDifferenceQuotient i (-h) φ x) := by
  have hmF := (memLp_indicator_iff_restrict hU).mpr hf
  calc
    _ = ∫ x in U, coordinateDifferenceQuotient i h (U.indicator f) x * φ x := by
      apply integral_congr_ae
      filter_upwards [ae_restrict_mem hU] with x hx
      by_cases hφx : φ x = 0
      · simp only [hφx, mul_zero]
      · simp only [coordinateDifferenceQuotient, indicator_of_mem hx,
          indicator_of_mem (hmap x hφx)]
    _ = ∫ x, coordinateDifferenceQuotient i h (U.indicator f) x * φ x :=
      setIntegral_eq_integral_of_forall_compl_eq_zero fun x hx => by
        rw [Function.notMem_support.mp (fun hs => hx (hsφ hs)), mul_zero]
    _ = -(∫ x, U.indicator f x * coordinateDifferenceQuotient i (-h) φ x) :=
      integral_coordinateDifferenceQuotient_mul hmF hφ i h
    _ = _ := by
      congr 1
      rw [← integral_indicator hU]
      apply integral_congr_ae
      exact Eventually.of_forall fun x => by
        by_cases hx : x ∈ U <;> simp [hx]

/-- Ball version of the sharp translation bound. The sole clearance requirement
is `r + ‖h‖ < R`, with concentric balls and a genuine H¹ function on the larger ball. -/
theorem HasH1GradientOn.lpNorm_translation_sub_le_ball {n : ℕ}
    {f : EuclideanSpace ℝ (Fin n) → ℝ}
    {G : EuclideanSpace ℝ (Fin n) → EuclideanSpace ℝ (Fin n)}
    {c : EuclideanSpace ℝ (Fin n)} {r R : ℝ}
    (hf : HasH1GradientOn f G (ball c R)) (h : EuclideanSpace ℝ (Fin n))
    (hclear : r + ‖h‖ < R) :
    lpNorm (fun x => f (x + h) - f x) 2 (volume.restrict (ball c r)) ≤
      ‖h‖ * lpNorm G 2 (volume.restrict (ball c R)) := by
  let ρ := (r + ‖h‖ + R) / 2
  let δ := (R - (r + ‖h‖)) / 2
  have hδ : 0 < δ := by dsimp [δ]; linarith
  have hmid : r + ‖h‖ < ρ := by dsimp [ρ]; linarith
  have hsum : δ + ρ = R := by dsimp [δ, ρ]; ring
  apply hf.lpNorm_translation_sub_le isOpen_ball isOpen_ball isOpen_ball.measurableSet hδ
    (V := ball c ρ) ?_ h ?_
  · intro x hx y hy
    have hdist := dist_triangle y x c
    have hxy : dist y x ≤ δ := hy
    have hxc : dist x c < ρ := hx
    change dist y c < R
    linarith
  · intro x hx t ht
    have htx : ‖t • h‖ ≤ ‖h‖ := by
      rw [norm_smul, Real.norm_of_nonneg ht.1]
      exact mul_le_of_le_one_left (norm_nonneg _) ht.2
    have hdist : dist (x + t • h) c ≤ ‖t • h‖ + dist x c := by
      have hh := dist_triangle (x + t • h) x c
      simpa only [dist_eq_norm, add_sub_cancel_left] using hh
    have hxc : dist x c < r := hx
    change dist (x + t • h) c < ρ
    linarith

/-- Coordinate difference quotients on a smaller concentric ball have their L²
norm bounded by the gradient norm on the larger ball whenever `r + |h| < R`. -/
theorem HasH1GradientOn.lpNorm_coordinateDifferenceQuotient_le_ball {n : ℕ}
    {f : EuclideanSpace ℝ (Fin n) → ℝ}
    {G : EuclideanSpace ℝ (Fin n) → EuclideanSpace ℝ (Fin n)}
    {c : EuclideanSpace ℝ (Fin n)} {r R : ℝ}
    (hf : HasH1GradientOn f G (ball c R)) (i : Fin n) {h : ℝ}
    (hh : h ≠ 0) (hclear : r + |h| < R) :
    lpNorm (LiquidDrop.coordinateDifferenceQuotient i h f) 2 (volume.restrict (ball c r)) ≤
      lpNorm G 2 (volume.restrict (ball c R)) := by
  have hb := hf.lpNorm_translation_sub_le_ball (h • EuclideanSpace.single i 1)
    (by simpa only [norm_smul, PiLp.norm_single, norm_one, mul_one, Real.norm_eq_abs] using hclear)
  have hhB := mul_le_mul_of_nonneg_left hb (norm_nonneg h⁻¹)
  change lpNorm (h⁻¹ • (fun x => f (x + h • EuclideanSpace.single i 1) - f x))
    2 (volume.restrict (ball c r)) ≤ _
  rw [lpNorm_const_smul]
  simpa only [coe_nnnorm, norm_smul, PiLp.norm_single, norm_one, mul_one, norm_inv,
    ← mul_assoc, inv_mul_cancel₀ (norm_ne_zero_iff.mpr hh), one_mul] using hhB

end LiquidDrop

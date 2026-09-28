import NoCompromise.BV.StrictApprox
import Mathlib.MeasureTheory.Integral.IntervalIntegral.ContDiff
import Mathlib.MeasureTheory.Measure.Haar.InnerProductSpace
import Mathlib.MeasureTheory.Function.Floor
import Mathlib.MeasureTheory.Integral.Average
import Mathlib.Topology.MetricSpace.Sequences
import Mathlib.MeasureTheory.Function.LpSpace.Complete
import Mathlib.MeasureTheory.Function.ConvergenceInMeasure

/-!
# Translation estimates and local BV compactness

The translation estimate follows from the fundamental theorem of calculus for smooth
functions, Tonelli, and strict approximation. All displacement segments are required
to stay in the open region where the derivative is estimated.

Half-open coordinate cells give measurable grid averages. Their L¹ error is bounded
by an average of translation errors, giving the grid approximation estimate with
explicit dimension constant n * 2^n. Only finitely many cells meet a bounded set.
Compact coefficient balls supply simultaneous subsequences for countably many grids.
The approximation errors then give an L¹ Cauchy subsequence on each fixed relatively
compact region, and lower semicontinuity gives a BV limit there. A countable
exhaustion and compatible almost-everywhere representatives give local BV compactness
on arbitrary open domains. The indicator conclusion is proved on the whole space;
the blueprint statement for general domains needs its perimeter scope clarified.
-/

open MeasureTheory Filter Metric Set InnerProductSpace
open scoped ENNReal Topology Gradient Pointwise Convolution

namespace LiquidDrop

set_option maxSynthPendingDepth 8

lemma continuousOn_gradient_of_contDiffOn {n : ℕ}
    {U : Set (EuclideanSpace ℝ (Fin n))} (hU : IsOpen U)
    {f : EuclideanSpace ℝ (Fin n) → ℝ} (hf : ContDiffOn ℝ 1 f U) :
    ContinuousOn (gradient f) U := by
  exact (toDual ℝ (EuclideanSpace ℝ (Fin n))).symm.continuous.comp_continuousOn
    (hf.continuousOn_fderiv_of_isOpen hU le_rfl)

/-- The change along a segment in an open C¹ domain is bounded by its gradient integral. -/
lemma enorm_sub_le_lintegral_gradient_segment {n : ℕ}
    {U : Set (EuclideanSpace ℝ (Fin n))} (hU : IsOpen U)
    {f : EuclideanSpace ℝ (Fin n) → ℝ} (hf : ContDiffOn ℝ 1 f U)
    (x h : EuclideanSpace ℝ (Fin n))
    (hseg : ∀ t ∈ Icc (0 : ℝ) 1, x + t • h ∈ U) :
    ‖f (x + h) - f x‖ₑ ≤
      ∫⁻ t in Icc (0 : ℝ) 1, ENNReal.ofReal ‖h‖ * ‖gradient f (x + t • h)‖ₑ := by
  have hc : ContDiffOn ℝ 1 (fun t : ℝ => f (x + t • h)) (Icc (0 : ℝ) 1) :=
    hf.comp (contDiff_const.add (contDiff_id.smul contDiff_const)).contDiffOn hseg
  have hd (t : ℝ) (ht : t ∈ Icc (0 : ℝ) 1) :
      deriv (fun t : ℝ => f (x + t • h)) t = inner ℝ (gradient f (x + t • h)) h := by
    have hd := ((hf.contDiffAt (hU.mem_nhds (hseg t ht))).differentiableAt one_ne_zero).hasFDerivAt
    have hp : HasDerivAt (fun t : ℝ => x + t • h) h t := by
      simpa only [one_smul, id_eq] using ((hasDerivAt_id t).smul_const h).const_add x
    simpa only [Function.comp_def, inner_gradient_left] using (hd.comp_hasDerivAt t hp).deriv
  have hline := enorm_sub_le_lintegral_deriv_of_contDiffOn_Icc hc (by norm_num : (0 : ℝ) ≤ 1)
  simp only [one_smul, zero_smul, add_zero] at hline
  refine hline.trans (lintegral_mono_ae ?_)
  filter_upwards [ae_restrict_mem measurableSet_Icc] with t ht
  rw [hd t ht]
  have hb := ENNReal.ofReal_le_ofReal (norm_inner_le_norm (𝕜 := ℝ) (gradient f (x + t • h)) h)
  simpa only [ENNReal.ofReal_mul (norm_nonneg _), ofReal_norm, mul_comm] using hb

/-- Tonelli and translation invariance give the smooth translation bound on any measurable
set whose displacement segments stay in the open differentiability domain. -/
theorem lintegral_translation_sub_le_of_contDiffOn {n : ℕ}
    {U Q : Set (EuclideanSpace ℝ (Fin n))} (hU : IsOpen U) (hQ : MeasurableSet Q)
    {f : EuclideanSpace ℝ (Fin n) → ℝ} (hf : ContDiffOn ℝ 1 f U)
    (h : EuclideanSpace ℝ (Fin n))
    (hseg : ∀ x ∈ Q, ∀ t ∈ Icc (0 : ℝ) 1, x + t • h ∈ U) :
    (∫⁻ x in Q, ‖f (x + h) - f x‖ₑ) ≤
      ENNReal.ofReal ‖h‖ * ∫⁻ x in U, ‖gradient f x‖ₑ := by
  classical
  let G := U.indicator (fun x => ‖gradient f x‖ₑ)
  have hG : Measurable G :=
    (continuousOn_gradient_of_contDiffOn hU hf).enorm.measurable_piecewise
      continuousOn_const hU.measurableSet
  have hm : Measurable (fun p : EuclideanSpace ℝ (Fin n) × ℝ =>
      ENNReal.ofReal ‖h‖ * G (p.1 + p.2 • h)) :=
    measurable_const.mul (hG.comp ((continuous_fst.add
      (continuous_snd.smul continuous_const)).measurable))
  calc
    _ ≤ ∫⁻ x in Q, ∫⁻ t in Icc (0 : ℝ) 1, ENNReal.ofReal ‖h‖ * G (x + t • h) := by
      apply lintegral_mono_ae
      filter_upwards [ae_restrict_mem hQ] with x hx
      apply (enorm_sub_le_lintegral_gradient_segment hU hf x h (hseg x hx)).trans_eq
      apply lintegral_congr_ae
      filter_upwards [ae_restrict_mem measurableSet_Icc] with t ht
      simp only [G, indicator_of_mem (hseg x hx t ht)]
    _ = ∫⁻ t in Icc (0 : ℝ) 1, ∫⁻ x in Q, ENNReal.ofReal ‖h‖ * G (x + t • h) :=
      lintegral_lintegral_swap hm.aemeasurable
    _ ≤ ∫⁻ _t in Icc (0 : ℝ) 1, ENNReal.ofReal ‖h‖ * ∫⁻ y, G y := by
      apply lintegral_mono
      intro t
      calc
        _ ≤ ∫⁻ x, ENNReal.ofReal ‖h‖ * G (x + t • h) :=
          lintegral_mono' Measure.restrict_le_self le_rfl
        _ = _ := by
          rw [lintegral_const_mul' _ _ ENNReal.ofReal_ne_top, lintegral_add_right_eq_self]
    _ = _ := by
      rw [setLIntegral_const]
      simp only [Real.volume_Icc, sub_zero, ENNReal.ofReal_one, mul_one]
      rw [lintegral_indicator hU.measurableSet]

/-- Restricting a translated integrable function to a set mapped into its domain does
not increase its L¹ norm. -/
lemma integrableOn_translate_and_norm_le {n : ℕ} {F : Type*} [NormedAddCommGroup F]
    {U Q : Set (EuclideanSpace ℝ (Fin n))} (hU : MeasurableSet U)
    {f : EuclideanSpace ℝ (Fin n) → F} (hf : IntegrableOn f U)
    (h : EuclideanSpace ℝ (Fin n)) (hmap : ∀ x ∈ Q, x + h ∈ U) :
    IntegrableOn (fun x => f (x + h)) Q ∧
      (∫ x in Q, ‖f (x + h)‖) ≤ ∫ x in U, ‖f x‖ := by
  have hp := (measurePreserving_add_right volume h).restrict_preimage hU
  have hi := hp.integrable_comp_of_integrable hf
  change IntegrableOn (fun x => f (x + h)) ((fun x => x + h) ⁻¹' U) at hi
  refine ⟨hi.mono_set hmap, ?_⟩
  calc
    _ ≤ ∫ x in (fun x => x + h) ⁻¹' U, ‖f (x + h)‖ :=
      setIntegral_mono_set hi.norm (Eventually.of_forall fun _ => norm_nonneg _)
        (Eventually.of_forall hmap)
    _ = _ := hp.integral_comp (MeasurableEquiv.addRight h).measurableEmbedding (fun x => ‖f x‖)

/-- The displacement of an L¹ error has at most twice its original L¹ norm. -/
lemma integrableOn_translation_sub_and_norm_le {n : ℕ} {F : Type*} [NormedAddCommGroup F]
    {U Q : Set (EuclideanSpace ℝ (Fin n))} (hU : MeasurableSet U) (hQU : Q ⊆ U)
    {f : EuclideanSpace ℝ (Fin n) → F} (hf : IntegrableOn f U)
    (h : EuclideanSpace ℝ (Fin n)) (hmap : ∀ x ∈ Q, x + h ∈ U) :
    IntegrableOn (fun x => f (x + h) - f x) Q ∧
      (∫ x in Q, ‖f (x + h) - f x‖) ≤ 2 * ∫ x in U, ‖f x‖ := by
  obtain ⟨hi, hb⟩ := integrableOn_translate_and_norm_le hU hf h hmap
  have hi' := hf.mono_set hQU
  refine ⟨hi.sub hi', ?_⟩
  calc
    _ ≤ ∫ x in Q, ‖f (x + h)‖ + ‖f x‖ :=
      integral_mono (hi.sub hi').norm (hi.norm.add hi'.norm) (fun _ => norm_sub_le _ _)
    _ = (∫ x in Q, ‖f (x + h)‖) + ∫ x in Q, ‖f x‖ := integral_add hi.norm hi'.norm
    _ ≤ (∫ x in U, ‖f x‖) + ∫ x in U, ‖f x‖ :=
      add_le_add hb (setIntegral_mono_set hf.norm (Eventually.of_forall fun _ => norm_nonneg _)
        (Eventually.of_forall hQU))
    _ = _ := (two_mul _).symm

/-- Integral norm is Lipschitz with respect to L¹ distance, also on a restricted domain. -/
lemma abs_setIntegral_norm_sub_le_integral_norm_sub {n : ℕ} {F : Type*}
    [NormedAddCommGroup F] {Q : Set (EuclideanSpace ℝ (Fin n))}
    {u v : EuclideanSpace ℝ (Fin n) → F} (hu : IntegrableOn u Q) (hv : IntegrableOn v Q) :
    |(∫ x in Q, ‖u x‖) - ∫ x in Q, ‖v x‖| ≤ ∫ x in Q, ‖u x - v x‖ := by
  rw [← integral_sub hu.norm hv.norm, ← Real.norm_eq_abs]
  apply norm_integral_le_of_norm_le (hu.sub hv).norm
  exact Eventually.of_forall fun x => abs_norm_sub_norm_le _ _

/-- L¹ approximation on a region controls the displacement integral on every set whose
original and translated points lie in that region. -/
theorem translation_norm_integral_stability {n : ℕ} {F : Type*}
    [NormedAddCommGroup F] {U Q : Set (EuclideanSpace ℝ (Fin n))}
    (hU : MeasurableSet U) (hQU : Q ⊆ U) (h : EuclideanSpace ℝ (Fin n))
    (hmap : ∀ x ∈ Q, x + h ∈ U) {f g : EuclideanSpace ℝ (Fin n) → F}
    (hif : IntegrableOn (fun x => f (x + h) - f x) Q)
    (he : IntegrableOn (fun x => g x - f x) U) :
    IntegrableOn (fun x => g (x + h) - g x) Q ∧
      |(∫ x in Q, ‖g (x + h) - g x‖) - ∫ x in Q, ‖f (x + h) - f x‖| ≤
        2 * ∫ x in U, ‖g x - f x‖ := by
  obtain ⟨hi, hb⟩ := integrableOn_translation_sub_and_norm_le hU hQU he h hmap
  have heq : (fun x => g (x + h) - g x) =
      (fun x => f (x + h) - f x + ((g (x + h) - f (x + h)) - (g x - f x))) := by
    funext x
    abel
  have hig : IntegrableOn (fun x => g (x + h) - g x) Q := by
    rw [heq]
    exact hif.add hi
  refine ⟨hig, (abs_setIntegral_norm_sub_le_integral_norm_sub hig hif).trans ?_⟩
  have heq' (x) : (g (x + h) - g x) - (f (x + h) - f x) =
      (g (x + h) - f (x + h)) - (g x - f x) := by abel
  simpa only [heq'] using hb

/-- The real-valued smooth translation bound, when the indicated integrals are finite. -/
theorem integral_translation_sub_le_of_contDiffOn {n : ℕ}
    {U Q : Set (EuclideanSpace ℝ (Fin n))} (hU : IsOpen U) (hQ : MeasurableSet Q)
    {f : EuclideanSpace ℝ (Fin n) → ℝ} (hf : ContDiffOn ℝ 1 f U)
    (h : EuclideanSpace ℝ (Fin n))
    (hseg : ∀ x ∈ Q, ∀ t ∈ Icc (0 : ℝ) 1, x + t • h ∈ U)
    (hi : IntegrableOn (fun x => f (x + h) - f x) Q)
    (hgrad : IntegrableOn (gradient f) U) :
    (∫ x in Q, ‖f (x + h) - f x‖) ≤ ‖h‖ * ∫ x in U, ‖gradient f x‖ := by
  have hb := lintegral_translation_sub_le_of_contDiffOn hU hQ hf h hseg
  rw [← ofReal_integral_norm_eq_lintegral_enorm hi,
    ← ofReal_integral_norm_eq_lintegral_enorm hgrad,
    ← ENNReal.ofReal_mul (norm_nonneg h)] at hb
  exact (ENNReal.ofReal_le_ofReal_iff (mul_nonneg (norm_nonneg h)
    (integral_nonneg fun _ => norm_nonneg _))).mp hb

/-- Translation estimate for locally BV functions with finite variation on the region
containing the segments. Integrability is needed only for the original displacement. -/
theorem translation_estimate_of_finite_variation {n : ℕ}
    {U Q : Set (EuclideanSpace ℝ (Fin n))} (hU : IsOpen U) (hQ : MeasurableSet Q)
    {f : EuclideanSpace ℝ (Fin n) → ℝ} (hf : IsLocallyBVOn f U)
    (hfin : variation f U < ∞) (h : EuclideanSpace ℝ (Fin n))
    (hseg : ∀ x ∈ Q, ∀ t ∈ Icc (0 : ℝ) 1, x + t • h ∈ U)
    (hi : IntegrableOn (fun x => f (x + h) - f x) Q) :
    (∫ x in Q, |f (x + h) - f x|) ≤ ‖h‖ * (variation f U).toReal := by
  obtain ⟨g, hg, hie, hL1, _, hgrad⟩ := strict_approximation_on hU hf
  obtain ⟨hig, hglim⟩ := hgrad hfin
  have hQU : Q ⊆ U := fun x hx => by
    simpa only [zero_smul, add_zero] using hseg x hx 0 ⟨le_rfl, zero_le_one⟩
  have hmap : ∀ x ∈ Q, x + h ∈ U := fun x hx => by
    simpa only [one_smul] using hseg x hx 1 ⟨zero_le_one, le_rfl⟩
  have hstab (j) := translation_norm_integral_stability hU.measurableSet hQU h hmap hi (hie j)
  have hlim : Tendsto (fun j => ∫ x in Q, ‖g j (x + h) - g j x‖) atTop
      (𝓝 (∫ x in Q, ‖f (x + h) - f x‖)) := by
    apply (tendsto_const_nhds (x := ∫ x in Q, ‖f (x + h) - f x‖)).congr_dist
    have he : Tendsto (fun j => 2 * ∫ x in U, ‖g j x - f x‖) atTop (𝓝 0) := by
      simpa only [Real.norm_eq_abs, mul_zero] using hL1.const_mul 2
    apply squeeze_zero (fun _ => dist_nonneg) (fun j => ?_) he
    rw [Real.dist_eq, abs_sub_comm]
    exact (hstab j).2
  have hb := le_of_tendsto_of_tendsto hlim (hglim.const_mul ‖h‖)
    (Eventually.of_forall fun j => integral_translation_sub_le_of_contDiffOn hU hQ
      ((hg j).of_le (by simp)) h hseg (hstab j).1 (hig j))
  simpa only [Real.norm_eq_abs] using hb

/-- A BV function satisfies the translation estimate on every measurable set whose
segments remain in its open BV domain. -/
theorem translation_estimate_on {n : ℕ}
    {U Q : Set (EuclideanSpace ℝ (Fin n))} (hU : IsOpen U) (hQ : MeasurableSet Q)
    {f : EuclideanSpace ℝ (Fin n) → ℝ} (hf : IsBVOn f U)
    (h : EuclideanSpace ℝ (Fin n))
    (hseg : ∀ x ∈ Q, ∀ t ∈ Icc (0 : ℝ) 1, x + t • h ∈ U) :
    (∫ x in Q, |f (x + h) - f x|) ≤ ‖h‖ * (variation f U).toReal := by
  have hQU : Q ⊆ U := fun x hx => by
    simpa only [zero_smul, add_zero] using hseg x hx 0 ⟨le_rfl, zero_le_one⟩
  have hmap : ∀ x ∈ Q, x + h ∈ U := fun x hx => by
    simpa only [one_smul] using hseg x hx 1 ⟨zero_le_one, le_rfl⟩
  apply translation_estimate_of_finite_variation hU hQ
    (isLocallyBVOn_of_variation_lt_top hU hf.1.locallyIntegrableOn hf.2) hf.2 h hseg
  exact (integrableOn_translate_and_norm_le hU.measurableSet hf.1 h hmap).1.sub (hf.1.mono_set hQU)

/-- Blueprint translation estimate in its local geometric form: the open, relatively
compact region A must contain all displacement segments from the measurable set Q. -/
theorem translation_estimate {n : ℕ}
    {U A Q : Set (EuclideanSpace ℝ (Fin n))} (hA : IsOpen A)
    (hcA : IsCompact (closure A)) (hAU : closure A ⊆ U) (hQ : MeasurableSet Q)
    {f : EuclideanSpace ℝ (Fin n) → ℝ} (hf : IsLocallyBVOn f U)
    (h : EuclideanSpace ℝ (Fin n))
    (hseg : ∀ x ∈ Q, ∀ t ∈ Icc (0 : ℝ) 1, x + t • h ∈ A) :
    (∫ x in Q, |f (x + h) - f x|) ≤ ‖h‖ * (variation f A).toReal := by
  have hif : IntegrableOn f A :=
    (hf.1.integrableOn_compact_subset hAU hcA).mono_set subset_closure
  exact translation_estimate_on hA hQ ⟨hif, hf.2 A hA hcA hAU⟩ h hseg


/-- Euclidean enlargement by radius r: add the closed Euclidean ball to the original set.
For an open original set, this enlargement is open, including at radius zero. -/
def euclideanEnlargement {n : ℕ} (Q : Set (EuclideanSpace ℝ (Fin n))) (r : ℝ) :
    Set (EuclideanSpace ℝ (Fin n)) := Q + closedBall 0 r

lemma isOpen_euclideanEnlargement {n : ℕ}
    {Q : Set (EuclideanSpace ℝ (Fin n))} (hQ : IsOpen Q) (r : ℝ) :
    IsOpen (euclideanEnlargement Q r) := hQ.add_right

lemma isCompact_closure_euclideanEnlargement {n : ℕ}
    {Q : Set (EuclideanSpace ℝ (Fin n))} (hQ : IsCompact (closure Q)) (r : ℝ) :
    IsCompact (closure (euclideanEnlargement Q r)) := by
  have hc := hQ.add (isCompact_closedBall (0 : EuclideanSpace ℝ (Fin n)) r)
  apply hc.of_isClosed_subset isClosed_closure
  exact closure_minimal (add_subset_add subset_closure Subset.rfl) hc.isClosed

/-- Every segment of length at most r starting in Q stays in its radius-r enlargement. -/
lemma add_smul_mem_euclideanEnlargement {n : ℕ}
    {Q : Set (EuclideanSpace ℝ (Fin n))} {x h : EuclideanSpace ℝ (Fin n)}
    {r t : ℝ} (hx : x ∈ Q) (hh : ‖h‖ ≤ r) (ht : t ∈ Icc (0 : ℝ) 1) :
    x + t • h ∈ euclideanEnlargement Q r := by
  refine ⟨x, hx, t • h, ?_, rfl⟩
  rw [mem_closedBall, dist_zero_right, norm_smul, Real.norm_of_nonneg ht.1]
  exact (mul_le_of_le_one_left (norm_nonneg h) ht.2).trans hh


/-- Translation estimate with a specified Euclidean enlargement. Any radius at least
as large as the displacement norm is allowed. -/
theorem translation_estimate_enlargement {n : ℕ}
    {U Q : Set (EuclideanSpace ℝ (Fin n))} (hQ : IsOpen Q)
    (hcQ : IsCompact (closure Q)) {r : ℝ}
    (hQU : closure (euclideanEnlargement Q r) ⊆ U)
    {f : EuclideanSpace ℝ (Fin n) → ℝ} (hf : IsLocallyBVOn f U)
    (h : EuclideanSpace ℝ (Fin n)) (hh : ‖h‖ ≤ r) :
    (∫ x in Q, |f (x + h) - f x|) ≤
      ‖h‖ * (variation f (euclideanEnlargement Q r)).toReal := by
  exact translation_estimate (isOpen_euclideanEnlargement hQ r)
    (isCompact_closure_euclideanEnlargement hcQ r) hQU hQ.measurableSet hf h
    (fun _ hx _ ht => add_smul_mem_euclideanEnlargement hx hh ht)

/-- Blueprint `lem:translation-estimate`. The radius is exactly the displacement norm.
The result holds for all open sets with compact closure, and hence for open cubes. -/
theorem translation_estimate_norm_enlargement {n : ℕ}
    {U Q : Set (EuclideanSpace ℝ (Fin n))} (hQ : IsOpen Q)
    (hcQ : IsCompact (closure Q)) (h : EuclideanSpace ℝ (Fin n))
    (hQU : closure (euclideanEnlargement Q ‖h‖) ⊆ U)
    {f : EuclideanSpace ℝ (Fin n) → ℝ} (hf : IsLocallyBVOn f U) :
    (∫ x in Q, |f (x + h) - f x|) ≤
      ‖h‖ * (variation f (euclideanEnlargement Q ‖h‖)).toReal :=
  translation_estimate_enlargement hQ hcQ hQU hf h le_rfl

/-- The half-open coordinate grid cell with lower corner δ k and side length δ. -/
def gridCell {n : ℕ} (δ : ℝ) (k : Fin n → ℤ) : Set (EuclideanSpace ℝ (Fin n)) :=
  {x | ∀ i, δ * (k i : ℝ) ≤ x i ∧ x i < δ * ((k i : ℝ) + 1)}

/-- The unique cell index selected by coordinate-wise floor when δ is positive. -/
noncomputable def gridIndex {n : ℕ} (δ : ℝ) (x : EuclideanSpace ℝ (Fin n)) : Fin n → ℤ :=
  fun i => ⌊x i / δ⌋

/-- The average over the cell containing x. -/
noncomputable def gridApproximation {n : ℕ} (δ : ℝ)
    (f : EuclideanSpace ℝ (Fin n) → ℝ) (x : EuclideanSpace ℝ (Fin n)) : ℝ :=
  ⨍ y in gridCell δ (gridIndex δ x), f y

lemma mem_gridCell_iff_gridIndex {n : ℕ} {δ : ℝ} (hδ : 0 < δ)
    {k : Fin n → ℤ} {x : EuclideanSpace ℝ (Fin n)} :
    x ∈ gridCell δ k ↔ gridIndex δ x = k := by
  simp only [gridCell, gridIndex, mem_ofPred_eq, funext_iff, Int.floor_eq_iff,
    le_div_iff₀ hδ, div_lt_iff₀ hδ, mul_comm]

lemma mem_gridCell_gridIndex {n : ℕ} {δ : ℝ} (hδ : 0 < δ)
    (x : EuclideanSpace ℝ (Fin n)) : x ∈ gridCell δ (gridIndex δ x) :=
  (mem_gridCell_iff_gridIndex hδ).mpr rfl

lemma gridCell_pairwise_disjoint {n : ℕ} {δ : ℝ} (hδ : 0 < δ) :
    Pairwise (fun k l : Fin n → ℤ => Disjoint (gridCell δ k) (gridCell δ l)) := by
  intro k l hkl
  apply disjoint_left.mpr
  intro x hx hy
  exact hkl ((mem_gridCell_iff_gridIndex hδ).mp hx |>.symm.trans
    ((mem_gridCell_iff_gridIndex hδ).mp hy))

lemma measurableSet_gridCell {n : ℕ} (δ : ℝ) (k : Fin n → ℤ) :
    MeasurableSet (gridCell δ k) := by
  change MeasurableSet {x : EuclideanSpace ℝ (Fin n) |
    ∀ i, δ * (k i : ℝ) ≤ x i ∧ x i < δ * ((k i : ℝ) + 1)}
  simp only [ofPred_forall]
  apply MeasurableSet.iInter
  intro i
  exact (measurableSet_le measurable_const
    (PiLp.continuous_apply 2 (fun _ : Fin n => ℝ) i).measurable).inter
    (measurableSet_lt (PiLp.continuous_apply 2 (fun _ : Fin n => ℝ) i).measurable measurable_const)

lemma measurable_gridIndex {n : ℕ} (δ : ℝ) : Measurable (gridIndex (n := n) δ) := by
  exact Measurable.of_eval fun i =>
    ((PiLp.continuous_apply 2 (fun _ : Fin n => ℝ) i).measurable.div_const δ).floor

lemma measurable_gridApproximation {n : ℕ} (δ : ℝ) (f : EuclideanSpace ℝ (Fin n) → ℝ) :
    Measurable (gridApproximation δ f) :=
  (Measurable.of_discrete (f := fun k : Fin n → ℤ => ⨍ y in gridCell δ k, f y)).comp
    (measurable_gridIndex δ)

lemma volume_gridCell {n : ℕ} (δ : ℝ) (k : Fin n → ℤ) :
    volume (gridCell δ k) = (ENNReal.ofReal δ) ^ n := by
  have heq : gridCell δ k = WithLp.ofLp ⁻¹'
      (univ.pi fun i : Fin n => Ico (δ * (k i : ℝ)) (δ * ((k i : ℝ) + 1))) := by
    ext x
    simp [gridCell]
  rw [heq, (PiLp.volume_preserving_ofLp (Fin n)).measure_preimage
    ((MeasurableSet.pi Set.countable_univ (fun _ _ => measurableSet_Ico)).nullMeasurableSet),
    volume_pi_pi]
  have hlen (i : Fin n) : δ * ((k i : ℝ) + 1) - δ * (k i : ℝ) = δ := by ring
  simp only [Real.volume_Ico, hlen, Finset.prod_const, Finset.card_univ, Fintype.card_fin]

lemma volume_real_gridCell {n : ℕ} {δ : ℝ} (hδ : 0 ≤ δ) (k : Fin n → ℤ) :
    volume.real (gridCell δ k) = δ ^ n := by
  rw [Measure.real, volume_gridCell, ENNReal.toReal_pow, ENNReal.toReal_ofReal hδ]

lemma gridApproximation_eq_inv_mul_integral {n : ℕ} {δ : ℝ} (hδ : 0 < δ)
    (f : EuclideanSpace ℝ (Fin n) → ℝ) (x : EuclideanSpace ℝ (Fin n)) :
    gridApproximation δ f x = (δ ^ n)⁻¹ * ∫ y in gridCell δ (gridIndex δ x), f y := by
  rw [gridApproximation, setAverage_eq, volume_real_gridCell hδ.le, smul_eq_mul]

lemma norm_le_sum_abs_coordinates {n : ℕ} (x : EuclideanSpace ℝ (Fin n)) :
    ‖x‖ ≤ ∑ i, |x i| := by
  have heq : (∑ i, PiLp.single 2 i (x i)) = x := by
    apply PiLp.ext
    intro i
    simp
  calc
    _ = ‖∑ i, PiLp.single 2 i (x i)‖ := congrArg norm heq.symm
    _ ≤ ∑ i, ‖(PiLp.single 2 i (x i) : EuclideanSpace ℝ (Fin n))‖ := norm_sum_le _ _
    _ = _ := by simp only [PiLp.norm_single, Real.norm_eq_abs]

lemma abs_coordinate_sub_le_of_mem_gridCell {n : ℕ} {δ : ℝ} {k : Fin n → ℤ}
    {x y : EuclideanSpace ℝ (Fin n)} (hx : x ∈ gridCell δ k) (hy : y ∈ gridCell δ k)
    (i : Fin n) : |y i - x i| ≤ δ := by
  obtain ⟨hx₁, hx₂⟩ := hx i
  obtain ⟨hy₁, hy₂⟩ := hy i
  rw [abs_le]
  constructor <;> nlinarith

lemma norm_sub_le_of_mem_gridCell {n : ℕ} {δ : ℝ} {k : Fin n → ℤ}
    {x y : EuclideanSpace ℝ (Fin n)} (hx : x ∈ gridCell δ k) (hy : y ∈ gridCell δ k) :
    ‖y - x‖ ≤ (n : ℝ) * δ := by
  calc
    _ ≤ ∑ i, |(y - x) i| := norm_le_sum_abs_coordinates _
    _ ≤ ∑ _i : Fin n, δ :=
      Finset.sum_le_sum fun i _ => abs_coordinate_sub_le_of_mem_gridCell hx hy i
    _ = _ := by simp

/-- Coordinate displacements between two points of one side-δ cell. -/
def gridDisplacements {n : ℕ} (δ : ℝ) : Set (EuclideanSpace ℝ (Fin n)) :=
  {h | ∀ i, |h i| ≤ δ}

lemma measurableSet_gridDisplacements {n : ℕ} (δ : ℝ) :
    MeasurableSet (gridDisplacements (n := n) δ) := by
  change MeasurableSet {h : EuclideanSpace ℝ (Fin n) | ∀ i, |h i| ≤ δ}
  simp only [ofPred_forall]
  exact MeasurableSet.iInter fun i =>
    measurableSet_le (PiLp.continuous_apply 2 (fun _ : Fin n => ℝ) i).abs.measurable
      measurable_const

lemma volume_gridDisplacements {n : ℕ} (δ : ℝ) :
    volume (gridDisplacements (n := n) δ) = (ENNReal.ofReal (2 * δ)) ^ n := by
  have heq : gridDisplacements (n := n) δ = WithLp.ofLp ⁻¹'
      (univ.pi fun _i : Fin n => Icc (-δ) δ) := by
    ext x
    simp [gridDisplacements, abs_le, Pi.le_def, forall_and]
  rw [heq, (PiLp.volume_preserving_ofLp (Fin n)).measure_preimage
    ((MeasurableSet.pi Set.countable_univ (fun _ _ => measurableSet_Icc)).nullMeasurableSet),
    volume_pi_pi]
  simp only [Real.volume_Icc, sub_neg_eq_add, ← two_mul, Finset.prod_const, Finset.card_univ,
    Fintype.card_fin]

lemma volume_real_gridDisplacements {n : ℕ} {δ : ℝ} (hδ : 0 ≤ δ) :
    volume.real (gridDisplacements (n := n) δ) = (2 * δ) ^ n := by
  rw [Measure.real, volume_gridDisplacements, ENNReal.toReal_pow,
    ENNReal.toReal_ofReal (mul_nonneg (by norm_num) hδ)]

lemma norm_le_of_mem_gridDisplacements {n : ℕ} {δ : ℝ}
    {h : EuclideanSpace ℝ (Fin n)} (hh : h ∈ gridDisplacements δ) :
    ‖h‖ ≤ (n : ℝ) * δ := by
  calc
    _ ≤ ∑ i, |h i| := norm_le_sum_abs_coordinates _
    _ ≤ ∑ _i : Fin n, δ := Finset.sum_le_sum fun i _ => hh i
    _ = _ := by simp

lemma sub_mem_gridDisplacements_of_mem_gridCell {n : ℕ} {δ : ℝ} {k : Fin n → ℤ}
    {x y : EuclideanSpace ℝ (Fin n)} (hx : x ∈ gridCell δ k) (hy : y ∈ gridCell δ k) :
    y - x ∈ gridDisplacements δ := fun i => abs_coordinate_sub_le_of_mem_gridCell hx hy i

/-- A bounded set meets only finitely many half-open grid cells of a fixed positive size. -/
lemma finite_gridIndex_image {n : ℕ} {δ : ℝ} (hδ : 0 < δ)
    {Q : Set (EuclideanSpace ℝ (Fin n))} (hQ : Bornology.IsBounded Q) :
    (gridIndex δ '' Q).Finite := by
  obtain ⟨R, _, hQR⟩ := hQ.subset_ball_lt 0 (0 : EuclideanSpace ℝ (Fin n))
  apply (Set.Finite.pi (fun _i : Fin n => Set.finite_Icc ⌊-R / δ⌋ ⌊R / δ⌋)).subset
  rintro k ⟨x, hx, rfl⟩
  intro i _
  have hxR : ‖x‖ ≤ R := (mem_ball_zero_iff.mp (hQR hx)).le
  have hxi : |x i| ≤ R := (PiLp.norm_apply_le x i).trans hxR
  exact ⟨Int.floor_mono (div_le_div_of_nonneg_right (abs_le.mp hxi).1 hδ.le),
    Int.floor_mono (div_le_div_of_nonneg_right (abs_le.mp hxi).2 hδ.le)⟩

lemma finite_gridCells_meeting {n : ℕ} {δ : ℝ} (hδ : 0 < δ)
    {Q : Set (EuclideanSpace ℝ (Fin n))} (hQ : Bornology.IsBounded Q) :
    {k : Fin n → ℤ | (Q ∩ gridCell δ k).Nonempty}.Finite := by
  apply (finite_gridIndex_image hδ hQ).subset
  rintro k ⟨x, hx, hxk⟩
  exact ⟨x, hx, (mem_gridCell_iff_gridIndex hδ).mp hxk⟩

/-- An integrable kernel times a translation difference is integrable on the product space. -/
lemma integrable_translation_difference_integrand {n : ℕ} {F : Type*}
    [NormedAddCommGroup F] [NormedSpace ℝ F]
    {k : EuclideanSpace ℝ (Fin n) → ℝ} {f : EuclideanSpace ℝ (Fin n) → F}
    (hk : Integrable k) (hf : Integrable f) :
    Integrable (fun p : EuclideanSpace ℝ (Fin n) × EuclideanSpace ℝ (Fin n) =>
      k p.2 • (f (p.1 - p.2) - f p.1)) (volume.prod volume) := by
  have hconv := hk.convolution_integrand (ContinuousLinearMap.lsmul ℝ ℝ) hf
  have hprod := (hk.smul_prod hf).swap
  have hs := hconv.sub hprod
  change Integrable (fun p => k p.2 • f (p.1 - p.2) - k p.2 • f p.1)
    (volume.prod volume) at hs
  simpa only [smul_sub] using hs

/-- Integrating translation errors over a finite-measure set of displacements produces
an integrable function and permits Fubini on every restricted spatial region. -/
theorem integrable_translation_average_and_swap {n : ℕ} {F : Type*}
    [NormedAddCommGroup F] [NormedSpace ℝ F]
    {D Q : Set (EuclideanSpace ℝ (Fin n))} (hD : MeasurableSet D) (hfin : volume D < ∞)
    {f : EuclideanSpace ℝ (Fin n) → F} (hf : Integrable f) :
    Integrable (fun x => ∫ h in D, ‖f (x - h) - f x‖) ∧
      (∫ x in Q, ∫ h in D, ‖f (x - h) - f x‖) =
        ∫ h in D, ∫ x in Q, ‖f (x - h) - f x‖ := by
  classical
  let : IsFiniteMeasure (volume.restrict D) := ⟨by simpa using hfin⟩
  let k := D.indicator (fun _ => (1 : ℝ))
  have hc : IntegrableOn (fun _ : EuclideanSpace ℝ (Fin n) => (1 : ℝ)) D := integrable_const 1
  have hk : Integrable k := hc.integrable_indicator hD
  have hp := integrable_translation_difference_integrand hk hf
  have heq (x h : EuclideanSpace ℝ (Fin n)) :
      ‖k h • (f (x - h) - f x)‖ = D.indicator (fun h => ‖f (x - h) - f x‖) h := by
    by_cases hh : h ∈ D <;> simp [k, hh]
  have hi := hp.integral_norm_prod_left
  change Integrable (fun x => ∫ h, ‖k h • (f (x - h) - f x)‖) at hi
  simp_rw [heq, integral_indicator hD] at hi
  refine ⟨hi, ?_⟩
  have hpr := hp.mono_measure (Measure.prod_mono (Measure.restrict_le_self (s := Q)) le_rfl)
  have hswap := integral_integral_swap
    (f := fun x h : EuclideanSpace ℝ (Fin n) => ‖k h • (f (x - h) - f x)‖) hpr.norm
  change (∫ x in Q, ∫ h, ‖k h • (f (x - h) - f x)‖) =
    ∫ h, ∫ x in Q, ‖k h • (f (x - h) - f x)‖ at hswap
  simp_rw [heq, integral_indicator₂, integral_indicator hD] at hswap
  exact hswap

/-- Deviation from a cell average is bounded by the average of pointwise deviations. -/
lemma abs_grid_error_le_cell_average {n : ℕ} {δ : ℝ} (hδ : 0 < δ)
    {f : EuclideanSpace ℝ (Fin n) → ℝ} (x : EuclideanSpace ℝ (Fin n))
    (hf : IntegrableOn f (gridCell δ (gridIndex δ x))) :
    |f x - gridApproximation δ f x| ≤
      (δ ^ n)⁻¹ * ∫ y in gridCell δ (gridIndex δ x), |f x - f y| := by
  have hfin : volume (gridCell δ (gridIndex δ x)) < ∞ := by simp [volume_gridCell]
  let : IsFiniteMeasure (volume.restrict (gridCell δ (gridIndex δ x))) := ⟨by simpa using hfin⟩
  have hc : IntegrableOn (fun _ : EuclideanSpace ℝ (Fin n) => f x)
      (gridCell δ (gridIndex δ x)) := integrable_const _
  have heq : f x - gridApproximation δ f x =
      (δ ^ n)⁻¹ * ∫ y in gridCell δ (gridIndex δ x), (f x - f y) := by
    rw [gridApproximation_eq_inv_mul_integral hδ, integral_sub hc hf, setIntegral_const,
      volume_real_gridCell hδ.le, smul_eq_mul, mul_sub, ← mul_assoc,
      inv_mul_cancel₀ (pow_ne_zero _ hδ.ne'), one_mul]
  rw [heq, abs_mul, abs_of_nonneg (inv_nonneg.mpr (pow_nonneg hδ.le _))]
  apply mul_le_mul_of_nonneg_left _ (inv_nonneg.mpr (pow_nonneg hδ.le _))
  simpa only [Real.norm_eq_abs] using norm_integral_le_integral_norm
    (fun y => f x - f y) (μ := volume.restrict (gridCell δ (gridIndex δ x)))

/-- The averaging error at a point is bounded by translation errors over the displacement box. -/
lemma abs_grid_error_le_translation_average {n : ℕ} {δ : ℝ} (hδ : 0 < δ)
    {f : EuclideanSpace ℝ (Fin n) → ℝ} (hf : Integrable f) (x : EuclideanSpace ℝ (Fin n)) :
    |f x - gridApproximation δ f x| ≤
      (δ ^ n)⁻¹ * ∫ h in gridDisplacements δ, ‖f (x - h) - f x‖ := by
  have hfin : volume (gridDisplacements (n := n) δ) < ∞ := by
    rw [volume_gridDisplacements]
    exact ENNReal.pow_lt_top ENNReal.ofReal_lt_top
  let : IsFiniteMeasure (volume.restrict (gridDisplacements (n := n) δ)) := ⟨by simpa using hfin⟩
  have hc : IntegrableOn (fun _ : EuclideanSpace ℝ (Fin n) => f x)
      (gridDisplacements δ) := integrable_const _
  have hmp : MeasurePreserving (fun h : EuclideanSpace ℝ (Fin n) => x - h) volume volume := by
    simpa only [sub_eq_add_neg, Function.comp_def] using
      (measurePreserving_add_left volume x).comp (Measure.measurePreserving_neg volume)
  have hi := hmp.integrable_comp_of_integrable hf
  change Integrable (fun h => f (x - h)) at hi
  have hp := hmp.restrict_preimage
    (measurableSet_gridCell δ (gridIndex δ x))
  have hs : (fun h => x - h) ⁻¹' gridCell δ (gridIndex δ x) ⊆ gridDisplacements δ := by
    intro h hh
    simpa only [sub_sub_cancel] using
      sub_mem_gridDisplacements_of_mem_gridCell hh (mem_gridCell_gridIndex hδ x)
  apply (abs_grid_error_le_cell_average hδ x hf.integrableOn).trans
  apply mul_le_mul_of_nonneg_left _ (inv_nonneg.mpr (pow_nonneg hδ.le _))
  calc
    _ = ∫ h in (fun h => x - h) ⁻¹' gridCell δ (gridIndex δ x), |f x - f (x - h)| :=
      (hp.integral_comp (Homeomorph.subLeft x).isClosedEmbedding.measurableEmbedding
        (fun y => |f x - f y|)).symm
    _ ≤ ∫ h in gridDisplacements δ, |f x - f (x - h)| :=
      setIntegral_mono_set (hc.sub hi.integrableOn).abs
        (Eventually.of_forall fun _ => abs_nonneg _) (Eventually.of_forall hs)
    _ = _ := by simp only [Real.norm_eq_abs, abs_sub_comm]

/-- The global L¹ averaging error is integrable. On any spatial set, its norm is controlled
by the average of the translation norm integrals over the displacement box. -/
theorem integrable_grid_error_and_bound {n : ℕ} {δ : ℝ} (hδ : 0 < δ)
    {f : EuclideanSpace ℝ (Fin n) → ℝ} (hf : Integrable f)
    (Q : Set (EuclideanSpace ℝ (Fin n))) :
    Integrable (fun x => f x - gridApproximation δ f x) ∧
      (∫ x in Q, |f x - gridApproximation δ f x|) ≤
        (δ ^ n)⁻¹ * ∫ h in gridDisplacements δ, ∫ x in Q, |f (x - h) - f x| := by
  obtain ⟨hi, hswap⟩ := integrable_translation_average_and_swap
    (Q := Q) (measurableSet_gridDisplacements δ) (by
      rw [volume_gridDisplacements]
      exact ENNReal.pow_lt_top ENNReal.ofReal_lt_top) hf
  have hb := hi.const_mul (δ ^ n)⁻¹
  have he : Integrable (fun x => f x - gridApproximation δ f x) := by
    apply hb.mono' (hf.1.sub (measurable_gridApproximation δ f).aestronglyMeasurable)
    exact Eventually.of_forall fun x => by
      simpa only [Real.norm_eq_abs, Pi.sub_apply] using
        abs_grid_error_le_translation_average hδ hf x
  refine ⟨he, ?_⟩
  calc
    _ ≤ ∫ x in Q, (δ ^ n)⁻¹ * ∫ h in gridDisplacements δ, ‖f (x - h) - f x‖ :=
      integral_mono he.abs.integrableOn hb.integrableOn
        (abs_grid_error_le_translation_average hδ hf)
    _ = _ := by rw [integral_const_mul, hswap]; simp only [Real.norm_eq_abs]

lemma integrable_gridApproximation {n : ℕ} {δ : ℝ} (hδ : 0 < δ)
    {f : EuclideanSpace ℝ (Fin n) → ℝ} (hf : Integrable f) :
    Integrable (gridApproximation δ f) := by
  have hi := hf.sub (integrable_grid_error_and_bound hδ hf univ).1
  change Integrable (fun x => f x - (f x - gridApproximation δ f x)) at hi
  simpa only [sub_sub_cancel] using hi

/-- A sufficient explicit dimension constant for the half-open grid approximation. -/
def gridApproximationConstant (n : ℕ) : ℝ := (n : ℝ) * (2 : ℝ) ^ n

lemma gridApproximationConstant_nonneg (n : ℕ) : 0 ≤ gridApproximationConstant n := by
  unfold gridApproximationConstant
  positivity

lemma natCast_le_gridApproximationConstant (n : ℕ) : (n : ℝ) ≤ gridApproximationConstant n := by
  unfold gridApproximationConstant
  simpa only [mul_one] using
    mul_le_mul_of_nonneg_left (one_le_pow₀ (by norm_num : (1 : ℝ) ≤ 2)) (Nat.cast_nonneg n)

lemma gridApproximationConstant_pos {n : ℕ} (hn : 0 < n) : 0 < gridApproximationConstant n :=
  (Nat.cast_pos.mpr hn).trans_le (natCast_le_gridApproximationConstant n)

lemma euclideanEnlargement_mono_radius {n : ℕ} (Q : Set (EuclideanSpace ℝ (Fin n)))
    {r R : ℝ} (hr : r ≤ R) : euclideanEnlargement Q r ⊆ euclideanEnlargement Q R :=
  add_subset_add Subset.rfl (closedBall_subset_closedBall hr)

lemma gridCell_gridIndex_subset_enlargement {n : ℕ} {δ : ℝ} (hδ : 0 < δ)
    {Q : Set (EuclideanSpace ℝ (Fin n))} {x : EuclideanSpace ℝ (Fin n)} (hx : x ∈ Q) :
    gridCell δ (gridIndex δ x) ⊆ euclideanEnlargement Q ((n : ℝ) * δ) := by
  intro y hy
  refine ⟨x, hx, y - x, ?_, by abel_nf⟩
  simpa only [mem_closedBall, dist_zero_right] using
    norm_sub_le_of_mem_gridCell (mem_gridCell_gridIndex hδ x) hy

lemma gridApproximation_congr_on_cell {n : ℕ} {δ : ℝ} (hδ : 0 < δ)
    {f g : EuclideanSpace ℝ (Fin n) → ℝ} {x : EuclideanSpace ℝ (Fin n)}
    (hfg : ∀ y ∈ gridCell δ (gridIndex δ x), f y = g y) :
    gridApproximation δ f x = gridApproximation δ g x := by
  rw [gridApproximation_eq_inv_mul_integral hδ, gridApproximation_eq_inv_mul_integral hδ]
  congr 1
  exact setIntegral_congr_fun (measurableSet_gridCell δ (gridIndex δ x)) hfg

/-- Compact localization makes both the grid average and its error integrable on Q,
independently of whether the variation is finite. -/
theorem integrableOn_gridApproximation_in_region {n : ℕ} {δ : ℝ} (hδ : 0 < δ)
    {U A Q : Set (EuclideanSpace ℝ (Fin n))} (hA : MeasurableSet A)
    (hcA : IsCompact (closure A)) (hAU : closure A ⊆ U) (hQ : MeasurableSet Q)
    (hreach : euclideanEnlargement Q ((n : ℝ) * δ) ⊆ A)
    {f : EuclideanSpace ℝ (Fin n) → ℝ} (hf : LocallyIntegrableOn f U) :
    IntegrableOn (gridApproximation δ f) Q ∧
      IntegrableOn (fun x => f x - gridApproximation δ f x) Q := by
  let F := A.indicator f
  have hif : IntegrableOn f A := (hf.integrableOn_compact_subset hAU hcA).mono_set subset_closure
  have hiF : Integrable F := hif.integrable_indicator hA
  have hcells (x) (hx : x ∈ Q) : gridCell δ (gridIndex δ x) ⊆ A :=
    (gridCell_gridIndex_subset_enlargement hδ hx).trans hreach
  have hQU : Q ⊆ A := fun x hx => hcells x hx (mem_gridCell_gridIndex hδ x)
  have havg (x) (hx : x ∈ Q) : gridApproximation δ F x = gridApproximation δ f x :=
    gridApproximation_congr_on_cell hδ fun y hy => indicator_of_mem (hcells x hx hy) f
  have he : IntegrableOn (fun x => f x - gridApproximation δ f x) Q := by
    apply (integrable_grid_error_and_bound hδ hiF Q).1.integrableOn.congr
    filter_upwards [ae_restrict_mem hQ] with x hx
    rw [havg x hx, show F x = f x from indicator_of_mem (hQU hx) f]
  refine ⟨?_, he⟩
  have hi := (hif.mono_set hQU).sub he
  change IntegrableOn (fun x => f x - (f x - gridApproximation δ f x)) Q at hi
  simpa only [sub_sub_cancel] using hi

/-- The grid error bound for a globally integrable function of finite variation on a
region containing the displacement enlargement. -/
theorem grid_approximation_of_integrable {n : ℕ} {δ : ℝ} (hδ : 0 < δ)
    {A Q : Set (EuclideanSpace ℝ (Fin n))} (hA : IsOpen A) (hQ : MeasurableSet Q)
    (hreach : euclideanEnlargement Q ((n : ℝ) * δ) ⊆ A)
    {f : EuclideanSpace ℝ (Fin n) → ℝ} (hf : Integrable f) (hfA : IsBVOn f A) :
    (∫ x in Q, |f x - gridApproximation δ f x|) ≤
      gridApproximationConstant n * δ * (variation f A).toReal := by
  have hfin : volume (gridDisplacements (n := n) δ) < ∞ := by
    rw [volume_gridDisplacements]
    exact ENNReal.pow_lt_top ENNReal.ofReal_lt_top
  let : IsFiniteMeasure (volume.restrict (gridDisplacements (n := n) δ)) := ⟨by simpa using hfin⟩
  have htrans (h : EuclideanSpace ℝ (Fin n)) (hh : h ∈ gridDisplacements δ) :
      (∫ x in Q, |f (x - h) - f x|) ≤ ((n : ℝ) * δ) * (variation f A).toReal := by
    have hs : ∀ x ∈ Q, ∀ t ∈ Icc (0 : ℝ) 1, x + t • (-h) ∈ A := by
      intro x hx t ht
      exact hreach (add_smul_mem_euclideanEnlargement hx
        (by simpa only [norm_neg] using norm_le_of_mem_gridDisplacements hh) ht)
    have hb := translation_estimate_on hA hQ hfA (-h) hs
    simp only [← sub_eq_add_neg, norm_neg] at hb
    exact hb.trans (mul_le_mul_of_nonneg_right (norm_le_of_mem_gridDisplacements hh)
      ENNReal.toReal_nonneg)
  calc
    _ ≤ (δ ^ n)⁻¹ * ∫ h in gridDisplacements δ, ∫ x in Q, |f (x - h) - f x| :=
      (integrable_grid_error_and_bound hδ hf Q).2
    _ ≤ (δ ^ n)⁻¹ * ∫ _h in gridDisplacements (n := n) δ,
        ((n : ℝ) * δ) * (variation f A).toReal := by
      apply mul_le_mul_of_nonneg_left _ (inv_nonneg.mpr (pow_nonneg hδ.le _))
      apply integral_mono_of_nonneg
        (Eventually.of_forall fun _ => integral_nonneg fun _ => abs_nonneg _) (integrable_const _)
      exact (ae_restrict_mem (measurableSet_gridDisplacements δ)).mono fun h hh => htrans h hh
    _ = _ := by
      rw [setIntegral_const, smul_eq_mul, volume_real_gridDisplacements hδ.le, mul_pow]
      unfold gridApproximationConstant
      calc
        _ = ((δ ^ n)⁻¹ * δ ^ n) * ((n : ℝ) * 2 ^ n * δ * (variation f A).toReal) := by ring
        _ = _ := by rw [inv_mul_cancel₀ (pow_ne_zero _ hδ.ne'), one_mul]

/-- Localization of grid approximation. Only local integrability of the original function
is needed, together with finite variation on the relatively compact enlarged region. -/
theorem grid_approximation_in_region {n : ℕ} {δ : ℝ} (hδ : 0 < δ)
    {U A Q : Set (EuclideanSpace ℝ (Fin n))} (hA : IsOpen A)
    (hcA : IsCompact (closure A)) (hAU : closure A ⊆ U) (hQ : MeasurableSet Q)
    (hreach : euclideanEnlargement Q ((n : ℝ) * δ) ⊆ A)
    {f : EuclideanSpace ℝ (Fin n) → ℝ} (hf : LocallyIntegrableOn f U)
    (hfin : variation f A < ∞) :
    (∫ x in Q, |f x - gridApproximation δ f x|) ≤
      gridApproximationConstant n * δ * (variation f A).toReal := by
  let F := A.indicator f
  have hif : IntegrableOn f A := (hf.integrableOn_compact_subset hAU hcA).mono_set subset_closure
  have hiF : Integrable F := hif.integrable_indicator hA.measurableSet
  have hvar : variation F A = variation f A :=
    variation_congr_ae A (indicator_ae_eq_restrict hA.measurableSet)
  have hF : IsBVOn F A := ⟨hiF.integrableOn, hvar ▸ hfin⟩
  have hcells (x) (hx : x ∈ Q) : gridCell δ (gridIndex δ x) ⊆ A :=
    (gridCell_gridIndex_subset_enlargement hδ hx).trans hreach
  have havg (x) (hx : x ∈ Q) : gridApproximation δ F x = gridApproximation δ f x :=
    gridApproximation_congr_on_cell hδ fun y hy => indicator_of_mem (hcells x hx hy) f
  calc
    _ = ∫ x in Q, |F x - gridApproximation δ F x| := by
      apply setIntegral_congr_fun hQ
      intro x hx
      change |f x - gridApproximation δ f x| = |F x - gridApproximation δ F x|
      rw [havg x hx]
      exact congrArg (fun v => |v - gridApproximation δ f x|)
        (indicator_of_mem (hcells x hx (mem_gridCell_gridIndex hδ x)) f).symm
    _ ≤ _ := by
      simpa only [hvar] using grid_approximation_of_integrable hδ hA hQ hreach hiF hF

/-- Finite-variation version of the blueprint grid bound, with C_n = n 2^n. -/
theorem grid_approximation_of_finite_variation {n : ℕ} {δ : ℝ} (hδ : 0 < δ)
    {U Q : Set (EuclideanSpace ℝ (Fin n))} (hQ : IsOpen Q) (hcQ : IsCompact (closure Q))
    (hQU : closure (euclideanEnlargement Q (gridApproximationConstant n * δ)) ⊆ U)
    {f : EuclideanSpace ℝ (Fin n) → ℝ} (hf : LocallyIntegrableOn f U)
    (hfin : variation f (euclideanEnlargement Q (gridApproximationConstant n * δ)) < ∞) :
    (∫ x in Q, |f x - gridApproximation δ f x|) ≤
      gridApproximationConstant n * δ *
        (variation f (euclideanEnlargement Q (gridApproximationConstant n * δ))).toReal := by
  exact grid_approximation_in_region hδ (isOpen_euclideanEnlargement hQ _)
    (isCompact_closure_euclideanEnlargement hcQ _) hQU hQ.measurableSet
    (euclideanEnlargement_mono_radius Q
      (mul_le_mul_of_nonneg_right (natCast_le_gridApproximationConstant n) hδ.le)) hf hfin

theorem integrableOn_gridApproximation {n : ℕ} {δ : ℝ} (hδ : 0 < δ)
    {U Q : Set (EuclideanSpace ℝ (Fin n))} (hQ : IsOpen Q) (hcQ : IsCompact (closure Q))
    (hQU : closure (euclideanEnlargement Q (gridApproximationConstant n * δ)) ⊆ U)
    {f : EuclideanSpace ℝ (Fin n) → ℝ} (hf : LocallyIntegrableOn f U) :
    IntegrableOn (gridApproximation δ f) Q ∧
      IntegrableOn (fun x => f x - gridApproximation δ f x) Q :=
  integrableOn_gridApproximation_in_region hδ (isOpen_euclideanEnlargement hQ _).measurableSet
    (isCompact_closure_euclideanEnlargement hcQ _) hQU hQ.measurableSet
    (euclideanEnlargement_mono_radius Q
      (mul_le_mul_of_nonneg_right (natCast_le_gridApproximationConstant n) hδ.le)) hf

/-- Blueprint `lem:grid-approx`, including infinite variation. The hypotheses explicitly
place the enlarged cube in a domain of local integrability. -/
theorem grid_approximation {n : ℕ} (hn : 0 < n) {δ : ℝ} (hδ : 0 < δ)
    {U Q : Set (EuclideanSpace ℝ (Fin n))} (hQ : IsOpen Q) (hcQ : IsCompact (closure Q))
    (hQU : closure (euclideanEnlargement Q (gridApproximationConstant n * δ)) ⊆ U)
    {f : EuclideanSpace ℝ (Fin n) → ℝ} (hf : LocallyIntegrableOn f U) :
    eLpNorm (fun x => f x - gridApproximation δ f x) 1 (volume.restrict Q) ≤
      ENNReal.ofReal (gridApproximationConstant n * δ) *
        variation f (euclideanEnlargement Q (gridApproximationConstant n * δ)) := by
  by_cases hfin : variation f (euclideanEnlargement Q (gridApproximationConstant n * δ)) < ∞
  · rw [eLpNorm_one_eq_lintegral_enorm
        (integrableOn_gridApproximation hδ hQ hcQ hQU hf).2.aestronglyMeasurable,
      ← ofReal_integral_norm_eq_lintegral_enorm (integrableOn_gridApproximation hδ hQ hcQ hQU hf).2]
    have hb := ENNReal.ofReal_le_ofReal
      (grid_approximation_of_finite_variation hδ hQ hcQ hQU hf hfin)
    rw [ENNReal.ofReal_mul (mul_nonneg (gridApproximationConstant_nonneg n) hδ.le),
      ENNReal.ofReal_toReal hfin.ne] at hb
    simpa only [Real.norm_eq_abs] using hb
  · have hv : variation f (euclideanEnlargement Q (gridApproximationConstant n * δ)) = ∞ :=
      top_le_iff.mp (le_of_not_gt hfin)
    have hc : ENNReal.ofReal (gridApproximationConstant n * δ) ≠ 0 :=
      ne_of_gt (ENNReal.ofReal_pos.mpr (mul_pos (gridApproximationConstant_pos hn) hδ))
    simp [hv, hc]

lemma abs_grid_average_le_integral_norm {n : ℕ} {δ : ℝ} (hδ : 0 < δ)
    (k : Fin n → ℤ) {A : Set (EuclideanSpace ℝ (Fin n))}
    {f : EuclideanSpace ℝ (Fin n) → ℝ} (hf : IntegrableOn f A)
    (hcell : gridCell δ k ⊆ A) :
    |⨍ y in gridCell δ k, f y| ≤ (δ ^ n)⁻¹ * ∫ y in A, |f y| := by
  rw [setAverage_eq, volume_real_gridCell hδ.le, smul_eq_mul, abs_mul,
    abs_of_nonneg (inv_nonneg.mpr (pow_nonneg hδ.le _))]
  apply mul_le_mul_of_nonneg_left _ (inv_nonneg.mpr (pow_nonneg hδ.le _))
  calc
    _ ≤ ∫ y in gridCell δ k, |f y| := by
      simpa only [Real.norm_eq_abs] using norm_integral_le_integral_norm (μ :=
        volume.restrict (gridCell δ k)) f
    _ ≤ _ := setIntegral_mono_set hf.abs (Eventually.of_forall fun _ => abs_nonneg _)
      (Eventually.of_forall hcell)

/-- The grid approximations of a sequence with uniformly bounded coefficients have a
uniformly convergent subsequence on each bounded set. This is finite-dimensional
compactness of the vectors of cell averages. -/
theorem exists_subseq_gridApproximation_tendstoUniformlyOn {n : ℕ} {δ : ℝ} (hδ : 0 < δ)
    {Q : Set (EuclideanSpace ℝ (Fin n))} (hQ : Bornology.IsBounded Q)
    (f : ℕ → EuclideanSpace ℝ (Fin n) → ℝ) {C : ℝ} (hC : 0 ≤ C)
    (hb : ∀ j k, k ∈ gridIndex δ '' Q → |⨍ y in gridCell δ k, f j y| ≤ C) :
    ∃ g : EuclideanSpace ℝ (Fin n) → ℝ, ∃ σ : ℕ → ℕ, StrictMono σ ∧
      TendstoUniformlyOn (fun j => gridApproximation δ (f (σ j))) g atTop Q := by
  classical
  let I := gridIndex δ '' Q
  have hI : I.Finite := finite_gridIndex_image hδ hQ
  let : Fintype I := hI.fintype
  let v : ℕ → I → ℝ := fun j k => ⨍ y in gridCell δ k.val, f j y
  have hv (j : ℕ) : v j ∈ closedBall (0 : I → ℝ) C := by
    rw [mem_closedBall, dist_zero_right]
    exact (pi_norm_le_iff_of_nonneg hC).mpr fun k => by
      simpa only [Real.norm_eq_abs] using hb j k.val k.property
  obtain ⟨a, _, σ, hσ, ha⟩ := (isCompact_closedBall (0 : I → ℝ) C).tendsto_subseq hv
  let g : EuclideanSpace ℝ (Fin n) → ℝ := fun x =>
    if hx : gridIndex δ x ∈ I then a ⟨gridIndex δ x, hx⟩ else 0
  refine ⟨g, σ, hσ, ?_⟩
  rw [Metric.tendstoUniformlyOn_iff]
  intro ε hε
  have hev := (Metric.tendsto_atTop.mp ha) ε hε
  obtain ⟨N, hN⟩ := hev
  filter_upwards [eventually_ge_atTop N] with j hj x hx
  have hi : gridIndex δ x ∈ I := mem_image_of_mem _ hx
  have heq : g x = a ⟨gridIndex δ x, hi⟩ := dite_eq_left hi
  rw [heq, Real.dist_eq]
  have hcoord := norm_le_pi_norm (v (σ j) - a) (⟨gridIndex δ x, hi⟩ : I)
  have hdist := hN j hj
  rw [dist_eq_norm] at hdist
  apply lt_of_le_of_lt _ hdist
  simpa only [Pi.sub_apply, Real.norm_eq_abs, abs_sub_comm, v, gridApproximation,
    Function.comp_def] using hcoord

/-- A uniform L¹ bound on a region containing all relevant cells supplies the
coefficient bound needed for fixed-grid subsequence extraction. -/
theorem exists_subseq_gridApproximation_of_integral_bound {n : ℕ} {δ : ℝ} (hδ : 0 < δ)
    {A Q : Set (EuclideanSpace ℝ (Fin n))} (hQ : Bornology.IsBounded Q)
    (hreach : euclideanEnlargement Q ((n : ℝ) * δ) ⊆ A)
    (f : ℕ → EuclideanSpace ℝ (Fin n) → ℝ) (hf : ∀ j, IntegrableOn (f j) A)
    {C : ℝ} (hC : 0 ≤ C) (hb : ∀ j, (∫ y in A, |f j y|) ≤ C) :
    ∃ g : EuclideanSpace ℝ (Fin n) → ℝ, ∃ σ : ℕ → ℕ, StrictMono σ ∧
      TendstoUniformlyOn (fun j => gridApproximation δ (f (σ j))) g atTop Q := by
  refine exists_subseq_gridApproximation_tendstoUniformlyOn hδ hQ f
    (C := (δ ^ n)⁻¹ * C) (mul_nonneg (inv_nonneg.mpr (pow_nonneg hδ.le n)) hC) ?_
  intro j k hk
  obtain ⟨x, hx, rfl⟩ := hk
  exact (abs_grid_average_le_integral_norm hδ _ (hf j)
    ((gridCell_gridIndex_subset_enlargement hδ hx).trans hreach)).trans
      (mul_le_mul_of_nonneg_left (hb j) (inv_nonneg.mpr (pow_nonneg hδ.le _)))

/-- A single subsequence works for a countable family of grids and bounded spatial sets.
The countable product of compact finite-dimensional coefficient balls performs the
diagonal extraction. -/
theorem exists_subseq_gridApproximation_countable {ι : Type*} [Countable ι] {n : ℕ}
    (δ : ι → ℝ) (hδ : ∀ m, 0 < δ m)
    (Q : ι → Set (EuclideanSpace ℝ (Fin n))) (hQ : ∀ m, Bornology.IsBounded (Q m))
    (f : ℕ → EuclideanSpace ℝ (Fin n) → ℝ) (C : ι → ℝ) (hC : ∀ m, 0 ≤ C m)
    (hb : ∀ m j k, k ∈ gridIndex (δ m) '' Q m →
      |⨍ y in gridCell (δ m) k, f j y| ≤ C m) :
    ∃ g : ι → EuclideanSpace ℝ (Fin n) → ℝ, ∃ σ : ℕ → ℕ, StrictMono σ ∧
      ∀ m, TendstoUniformlyOn (fun j => gridApproximation (δ m) (f (σ j)))
        (g m) atTop (Q m) := by
  classical
  let I (m : ι) := gridIndex (δ m) '' Q m
  let (m : ι) : Fintype (I m) := (finite_gridIndex_image (hδ m) (hQ m)).fintype
  let B (m : ι) := closedBall (0 : I m → ℝ) (C m)
  let (m : ι) : CompactSpace (B m) :=
    isCompact_iff_compactSpace.mp (isCompact_closedBall _ _)
  let v : ℕ → (m : ι) → I m → ℝ := fun j m k => ⨍ y in gridCell (δ m) k.val, f j y
  have hv (j : ℕ) (m : ι) : v j m ∈ B m := by
    change ‖v j m - 0‖ ≤ C m
    rw [sub_zero]
    exact (pi_norm_le_iff_of_nonneg (hC m)).mpr fun k => by
      simpa only [Real.norm_eq_abs] using hb m j k.val k.property
  let u (j : ℕ) (m : ι) : B m := ⟨v j m, hv j m⟩
  obtain ⟨a, σ, hσ, ha⟩ := CompactSpace.tendsto_subseq u
  let g (m : ι) (x : EuclideanSpace ℝ (Fin n)) : ℝ :=
    if hx : gridIndex (δ m) x ∈ I m then (a m).val ⟨gridIndex (δ m) x, hx⟩ else 0
  refine ⟨g, σ, hσ, ?_⟩
  intro m
  have hc : Continuous (fun b : (m : ι) → B m => (b m).val) :=
    continuous_subtype_val.comp (continuous_apply m)
  have ham : Tendsto (fun j => v (σ j) m) atTop (𝓝 (a m).val) :=
    hc.continuousAt.tendsto.comp ha
  rw [Metric.tendstoUniformlyOn_iff]
  intro ε hε
  obtain ⟨N, hN⟩ := (Metric.tendsto_atTop.mp ham) ε hε
  filter_upwards [eventually_ge_atTop N] with j hj x hx
  have hi : gridIndex (δ m) x ∈ I m := mem_image_of_mem _ hx
  have heq : g m x = (a m).val ⟨gridIndex (δ m) x, hi⟩ := dite_eq_left hi
  rw [heq, Real.dist_eq]
  have hcoord := norm_le_pi_norm (v (σ j) m - (a m).val) (⟨gridIndex (δ m) x, hi⟩ : I m)
  have hdist := hN j hj
  rw [dist_eq_norm] at hdist
  apply lt_of_le_of_lt _ hdist
  simpa only [Pi.sub_apply, Real.norm_eq_abs, abs_sub_comm, v, gridApproximation] using hcoord


lemma dist_toL1_eq_integral_norm_sub {α : Type*} [MeasurableSpace α] {μ : Measure α}
    {f g : α → ℝ} (hf : Integrable f μ) (hg : Integrable g μ) :
    dist (hf.toL1 f) (hg.toL1 g) = ∫ x, ‖f x - g x‖ ∂μ := by
  rw [L1.dist_eq_integral_dist]
  apply integral_congr_ae
  filter_upwards [hf.coeFn_toL1, hg.coeFn_toL1] with x hx hy
  rw [hx, hy, dist_eq_norm]

/-- Uniform convergence on a set of finite measure makes the corresponding L¹
classes Cauchy. Integrability is only required of the members of the sequence. -/
theorem cauchySeq_toL1_of_tendstoUniformlyOn {α : Type*} [MeasurableSpace α]
    {μ : Measure α} {Q : Set α} (hQ : MeasurableSet Q) (hfin : μ Q < ∞)
    (f : ℕ → α → ℝ) (hf : ∀ j, IntegrableOn (f j) Q μ) {g : α → ℝ}
    (hg : TendstoUniformlyOn f g atTop Q) :
    CauchySeq (fun j => (hf j).toL1 (f j)) := by
  let : IsFiniteMeasure (μ.restrict Q) := ⟨by simpa using hfin⟩
  rw [Metric.cauchySeq_iff]
  intro ε hε
  let η := ε / (4 * (μ.real Q + 1))
  have hη : 0 < η := div_pos hε (by positivity)
  obtain ⟨N, hN⟩ := eventually_atTop.mp ((Metric.tendstoUniformlyOn_iff.mp hg) η hη)
  refine ⟨N, ?_⟩
  intro j hj k hk
  rw [dist_toL1_eq_integral_norm_sub (hf j) (hf k)]
  have hdist (x) (hx : x ∈ Q) : ‖f j x - f k x‖ ≤ 2 * η := by
    have h1 := hN j hj x hx
    have h2 := hN k hk x hx
    have ht := dist_triangle (f j x) (g x) (f k x)
    rw [dist_comm (f j x) (g x)] at ht
    rw [← dist_eq_norm]
    linarith
  calc
    _ ≤ ∫ _x in Q, 2 * η ∂μ :=
      integral_mono_ae ((hf j).sub (hf k)).norm (integrable_const _)
        ((ae_restrict_mem hQ).mono fun x hx => hdist x hx)
    _ = μ.real Q * (2 * η) := by rw [setIntegral_const, smul_eq_mul]
    _ < ε := by
      dsimp [η]
      have hv : 0 ≤ μ.real Q := measureReal_nonneg
      have hd : 0 < μ.real Q + 1 := by positivity
      field_simp
      nlinarith

/-- Uniformly small errors transfer the Cauchy property from every fixed
approximation scale to the original sequence. -/
theorem cauchySeq_of_uniform_approximation {X : Type*} [PseudoMetricSpace X]
    (f : ℕ → X) (a : ℕ → ℕ → X) (e : ℕ → ℝ) (he : Tendsto e atTop (𝓝 0))
    (hb : ∀ m j, dist (f j) (a m j) ≤ e m) (ha : ∀ m, CauchySeq (a m)) :
    CauchySeq f := by
  rw [Metric.cauchySeq_iff]
  intro ε hε
  obtain ⟨m, hm⟩ := (he.eventually (gt_mem_nhds (by linarith : (0 : ℝ) < ε / 3))).exists
  obtain ⟨N, hN⟩ := Metric.cauchySeq_iff.mp (ha m) (ε / 3) (by linarith)
  refine ⟨N, ?_⟩
  intro j hj k hk
  have ht := dist_triangle4 (f j) (a m j) (a m k) (f k)
  have hjb := hb m j
  have hkb := hb m k
  have hmid := hN j hj k hk
  rw [dist_comm (a m k) (f k)] at ht
  linarith


lemma exists_l1_limit_of_cauchySeq_toL1 {α : Type*} [MeasurableSpace α] {μ : Measure α}
    (f : ℕ → α → ℝ) (hf : ∀ j, Integrable (f j) μ)
    (hc : CauchySeq (fun j => (hf j).toL1 (f j))) :
    ∃ g : α → ℝ, Integrable g μ ∧
      Tendsto (fun j => ∫ x, |f j x - g x| ∂μ) atTop (𝓝 0) := by
  obtain ⟨g, hg⟩ := cauchySeq_tendsto_of_complete hc
  refine ⟨g, L1.integrable_coeFn g, ?_⟩
  have ht := (tendsto_iff_dist_tendsto_zero.mp hg)
  convert ht using 1
  ext j
  rw [L1.dist_eq_integral_dist]
  apply integral_congr_ae
  filter_upwards [(hf j).coeFn_toL1] with x hx
  rw [hx, Real.dist_eq]

/-- Grid compactness on a fixed bounded measurable set. The grid scales tend to
zero, and all their cells meeting Q remain in the open region with uniform bounds. -/
theorem exists_subseq_l1_of_grid_scales {n : ℕ}
    {A Q : Set (EuclideanSpace ℝ (Fin n))} (hA : IsOpen A)
    (hQ : MeasurableSet Q) (hbQ : Bornology.IsBounded Q)
    (δ : ℕ → ℝ) (hδ : ∀ m, 0 < δ m) (htδ : Tendsto δ atTop (𝓝 0))
    (hreach : ∀ m, euclideanEnlargement Q ((n : ℝ) * δ m) ⊆ A)
    (f : ℕ → EuclideanSpace ℝ (Fin n) → ℝ) (hf : ∀ j, Integrable (f j))
    (hfA : ∀ j, IsBVOn (f j) A) {L V : ℝ} (hL : 0 ≤ L)
    (hLbound : ∀ j, (∫ x in A, |f j x|) ≤ L)
    (hVbound : ∀ j, (variation (f j) A).toReal ≤ V) :
    ∃ g : EuclideanSpace ℝ (Fin n) → ℝ, ∃ σ : ℕ → ℕ, StrictMono σ ∧
      IntegrableOn g Q ∧
      Tendsto (fun j => ∫ x in Q, |f (σ j) x - g x|) atTop (𝓝 0) := by
  let C (m : ℕ) := ((δ m) ^ n)⁻¹ * L
  have hC (m) : 0 ≤ C m := mul_nonneg (inv_nonneg.mpr (pow_nonneg (hδ m).le _)) hL
  have hc (m j : ℕ) (k : Fin n → ℤ) (hk : k ∈ gridIndex (δ m) '' Q) :
      |⨍ y in gridCell (δ m) k, f j y| ≤ C m := by
    obtain ⟨x, hx, rfl⟩ := hk
    exact (abs_grid_average_le_integral_norm (hδ m) _ (hfA j).1
      ((gridCell_gridIndex_subset_enlargement (hδ m) hx).trans (hreach m))).trans
        (mul_le_mul_of_nonneg_left (hLbound j)
          (inv_nonneg.mpr (pow_nonneg (hδ m).le _)))
  obtain ⟨a, σ, hσ, ha⟩ := exists_subseq_gridApproximation_countable
    δ hδ (fun _ => Q) (fun _ => hbQ) f C hC hc
  have hi (j) : IntegrableOn (f (σ j)) Q := (hf (σ j)).integrableOn
  have hia (m j) : IntegrableOn (gridApproximation (δ m) (f (σ j))) Q :=
    (integrable_gridApproximation (hδ m) (hf (σ j))).integrableOn
  let u (j) := (hi j).toL1 (f (σ j))
  let v (m j) := (hia m j).toL1 (gridApproximation (δ m) (f (σ j)))
  have hcv (m) : CauchySeq (v m) :=
    cauchySeq_toL1_of_tendstoUniformlyOn hQ hbQ.measure_lt_top _ (hia m) (ha m)
  let e (m) := gridApproximationConstant n * δ m * V
  have he : Tendsto e atTop (𝓝 0) := by
    simpa only [mul_zero, zero_mul] using (htδ.const_mul (gridApproximationConstant n)).mul_const V
  have hdist (m j) : dist (u j) (v m j) ≤ e m := by
    rw [dist_toL1_eq_integral_norm_sub (hi j) (hia m j)]
    simp only [Real.norm_eq_abs]
    exact (grid_approximation_of_integrable (hδ m) hA hQ (hreach m)
      (hf (σ j)) (hfA (σ j))).trans
        (mul_le_mul_of_nonneg_left (hVbound (σ j))
          (mul_nonneg (gridApproximationConstant_nonneg n) (hδ m).le))
  have hcu := cauchySeq_of_uniform_approximation u v e he hdist hcv
  obtain ⟨g, hig, htg⟩ := exists_l1_limit_of_cauchySeq_toL1 (fun j => f (σ j)) hi hcu
  exact ⟨g, σ, hσ, hig, htg⟩

/-- Compact containment supplies a positive radius for all the grid cells used in
local compactness. -/
lemma exists_pos_enlargement_subset {n : ℕ} {A Q : Set (EuclideanSpace ℝ (Fin n))}
    (hA : IsOpen A) (hcQ : IsCompact (closure Q)) (hQA : closure Q ⊆ A) :
    ∃ r > 0, euclideanEnlargement Q r ⊆ A := by
  obtain ⟨r, hr, hsub⟩ := hcQ.exists_cthickening_subset_open hA hQA
  refine ⟨r, hr, ?_⟩
  rintro y ⟨x, hx, z, hz, rfl⟩
  apply hsub
  apply closedBall_subset_cthickening (subset_closure hx) r
  simpa only [mem_closedBall, dist_eq_norm, add_sub_cancel_left, sub_zero] using hz

/-- The fixed-domain part of local BV compactness: uniform L¹ and variation
bounds on A give an L¹-convergent subsequence on every relatively compact
measurable Q in A. No global integrability of the original functions is assumed. -/
theorem exists_subseq_l1_of_bv_bounds {n : ℕ}
    {A Q : Set (EuclideanSpace ℝ (Fin n))} (hA : IsOpen A) (hQ : MeasurableSet Q)
    (hcQ : IsCompact (closure Q)) (hQA : closure Q ⊆ A)
    (f : ℕ → EuclideanSpace ℝ (Fin n) → ℝ) (hf : ∀ j, IsBVOn (f j) A)
    {L V : ℝ} (hL : 0 ≤ L) (hLbound : ∀ j, (∫ x in A, |f j x|) ≤ L)
    (hVbound : ∀ j, (variation (f j) A).toReal ≤ V) :
    ∃ g : EuclideanSpace ℝ (Fin n) → ℝ, ∃ σ : ℕ → ℕ, StrictMono σ ∧
      IntegrableOn g Q ∧
      Tendsto (fun j => ∫ x in Q, |f (σ j) x - g x|) atTop (𝓝 0) := by
  obtain ⟨r, hr, hreach⟩ := exists_pos_enlargement_subset hA hcQ hQA
  let δ (m : ℕ) := (r / ((n : ℝ) + 1)) * (1 / ((m : ℝ) + 1))
  have hδ (m) : 0 < δ m := by dsimp [δ]; positivity
  have htδ : Tendsto δ atTop (𝓝 0) := by
    simpa only [mul_zero] using
      (tendsto_one_div_add_atTop_nhds_zero_nat (𝕜 := ℝ)).const_mul (r / ((n : ℝ) + 1))
  have hreachδ (m) : euclideanEnlargement Q ((n : ℝ) * δ m) ⊆ A := by
    apply Subset.trans (euclideanEnlargement_mono_radius Q ?_) hreach
    have hfrac : 1 / ((m : ℝ) + 1) ≤ 1 := by
      rw [div_le_one (by positivity : (0 : ℝ) < (m : ℝ) + 1)]
      linarith [show (0 : ℝ) ≤ (m : ℝ) from Nat.cast_nonneg m]
    have hδle : δ m ≤ r / ((n : ℝ) + 1) :=
      mul_le_of_le_one_right (by positivity) hfrac
    calc
      _ ≤ (n : ℝ) * (r / ((n : ℝ) + 1)) := mul_le_mul_of_nonneg_left hδle (Nat.cast_nonneg n)
      _ ≤ r := by
        rw [← mul_div_assoc, div_le_iff₀ (by positivity : (0 : ℝ) < (n : ℝ) + 1)]
        nlinarith
  let F (j) := A.indicator (f j)
  have hiF (j) : Integrable (F j) := (hf j).1.integrable_indicator hA.measurableSet
  have heq (j) : F j =ᵐ[volume.restrict A] f j := indicator_ae_eq_restrict hA.measurableSet
  have hvar (j) : variation (F j) A = variation (f j) A := variation_congr_ae A (heq j)
  have hFA (j) : IsBVOn (F j) A := ⟨(hiF j).integrableOn, by rw [hvar]; exact (hf j).2⟩
  have hLA (j) : (∫ x in A, |F j x|) ≤ L := by
    calc
      _ = ∫ x in A, |f j x| := integral_congr_ae ((heq j).fun_comp abs)
      _ ≤ L := hLbound j
  have hVA (j) : (variation (F j) A).toReal ≤ V := by rw [hvar]; exact hVbound j
  obtain ⟨g, σ, hσ, hig, ht⟩ := exists_subseq_l1_of_grid_scales hA hQ
    (hcQ.isBounded.subset subset_closure) δ hδ htδ hreachδ F hiF hFA hL hLA hVA
  refine ⟨g, σ, hσ, hig, ?_⟩
  convert ht using 1
  ext j
  apply setIntegral_congr_fun hQ
  intro x hx
  change |f (σ j) x - g x| = |F (σ j) x - g x|
  rw [show F (σ j) x = f (σ j) x from indicator_of_mem (hQA (subset_closure hx)) _]

/-- L¹ convergence on an open region preserves a uniform finite variation bound. -/
theorem variation_le_of_l1_convergence {n : ℕ}
    {Q : Set (EuclideanSpace ℝ (Fin n))} (hQ : IsOpen Q)
    {f : ℕ → EuclideanSpace ℝ (Fin n) → ℝ} (hf : ∀ j, IntegrableOn (f j) Q)
    {g : EuclideanSpace ℝ (Fin n) → ℝ} (hg : IntegrableOn g Q)
    (ht : Tendsto (fun j => ∫ x in Q, |f j x - g x|) atTop (𝓝 0))
    {V : ℝ} (hV : ∀ j, variation (f j) Q ≤ ENNReal.ofReal V) :
    variation g Q ≤ ENNReal.ofReal V := by
  have hlocal (K : Set (EuclideanSpace ℝ (Fin n))) (_hK : IsCompact K) (hKQ : K ⊆ Q) :
      Tendsto (fun j => ∫ x in K, |f j x - g x|) atTop (𝓝 0) := by
    apply squeeze_zero (fun _ => integral_nonneg fun _ => abs_nonneg _) _ ht
    intro j
    exact setIntegral_mono_set ((hf j).sub hg).abs
      (Eventually.of_forall fun _ => abs_nonneg _) (Eventually.of_forall hKQ)
  have hlsc := variation_le_liminf_of_locally_l1 hQ
    (fun j => (hf j).locallyIntegrableOn) hg.locallyIntegrableOn hlocal
  exact hlsc.trans ((liminf_le_liminf (Eventually.of_forall hV)).trans_eq (liminf_const _))

/-- On an open relatively compact set, the fixed-region BV limit also has finite
variation, with the original uniform variation bound. -/
theorem exists_subseq_bvOn_of_bv_bounds {n : ℕ}
    {A Q : Set (EuclideanSpace ℝ (Fin n))} (hA : IsOpen A) (hQ : IsOpen Q)
    (hcQ : IsCompact (closure Q)) (hQA : closure Q ⊆ A)
    (f : ℕ → EuclideanSpace ℝ (Fin n) → ℝ) (hf : ∀ j, IsBVOn (f j) A)
    {L V : ℝ} (hL : 0 ≤ L) (hLbound : ∀ j, (∫ x in A, |f j x|) ≤ L)
    (hVbound : ∀ j, (variation (f j) A).toReal ≤ V) :
    ∃ g : EuclideanSpace ℝ (Fin n) → ℝ, ∃ σ : ℕ → ℕ, StrictMono σ ∧
      IsBVOn g Q ∧ variation g Q ≤ ENNReal.ofReal V ∧
      Tendsto (fun j => ∫ x in Q, |f (σ j) x - g x|) atTop (𝓝 0) := by
  obtain ⟨g, σ, hσ, hig, ht⟩ := exists_subseq_l1_of_bv_bounds hA hQ.measurableSet
    hcQ hQA f hf hL hLbound hVbound
  have hQA' : Q ⊆ A := subset_closure.trans hQA
  have hb (j) : variation (f (σ j)) Q ≤ ENNReal.ofReal V := by
    apply (variation_mono hA.measurableSet hQA').trans
    rw [← ENNReal.ofReal_toReal (hf (σ j)).2.ne]
    exact ENNReal.ofReal_le_ofReal (hVbound (σ j))
  have hvg := variation_le_of_l1_convergence hQ
    (fun j => (hf (σ j)).1.mono_set hQA') hig ht hb
  exact ⟨g, σ, hσ, ⟨hig, hvg.trans_lt ENNReal.ofReal_lt_top⟩, hvg, ht⟩

/-- An open Euclidean domain has an increasing open exhaustion with compact
closures, each closure contained in the next member. -/
theorem exists_open_relatively_compact_exhaustion {n : ℕ}
    {U : Set (EuclideanSpace ℝ (Fin n))} (hU : IsOpen U) :
    ∃ Q : ℕ → Set (EuclideanSpace ℝ (Fin n)), Monotone Q ∧
      (∀ m, IsOpen (Q m)) ∧ (∀ m, IsCompact (closure (Q m))) ∧
      (∀ m, closure (Q m) ⊆ Q (m + 1)) ∧ (⋃ m, Q m) = U := by
  let : LocallyCompactSpace U := hU.locallyCompactSpace
  let K := CompactExhaustion.choice U
  let Q (m) := Subtype.val '' interior (K m)
  have hc (m) : IsCompact (Subtype.val '' K m : Set (EuclideanSpace ℝ (Fin n))) :=
    (K.isCompact m).image continuous_subtype_val
  have hcl (m) : closure (Q m) ⊆ Subtype.val '' K m :=
    closure_minimal (image_mono interior_subset) (hc m).isClosed
  refine ⟨Q, ?_, ?_, ?_, ?_, ?_⟩
  · intro i j hij
    exact image_mono (interior_mono (K.subset hij))
  · intro m
    exact hU.isOpenMap_subtype_val _ isOpen_interior
  · intro m
    exact (hc m).of_isClosed_subset isClosed_closure (hcl m)
  · intro m
    exact (hcl m).trans (image_mono (K.subset_interior_succ m))
  · apply Subset.antisymm
    · intro x hx
      obtain ⟨m, hm⟩ := mem_iUnion.mp hx
      obtain ⟨y, _, rfl⟩ := hm
      exact y.property
    · intro x hx
      obtain ⟨m, hm⟩ := K.exists_mem ⟨x, hx⟩
      exact mem_iUnion.mpr ⟨m + 1, ⟨⟨x, hx⟩, K.subset_interior_succ m hm, rfl⟩⟩

lemma compact_subset_exhaustion {n : ℕ}
    {U : Set (EuclideanSpace ℝ (Fin n))} {Q : ℕ → Set (EuclideanSpace ℝ (Fin n))}
    (hmono : Monotone Q) (hQ : ∀ m, IsOpen (Q m)) (hcover : (⋃ m, Q m) = U)
    {K : Set (EuclideanSpace ℝ (Fin n))} (hK : IsCompact K) (hKU : K ⊆ U) :
    ∃ m, K ⊆ Q m := by
  apply hK.elim_directed_cover Q hQ
  · simpa only [hcover] using hKU
  · exact hmono.directed_le

lemma exists_grid_scales_in_region {n : ℕ} {A Q : Set (EuclideanSpace ℝ (Fin n))}
    (hA : IsOpen A) (hcQ : IsCompact (closure Q)) (hQA : closure Q ⊆ A) :
    ∃ δ : ℕ → ℝ, (∀ m, 0 < δ m) ∧ Tendsto δ atTop (𝓝 0) ∧
      ∀ m, euclideanEnlargement Q ((n : ℝ) * δ m) ⊆ A := by
  obtain ⟨r, hr, hreach⟩ := exists_pos_enlargement_subset hA hcQ hQA
  let δ (m : ℕ) := (r / ((n : ℝ) + 1)) * (1 / ((m : ℝ) + 1))
  have hδ (m) : 0 < δ m := by dsimp [δ]; positivity
  refine ⟨δ, hδ, ?_, ?_⟩
  · simpa only [mul_zero] using
      (tendsto_one_div_add_atTop_nhds_zero_nat (𝕜 := ℝ)).const_mul (r / ((n : ℝ) + 1))
  · intro m
    apply Subset.trans (euclideanEnlargement_mono_radius Q ?_) hreach
    have hfrac : 1 / ((m : ℝ) + 1) ≤ 1 := by
      rw [div_le_one (by positivity : (0 : ℝ) < (m : ℝ) + 1)]
      linarith [show (0 : ℝ) ≤ (m : ℝ) from Nat.cast_nonneg m]
    have hδle : δ m ≤ r / ((n : ℝ) + 1) :=
      mul_le_of_le_one_right (by positivity) hfrac
    calc
      _ ≤ (n : ℝ) * (r / ((n : ℝ) + 1)) := mul_le_mul_of_nonneg_left hδle (Nat.cast_nonneg n)
      _ ≤ r := by
        rw [← mul_div_assoc, div_le_iff₀ (by positivity : (0 : ℝ) < (n : ℝ) + 1)]
        nlinarith

/-- A common subsequence converges in L¹ on countably many relatively compact
regions. All bounds are local to their respective enclosing regions. -/
theorem exists_subseq_l1_countable_regions {n : ℕ}
    {U : Set (EuclideanSpace ℝ (Fin n))}
    (A Q : ℕ → Set (EuclideanSpace ℝ (Fin n)))
    (hA : ∀ m, IsOpen (A m)) (hcA : ∀ m, IsCompact (closure (A m)))
    (hAU : ∀ m, closure (A m) ⊆ U)
    (hQ : ∀ m, MeasurableSet (Q m)) (hcQ : ∀ m, IsCompact (closure (Q m)))
    (hQA : ∀ m, closure (Q m) ⊆ A m)
    (f : ℕ → EuclideanSpace ℝ (Fin n) → ℝ) (hf : ∀ j, LocallyIntegrableOn (f j) U)
    (hfin : ∀ m j, variation (f j) (A m) < ∞)
    (L V : ℕ → ℝ) (hL : ∀ m, 0 ≤ L m)
    (hLb : ∀ m j, (∫ x in A m, |f j x|) ≤ L m)
    (hVb : ∀ m j, (variation (f j) (A m)).toReal ≤ V m) :
    ∃ g : ℕ → EuclideanSpace ℝ (Fin n) → ℝ, ∃ σ : ℕ → ℕ, StrictMono σ ∧
      ∀ m, IntegrableOn (g m) (Q m) ∧
        Tendsto (fun j => ∫ x in Q m, |f (σ j) x - g m x|) atTop (𝓝 0) := by
  choose δ hδ htδ hreach using fun m => exists_grid_scales_in_region (hA m) (hcQ m) (hQA m)
  have hif (m j) : IntegrableOn (f j) (A m) :=
    ((hf j).integrableOn_compact_subset (hAU m) (hcA m)).mono_set subset_closure
  let C (p : ℕ × ℕ) := ((δ p.1 p.2) ^ n)⁻¹ * L p.1
  have hC (p) : 0 ≤ C p :=
    mul_nonneg (inv_nonneg.mpr (pow_nonneg (hδ p.1 p.2).le _)) (hL p.1)
  have hc (p : ℕ × ℕ) (j : ℕ) (k : Fin n → ℤ)
      (hk : k ∈ gridIndex (δ p.1 p.2) '' Q p.1) :
      |⨍ y in gridCell (δ p.1 p.2) k, f j y| ≤ C p := by
    obtain ⟨x, hx, rfl⟩ := hk
    exact (abs_grid_average_le_integral_norm (hδ p.1 p.2) _ (hif p.1 j)
      ((gridCell_gridIndex_subset_enlargement (hδ p.1 p.2) hx).trans (hreach p.1 p.2))).trans
        (mul_le_mul_of_nonneg_left (hLb p.1 j)
          (inv_nonneg.mpr (pow_nonneg (hδ p.1 p.2).le _)))
  obtain ⟨a, σ, hσ, ha⟩ := exists_subseq_gridApproximation_countable
    (fun p : ℕ × ℕ => δ p.1 p.2) (fun p => hδ p.1 p.2) (fun p => Q p.1)
    (fun p => (hcQ p.1).isBounded.subset subset_closure) f C hC hc
  have hlim (m) : ∃ g : EuclideanSpace ℝ (Fin n) → ℝ, IntegrableOn g (Q m) ∧
      Tendsto (fun j => ∫ x in Q m, |f (σ j) x - g x|) atTop (𝓝 0) := by
    have hi (j) : IntegrableOn (f (σ j)) (Q m) :=
      (hif m (σ j)).mono_set (subset_closure.trans (hQA m))
    have hia (k j) : IntegrableOn (gridApproximation (δ m k) (f (σ j))) (Q m) :=
      (integrableOn_gridApproximation_in_region (hδ m k) (hA m).measurableSet
        (hcA m) (hAU m) (hQ m) (hreach m k) (hf (σ j))).1
    let u (j) := (hi j).toL1 (f (σ j))
    let v (k j) := (hia k j).toL1 (gridApproximation (δ m k) (f (σ j)))
    have hcv (k) : CauchySeq (v k) :=
      cauchySeq_toL1_of_tendstoUniformlyOn (hQ m)
        ((hcQ m).isBounded.subset subset_closure).measure_lt_top _ (hia k) (ha (m, k))
    let e (k) := gridApproximationConstant n * δ m k * V m
    have he : Tendsto e atTop (𝓝 0) := by
      simpa only [mul_zero, zero_mul] using
        ((htδ m).const_mul (gridApproximationConstant n)).mul_const (V m)
    have hdist (k j) : dist (u j) (v k j) ≤ e k := by
      rw [dist_toL1_eq_integral_norm_sub (hi j) (hia k j)]
      simp only [Real.norm_eq_abs]
      exact (grid_approximation_in_region (hδ m k) (hA m) (hcA m) (hAU m)
        (hQ m) (hreach m k) (hf (σ j)) (hfin m (σ j))).trans
          (mul_le_mul_of_nonneg_left (hVb m (σ j))
            (mul_nonneg (gridApproximationConstant_nonneg n) (hδ m k).le))
    exact exists_l1_limit_of_cauchySeq_toL1 (fun j => f (σ j)) hi
      (cauchySeq_of_uniform_approximation u v e he hdist hcv)
  choose g hig htg using hlim
  exact ⟨g, σ, hσ, fun m => ⟨hig m, htg m⟩⟩



lemma tendsto_l1_on_subset {α : Type*} [MeasurableSpace α] {μ : Measure α}
    {A Q : Set α} (hQA : Q ⊆ A) {f : ℕ → α → ℝ} {g : α → ℝ}
    (hf : ∀ j, IntegrableOn (f j) A μ) (hg : IntegrableOn g A μ)
    (ht : Tendsto (fun j => ∫ x in A, |f j x - g x| ∂μ) atTop (𝓝 0)) :
    Tendsto (fun j => ∫ x in Q, |f j x - g x| ∂μ) atTop (𝓝 0) := by
  apply squeeze_zero (fun _ => integral_nonneg fun _ => abs_nonneg _) _ ht
  intro j
  exact setIntegral_mono_set ((hf j).sub hg).abs
    (Eventually.of_forall fun _ => abs_nonneg _) (Eventually.of_forall hQA)

lemma ae_eq_of_l1_limits {α : Type*} [MeasurableSpace α] {μ : Measure α}
    {f : ℕ → α → ℝ} {g h : α → ℝ} (hf : ∀ j, Integrable (f j) μ)
    (hg : Integrable g μ) (hh : Integrable h μ)
    (htg : Tendsto (fun j => ∫ x, |f j x - g x| ∂μ) atTop (𝓝 0))
    (hth : Tendsto (fun j => ∫ x, |f j x - h x| ∂μ) atTop (𝓝 0)) :
    g =ᵐ[μ] h := by
  have htg' : Tendsto (fun j => (hf j).toL1 (f j)) atTop (𝓝 (hg.toL1 g)) := by
    rw [tendsto_iff_dist_tendsto_zero]
    simpa only [dist_toL1_eq_integral_norm_sub, Real.norm_eq_abs] using htg
  have hth' : Tendsto (fun j => (hf j).toL1 (f j)) atTop (𝓝 (hh.toL1 h)) := by
    rw [tendsto_iff_dist_tendsto_zero]
    simpa only [dist_toL1_eq_integral_norm_sub, Real.norm_eq_abs] using hth
  have heq := tendsto_nhds_unique htg' hth'
  filter_upwards [hg.coeFn_toL1, hh.coeFn_toL1] with x hx hy
  rw [← hx, ← hy]
  exact congrArg (fun v : α →₁[μ] ℝ => v x) heq

/-- Compatible almost-everywhere representatives on a countable measurable cover
glue to a single actual function. The smallest index containing each point is used. -/
theorem exists_ae_gluing_of_compatible {α : Type*} [MeasurableSpace α] {μ : Measure α}
    (Q : ℕ → Set α) (hQ : ∀ m, MeasurableSet (Q m))
    (g : ℕ → α → ℝ) (hcompat : ∀ i j, i ≤ j → g i =ᵐ[μ.restrict (Q i)] g j) :
    ∃ G : α → ℝ, ∀ m, G =ᵐ[μ.restrict (Q m)] g m := by
  classical
  let G (x : α) := if hx : ∃ m, x ∈ Q m then g (Nat.find hx) x else 0
  refine ⟨G, ?_⟩
  intro m
  have hgood : ∀ᵐ x ∂μ, ∀ i, i ≤ m → x ∈ Q i → g i x = g m x := by
    apply ae_all_iff.mpr
    intro i
    by_cases hi : i ≤ m
    · simpa only [hi, true_implies] using (ae_restrict_iff' (hQ i)).mp (hcompat i m hi)
    · exact Eventually.of_forall fun _ him => (hi him).elim
  filter_upwards [hgood.filter_mono (ae_mono Measure.restrict_le_self),
    ae_restrict_mem (hQ m)] with x hx hxm
  have hex : ∃ i, x ∈ Q i := ⟨m, hxm⟩
  change (if hx : ∃ i, x ∈ Q i then g (Nat.find hx) x else 0) = g m x
  rw [dite_eq_left hex]
  exact hx (Nat.find hex) (Nat.find_min' hex hxm) (Nat.find_spec hex)

/-- Blueprint local BV compactness, function-valued clause. Uniform bounds are
required on every open set with compact closure in the original open domain. -/
theorem bv_compactness {n : ℕ} {U : Set (EuclideanSpace ℝ (Fin n))} (hU : IsOpen U)
    (f : ℕ → EuclideanSpace ℝ (Fin n) → ℝ) (hf : ∀ j, IsLocallyBVOn (f j) U)
    (hbound : ∀ A : Set (EuclideanSpace ℝ (Fin n)), IsOpen A →
      IsCompact (closure A) → closure A ⊆ U → ∃ C : ℝ, ∀ j,
        (∫ x in A, |f j x|) + (variation (f j) A).toReal ≤ C) :
    ∃ g : EuclideanSpace ℝ (Fin n) → ℝ, ∃ σ : ℕ → ℕ, StrictMono σ ∧
      IsLocallyBVOn g U ∧
      ∀ K : Set (EuclideanSpace ℝ (Fin n)), IsCompact K → K ⊆ U →
        Tendsto (fun j => ∫ x in K, |f (σ j) x - g x|) atTop (𝓝 0) := by
  obtain ⟨Q, hmono, hQ, hcQ, hnext, hcover⟩ := exists_open_relatively_compact_exhaustion hU
  have hQU (m) : Q m ⊆ U := by rw [← hcover]; exact subset_iUnion Q m
  have hcQU (m) : closure (Q m) ⊆ U := (hnext m).trans (hQU (m + 1))
  choose C hC using fun m => hbound (Q (m + 1)) (hQ (m + 1)) (hcQ (m + 1)) (hcQU (m + 1))
  have hC₀ (m) : 0 ≤ C m :=
    (add_nonneg (integral_nonneg fun _ => abs_nonneg _) ENNReal.toReal_nonneg).trans (hC m 0)
  have hCL (m j) : (∫ x in Q (m + 1), |f j x|) ≤ C m := by
    have := hC m j
    linarith [ENNReal.toReal_nonneg (a := variation (f j) (Q (m + 1)))]
  have hCV (m j) : (variation (f j) (Q (m + 1))).toReal ≤ C m := by
    have := hC m j
    have hnonneg : 0 ≤ ∫ x in Q (m + 1), |f j x| := integral_nonneg fun _ => abs_nonneg _
    linarith
  have hfin (m j) : variation (f j) (Q (m + 1)) < ∞ :=
    (hf j).2 _ (hQ (m + 1)) (hcQ (m + 1)) (hcQU (m + 1))
  obtain ⟨g, σ, hσ, hg⟩ := exists_subseq_l1_countable_regions (fun m => Q (m + 1)) Q
    (fun m => hQ (m + 1)) (fun m => hcQ (m + 1)) (fun m => hcQU (m + 1))
    (fun m => (hQ m).measurableSet) hcQ hnext f (fun j => (hf j).1) hfin C C hC₀ hCL hCV
  have hif (m j) : IntegrableOn (f (σ j)) (Q m) :=
    ((hf (σ j)).1.integrableOn_compact_subset (hcQU m) (hcQ m)).mono_set subset_closure
  have hcompat (i j : ℕ) (hij : i ≤ j) : g i =ᵐ[volume.restrict (Q i)] g j := by
    exact ae_eq_of_l1_limits (hif i) (hg i).1 ((hg j).1.mono_set (hmono hij)) (hg i).2
      (tendsto_l1_on_subset (hmono hij) (hif j) (hg j).1 (hg j).2)
  obtain ⟨G, hG⟩ := exists_ae_gluing_of_compatible Q (fun m => (hQ m).measurableSet) g hcompat
  have hiG (m) : IntegrableOn G (Q m) := (hg m).1.congr (hG m).symm
  have htG (m) : Tendsto (fun j => ∫ x in Q m, |f (σ j) x - G x|) atTop (𝓝 0) := by
    convert (hg m).2 using 1
    ext j
    exact integral_congr_ae ((EventuallyEq.rfl.sub (hG m)).fun_comp abs)
  have hlocalG : LocallyIntegrableOn G U := by
    apply (locallyIntegrableOn_iff hU.isLocallyClosed).mpr
    intro K hKU hK
    obtain ⟨m, hm⟩ := compact_subset_exhaustion hmono hQ hcover hK hKU
    exact (hiG m).mono_set hm
  have htK (K : Set (EuclideanSpace ℝ (Fin n))) (hK : IsCompact K) (hKU : K ⊆ U) :
      Tendsto (fun j => ∫ x in K, |f (σ j) x - G x|) atTop (𝓝 0) := by
    obtain ⟨m, hm⟩ := compact_subset_exhaustion hmono hQ hcover hK hKU
    exact tendsto_l1_on_subset hm (hif m) (hiG m) (htG m)
  refine ⟨G, σ, hσ, ⟨hlocalG, ?_⟩, htK⟩
  intro A hA hcA hAU
  obtain ⟨B, hB⟩ := hbound A hA hcA hAU
  have hAU' : A ⊆ U := subset_closure.trans hAU
  have hb (j) : variation (f (σ j)) A ≤ ENNReal.ofReal B := by
    rw [← ENNReal.ofReal_toReal ((hf (σ j)).2 A hA hcA hAU).ne]
    apply ENNReal.ofReal_le_ofReal
    have := hB (σ j)
    have hnonneg : 0 ≤ ∫ x in A, |f (σ j) x| := integral_nonneg fun _ => abs_nonneg _
    linarith
  have hlsc := variation_le_liminf_of_locally_l1 hA
    (fun j => (hf (σ j)).1.mono_set hAU') (hlocalG.mono_set hAU')
    (fun K hK hKA => htK K hK (hKA.trans hAU'))
  exact (hlsc.trans ((liminf_le_liminf (Eventually.of_forall hb)).trans_eq
    (liminf_const _))).trans_lt ENNReal.ofReal_lt_top



/-- L¹ convergence preserves membership in any fixed closed set almost everywhere. -/
lemma ae_mem_closed_of_l1_convergence {α : Type*} [MeasurableSpace α] {μ : Measure α}
    {f : ℕ → α → ℝ} {g : α → ℝ} (hf : ∀ j, Integrable (f j) μ) (hg : Integrable g μ)
    (ht : Tendsto (fun j => ∫ x, |f j x - g x| ∂μ) atTop (𝓝 0))
    {S : Set ℝ} (hS : IsClosed S) (hmem : ∀ j, ∀ᵐ x ∂μ, f j x ∈ S) :
    ∀ᵐ x ∂μ, g x ∈ S := by
  have he : Tendsto (fun j => eLpNorm (f j - g) 1 μ) atTop (𝓝 0) := by
    have ht' := ENNReal.continuous_ofReal.continuousAt.tendsto.comp ht
    simp only [ENNReal.ofReal_zero] at ht'
    convert ht' using 1
    ext j
    rw [eLpNorm_one_eq_lintegral_enorm ((hf j).sub hg).aestronglyMeasurable,
      ← ofReal_integral_norm_eq_lintegral_enorm ((hf j).sub hg)]
    simp only [Real.norm_eq_abs, Pi.sub_apply, Function.comp_def]
  have hm := tendstoInMeasure_of_tendsto_eLpNorm one_ne_zero he
  obtain ⟨σ, _, hσ⟩ := hm.exists_seq_tendsto_ae
  filter_upwards [hσ, ae_all_iff.mpr hmem] with x hx hfx
  exact hS.mem_of_tendsto hx (Eventually.of_forall fun j => hfx (σ j))

/-- A measurable representative of a function taking values zero and one almost
everywhere is an indicator. The resulting set is measurable in the ambient space. -/
lemma exists_measurable_indicator_of_ae_zero_or_one {α : Type*} [MeasurableSpace α]
    {μ : Measure α} {g : α → ℝ} (hg : AEStronglyMeasurable g μ)
    (hval : ∀ᵐ x ∂μ, g x = 0 ∨ g x = 1) :
    ∃ E : Set α, MeasurableSet E ∧ g =ᵐ[μ] E.indicator (fun _ => (1 : ℝ)) := by
  let E := {x | hg.mk g x = 1}
  have hE : MeasurableSet E := measurableSet_eq_fun hg.measurable_mk measurable_const
  refine ⟨E, hE, ?_⟩
  filter_upwards [hg.ae_eq_mk, hval] with x hx hvalx
  rcases hvalx with hzero | hone
  · have hxE : x ∉ E := by
      change ¬hg.mk g x = 1
      rw [← hx, hzero]
      norm_num
    rw [indicator_of_notMem hxE, hzero]
  · have hxE : x ∈ E := by change hg.mk g x = 1; rw [← hx, hone]
    rw [indicator_of_mem hxE, hone]

/-- Closed-value constraints pass to local L¹ limits throughout an open domain. -/
lemma ae_mem_closed_of_locally_l1_convergence {n : ℕ}
    {U : Set (EuclideanSpace ℝ (Fin n))} (hU : IsOpen U)
    {f : ℕ → EuclideanSpace ℝ (Fin n) → ℝ} (hf : ∀ j, LocallyIntegrableOn (f j) U)
    {g : EuclideanSpace ℝ (Fin n) → ℝ} (hg : LocallyIntegrableOn g U)
    (ht : ∀ K : Set (EuclideanSpace ℝ (Fin n)), IsCompact K → K ⊆ U →
      Tendsto (fun j => ∫ x in K, |f j x - g x|) atTop (𝓝 0))
    {S : Set ℝ} (hS : IsClosed S) (hmem : ∀ j, ∀ᵐ x ∂volume.restrict U, f j x ∈ S) :
    ∀ᵐ x ∂volume.restrict U, g x ∈ S := by
  obtain ⟨Q, _, _, hcQ, hnext, hcover⟩ := exists_open_relatively_compact_exhaustion hU
  have hQU (m) : closure (Q m) ⊆ U := by
    rw [← hcover]
    exact (hnext m).trans (subset_iUnion Q (m + 1))
  rw [← hcover, ae_restrict_iUnion_iff]
  intro m
  have hc := ae_mem_closed_of_l1_convergence
    (fun j => (hf j).integrableOn_compact_subset (hQU m) (hcQ m))
    (hg.integrableOn_compact_subset (hQU m) (hcQ m)) (ht _ (hcQ m) (hQU m)) hS
    (fun j => (hmem j).filter_mono (ae_mono (Measure.restrict_mono (hQU m) le_rfl)))
  exact hc.filter_mono (ae_mono (Measure.restrict_mono subset_closure le_rfl))

lemma IsLocallyBVOn.congr_ae {n : ℕ} {U : Set (EuclideanSpace ℝ (Fin n))}
    {f g : EuclideanSpace ℝ (Fin n) → ℝ} (hf : IsLocallyBVOn f U)
    (hfg : f =ᵐ[volume.restrict U] g) : IsLocallyBVOn g U := by
  refine ⟨hf.1.congr hfg, ?_⟩
  intro A hA hcA hAU
  have heq := hfg.filter_mono (ae_mono (Measure.restrict_mono (subset_closure.trans hAU) le_rfl))
  rw [← variation_congr_ae A heq]
  exact hf.2 A hA hcA hAU

/-- On the whole Euclidean space, local compactness of indicators produces a
measurable set of locally finite perimeter in the global sense. -/
theorem bv_compactness_indicators_univ {n : ℕ}
    (E : ℕ → Set (EuclideanSpace ℝ (Fin n)))
    (hE : ∀ j, HasLocallyFinitePerimeter (E j)) (hmE : ∀ j, NullMeasurableSet (E j) volume)
    (hbound : ∀ A : Set (EuclideanSpace ℝ (Fin n)), IsOpen A → IsCompact (closure A) →
      ∃ C : ℝ, ∀ j, (∫ x in A, |(E j).indicator (fun _ => (1 : ℝ)) x|) +
        (perimeterIn (E j) A).toReal ≤ C) :
    ∃ F : Set (EuclideanSpace ℝ (Fin n)), MeasurableSet F ∧ HasLocallyFinitePerimeter F ∧
      ∃ σ : ℕ → ℕ, StrictMono σ ∧
        ∀ K : Set (EuclideanSpace ℝ (Fin n)), IsCompact K →
          Tendsto (fun j => ∫ x in K,
            |(E (σ j)).indicator (fun _ => (1 : ℝ)) x - F.indicator (fun _ => (1 : ℝ)) x|)
            atTop (𝓝 0) := by
  let f (j) := (E j).indicator (fun _ => (1 : ℝ))
  have hf (j) : IsLocallyBVOn (f j) univ := (hE j).isLocallyBVOn_indicator (hmE j) univ
  obtain ⟨g, σ, hσ, hg, ht⟩ := bv_compactness isOpen_univ f hf
    (fun A hA hcA _ => hbound A hA hcA)
  have hval : ∀ᵐ x ∂volume.restrict (univ : Set (EuclideanSpace ℝ (Fin n))),
      g x = 0 ∨ g x = 1 := by
    have hc := ae_mem_closed_of_locally_l1_convergence isOpen_univ
      (fun j => (hf (σ j)).1) hg.1 ht
      (isClosed_singleton.union isClosed_singleton : IsClosed ({0, 1} : Set ℝ))
      (fun j => Eventually.of_forall fun x => by
        by_cases hx : x ∈ E (σ j) <;> simp [f, hx])
    simpa only [mem_union, mem_singleton_iff] using hc
  obtain ⟨F, hmF, hF⟩ :=
    exists_measurable_indicator_of_ae_zero_or_one hg.1.aestronglyMeasurable hval
  have hBV := hg.congr_ae hF
  refine ⟨F, hmF, (fun A hA hcA => hBV.2 A hA hcA (subset_univ _)), σ, hσ, ?_⟩
  intro K hK
  have heq := hF.filter_mono (ae_mono (Measure.restrict_mono (subset_univ K) le_rfl))
  convert ht K hK (subset_univ K) using 1
  ext j
  exact integral_congr_ae ((EventuallyEq.rfl.sub heq.symm).fun_comp abs)

end LiquidDrop

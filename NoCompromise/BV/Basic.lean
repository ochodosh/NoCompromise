import NoCompromise.BV.Defs
import NoCompromise.Measure.SignedRiesz
import Mathlib.Analysis.Normed.Module.HahnBanach
import Mathlib.Tactic
import Mathlib.Topology.Order.LiminfLimsup
import Mathlib.MeasureTheory.Group.Integral
import Mathlib.Analysis.Calculus.ContDiff.Comp
import Mathlib.Analysis.Calculus.ContDiff.Operations
import Mathlib.Analysis.Calculus.FDeriv.Equiv
import Mathlib.MeasureTheory.Measure.Haar.NormedSpace
import Mathlib.Analysis.Calculus.LineDeriv.IntegrationByParts
import Mathlib.Analysis.Calculus.BumpFunction.Convolution
import Mathlib.Analysis.Calculus.ContDiff.Convolution
import Mathlib.MeasureTheory.Integral.DominatedConvergence
import Mathlib.MeasureTheory.Measure.Decomposition.RadonNikodym
import Mathlib.MeasureTheory.SpecificCodomains.WithLp
import Mathlib.MeasureTheory.Function.SpecialFunctions.Inner
import Mathlib.MeasureTheory.Function.ContinuousMapDense
import Mathlib.MeasureTheory.VectorMeasure.WithDensityVec
import Mathlib.Geometry.Manifold.PartitionOfUnity
import Mathlib.Geometry.Manifold.ContMDiff.NormedSpace
import Mathlib.MeasureTheory.Measure.Hausdorff

/-!
# Perimeter invariances, test fields, and derivative representations

Blueprint `lem:perimeter-invariances`, `lem:lsc`, and `lem:test-class`. The compatibility theorem
identifies the dimension-three perimeter with the original showcase definition.
Null invariance, translation, dilation, and complement invariance are proved
in arbitrary dimension (positive dimension for dilation). Lower semicontinuity
under local L¹ convergence follows directly from the test-field definition.
Normalized bump convolution proves that smooth fields give the same variation
supremum, preserving the support and norm constraints. Finite variation bounds
the distributional pairing, which extends continuously and has coordinate signed
Riesz representatives. Local extensions agree on continuous supported tests in
overlaps and glue on the full open domain. Positive Radon–Nikodym yields a
locally finite regular measure and a measurable unit polar direction. Continuous
unit fields recover the polar mass by L¹ approximation, proving equality with
variation on every open subregion. Compatible compact vector restrictions have
exactly this total variation, and the outward-normal sign convention is proved.
For arbitrary locally integrable functions, finite smooth partitions of test
fields prove open-cover subadditivity. The metric outer extension yields a
Borel variation measure even without local finiteness. Perimeter locality and
separated-union additivity follow, including infinite-perimeter cases.
-/

open MeasureTheory Filter Metric Set
open scoped ENNReal symmDiff Topology BoundedContinuousFunction Manifold

namespace LiquidDrop

theorem divergence_eq_divergenceN (X : AmbientSpace → AmbientSpace) (x : AmbientSpace) :
    divergence X x = divergenceN X x := rfl

/-- The indicator-function and set-integral definitions agree for Lebesgue-measurable sets. -/
theorem perimeterN_eq_perimeter (E : Set AmbientSpace) (hE : NullMeasurableSet E volume) :
    perimeterN E = perimeter E := by
  have hind (X : AmbientSpace → AmbientSpace) :
      (∫ x, E.indicator (fun _ => (1 : ℝ)) x * divergenceN X x) =
        ∫ x in E, divergence X x := by
    have hfun : (fun x => E.indicator (fun _ => (1 : ℝ)) x * divergenceN X x) =
        E.indicator (divergence X) := by
      funext x
      by_cases hx : x ∈ E <;> simp [hx, divergence_eq_divergenceN]
    rw [hfun, integral_indicator₀ hE]
  simp only [perimeterN, perimeterIn, variation, IsVariationTestField, Set.subset_univ,
    true_and, iSup_and, setIntegral_univ, hind, perimeter]

/-- Variation depends only on the function's almost-everywhere values in the region. -/
theorem variation_congr_ae {n : ℕ} {f g : EuclideanSpace ℝ (Fin n) → ℝ}
    (U : Set (EuclideanSpace ℝ (Fin n))) (hfg : f =ᵐ[volume.restrict U] g) :
    variation f U = variation g U := by
  unfold variation
  congr 1
  funext X
  congr 1
  funext hX
  congr 1
  apply integral_congr_ae
  filter_upwards [hfg] with x hx
  rw [hx]

/-- The null-set part of blueprint `lem:perimeter-invariances`, in a local form. -/
theorem perimeterIn_congr_ae {n : ℕ} {E F : Set (EuclideanSpace ℝ (Fin n))}
    (U : Set (EuclideanSpace ℝ (Fin n))) (hEF : E =ᵐ[volume.restrict U] F) :
    perimeterIn E U = perimeterIn F U := by
  exact variation_congr_ae U (indicator_ae_eq_of_ae_eq_set hEF)

theorem perimeterN_congr_ae {n : ℕ} {E F : Set (EuclideanSpace ℝ (Fin n))}
    (hEF : E =ᵐ[volume] F) : perimeterN E = perimeterN F := by
  apply perimeterIn_congr_ae
  simpa only [Measure.restrict_univ] using hEF

/-- Null-set invariance for the original showcase perimeter, without a measurability assumption. -/
theorem perimeter_congr_ae {E F : Set AmbientSpace} (hEF : E =ᵐ[volume] F) :
    perimeter E = perimeter F := by
  simp only [perimeter, Measure.restrict_congr_set hEF]

theorem perimeterIn_eq_of_symmDiff_null {n : ℕ} {E F : Set (EuclideanSpace ℝ (Fin n))}
    (U : Set (EuclideanSpace ℝ (Fin n))) (hEF : volume (E ∆ F) = 0) :
    perimeterIn E U = perimeterIn F U := by
  apply perimeterIn_congr_ae
  exact ae_restrict_of_ae (measure_symmDiff_eq_zero_iff.mp hEF)

/-! ## Lower semicontinuity -/

lemma continuous_divergenceN {n : ℕ}
    {X : EuclideanSpace ℝ (Fin n) → EuclideanSpace ℝ (Fin n)} (hX : ContDiff ℝ 1 X) :
    Continuous (divergenceN X) := by
  have hc := hX.continuous_fderiv one_ne_zero
  unfold divergenceN
  fun_prop

lemma divergenceN_eq_zero_of_notMem_tsupport {n : ℕ}
    {X : EuclideanSpace ℝ (Fin n) → EuclideanSpace ℝ (Fin n)}
    {x : EuclideanSpace ℝ (Fin n)} (hx : x ∉ tsupport X) : divergenceN X x = 0 := by
  simp [divergenceN, fderiv_of_notMem_tsupport ℝ hx]

/-- Lower semicontinuity follows from convergence against every variation test field. -/
theorem variation_le_liminf_of_test_integrals {n : ℕ}
    {f : ℕ → EuclideanSpace ℝ (Fin n) → ℝ} {g : EuclideanSpace ℝ (Fin n) → ℝ}
    {U : Set (EuclideanSpace ℝ (Fin n))}
    (hconv : ∀ X, IsVariationTestField U X →
      Tendsto (fun j => ∫ x in U, f j x * divergenceN X x) atTop
        (𝓝 (∫ x in U, g x * divergenceN X x))) :
    variation g U ≤ liminf (fun j => variation (f j) U) atTop := by
  apply iSup_le
  intro X
  apply iSup_le
  intro hX
  have hlim := ENNReal.continuous_ofReal.continuousAt.tendsto.comp (hconv X hX)
  calc
    _ = liminf (fun j => ENNReal.ofReal (∫ x in U, f j x * divergenceN X x)) atTop :=
      hlim.liminf_eq.symm
    _ ≤ _ := by
      refine liminf_le_liminf ?_
      filter_upwards [] with j
      apply le_iSup_of_le X
      exact le_iSup (fun _ : IsVariationTestField U X =>
        ENNReal.ofReal (∫ x in U, f j x * divergenceN X x)) hX

/-- Local L¹ convergence allows integration against continuous functions on a compact set. -/
theorem tendsto_integral_mul_of_l1_on_compact {n : ℕ}
    {f : ℕ → EuclideanSpace ℝ (Fin n) → ℝ} {g ψ : EuclideanSpace ℝ (Fin n) → ℝ}
    {K : Set (EuclideanSpace ℝ (Fin n))} (hK : IsCompact K)
    (hf : ∀ j, IntegrableOn (f j) K) (hg : IntegrableOn g K) (hψ : ContinuousOn ψ K)
    (hconv : Tendsto (fun j => ∫ x in K, |f j x - g x|) atTop (𝓝 0)) :
    Tendsto (fun j => ∫ x in K, f j x * ψ x) atTop (𝓝 (∫ x in K, g x * ψ x)) := by
  obtain ⟨C, hC⟩ := hK.exists_bound_of_continuousOn hψ
  apply tendsto_iff_norm_sub_tendsto_zero.mpr
  refine squeeze_zero (g := fun j => (∫ x in K, |f j x - g x|) * C)
    (fun _ => norm_nonneg _) ?_ ?_
  · intro j
    rw [← integral_sub ((hf j).mul_continuousOn hψ hK) (hg.mul_continuousOn hψ hK)]
    calc
      _ ≤ ∫ x in K, ‖f j x * ψ x - g x * ψ x‖ := norm_integral_le_integral_norm _
      _ ≤ ∫ x in K, |f j x - g x| * C := by
        apply integral_mono_ae
        · exact (((hf j).mul_continuousOn hψ hK).sub (hg.mul_continuousOn hψ hK)).norm
        · exact ((hf j).sub hg).abs.mul_const C
        · filter_upwards [ae_restrict_mem hK.measurableSet] with x hx
          rw [← sub_mul, norm_mul, Real.norm_eq_abs]
          exact mul_le_mul_of_nonneg_left (hC x hx) (abs_nonneg _)
      _ = _ := integral_mul_const C _
  · simpa using hconv.mul_const C

/-- Blueprint `lem:lsc`: lower semicontinuity under local L¹ convergence. -/
theorem variation_le_liminf_of_locally_l1 {n : ℕ}
    {f : ℕ → EuclideanSpace ℝ (Fin n) → ℝ} {g : EuclideanSpace ℝ (Fin n) → ℝ}
    {U : Set (EuclideanSpace ℝ (Fin n))} (hU : IsOpen U)
    (hf : ∀ j, LocallyIntegrableOn (f j) U) (hg : LocallyIntegrableOn g U)
    (hconv : ∀ K : Set (EuclideanSpace ℝ (Fin n)), IsCompact K → K ⊆ U →
      Tendsto (fun j => ∫ x in K, |f j x - g x|) atTop (𝓝 0)) :
    variation g U ≤ liminf (fun j => variation (f j) U) atTop := by
  apply variation_le_liminf_of_test_integrals
  intro X hX
  have hsupport (u : EuclideanSpace ℝ (Fin n) → ℝ) :
      (∫ x in U, u x * divergenceN X x) = ∫ x in tsupport X, u x * divergenceN X x := by
    apply setIntegral_eq_of_subset_of_forall_sdiff_eq_zero hU.measurableSet hX.2.2.1
    intro x hx
    rw [divergenceN_eq_zero_of_notMem_tsupport hx.2, mul_zero]
  simp_rw [hsupport]
  exact tendsto_integral_mul_of_l1_on_compact hX.2.1
    (fun j => (hf j).integrableOn_compact_subset hX.2.2.1 hX.2.1)
    (hg.integrableOn_compact_subset hX.2.2.1 hX.2.1)
    (continuous_divergenceN hX.1).continuousOn (hconv _ hX.2.1 hX.2.2.1)

lemma locallyIntegrable_indicator_one {n : ℕ} {E : Set (EuclideanSpace ℝ (Fin n))}
    (hE : NullMeasurableSet E volume) : LocallyIntegrable (E.indicator (fun _ => (1 : ℝ))) := by
  have hb := (locallyIntegrable_const (μ := volume) (1 : ℝ)).indicator
    (measurableSet_toMeasurable volume E)
  exact hb.congr (indicator_ae_eq_of_ae_eq_set hE.toMeasurable_ae_eq)

/-- The perimeter consequence of blueprint `lem:lsc`, for Lebesgue-measurable sets. -/
theorem perimeterIn_le_liminf_of_locally_l1 {n : ℕ}
    {E : ℕ → Set (EuclideanSpace ℝ (Fin n))} {F U : Set (EuclideanSpace ℝ (Fin n))}
    (hU : IsOpen U) (hE : ∀ j, NullMeasurableSet (E j) volume)
    (hF : NullMeasurableSet F volume)
    (hconv : ∀ K : Set (EuclideanSpace ℝ (Fin n)), IsCompact K → K ⊆ U →
      Tendsto (fun j => ∫ x in K,
        |(E j).indicator (fun _ => (1 : ℝ)) x - F.indicator (fun _ => (1 : ℝ)) x|)
        atTop (𝓝 0)) :
    perimeterIn F U ≤ liminf (fun j => perimeterIn (E j) U) atTop :=
  variation_le_liminf_of_locally_l1 hU
    (fun j => (locallyIntegrable_indicator_one (hE j)).locallyIntegrableOn U)
    ((locallyIntegrable_indicator_one hF).locallyIntegrableOn U) hconv


/-! ## Translation invariance -/

lemma divergenceN_comp_add_left {n : ℕ}
    (X : EuclideanSpace ℝ (Fin n) → EuclideanSpace ℝ (Fin n))
    (a x : EuclideanSpace ℝ (Fin n)) :
    divergenceN (fun y => X (a + y)) x = divergenceN X (a + x) := by
  simp only [divergenceN, fderiv_comp_add_left]

lemma IsVariationTestField.comp_add_left {n : ℕ}
    {U : Set (EuclideanSpace ℝ (Fin n))}
    {X : EuclideanSpace ℝ (Fin n) → EuclideanSpace ℝ (Fin n)}
    (a : EuclideanSpace ℝ (Fin n)) (hX : IsVariationTestField ((fun x => a + x) '' U) X) :
    IsVariationTestField U (fun x => X (a + x)) := by
  refine ⟨hX.1.comp (contDiff_const.add contDiff_id),
    hX.2.1.comp_homeomorph (Homeomorph.addLeft a), ?_, fun x => hX.2.2.2 (a + x)⟩
  intro x hx
  have hpre : a + x ∈ tsupport X :=
    tsupport_comp_subset_preimage X (continuous_const.add continuous_id) hx
  obtain ⟨y, hy, hay⟩ := hX.2.2.1 hpre
  exact (add_left_cancel hay) ▸ hy

lemma variation_translate_le {n : ℕ} (f : EuclideanSpace ℝ (Fin n) → ℝ)
    (U : Set (EuclideanSpace ℝ (Fin n))) (a : EuclideanSpace ℝ (Fin n)) :
    variation f ((fun x => a + x) '' U) ≤ variation (fun x => f (a + x)) U := by
  apply iSup_le
  intro X
  apply iSup_le
  intro hX
  rw [(measurePreserving_add_left volume a).setIntegral_image_emb
    (MeasurableEquiv.addLeft a).measurableEmbedding]
  have hdiv : (fun x => f (a + x) * divergenceN X (a + x)) =
      (fun x => f (a + x) * divergenceN (fun y => X (a + y)) x) := by
    simp only [divergenceN_comp_add_left]
  rw [hdiv]
  apply le_iSup_of_le (fun x => X (a + x))
  exact le_iSup (fun _ : IsVariationTestField U (fun x => X (a + x)) =>
    ENNReal.ofReal (∫ x in U, f (a + x) * divergenceN (fun y => X (a + y)) x))
    (hX.comp_add_left a)

/-- Translation of a region is equivalent to pulling back the function. -/
theorem variation_translate {n : ℕ} (f : EuclideanSpace ℝ (Fin n) → ℝ)
    (U : Set (EuclideanSpace ℝ (Fin n))) (a : EuclideanSpace ℝ (Fin n)) :
    variation f ((fun x => a + x) '' U) = variation (fun x => f (a + x)) U := by
  apply le_antisymm (variation_translate_le f U a)
  have h := variation_translate_le (fun x => f (a + x)) ((fun x => a + x) '' U) (-a)
  have hset : (fun x => -a + x) '' ((fun x => a + x) '' U) = U := by
    rw [image_image]
    have hid : (fun x => -a + (a + x)) = id := by funext x; simp
    rw [hid, image_id]
  rw [hset] at h
  simpa only [add_neg_cancel_left] using h

/-- Translation invariance in blueprint `lem:perimeter-invariances`. -/
theorem perimeterIn_translate {n : ℕ} (E U : Set (EuclideanSpace ℝ (Fin n)))
    (a : EuclideanSpace ℝ (Fin n)) :
    perimeterIn ((fun x => a + x) '' E) ((fun x => a + x) '' U) = perimeterIn E U := by
  unfold perimeterIn
  rw [variation_translate]
  congr 1
  funext x
  have hmem : a + x ∈ (fun y => a + y) '' E ↔ x ∈ E := by
    exact (Function.Injective.mem_set_image (fun _ _ h => add_left_cancel h))
  by_cases hx : x ∈ E
  · rw [indicator_of_mem (hmem.mpr hx), indicator_of_mem hx]
  · rw [indicator_of_notMem (mt hmem.mp hx), indicator_of_notMem hx]

/-- Global translation invariance in arbitrary dimension. -/
theorem perimeterN_translate {n : ℕ} (E : Set (EuclideanSpace ℝ (Fin n)))
    (a : EuclideanSpace ℝ (Fin n)) :
    perimeterN ((fun x => a + x) '' E) = perimeterN E := by
  have hsurj : Function.Surjective (fun x : EuclideanSpace ℝ (Fin n) => a + x) :=
    fun y => ⟨-a + y, by simp⟩
  simpa only [perimeterN, image_univ_of_surjective hsurj] using perimeterIn_translate E univ a


/-! ## Dilation -/

lemma setIntegral_image_smul {n : ℕ} (f : EuclideanSpace ℝ (Fin n) → ℝ)
    (U : Set (EuclideanSpace ℝ (Fin n))) {r : ℝ} (hr : 0 < r) :
    (∫ x in (fun y => r • y) '' U, f x) = r ^ n * ∫ x in U, f (r • x) := by
  let e := (Homeomorph.smul (isUnit_iff_ne_zero.mpr hr.ne').unit :
    EuclideanSpace ℝ (Fin n) ≃ₜ EuclideanSpace ℝ (Fin n)).toMeasurableEquiv
  have hm := e.measurableEmbedding.setIntegral_map (μ := volume) f ((fun y => r • y) '' U)
  have he : (e : EuclideanSpace ℝ (Fin n) → EuclideanSpace ℝ (Fin n)) = (fun x => r • x) := rfl
  rw [he, Measure.map_addHaar_smul volume hr.ne', Measure.restrict_smul,
    integral_smul_measure] at hm
  rw [ENNReal.toReal_ofReal (abs_nonneg _), abs_of_pos (inv_pos.mpr (pow_pos hr _))] at hm
  have hi : Function.Injective (fun x : EuclideanSpace ℝ (Fin n) => r • x) :=
    e.injective
  rw [hi.preimage_image] at hm
  simp only [finrank_euclideanSpace, Fintype.card_fin, smul_eq_mul] at hm
  calc
    _ = r ^ n * ((r ^ n)⁻¹ * ∫ x in (fun y => r • y) '' U, f x) := by
      rw [← mul_assoc, mul_inv_cancel₀ (pow_ne_zero _ hr.ne'), one_mul]
    _ = _ := by rw [hm]

lemma divergenceN_comp_smul {n : ℕ}
    (X : EuclideanSpace ℝ (Fin n) → EuclideanSpace ℝ (Fin n))
    (r : ℝ) (x : EuclideanSpace ℝ (Fin n)) :
    divergenceN (fun y => X (r • y)) x = r * divergenceN X (r • x) := by
  simp [divergenceN, fderiv_comp_smul, Finset.mul_sum]

lemma IsVariationTestField.comp_smul {n : ℕ}
    {U : Set (EuclideanSpace ℝ (Fin n))}
    {X : EuclideanSpace ℝ (Fin n) → EuclideanSpace ℝ (Fin n)}
    {r : ℝ} (hr : 0 < r) (hX : IsVariationTestField ((fun x => r • x) '' U) X) :
    IsVariationTestField U (fun x => X (r • x)) := by
  have hc : ContDiff ℝ 1 (fun x : EuclideanSpace ℝ (Fin n) => r • x) :=
    ContDiff.const_smul r contDiff_id
  refine ⟨hX.1.comp hc,
    hX.2.1.comp_homeomorph (Homeomorph.smul (isUnit_iff_ne_zero.mpr hr.ne').unit), ?_,
    fun x => hX.2.2.2 (r • x)⟩
  intro x hx
  have hpre : r • x ∈ tsupport X :=
    tsupport_comp_subset_preimage X
      (show Continuous (fun y : EuclideanSpace ℝ (Fin n) => r • y) by fun_prop) hx
  obtain ⟨y, hy, hxy⟩ := hX.2.2.1 hpre
  exact ((smul_right_injective _ hr.ne') hxy) ▸ hy

lemma variation_smul_le {n : ℕ} (hn : 0 < n) (f : EuclideanSpace ℝ (Fin n) → ℝ)
    (U : Set (EuclideanSpace ℝ (Fin n))) {r : ℝ} (hr : 0 < r) :
    variation f ((fun x => r • x) '' U) ≤
      ENNReal.ofReal (r ^ (n - 1)) * variation (fun x => f (r • x)) U := by
  apply iSup_le
  intro X
  apply iSup_le
  intro hX
  have hpow : r ^ n = r ^ (n - 1) * r := by
    conv_lhs => rw [← Nat.sub_add_cancel hn, pow_succ]
  have hint : (∫ x in (fun y => r • y) '' U, f x * divergenceN X x) =
      r ^ (n - 1) * ∫ x in U, f (r • x) * divergenceN (fun y => X (r • y)) x := by
    rw [setIntegral_image_smul _ _ hr]
    simp_rw [divergenceN_comp_smul]
    rw [show (fun x => f (r • x) * (r * divergenceN X (r • x))) =
      (fun x => r * (f (r • x) * divergenceN X (r • x))) by funext x; ring]
    rw [integral_const_mul, hpow, mul_assoc]
  rw [hint, ENNReal.ofReal_mul (pow_nonneg hr.le _)]
  gcongr
  apply le_iSup_of_le (fun x => X (r • x))
  exact le_iSup (fun _ : IsVariationTestField U (fun x => X (r • x)) =>
    ENNReal.ofReal (∫ x in U, f (r • x) * divergenceN (fun y => X (r • y)) x))
    (hX.comp_smul hr)

/-- Dilation of variation in dimension `n ≥ 1`. -/
theorem variation_smul {n : ℕ} (hn : 0 < n) (f : EuclideanSpace ℝ (Fin n) → ℝ)
    (U : Set (EuclideanSpace ℝ (Fin n))) {r : ℝ} (hr : 0 < r) :
    variation f ((fun x => r • x) '' U) =
      ENNReal.ofReal (r ^ (n - 1)) * variation (fun x => f (r • x)) U := by
  apply le_antisymm (variation_smul_le hn f U hr)
  have h := variation_smul_le hn (fun x => f (r • x)) ((fun x => r • x) '' U)
    (inv_pos.mpr hr)
  have hset : (fun x => r⁻¹ • x) '' ((fun x => r • x) '' U) = U := by
    rw [image_image]
    have hid : (fun x : EuclideanSpace ℝ (Fin n) => r⁻¹ • (r • x)) = id := by
      funext x
      simp [smul_smul, hr.ne']
    rw [hid, image_id]
  rw [hset] at h
  simp only [smul_smul, mul_inv_cancel₀ hr.ne', one_smul] at h
  calc
    _ ≤ ENNReal.ofReal (r ^ (n - 1)) *
        (ENNReal.ofReal ((r⁻¹) ^ (n - 1)) * variation f ((fun x => r • x) '' U)) := by
      gcongr
    _ = _ := by
      rw [← mul_assoc, ← ENNReal.ofReal_mul (pow_nonneg hr.le _), inv_pow,
        mul_inv_cancel₀ (pow_ne_zero _ hr.ne'), ENNReal.ofReal_one, one_mul]

/-- Dilation invariance in blueprint `lem:perimeter-invariances`. -/
theorem perimeterIn_smul {n : ℕ} (hn : 0 < n) (E U : Set (EuclideanSpace ℝ (Fin n)))
    {r : ℝ} (hr : 0 < r) :
    perimeterIn ((fun x => r • x) '' E) ((fun x => r • x) '' U) =
      ENNReal.ofReal (r ^ (n - 1)) * perimeterIn E U := by
  unfold perimeterIn
  rw [variation_smul hn _ _ hr]
  congr 2
  funext x
  have hmem : r • x ∈ (fun y => r • y) '' E ↔ x ∈ E :=
    (smul_right_injective _ hr.ne').mem_set_image
  by_cases hx : x ∈ E
  · rw [indicator_of_mem (hmem.mpr hx), indicator_of_mem hx]
  · rw [indicator_of_notMem (mt hmem.mp hx), indicator_of_notMem hx]

/-- Global perimeter scales by the `(n - 1)`st power of the dilation. -/
theorem perimeterN_smul {n : ℕ} (hn : 0 < n) (E : Set (EuclideanSpace ℝ (Fin n)))
    {r : ℝ} (hr : 0 < r) :
    perimeterN ((fun x => r • x) '' E) = ENNReal.ofReal (r ^ (n - 1)) * perimeterN E := by
  have hsurj : Function.Surjective (fun x : EuclideanSpace ℝ (Fin n) => r • x) :=
    fun y => ⟨r⁻¹ • y, by simp [smul_smul, hr.ne']⟩
  simpa only [perimeterN, image_univ_of_surjective hsurj] using perimeterIn_smul hn E univ hr


/-! ## Complement invariance -/

lemma integrable_fderiv_apply_of_compactSupport {n : ℕ}
    {X : EuclideanSpace ℝ (Fin n) → EuclideanSpace ℝ (Fin n)}
    (hX : ContDiff ℝ 1 X) (hcompact : HasCompactSupport X) (v : EuclideanSpace ℝ (Fin n)) :
    Integrable (fun x => fderiv ℝ X x v) :=
  ((hX.continuous_fderiv one_ne_zero).clm_apply continuous_const).integrable_of_hasCompactSupport
    (hcompact.fderiv_apply ℝ v)

lemma integral_fderiv_apply_eq_zero {n : ℕ}
    {X : EuclideanSpace ℝ (Fin n) → EuclideanSpace ℝ (Fin n)}
    (hX : ContDiff ℝ 1 X) (hcompact : HasCompactSupport X) (v : EuclideanSpace ℝ (Fin n)) :
    (∫ x, fderiv ℝ X x v) = 0 := by
  have h := integral_smul_fderiv_eq_neg_fderiv_smul_of_integrable
    (μ := volume) (f := fun _ : EuclideanSpace ℝ (Fin n) => (1 : ℝ)) (g := X) (v := v)
    (by simp)
    (by simpa using integrable_fderiv_apply_of_compactSupport hX hcompact v)
    (by simpa using hX.continuous.integrable_of_hasCompactSupport hcompact)
    (fun _ _ => differentiableAt_const _) (fun x _ => hX.differentiable one_ne_zero x)
  simpa using h

lemma integrable_divergenceN {n : ℕ}
    {X : EuclideanSpace ℝ (Fin n) → EuclideanSpace ℝ (Fin n)}
    (hX : ContDiff ℝ 1 X) (hcompact : HasCompactSupport X) : Integrable (divergenceN X) := by
  apply (continuous_divergenceN hX).integrable_of_hasCompactSupport
  apply hcompact.mono'
  intro x hx
  by_contra hx'
  exact hx (divergenceN_eq_zero_of_notMem_tsupport hx')

lemma integral_divergenceN_eq_zero {n : ℕ}
    {X : EuclideanSpace ℝ (Fin n) → EuclideanSpace ℝ (Fin n)}
    (hX : ContDiff ℝ 1 X) (hcompact : HasCompactSupport X) : (∫ x, divergenceN X x) = 0 := by
  have hi (i : Fin n) := integrable_fderiv_apply_of_compactSupport hX hcompact
    (EuclideanSpace.single i 1)
  let hpi (i : Fin n) := (PiLp.proj (𝕜 := ℝ) (p := 2) (β := fun _ : Fin n => ℝ) i)
  unfold divergenceN
  change (∫ x, ∑ i, hpi i (fderiv ℝ X x (EuclideanSpace.single i 1))) = 0
  rw [integral_finsetSum _ (fun i _ => (hpi i).integrable_comp (hi i))]
  apply Finset.sum_eq_zero
  intro i _
  change (∫ x, hpi i (fderiv ℝ X x (EuclideanSpace.single i 1))) = 0
  rw [(hpi i).integral_comp_comm (hi i), integral_fderiv_apply_eq_zero hX hcompact, map_zero]

lemma divergenceN_neg {n : ℕ}
    (X : EuclideanSpace ℝ (Fin n) → EuclideanSpace ℝ (Fin n))
    (x : EuclideanSpace ℝ (Fin n)) : divergenceN (-X) x = -divergenceN X x := by
  simp [divergenceN, fderiv_neg, Finset.sum_neg_distrib]

lemma IsVariationTestField.neg {n : ℕ} {U : Set (EuclideanSpace ℝ (Fin n))}
    {X : EuclideanSpace ℝ (Fin n) → EuclideanSpace ℝ (Fin n)}
    (hX : IsVariationTestField U X) : IsVariationTestField U (-X) := by
  exact ⟨hX.1.neg, hX.2.1.neg, by simpa using hX.2.2.1, by simpa using hX.2.2.2⟩

lemma perimeterIn_compl_le {n : ℕ} {E U : Set (EuclideanSpace ℝ (Fin n))}
    (hE : NullMeasurableSet E volume) (_hU : IsOpen U) : perimeterIn Eᶜ U ≤ perimeterIn E U := by
  apply iSup_le
  intro X
  apply iSup_le
  intro hX
  have hint := integrable_divergenceN hX.1 hX.2.1
  have hEi : IntegrableOn (fun x => E.indicator (fun _ => (1 : ℝ)) x * divergenceN X x) U := by
    have heq : (fun x => E.indicator (fun _ => (1 : ℝ)) x * divergenceN X x) =
        E.indicator (divergenceN X) := by
      funext x
      by_cases hx : x ∈ E <;> simp [hx]
    rw [heq]
    exact (hint.indicator₀ hE).integrableOn
  have hdivzero : (∫ x in U, divergenceN X x) = 0 := by
    rw [setIntegral_eq_integral_of_forall_compl_eq_zero]
    · exact integral_divergenceN_eq_zero hX.1 hX.2.1
    · intro x hx
      exact divergenceN_eq_zero_of_notMem_tsupport (fun h => hx (hX.2.2.1 h))
  have heq : (fun x => Eᶜ.indicator (fun _ => (1 : ℝ)) x * divergenceN X x) =
      (fun x => divergenceN X x - E.indicator (fun _ => (1 : ℝ)) x * divergenceN X x) := by
    funext x
    by_cases hx : x ∈ E <;> simp [hx]
  rw [heq, integral_sub hint.integrableOn hEi, hdivzero, zero_sub]
  have hneg : -(∫ x in U, E.indicator (fun _ => (1 : ℝ)) x * divergenceN X x) =
      ∫ x in U, E.indicator (fun _ => (1 : ℝ)) x * divergenceN (-X) x := by
    simp only [divergenceN_neg, mul_neg, integral_neg]
  rw [hneg]
  apply le_iSup_of_le (-X)
  exact le_iSup (fun _ : IsVariationTestField U (-X) =>
    ENNReal.ofReal (∫ x in U, E.indicator (fun _ => (1 : ℝ)) x * divergenceN (-X) x)) hX.neg

/-- Complement invariance in blueprint `lem:perimeter-invariances`. -/
theorem perimeterIn_compl {n : ℕ} {E U : Set (EuclideanSpace ℝ (Fin n))}
    (hE : NullMeasurableSet E volume) (hU : IsOpen U) : perimeterIn Eᶜ U = perimeterIn E U := by
  apply le_antisymm (perimeterIn_compl_le hE hU)
  simpa only [compl_compl] using perimeterIn_compl_le hE.compl hU

/-- Taking the complement preserves global perimeter. -/
theorem perimeterN_compl {n : ℕ} {E : Set (EuclideanSpace ℝ (Fin n))}
    (hE : NullMeasurableSet E volume) : perimeterN Eᶜ = perimeterN E :=
  perimeterIn_compl hE isOpen_univ


/-! ## Smooth test fields -/

/-- Smooth fields with the same support and norm requirements as variation test fields. -/
def IsSmoothVariationTestField {n : ℕ} (U : Set (EuclideanSpace ℝ (Fin n)))
    (X : EuclideanSpace ℝ (Fin n) → EuclideanSpace ℝ (Fin n)) : Prop :=
  ContDiff ℝ (⊤ : ℕ∞) X ∧ HasCompactSupport X ∧ tsupport X ⊆ U ∧ ∀ x, ‖X x‖ ≤ 1

lemma IsSmoothVariationTestField.toVariationTestField {n : ℕ}
    {U : Set (EuclideanSpace ℝ (Fin n))}
    {X : EuclideanSpace ℝ (Fin n) → EuclideanSpace ℝ (Fin n)}
    (hX : IsSmoothVariationTestField U X) : IsVariationTestField U X :=
  ⟨hX.1.of_le (by simp), hX.2⟩

/-- The variation supremum restricted to smooth compactly supported fields. -/
noncomputable def smoothVariation {n : ℕ} (f : EuclideanSpace ℝ (Fin n) → ℝ)
    (U : Set (EuclideanSpace ℝ (Fin n))) : ℝ≥0∞ :=
  ⨆ X, ⨆ (_ : IsSmoothVariationTestField U X),
    ENNReal.ofReal (∫ x in U, f x * divergenceN X x)

private noncomputable def divergenceTrace (n : ℕ) :
    (EuclideanSpace ℝ (Fin n) →L[ℝ] EuclideanSpace ℝ (Fin n)) →L[ℝ] ℝ :=
  ∑ i, (EuclideanSpace.proj i).comp
    (ContinuousLinearMap.apply ℝ (EuclideanSpace ℝ (Fin n)) (EuclideanSpace.single i 1))

private lemma divergenceTrace_apply {n : ℕ}
    (A : EuclideanSpace ℝ (Fin n) →L[ℝ] EuclideanSpace ℝ (Fin n)) :
    divergenceTrace n A = ∑ i, A (EuclideanSpace.single i 1) i := by
  simp [divergenceTrace]

open ContinuousLinearMap in
/-- Mollification by a normalized smooth bump. -/
noncomputable def mollifyTestField {n : ℕ} (φ : ContDiffBump (0 : EuclideanSpace ℝ (Fin n)))
    (X : EuclideanSpace ℝ (Fin n) → EuclideanSpace ℝ (Fin n)) :=
  MeasureTheory.convolution (φ.normed volume) X (lsmul ℝ ℝ) volume

open scoped Convolution Pointwise

lemma mollifyTestField_contDiff {n : ℕ}
    (φ : ContDiffBump (0 : EuclideanSpace ℝ (Fin n)))
    {X : EuclideanSpace ℝ (Fin n) → EuclideanSpace ℝ (Fin n)} (hX : Continuous X) :
    ContDiff ℝ (⊤ : ℕ∞) (mollifyTestField φ X) :=
  φ.hasCompactSupport_normed.contDiff_convolution_left _ φ.contDiff_normed hX.locallyIntegrable

lemma mollifyTestField_norm_le {n : ℕ}
    (φ : ContDiffBump (0 : EuclideanSpace ℝ (Fin n)))
    {X : EuclideanSpace ℝ (Fin n) → EuclideanSpace ℝ (Fin n)}
    (hX : Continuous X) (hbound : ∀ x, ‖X x‖ ≤ 1) (x : EuclideanSpace ℝ (Fin n)) :
    ‖mollifyTestField φ X x‖ ≤ 1 := by
  simpa only [dist_zero_right, mollifyTestField] using
    (dist_convolution_le (μ := volume) (x₀ := x) (z₀ := 0) zero_le_one
      (φ.support_normed_eq.subset) φ.nonneg_normed φ.integral_normed
      hX.aestronglyMeasurable (fun y _ => by simpa using hbound y))

lemma mollifyTestField_support {n : ℕ}
    (φ : ContDiffBump (0 : EuclideanSpace ℝ (Fin n)))
    {X : EuclideanSpace ℝ (Fin n) → EuclideanSpace ℝ (Fin n)}
    {δ : ℝ} (hδ : φ.rOut ≤ δ) :
    tsupport (mollifyTestField φ X) ⊆ cthickening δ (tsupport X) := by
  apply closure_minimal _ isClosed_cthickening
  intro x hx
  obtain ⟨a, ha, b, hb, rfl⟩ := support_convolution_subset_swap
    (ContinuousLinearMap.lsmul ℝ ℝ) hx
  apply mem_cthickening_of_dist_le (a + b) a δ _ (subset_closure ha)
  have hb' : ‖b‖ < φ.rOut := by
    simpa only [φ.support_normed_eq, mem_ball_zero_iff] using hb
  simpa only [dist_eq_norm, add_sub_cancel_left] using hb'.le.trans hδ

lemma divergenceN_mollifyTestField {n : ℕ}
    (φ : ContDiffBump (0 : EuclideanSpace ℝ (Fin n)))
    {X : EuclideanSpace ℝ (Fin n) → EuclideanSpace ℝ (Fin n)}
    (hX : ContDiff ℝ 1 X) (hcX : HasCompactSupport X) (x : EuclideanSpace ℝ (Fin n)) :
    divergenceN (mollifyTestField φ X) x =
      (φ.normed volume ⋆[ContinuousLinearMap.lsmul ℝ ℝ, volume] divergenceN X) x := by
  have hpre : (ContinuousLinearMap.lsmul ℝ ℝ (E := EuclideanSpace ℝ (Fin n))).precompR
      (EuclideanSpace ℝ (Fin n)) = ContinuousLinearMap.lsmul ℝ ℝ := by
    ext c A v
    rfl
  have hd := (hcX.hasFDerivAt_convolution_right (μ := volume) (ContinuousLinearMap.lsmul ℝ ℝ)
    (φ.continuous_normed (μ := volume)).locallyIntegrable hX x).fderiv
  rw [hpre] at hd
  rw [show divergenceN (mollifyTestField φ X) x =
    divergenceTrace n (fderiv ℝ (mollifyTestField φ X) x) by
      rw [divergenceTrace_apply]; rfl]
  change divergenceTrace n
    (fderiv ℝ (φ.normed volume ⋆[ContinuousLinearMap.lsmul ℝ ℝ, volume] X) x) = _
  rw [hd]
  have hi := (hcX.fderiv ℝ).convolutionExists_right (μ := volume) (ContinuousLinearMap.lsmul ℝ ℝ)
    (φ.continuous_normed (μ := volume)).locallyIntegrable (hX.continuous_fderiv one_ne_zero) x
  rw [convolution_def, ← (divergenceTrace n).integral_comp_comm hi]
  simp only [convolution_def, ContinuousLinearMap.lsmul_apply, map_smul,
    divergenceTrace_apply, divergenceN, smul_eq_mul]

/-- Every admissible C¹ field can be approximated, in its pairing with a locally integrable
function, by admissible smooth fields. All the approximating supports lie in one compact
subset of the given open set. -/
theorem exists_smoothVariationTestField_sequence {n : ℕ}
    {U : Set (EuclideanSpace ℝ (Fin n))} (hU : IsOpen U)
    {f : EuclideanSpace ℝ (Fin n) → ℝ} (hf : LocallyIntegrableOn f U)
    {X : EuclideanSpace ℝ (Fin n) → EuclideanSpace ℝ (Fin n)}
    (hX : IsVariationTestField U X) :
    ∃ Y : ℕ → EuclideanSpace ℝ (Fin n) → EuclideanSpace ℝ (Fin n),
      (∀ j, IsSmoothVariationTestField U (Y j)) ∧
      Tendsto (fun j => ∫ x in U, f x * divergenceN (Y j) x) atTop
        (𝓝 (∫ x in U, f x * divergenceN X x)) := by
  obtain ⟨δ, hδ, hδU⟩ := hX.2.1.exists_cthickening_subset_open hU hX.2.2.1
  let K := cthickening δ (tsupport X)
  have hK : IsCompact K := hX.2.1.cthickening
  have hXK : tsupport X ⊆ K := self_subset_cthickening _
  have hfK : IntegrableOn f K := hf.integrableOn_compact_subset hδU hK
  let φ (j : ℕ) : ContDiffBump (0 : EuclideanSpace ℝ (Fin n)) :=
    ⟨(δ / ((j : ℝ) + 1)) / 2, δ / ((j : ℝ) + 1), by positivity,
      half_lt_self (by positivity)⟩
  have hφδ (j : ℕ) : (φ j).rOut ≤ δ := by
    exact div_le_self hδ.le (by have := Nat.cast_nonneg (α := ℝ) j; linarith)
  have hφlim : Tendsto (fun j => (φ j).rOut) atTop (𝓝 0) := by
    simpa only [mul_one_div, mul_zero] using
      (tendsto_one_div_add_atTop_nhds_zero_nat (𝕜 := ℝ)).const_mul δ
  let Y := fun j => mollifyTestField (φ j) X
  have hYK (j : ℕ) : tsupport (Y j) ⊆ K := mollifyTestField_support (φ j) (hφδ j)
  have hY (j : ℕ) : IsSmoothVariationTestField U (Y j) := by
    refine ⟨mollifyTestField_contDiff _ hX.1.continuous, ?_, (hYK j).trans hδU,
      mollifyTestField_norm_le _ hX.1.continuous hX.2.2.2⟩
    exact (φ j).hasCompactSupport_normed.convolution (ContinuousLinearMap.lsmul ℝ ℝ) hX.2.1
  have hcdiv : HasCompactSupport (divergenceN X) := by
    apply hX.2.1.mono'
    intro x hx
    by_contra hx'
    exact hx (divergenceN_eq_zero_of_notMem_tsupport hx')
  obtain ⟨C, hC⟩ := hcdiv.exists_bound_of_continuous (continuous_divergenceN hX.1)
  have hC0 : 0 ≤ C := (norm_nonneg _).trans (hC 0)
  have hYbound (j : ℕ) (x : EuclideanSpace ℝ (Fin n)) : ‖divergenceN (Y j) x‖ ≤ C := by
    rw [divergenceN_mollifyTestField (φ j) hX.1 hX.2.1]
    simpa only [dist_zero_right] using
      (dist_convolution_le (μ := volume) (x₀ := x) (z₀ := 0) hC0
        (φ j).support_normed_eq.subset (φ j).nonneg_normed (φ j).integral_normed
        (continuous_divergenceN hX.1).aestronglyMeasurable
        (fun y _ => by simpa using hC y))
  have hYlim (x : EuclideanSpace ℝ (Fin n)) :
      Tendsto (fun j => divergenceN (Y j) x) atTop (𝓝 (divergenceN X x)) := by
    simp_rw [show ∀ j, divergenceN (Y j) x =
      ((φ j).normed volume ⋆[ContinuousLinearMap.lsmul ℝ ℝ, volume] divergenceN X) x
      from fun j => divergenceN_mollifyTestField (φ j) hX.1 hX.2.1 x]
    exact ContDiffBump.convolution_tendsto_right_of_continuous hφlim
      (continuous_divergenceN hX.1) x
  have hrestrict (Z : EuclideanSpace ℝ (Fin n) → EuclideanSpace ℝ (Fin n))
      (hZ : tsupport Z ⊆ K) :
      (∫ x in U, f x * divergenceN Z x) = ∫ x in K, f x * divergenceN Z x := by
    apply setIntegral_eq_of_subset_of_forall_sdiff_eq_zero hU.measurableSet hδU
    intro x hx
    rw [divergenceN_eq_zero_of_notMem_tsupport (fun h => hx.2 (hZ h)), mul_zero]
  refine ⟨Y, hY, ?_⟩
  simp_rw [hrestrict _ (hYK _), hrestrict X hXK]
  apply tendsto_integral_of_dominated_convergence (fun x => ‖f x‖ * C)
  · intro j
    exact hfK.aestronglyMeasurable.mul
      (continuous_divergenceN (hY j).toVariationTestField.1).aestronglyMeasurable
  · exact hfK.norm.mul_const C
  · intro j
    exact Eventually.of_forall fun x => by
      rw [norm_mul]
      exact mul_le_mul_of_nonneg_left (hYbound j x) (norm_nonneg _)
  · exact Eventually.of_forall fun x => (hYlim x).const_mul (f x)

/-- Blueprint `lem:test-class`: C¹ and smooth compactly supported vector fields give
exactly the same variation supremum on an open set. -/
theorem variation_eq_smoothVariation {n : ℕ}
    {U : Set (EuclideanSpace ℝ (Fin n))} (hU : IsOpen U)
    {f : EuclideanSpace ℝ (Fin n) → ℝ} (hf : LocallyIntegrableOn f U) :
    variation f U = smoothVariation f U := by
  apply le_antisymm
  · apply iSup_le
    intro X
    apply iSup_le
    intro hX
    obtain ⟨Y, hY, hlim⟩ := exists_smoothVariationTestField_sequence hU hf hX
    apply le_of_tendsto (ENNReal.continuous_ofReal.tendsto _ |>.comp hlim)
    exact Eventually.of_forall fun j =>
      le_iSup_of_le (Y j) (le_iSup_of_le (hY j) le_rfl)
  · apply iSup_le
    intro X
    apply iSup_le
    intro hX
    exact le_iSup_of_le X (le_iSup_of_le hX.toVariationTestField le_rfl)

/-! ## Distributional derivative and its finite-variation bound -/

set_option maxSynthPendingDepth 8

lemma divergenceN_const_smul {n : ℕ} (c : ℝ)
    (X : EuclideanSpace ℝ (Fin n) → EuclideanSpace ℝ (Fin n))
    (x : EuclideanSpace ℝ (Fin n)) : divergenceN (c • X) x = c * divergenceN X x := by
  simp [divergenceN, fderiv_const_smul_field, Finset.mul_sum]

lemma divergenceN_add {n : ℕ}
    {X Y : EuclideanSpace ℝ (Fin n) → EuclideanSpace ℝ (Fin n)}
    (hX : ContDiff ℝ 1 X) (hY : ContDiff ℝ 1 Y) (x : EuclideanSpace ℝ (Fin n)) :
    divergenceN (X + Y) x = divergenceN X x + divergenceN Y x := by
  simp [divergenceN, fderiv_add (hX.differentiable one_ne_zero x)
    (hY.differentiable one_ne_zero x), Finset.sum_add_distrib]

/-- Local integrability suffices for pairing with the divergence of a supported C¹ field. -/
lemma integrable_mul_divergenceN {n : ℕ}
    {U : Set (EuclideanSpace ℝ (Fin n))} {f : EuclideanSpace ℝ (Fin n) → ℝ}
    (hf : LocallyIntegrableOn f U)
    {X : EuclideanSpace ℝ (Fin n) → EuclideanSpace ℝ (Fin n)}
    (hX : ContDiff ℝ 1 X) (hcX : HasCompactSupport X) (hsX : tsupport X ⊆ U) :
    Integrable (fun x => f x * divergenceN X x) := by
  have hi := (hf.integrableOn_compact_subset hsX hcX).mul_continuousOn
    (continuous_divergenceN hX).continuousOn hcX
  apply (integrableOn_iff_integrable_of_support_subset ?_).mp hi
  intro x hx
  by_contra hx'
  exact hx (by simp [divergenceN_eq_zero_of_notMem_tsupport hx'])

lemma abs_integral_mul_divergenceN_le_variation {n : ℕ}
    {U : Set (EuclideanSpace ℝ (Fin n))} {f : EuclideanSpace ℝ (Fin n) → ℝ}
    (hV : variation f U ≠ ∞)
    {X : EuclideanSpace ℝ (Fin n) → EuclideanSpace ℝ (Fin n)}
    (hX : IsVariationTestField U X) :
    |∫ x in U, f x * divergenceN X x| ≤ (variation f U).toReal := by
  have hle (Y) (hY : IsVariationTestField U Y) :
      (∫ x in U, f x * divergenceN Y x) ≤ (variation f U).toReal :=
    (ENNReal.ofReal_le_iff_le_toReal hV).mp
      (le_iSup_of_le Y (le_iSup_of_le hY le_rfl))
  apply abs_le.mpr
  constructor
  · have h := hle (-X) hX.neg
    simp only [divergenceN_neg, mul_neg, integral_neg] at h
    linarith
  · exact hle X hX

/-- The distributional pairing has operator norm at most the finite variation.
The bound is valid for every nonnegative uniform bound on the field. -/
theorem abs_integral_mul_divergenceN_le_mul_variation {n : ℕ}
    {U : Set (EuclideanSpace ℝ (Fin n))} {f : EuclideanSpace ℝ (Fin n) → ℝ}
    (hV : variation f U ≠ ∞)
    {X : EuclideanSpace ℝ (Fin n) → EuclideanSpace ℝ (Fin n)}
    (hX : ContDiff ℝ 1 X) (hcX : HasCompactSupport X) (hsX : tsupport X ⊆ U)
    {C : ℝ} (hC : 0 ≤ C) (hb : ∀ x, ‖X x‖ ≤ C) :
    |∫ x in U, f x * divergenceN X x| ≤ (variation f U).toReal * C := by
  rcases hC.eq_or_lt with rfl | hC
  · have hz : X = 0 := by funext x; exact norm_le_zero_iff.mp (hb x)
    simp [hz, divergenceN]
  have htest : IsVariationTestField U (C⁻¹ • X) := by
    refine ⟨?_, hcX.smul_left, ?_, ?_⟩
    · change ContDiff ℝ 1 (fun x => C⁻¹ • X x)
      exact ContDiff.const_smul (𝕜 := ℝ) (R := ℝ) C⁻¹ hX
    · exact (tsupport_smul_subset_right (fun _ => C⁻¹) X).trans hsX
    · intro x
      simp only [Pi.smul_apply, norm_smul, Real.norm_eq_abs, abs_inv, abs_of_pos hC]
      exact (mul_le_mul_of_nonneg_left (hb x) (inv_nonneg.mpr hC.le)).trans_eq
        (inv_mul_cancel₀ hC.ne')
  have h := abs_integral_mul_divergenceN_le_variation hV htest
  simp_rw [divergenceN_const_smul, mul_left_comm (f _) C⁻¹] at h
  rw [integral_const_mul, abs_mul, abs_inv, abs_of_pos hC] at h
  calc
    |∫ x in U, f x * divergenceN X x| =
        C * (C⁻¹ * |∫ x in U, f x * divergenceN X x|) := by
      rw [← mul_assoc, mul_inv_cancel₀ hC.ne', one_mul]
    _ ≤ C * (variation f U).toReal := mul_le_mul_of_nonneg_left h hC.le
    _ = _ := mul_comm _ _

/-- C¹ compactly supported fields inside an open domain, as a subspace of bounded
continuous fields with the uniform norm. -/
def c1SupportedFields {n : ℕ} (U : Set (EuclideanSpace ℝ (Fin n))) :
    Submodule ℝ (EuclideanSpace ℝ (Fin n) →ᵇ EuclideanSpace ℝ (Fin n)) where
  carrier := {X | ContDiff ℝ 1 X ∧ HasCompactSupport X ∧ tsupport X ⊆ U}
  zero_mem' := by
    refine ⟨contDiff_const, HasCompactSupport.zero, ?_⟩
    simp
  add_mem' := by
    intro X Y hX hY
    exact ⟨hX.1.add hY.1, hX.2.1.add hY.2.1,
      (tsupport_add X Y).trans (union_subset hX.2.2 hY.2.2)⟩
  smul_mem' := by
    intro c X hX
    exact ⟨hX.1.const_smul c, hX.2.1.smul_left,
      (tsupport_smul_subset_right (fun _ => c) X).trans hX.2.2⟩

/-- The distributional derivative paired against a supported vector field.
The minus sign agrees with the usual distributional derivative convention. -/
noncomputable def distributionalVariationFunctional {n : ℕ}
    {U : Set (EuclideanSpace ℝ (Fin n))} {f : EuclideanSpace ℝ (Fin n) → ℝ}
    (hf : LocallyIntegrableOn f U) : c1SupportedFields U →ₗ[ℝ] ℝ where
  toFun X := -(∫ x in U, f x * divergenceN X.val x)
  map_add' X Y := by
    have hi (Z : c1SupportedFields U) :=
      (integrable_mul_divergenceN hf Z.property.1 Z.property.2.1 Z.property.2.2).integrableOn
        (s := U)
    change -(∫ x in U, f x * divergenceN (X.val + Y.val) x) = _
    simp only [BoundedContinuousFunction.coe_add, divergenceN_add X.property.1 Y.property.1,
      mul_add, integral_add (hi X) (hi Y), neg_add]
  map_smul' c X := by
    change -(∫ x in U, f x * divergenceN (c • X.val) x) = _
    simp only [BoundedContinuousFunction.coe_smul]
    change -(∫ x in U, f x * divergenceN (c • (X.val : _ → _)) x) = _
    simp_rw [divergenceN_const_smul, mul_left_comm (f _) c]
    rw [integral_const_mul]
    simp only [RingHom.id_apply, smul_eq_mul, mul_neg]

/-- Agreement of a bounded continuous vector functional with the distributional pairing
on every compactly supported C¹ field in the indicated domain. -/
def RepresentsDistributionalVariation {n : ℕ} (f : EuclideanSpace ℝ (Fin n) → ℝ)
    (U : Set (EuclideanSpace ℝ (Fin n)))
    (Λ : (EuclideanSpace ℝ (Fin n) →ᵇ EuclideanSpace ℝ (Fin n)) →L[ℝ] ℝ) : Prop :=
  ∀ X : EuclideanSpace ℝ (Fin n) →ᵇ EuclideanSpace ℝ (Fin n),
    ContDiff ℝ 1 X → HasCompactSupport X → tsupport X ⊆ U →
    Λ X = -(∫ x in U, f x * divergenceN X x)

/-- On a domain with finite variation, the distributional pairing extends to all bounded
continuous vector fields without increasing its variation bound. This extension is used
only on compactly supported fields in the construction of the derivative measure. -/
theorem exists_distributionalVariation_extension {n : ℕ}
    {U : Set (EuclideanSpace ℝ (Fin n))} {f : EuclideanSpace ℝ (Fin n) → ℝ}
    (hf : LocallyIntegrableOn f U) (hV : variation f U ≠ ∞) :
    ∃ Λ : (EuclideanSpace ℝ (Fin n) →ᵇ EuclideanSpace ℝ (Fin n)) →L[ℝ] ℝ,
      ‖Λ‖ ≤ (variation f U).toReal ∧ RepresentsDistributionalVariation f U Λ := by
  let L : c1SupportedFields U →ₗ[ℝ] ℝ := distributionalVariationFunctional hf
  have hbound (X : c1SupportedFields U) : ‖L X‖ ≤ (variation f U).toReal * ‖X‖ := by
    change ‖-(∫ x in U, f x * divergenceN X.val x)‖ ≤ (variation f U).toReal * ‖X.val‖
    rw [norm_neg, Real.norm_eq_abs]
    exact
      abs_integral_mul_divergenceN_le_mul_variation hV X.property.1 X.property.2.1
        X.property.2.2 (norm_nonneg X.val) X.val.norm_coe_le_norm
  let Lc : c1SupportedFields U →L[ℝ] ℝ := L.mkContinuous (variation f U).toReal hbound
  obtain ⟨Λ, hΛ, hnorm⟩ := exists_extension_norm_eq (c1SupportedFields U) Lc
  refine ⟨Λ, hnorm.le.trans (L.mkContinuous_norm_le ENNReal.toReal_nonneg hbound), ?_⟩
  intro X hX hcX hsX
  exact hΛ ⟨X, hX, hcX, hsX⟩

/-- Embed a scalar bounded continuous test function in one Euclidean coordinate. -/
noncomputable def coordinateTestField {n : ℕ} (i : Fin n) :
    (EuclideanSpace ℝ (Fin n) →ᵇ ℝ) →L[ℝ]
      (EuclideanSpace ℝ (Fin n) →ᵇ EuclideanSpace ℝ (Fin n)) :=
  ((ContinuousLinearMap.id ℝ ℝ).smulRight (EuclideanSpace.single i 1)).compLeftContinuousBounded _

@[simp] lemma coordinateTestField_apply {n : ℕ} (i : Fin n)
    (φ : EuclideanSpace ℝ (Fin n) →ᵇ ℝ) (x : EuclideanSpace ℝ (Fin n)) :
    coordinateTestField i φ x = φ x • EuclideanSpace.single i 1 := rfl

lemma norm_coordinateTestField_le {n : ℕ} (i : Fin n)
    (φ : EuclideanSpace ℝ (Fin n) →ᵇ ℝ) : ‖coordinateTestField i φ‖ ≤ ‖φ‖ := by
  apply (BoundedContinuousFunction.norm_le (norm_nonneg φ)).mpr
  intro x
  simpa only [coordinateTestField_apply, norm_smul, PiLp.norm_single, norm_one, mul_one]
    using φ.norm_coe_le_norm x

lemma divergenceN_coordinateTestField {n : ℕ} (i : Fin n)
    {φ : EuclideanSpace ℝ (Fin n) →ᵇ ℝ} (hφ : ContDiff ℝ 1 φ)
    (x : EuclideanSpace ℝ (Fin n)) :
    divergenceN (coordinateTestField i φ) x = fderiv ℝ φ x (EuclideanSpace.single i 1) := by
  change divergenceN (fun y => φ y • EuclideanSpace.single i 1) x = _
  simp [divergenceN, fderiv_smul_const (hφ.differentiable one_ne_zero x)]

open scoped CompactlySupported

/-- Restrict a vector functional to scalar compactly supported tests in one coordinate. -/
noncomputable def coordinateTestFunctional {n : ℕ}
    (Λ : (EuclideanSpace ℝ (Fin n) →ᵇ EuclideanSpace ℝ (Fin n)) →L[ℝ] ℝ)
    (i : Fin n) : C_c(EuclideanSpace ℝ (Fin n), ℝ) →ₗ[ℝ] ℝ where
  toFun φ := Λ (coordinateTestField i φ.toBoundedContinuousFunction)
  map_add' φ ψ := by
    rw [← map_add]
    congr 1
    apply BoundedContinuousFunction.ext
    intro x
    change (φ x + ψ x) • EuclideanSpace.single i (1 : ℝ) =
      φ x • EuclideanSpace.single i (1 : ℝ) + ψ x • EuclideanSpace.single i (1 : ℝ)
    exact add_smul _ _ _
  map_smul' c φ := by
    rw [← map_smul]
    congr 1
    apply BoundedContinuousFunction.ext
    intro x
    change (c * φ x) • EuclideanSpace.single i (1 : ℝ) = c • (φ x • EuclideanSpace.single i (1 : ℝ))
    exact mul_smul _ _ _

lemma locallyBounded_coordinateTestFunctional {n : ℕ}
    (Λ : (EuclideanSpace ℝ (Fin n) →ᵇ EuclideanSpace ℝ (Fin n)) →L[ℝ] ℝ)
    (i : Fin n) : IsLocallyBoundedFunctional (coordinateTestFunctional Λ i) := by
  intro K hK
  refine ⟨‖Λ‖, norm_nonneg Λ, fun φ _ => ?_⟩
  calc
    |coordinateTestFunctional Λ i φ| ≤
        ‖Λ‖ * ‖coordinateTestField i φ.toBoundedContinuousFunction‖ :=
      Λ.le_opNorm _
    _ ≤ ‖Λ‖ * ‖φ.toBoundedContinuousFunction‖ :=
      mul_le_mul_of_nonneg_left (norm_coordinateTestField_le i _) (norm_nonneg _)

/-- Finite variation gives signed Radon representatives of every coordinate derivative.
The representatives are ambient measures; the test identity concerns fields supported in `U`.
This is the finite-domain representation step of blueprint `thm:polar`. -/
theorem exists_coordinateDerivative_measures {n : ℕ}
    {U : Set (EuclideanSpace ℝ (Fin n))} {f : EuclideanSpace ℝ (Fin n) → ℝ}
    (hf : LocallyIntegrableOn f U) (hV : variation f U ≠ ∞) :
    ∃ μpos μneg : Fin n → Measure (EuclideanSpace ℝ (Fin n)),
      (∀ i, (μpos i).Regular ∧ (μneg i).Regular ∧
        IsFiniteMeasureOnCompacts (μpos i) ∧ IsFiniteMeasureOnCompacts (μneg i)) ∧
      ∀ i (φ : C_c(EuclideanSpace ℝ (Fin n), ℝ)), ContDiff ℝ 1 φ → tsupport φ ⊆ U →
        -(∫ x in U, f x * fderiv ℝ φ x (EuclideanSpace.single i 1)) =
          (∫ x, φ x ∂μpos i) - ∫ x, φ x ∂μneg i := by
  obtain ⟨Λ, _, hΛ⟩ := exists_distributionalVariation_extension hf hV
  have hrep (i : Fin n) := signed_riesz (coordinateTestFunctional Λ i)
    (locallyBounded_coordinateTestFunctional Λ i)
  choose μpos μneg hp hn hfp hfn hrep using hrep
  refine ⟨μpos, μneg, fun i => ⟨hp i, hn i, hfp i, hfn i⟩, ?_⟩
  intro i φ hφ hsφ
  rw [← hrep i φ]
  change _ = Λ (coordinateTestField i φ.toBoundedContinuousFunction)
  have hcont : ContDiff ℝ 1 (coordinateTestField i φ.toBoundedContinuousFunction) :=
    hφ.smul contDiff_const
  have hcompact : HasCompactSupport (coordinateTestField i φ.toBoundedContinuousFunction) :=
    φ.hasCompactSupport.smul_right
  have hsupport : tsupport (coordinateTestField i φ.toBoundedContinuousFunction) ⊆ U :=
    (tsupport_smul_subset_left φ (fun _ => EuclideanSpace.single i 1)).trans hsφ
  rw [hΛ _ hcont hcompact hsupport]
  simp only [divergenceN_coordinateTestField i (φ := φ.toBoundedContinuousFunction) hφ]
  rfl

/-- A locally BV function has a finite-variation open neighborhood of every compact
subset of its domain. The closure of that neighborhood is compact and remains in the domain. -/
lemma IsLocallyBVOn.exists_finite_variation_neighborhood {n : ℕ}
    {U K : Set (EuclideanSpace ℝ (Fin n))} (hU : IsOpen U)
    {f : EuclideanSpace ℝ (Fin n) → ℝ} (hf : IsLocallyBVOn f U)
    (hK : IsCompact K) (hKU : K ⊆ U) :
    ∃ A, IsOpen A ∧ K ⊆ A ∧ closure A ⊆ U ∧ IsCompact (closure A) ∧
      variation f A ≠ ∞ := by
  obtain ⟨A, hA, hKA, hAU, hcA⟩ := exists_open_between_and_isCompact_closure hK hU hKU
  exact ⟨A, hA, hKA, hAU, hcA, (hf.2 A hA hcA hAU).ne⟩

/-- Coordinate derivative measures exist near every compact subset of an open locally BV
domain. Compatibility and identification of their total variation are subsequent steps. -/
theorem exists_local_coordinateDerivative_measures {n : ℕ}
    {U K : Set (EuclideanSpace ℝ (Fin n))} (hU : IsOpen U)
    {f : EuclideanSpace ℝ (Fin n) → ℝ} (hf : IsLocallyBVOn f U)
    (hK : IsCompact K) (hKU : K ⊆ U) :
    ∃ A : Set (EuclideanSpace ℝ (Fin n)),
      IsOpen A ∧ K ⊆ A ∧ closure A ⊆ U ∧ IsCompact (closure A) ∧
      ∃ μpos μneg : Fin n → Measure (EuclideanSpace ℝ (Fin n)),
        (∀ i, (μpos i).Regular ∧ (μneg i).Regular ∧
          IsFiniteMeasureOnCompacts (μpos i) ∧ IsFiniteMeasureOnCompacts (μneg i)) ∧
        ∀ i (φ : C_c(EuclideanSpace ℝ (Fin n), ℝ)), ContDiff ℝ 1 φ → tsupport φ ⊆ A →
          -(∫ x in U, f x * fderiv ℝ φ x (EuclideanSpace.single i 1)) =
            (∫ x, φ x ∂μpos i) - ∫ x, φ x ∂μneg i := by
  obtain ⟨A, hA, hKA, hAU, hcA, hV⟩ := hf.exists_finite_variation_neighborhood hU hK hKU
  have hAU' : A ⊆ U := subset_closure.trans hAU
  obtain ⟨μpos, μneg, hμ, hrep⟩ := exists_coordinateDerivative_measures
    (hf.1.mono_set hAU') hV
  refine ⟨A, hA, hKA, hAU, hcA, μpos, μneg, hμ, ?_⟩
  intro i φ hφ hsφ
  rw [← hrep i φ hφ hsφ]
  congr 1
  apply setIntegral_eq_of_subset_of_forall_sdiff_eq_zero hU.measurableSet hAU'
  intro x hx
  rw [fderiv_of_notMem_tsupport ℝ (fun h => hx.2 (hsφ h)), zero_apply, mul_zero]

/-- Normalized convolution approximates a uniformly continuous field uniformly. -/
theorem tendstoUniformly_mollifyTestField {n : ℕ}
    {φ : ℕ → ContDiffBump (0 : EuclideanSpace ℝ (Fin n))}
    (hφ : Tendsto (fun j => (φ j).rOut) atTop (𝓝 0))
    {X : EuclideanSpace ℝ (Fin n) → EuclideanSpace ℝ (Fin n)}
    (hX : UniformContinuous X) :
    TendstoUniformly (fun j => mollifyTestField (φ j) X) X atTop := by
  apply Metric.tendstoUniformly_iff.mpr
  intro ε hε
  obtain ⟨δ, hδ, hdist⟩ := Metric.uniformContinuous_iff.mp hX (ε / 2) (half_pos hε)
  filter_upwards [hφ.eventually (gt_mem_nhds hδ)] with j hj x
  rw [dist_comm]
  apply lt_of_le_of_lt _ (half_lt_self hε)
  exact (φ j).dist_normed_convolution_le hX.continuous.aestronglyMeasurable
    (fun y hy => (hdist ((mem_ball.mp hy).trans hj)).le)

/-- Continuous functionals agreeing on supported C¹ fields agree on all supported continuous
fields. This removes the choice of Hahn–Banach extension from local derivative pairings. -/
theorem vectorFunctionals_eq_on_compactSupport {n : ℕ}
    {U : Set (EuclideanSpace ℝ (Fin n))} (hU : IsOpen U)
    (Λ Λ' : (EuclideanSpace ℝ (Fin n) →ᵇ EuclideanSpace ℝ (Fin n)) →L[ℝ] ℝ)
    (hagree : ∀ X : EuclideanSpace ℝ (Fin n) →ᵇ EuclideanSpace ℝ (Fin n),
      ContDiff ℝ 1 X → HasCompactSupport X → tsupport X ⊆ U → Λ X = Λ' X)
    (X : EuclideanSpace ℝ (Fin n) →ᵇ EuclideanSpace ℝ (Fin n))
    (hcX : HasCompactSupport X) (hsX : tsupport X ⊆ U) : Λ X = Λ' X := by
  obtain ⟨δ, hδ, hδU⟩ := hcX.exists_cthickening_subset_open hU hsX
  let φ (j : ℕ) : ContDiffBump (0 : EuclideanSpace ℝ (Fin n)) :=
    ⟨(δ / ((j : ℝ) + 1)) / 2, δ / ((j : ℝ) + 1), by positivity,
      half_lt_self (by positivity)⟩
  have hφδ (j : ℕ) : (φ j).rOut ≤ δ :=
    div_le_self hδ.le (by have := Nat.cast_nonneg (α := ℝ) j; linarith)
  have hφlim : Tendsto (fun j => (φ j).rOut) atTop (𝓝 0) := by
    simpa only [mul_one_div, mul_zero] using
      (tendsto_one_div_add_atTop_nhds_zero_nat (𝕜 := ℝ)).const_mul δ
  let Y (j : ℕ) : C_c(EuclideanSpace ℝ (Fin n), EuclideanSpace ℝ (Fin n)) :=
    { toFun := mollifyTestField (φ j) X
      continuous_toFun := (mollifyTestField_contDiff (φ j) X.continuous).continuous
      hasCompactSupport' :=
        (φ j).hasCompactSupport_normed.convolution (ContinuousLinearMap.lsmul ℝ ℝ) hcX }
  have hYlim : Tendsto (fun j => (Y j).toBoundedContinuousFunction) atTop (𝓝 X) := by
    apply BoundedContinuousFunction.tendsto_iff_tendstoUniformly.mpr
    exact tendstoUniformly_mollifyTestField hφlim (hcX.uniformContinuous_of_continuous X.continuous)
  have heq (j : ℕ) :
      Λ (Y j).toBoundedContinuousFunction = Λ' (Y j).toBoundedContinuousFunction := by
    apply hagree
    · exact (mollifyTestField_contDiff (φ j) X.continuous).of_le (by simp)
    · exact (Y j).hasCompactSupport
    · exact (mollifyTestField_support (φ j) (hφδ j)).trans hδU
  exact tendsto_nhds_unique
    (((Λ.continuous.tendsto X).comp hYlim).congr' (Eventually.of_forall heq))
    ((Λ'.continuous.tendsto X).comp hYlim)


/-- Local continuous extensions agree on every continuous test field supported in their
overlap. Thus arbitrary extension choices give compatible local derivative pairings. -/
theorem RepresentsDistributionalVariation.eq_on_overlap {n : ℕ}
    {U V : Set (EuclideanSpace ℝ (Fin n))} (hU : IsOpen U) (hV : IsOpen V)
    {f : EuclideanSpace ℝ (Fin n) → ℝ}
    {Λ Λ' : (EuclideanSpace ℝ (Fin n) →ᵇ EuclideanSpace ℝ (Fin n)) →L[ℝ] ℝ}
    (hΛ : RepresentsDistributionalVariation f U Λ)
    (hΛ' : RepresentsDistributionalVariation f V Λ')
    (X : EuclideanSpace ℝ (Fin n) →ᵇ EuclideanSpace ℝ (Fin n))
    (hcX : HasCompactSupport X) (hsXU : tsupport X ⊆ U) (hsXV : tsupport X ⊆ V) :
    Λ X = Λ' X := by
  apply vectorFunctionals_eq_on_compactSupport (hU.inter hV) Λ Λ' _ X hcX
    (subset_inter hsXU hsXV)
  intro Y hY hcY hsY
  rw [hΛ Y hY hcY (hsY.trans inter_subset_left),
    hΛ' Y hY hcY (hsY.trans inter_subset_right)]
  congr 1
  have hzero (x) (hx : x ∉ U ∩ V) : f x * divergenceN Y x = 0 := by
    rw [divergenceN_eq_zero_of_notMem_tsupport (fun h => hx (hsY h)), mul_zero]
  calc
    (∫ x in U, f x * divergenceN Y x) = ∫ x in U ∩ V, f x * divergenceN Y x :=
      setIntegral_eq_of_subset_of_forall_sdiff_eq_zero hU.measurableSet inter_subset_left
        (fun x hx => hzero x hx.2)
    _ = ∫ x in V, f x * divergenceN Y x :=
      (setIntegral_eq_of_subset_of_forall_sdiff_eq_zero hV.measurableSet inter_subset_right
        (fun x hx => hzero x hx.2)).symm

/-! ## Gluing the derivative functional on an open domain -/

/-- Compactly supported continuous fields in the domain, with their ambient uniform norm. -/
def continuousSupportedFields {n : ℕ} (U : Set (EuclideanSpace ℝ (Fin n))) :
    Submodule ℝ (EuclideanSpace ℝ (Fin n) →ᵇ EuclideanSpace ℝ (Fin n)) where
  carrier := {X | HasCompactSupport X ∧ tsupport X ⊆ U}
  zero_mem' := by exact ⟨HasCompactSupport.zero, by simp⟩
  add_mem' := by
    intro X Y hX hY
    exact ⟨hX.1.add hY.1, (tsupport_add X Y).trans (union_subset hX.2 hY.2)⟩
  smul_mem' := by
    intro c X hX
    exact ⟨hX.1.smul_left, (tsupport_smul_subset_right (fun _ => c) X).trans hX.2⟩

/-- A continuous representative of the derivative pairing exists near each compact set. -/
lemma IsLocallyBVOn.exists_variation_extension_neighborhood {n : ℕ}
    {U K : Set (EuclideanSpace ℝ (Fin n))} (hU : IsOpen U)
    {f : EuclideanSpace ℝ (Fin n) → ℝ} (hf : IsLocallyBVOn f U)
    (hK : IsCompact K) (hKU : K ⊆ U) :
    ∃ A : Set (EuclideanSpace ℝ (Fin n)),
      ∃ Λ : (EuclideanSpace ℝ (Fin n) →ᵇ EuclideanSpace ℝ (Fin n)) →L[ℝ] ℝ,
        IsOpen A ∧ K ⊆ A ∧ A ⊆ U ∧ RepresentsDistributionalVariation f A Λ := by
  obtain ⟨A, hA, hKA, hAU, _, hV⟩ := hf.exists_finite_variation_neighborhood hU hK hKU
  have hAU' : A ⊆ U := subset_closure.trans hAU
  obtain ⟨Λ, _, hΛ⟩ := exists_distributionalVariation_extension (hf.1.mono_set hAU') hV
  exact ⟨A, Λ, hA, hKA, hAU', hΛ⟩

/-- The local derivative pairings glue to a locally uniformly bounded linear functional on
all continuous compactly supported vector fields in an open locally BV domain. The result
agrees with every local continuous extension, so it is independent of extension choices. -/
theorem exists_glued_distributionalVariationFunctional {n : ℕ}
    {U : Set (EuclideanSpace ℝ (Fin n))} (hU : IsOpen U)
    {f : EuclideanSpace ℝ (Fin n) → ℝ} (hf : IsLocallyBVOn f U) :
    ∃ L : continuousSupportedFields U →ₗ[ℝ] ℝ,
      (∀ K : Set (EuclideanSpace ℝ (Fin n)), IsCompact K → K ⊆ U →
        ∃ C : ℝ, 0 ≤ C ∧ ∀ X : continuousSupportedFields U, tsupport X.val ⊆ K →
          |L X| ≤ C * ‖X.val‖) ∧
      (∀ A : Set (EuclideanSpace ℝ (Fin n)), IsOpen A →
        ∀ Λ : (EuclideanSpace ℝ (Fin n) →ᵇ EuclideanSpace ℝ (Fin n)) →L[ℝ] ℝ,
          RepresentsDistributionalVariation f A Λ →
          ∀ X : continuousSupportedFields U, tsupport X.val ⊆ A → L X = Λ X.val) ∧
      ∀ X : continuousSupportedFields U, ContDiff ℝ 1 X.val →
        L X = -(∫ x in U, f x * divergenceN X.val x) := by
  have hex (X : continuousSupportedFields U) :=
    hf.exists_variation_extension_neighborhood hU X.property.1 X.property.2
  choose A Λ hA hXA hAU hΛ using hex
  let a (X : continuousSupportedFields U) := Λ X X.val
  have ha (B : Set (EuclideanSpace ℝ (Fin n))) (hB : IsOpen B)
      (Γ : (EuclideanSpace ℝ (Fin n) →ᵇ EuclideanSpace ℝ (Fin n)) →L[ℝ] ℝ)
      (hΓ : RepresentsDistributionalVariation f B Γ)
      (X : continuousSupportedFields U) (hsX : tsupport X.val ⊆ B) : a X = Γ X.val :=
    (hΛ X).eq_on_overlap (hA X) hB hΓ X.val X.property.1 (hXA X) hsX
  let L : continuousSupportedFields U →ₗ[ℝ] ℝ :=
    { toFun := a
      map_add' X Y := by
        obtain ⟨B, Γ, hB, hKB, _, hΓ⟩ := hf.exists_variation_extension_neighborhood hU
          (X.property.1.union Y.property.1) (union_subset X.property.2 Y.property.2)
        have hXB : tsupport X.val ⊆ B := subset_union_left.trans hKB
        have hYB : tsupport Y.val ⊆ B := subset_union_right.trans hKB
        have hadd : tsupport (X + Y).val ⊆ B := (tsupport_add X.val Y.val).trans hKB
        rw [ha B hB Γ hΓ (X + Y) hadd, ha B hB Γ hΓ X hXB, ha B hB Γ hΓ Y hYB]
        exact Γ.map_add X.val Y.val
      map_smul' c X := by
        have hsmul : tsupport (c • X).val ⊆ A X :=
          (tsupport_smul_subset_right (fun _ => c) X.val).trans (hXA X)
        rw [ha (A X) (hA X) (Λ X) (hΛ X) (c • X) hsmul,
          ha (A X) (hA X) (Λ X) (hΛ X) X (hXA X)]
        exact (Λ X).map_smul c X.val }
  refine ⟨L, ?_, ha, ?_⟩
  · intro K hK hKU
    obtain ⟨B, Γ, hB, hKB, _, hΓ⟩ := hf.exists_variation_extension_neighborhood hU hK hKU
    refine ⟨‖Γ‖, norm_nonneg Γ, fun X hsX => ?_⟩
    change |a X| ≤ _
    rw [ha B hB Γ hΓ X (hsX.trans hKB)]
    exact Γ.le_opNorm X.val
  · intro X hX
    change Λ X X.val = _
    rw [hΛ X X.val hX X.property.1 (hXA X)]
    congr 1
    symm
    apply setIntegral_eq_of_subset_of_forall_sdiff_eq_zero hU.measurableSet (hAU X)
    intro x hx
    rw [divergenceN_eq_zero_of_notMem_tsupport (fun h => hx.2 (hXA X h)), mul_zero]

/-- Zero extend a scalar test from the open subtype and place it in one Euclidean coordinate. -/
noncomputable def openCoordinateTestField {n : ℕ}
    {U : Set (EuclideanSpace ℝ (Fin n))} (hU : IsOpen U) (i : Fin n) :
    C_c(U, ℝ) →ₗ[ℝ] continuousSupportedFields U where
  toFun φ :=
    ⟨coordinateTestField i (zeroExtendCC hU φ).toBoundedContinuousFunction,
      (zeroExtendCC hU φ).hasCompactSupport.smul_right,
      (tsupport_smul_subset_left (zeroExtendCC hU φ)
        (fun _ => EuclideanSpace.single i (1 : ℝ))).trans (tsupport_zeroExtendCC_subset hU φ)⟩
  map_add' φ ψ := by
    apply Subtype.ext
    apply BoundedContinuousFunction.ext
    intro x
    change (zeroExtendCC hU (φ + ψ) x) • EuclideanSpace.single i (1 : ℝ) =
      (zeroExtendCC hU φ x) • EuclideanSpace.single i (1 : ℝ) +
        (zeroExtendCC hU ψ x) • EuclideanSpace.single i (1 : ℝ)
    rw [map_add]
    exact add_smul _ _ _
  map_smul' c φ := by
    apply Subtype.ext
    apply BoundedContinuousFunction.ext
    intro x
    change (zeroExtendCC hU (c • φ) x) • EuclideanSpace.single i (1 : ℝ) =
      c • ((zeroExtendCC hU φ x) • EuclideanSpace.single i (1 : ℝ))
    rw [map_smul]
    exact mul_smul _ _ _

lemma norm_openCoordinateTestField_le {n : ℕ}
    {U : Set (EuclideanSpace ℝ (Fin n))} (hU : IsOpen U) (i : Fin n) (φ : C_c(U, ℝ)) :
    ‖(openCoordinateTestField hU i φ).val‖ ≤ ‖φ.toBoundedContinuousFunction‖ :=
  (norm_coordinateTestField_le i _).trans_eq (norm_zeroExtendCC hU φ)

lemma tsupport_openCoordinateTestField_subset {n : ℕ}
    {U : Set (EuclideanSpace ℝ (Fin n))} (hU : IsOpen U) (i : Fin n) (φ : C_c(U, ℝ)) :
    tsupport (openCoordinateTestField hU i φ).val ⊆ Subtype.val '' tsupport φ := by
  rw [← tsupport_zeroExtendCC hU φ]
  exact tsupport_smul_subset_left (zeroExtendCC hU φ)
    (fun _ => EuclideanSpace.single i (1 : ℝ))

/-- The coordinate derivative functionals on the actual open subtype are locally bounded.
The test identity is stated using ambient C¹ functions with support in that open set. -/
theorem exists_distributional_coordinateFunctionals {n : ℕ}
    {U : Set (EuclideanSpace ℝ (Fin n))} (hU : IsOpen U)
    {f : EuclideanSpace ℝ (Fin n) → ℝ} (hf : IsLocallyBVOn f U) :
    ∃ L : Fin n → C_c(U, ℝ) →ₗ[ℝ] ℝ,
      (∀ i, IsLocallyBoundedFunctional (L i)) ∧
      ∀ i (φ : C_c(EuclideanSpace ℝ (Fin n), ℝ)),
        ContDiff ℝ 1 φ → ∀ hsφ : tsupport φ ⊆ U,
          L i (restrictSupportedCC ⟨φ, hsφ⟩) =
            -(∫ x in U, f x * fderiv ℝ φ x (EuclideanSpace.single i 1)) := by
  obtain ⟨Γ, hbound, _, hrep⟩ := exists_glued_distributionalVariationFunctional hU hf
  let L (i : Fin n) := Γ.comp (openCoordinateTestField hU i)
  refine ⟨L, ?_, ?_⟩
  · intro i K hK
    have hKU : Subtype.val '' K ⊆ U := by rintro _ ⟨x, _, rfl⟩; exact x.property
    obtain ⟨C, hC, hb⟩ := hbound (Subtype.val '' K) (hK.image continuous_subtype_val) hKU
    refine ⟨C, hC, fun φ hsφ => ?_⟩
    have hs : tsupport (openCoordinateTestField hU i φ).val ⊆ Subtype.val '' K :=
      (tsupport_openCoordinateTestField_subset hU i φ).trans (image_mono hsφ)
    exact (hb _ hs).trans
      (mul_le_mul_of_nonneg_left (norm_openCoordinateTestField_le hU i φ) hC)
  · intro i φ hφ hsφ
    let X := openCoordinateTestField hU i (restrictSupportedCC ⟨φ, hsφ⟩)
    have hX : X.val = coordinateTestField i φ.toBoundedContinuousFunction := by
      change coordinateTestField i
        (zeroExtendCC hU (restrictSupportedCC ⟨φ, hsφ⟩)).toBoundedContinuousFunction = _
      rw [zeroExtendCC_restrictSupportedCC]
    have hcX : ContDiff ℝ 1 X.val := by
      rw [hX]
      exact hφ.smul_const (EuclideanSpace.single i 1)
    change Γ X = _
    rw [hrep X hcX, hX]
    simp only [divergenceN_coordinateTestField i (φ := φ.toBoundedContinuousFunction) hφ]
    rfl

/-- On the entire open locally BV domain, each coordinate derivative is represented by
one pair of regular positive measures finite on compact sets. No finite global variation
or global integrability assumption is imposed. This is the Riesz stage of `thm:polar`. -/
theorem exists_global_coordinateDerivative_measures {n : ℕ}
    {U : Set (EuclideanSpace ℝ (Fin n))} (hU : IsOpen U)
    {f : EuclideanSpace ℝ (Fin n) → ℝ} (hf : IsLocallyBVOn f U) :
    ∃ μpos μneg : Fin n → Measure U,
      (∀ i, (μpos i).Regular ∧ (μneg i).Regular ∧
        IsFiniteMeasureOnCompacts (μpos i) ∧ IsFiniteMeasureOnCompacts (μneg i)) ∧
      ∀ i (φ : C_c(EuclideanSpace ℝ (Fin n), ℝ)), ContDiff ℝ 1 φ → tsupport φ ⊆ U →
        -(∫ x in U, f x * fderiv ℝ φ x (EuclideanSpace.single i 1)) =
          (∫ x : U, φ x ∂μpos i) - ∫ x : U, φ x ∂μneg i := by
  let := hU.locallyCompactSpace
  obtain ⟨L, hL, hrep⟩ := exists_distributional_coordinateFunctionals hU hf
  have hμ (i : Fin n) := signed_riesz (L i) (hL i)
  choose μpos μneg hp hn hfp hfn hμ using hμ
  refine ⟨μpos, μneg, fun i => ⟨hp i, hn i, hfp i, hfn i⟩, ?_⟩
  intro i φ hφ hsφ
  rw [← hrep i φ hφ hsφ]
  exact hμ i (restrictSupportedCC ⟨φ, hsφ⟩)

/-! ## Polar density from positive Radon–Nikodym derivatives -/

section CoordinatePolar

variable {S : Type*} [MeasurableSpace S] {n : ℕ}

/-- A positive measure dominating both signs of every coordinate representative. -/
noncomputable def coordinateDominatingMeasure (μpos μneg : Fin n → Measure S) : Measure S :=
  ∑ i, (μpos i + μneg i)

lemma coordinate_pos_le_dominating (μpos μneg : Fin n → Measure S) (i : Fin n) :
    μpos i ≤ coordinateDominatingMeasure μpos μneg := by
  intro A
  rw [coordinateDominatingMeasure, Measure.finsetSum_apply]
  calc
    μpos i A ≤ (μpos i + μneg i) A := by simp only [Measure.add_apply]; exact le_self_add
    _ ≤ ∑ j, (μpos j + μneg j) A :=
      Finset.single_le_sum (f := fun j : Fin n => (μpos j + μneg j) A)
        (fun _ _ => zero_le) (Finset.mem_univ i)

lemma coordinate_neg_le_dominating (μpos μneg : Fin n → Measure S) (i : Fin n) :
    μneg i ≤ coordinateDominatingMeasure μpos μneg := by
  intro A
  rw [coordinateDominatingMeasure, Measure.finsetSum_apply]
  calc
    μneg i A ≤ (μpos i + μneg i) A := by simp only [Measure.add_apply]; exact le_add_self
    _ ≤ ∑ j, (μpos j + μneg j) A :=
      Finset.single_le_sum (f := fun j : Fin n => (μpos j + μneg j) A)
        (fun _ _ => zero_le) (Finset.mem_univ i)

instance coordinateDominatingMeasure_finiteOnCompacts [TopologicalSpace S]
    (μpos μneg : Fin n → Measure S)
    [∀ i, IsFiniteMeasureOnCompacts (μpos i)] [∀ i, IsFiniteMeasureOnCompacts (μneg i)] :
    IsFiniteMeasureOnCompacts (coordinateDominatingMeasure μpos μneg) where
  lt_top_of_isCompact K hK := by
    rw [coordinateDominatingMeasure, Measure.finsetSum_apply]
    apply ENNReal.sum_lt_top.mpr
    intro i _
    rw [Measure.add_apply]
    exact ENNReal.add_lt_top.mpr ⟨hK.measure_lt_top, hK.measure_lt_top⟩

/-- The Euclidean density of the signed coordinate representatives against their common
positive dominating measure. Only positive-measure Radon–Nikodym derivatives are used. -/
noncomputable def coordinateRNDensity (μpos μneg : Fin n → Measure S) :
    S → EuclideanSpace ℝ (Fin n) :=
  fun x => WithLp.toLp 2 (fun i =>
    ((μpos i).rnDeriv (coordinateDominatingMeasure μpos μneg) x).toReal -
      ((μneg i).rnDeriv (coordinateDominatingMeasure μpos μneg) x).toReal)

@[simp] lemma coordinateRNDensity_apply (μpos μneg : Fin n → Measure S) (x : S) (i : Fin n) :
    coordinateRNDensity μpos μneg x i =
      ((μpos i).rnDeriv (coordinateDominatingMeasure μpos μneg) x).toReal -
        ((μneg i).rnDeriv (coordinateDominatingMeasure μpos μneg) x).toReal := rfl

lemma measurable_coordinateRNDensity (μpos μneg : Fin n → Measure S) :
    Measurable (coordinateRNDensity μpos μneg) :=
  (WithLp.measurable_toLp _ _).comp (Measurable.of_eval fun i =>
    (Measure.measurable_rnDeriv (μpos i) _).ennreal_toReal.sub
      (Measure.measurable_rnDeriv (μneg i) _).ennreal_toReal)

/-- The measure with density equal to the Euclidean norm of the signed coordinate density.
Its identification with the BV variation supremum is a separate theorem. -/
noncomputable def coordinatePolarMeasure (μpos μneg : Fin n → Measure S) : Measure S :=
  (coordinateDominatingMeasure μpos μneg).withDensity
    (fun x => ENNReal.ofReal ‖coordinateRNDensity μpos μneg x‖)

/-- Normalize the signed density, taking zero where it vanishes. That zero set has zero
measure for `coordinatePolarMeasure`, so the direction is a unit vector almost everywhere. -/
noncomputable def coordinatePolarDirection (μpos μneg : Fin n → Measure S) :
    S → EuclideanSpace ℝ (Fin n) :=
  fun x => ‖coordinateRNDensity μpos μneg x‖⁻¹ • coordinateRNDensity μpos μneg x

lemma measurable_coordinatePolarDirection (μpos μneg : Fin n → Measure S) :
    Measurable (coordinatePolarDirection μpos μneg) :=
  (measurable_coordinateRNDensity μpos μneg).norm.inv.smul
    (measurable_coordinateRNDensity μpos μneg)

lemma norm_coordinatePolarDirection_ae (μpos μneg : Fin n → Measure S) :
    ∀ᵐ x ∂coordinatePolarMeasure μpos μneg, ‖coordinatePolarDirection μpos μneg x‖ = 1 := by
  rw [coordinatePolarMeasure,
    ae_withDensity_iff (measurable_coordinateRNDensity μpos μneg).norm.ennreal_ofReal]
  apply Eventually.of_forall
  intro x hx
  have hn : ‖coordinateRNDensity μpos μneg x‖ ≠ 0 := by
    intro h
    exact hx (by rw [h, ENNReal.ofReal_zero])
  simp only [coordinatePolarDirection, norm_smul, norm_inv, norm_norm, inv_mul_cancel₀ hn]

lemma norm_smul_coordinatePolarDirection (μpos μneg : Fin n → Measure S) (x : S) :
    ‖coordinateRNDensity μpos μneg x‖ • coordinatePolarDirection μpos μneg x =
      coordinateRNDensity μpos μneg x := by
  by_cases hx : coordinateRNDensity μpos μneg x = 0
  · simp [coordinatePolarDirection, hx]
  · rw [coordinatePolarDirection, smul_smul, mul_inv_cancel₀ (norm_ne_zero_iff.mpr hx), one_smul]

variable [TopologicalSpace S]
  (μpos μneg : Fin n → Measure S)
  [∀ i, IsFiniteMeasureOnCompacts (μpos i)] [∀ i, IsFiniteMeasureOnCompacts (μneg i)]

lemma integrableOn_coordinateRNDensity {K : Set S} (hK : IsCompact K) :
    IntegrableOn (coordinateRNDensity μpos μneg) K (coordinateDominatingMeasure μpos μneg) := by
  apply Integrable.of_eval_piLp
  intro i
  exact (Measure.integrableOn_toReal_rnDeriv hK.measure_ne_top).sub
    (Measure.integrableOn_toReal_rnDeriv hK.measure_ne_top)

instance coordinatePolarMeasure_finiteOnCompacts [T2Space S] [BorelSpace S] :
    IsFiniteMeasureOnCompacts (coordinatePolarMeasure μpos μneg) where
  lt_top_of_isCompact K hK := by
    rw [coordinatePolarMeasure, withDensity_apply _ hK.measurableSet]
    exact (hasFiniteIntegral_iff_norm _).mp
      (integrableOn_coordinateRNDensity μpos μneg hK).hasFiniteIntegral

variable [BorelSpace S] [SigmaCompactSpace S]

lemma integral_coordinateRNDensity (i : Fin n) (φ : C_c(S, ℝ)) :
    (∫ x, φ x ∂μpos i) - ∫ x, φ x ∂μneg i =
      ∫ x, φ x * coordinateRNDensity μpos μneg x i ∂coordinateDominatingMeasure μpos μneg := by
  let ν := coordinateDominatingMeasure μpos μneg
  have hp : ν.withDensity ((μpos i).rnDeriv ν) = μpos i :=
    Measure.withDensity_rnDeriv_eq _ _
      (Measure.absolutelyContinuous_of_le (coordinate_pos_le_dominating μpos μneg i))
  have hn : ν.withDensity ((μneg i).rnDeriv ν) = μneg i :=
    Measure.withDensity_rnDeriv_eq _ _
      (Measure.absolutelyContinuous_of_le (coordinate_neg_le_dominating μpos μneg i))
  have hip : Integrable (fun x => ((μpos i).rnDeriv ν x).toReal • φ x) ν := by
    apply (integrable_withDensity_iff_integrable_smul' (Measure.measurable_rnDeriv _ _)
      (Measure.rnDeriv_lt_top _ _)).mp
    rw [hp]
    exact φ.continuous.integrable_of_hasCompactSupport φ.hasCompactSupport
  have hin : Integrable (fun x => ((μneg i).rnDeriv ν x).toReal • φ x) ν := by
    apply (integrable_withDensity_iff_integrable_smul' (Measure.measurable_rnDeriv _ _)
      (Measure.rnDeriv_lt_top _ _)).mp
    rw [hn]
    exact φ.continuous.integrable_of_hasCompactSupport φ.hasCompactSupport
  rw [← hp, ← hn, integral_withDensity_eq_integral_toReal_smul
    (Measure.measurable_rnDeriv _ _) (Measure.rnDeriv_lt_top _ _),
    integral_withDensity_eq_integral_toReal_smul
      (Measure.measurable_rnDeriv _ _) (Measure.rnDeriv_lt_top _ _), ← integral_sub hip hin]
  apply integral_congr_ae
  exact Eventually.of_forall fun x => by simp [coordinateRNDensity, smul_eq_mul]; ring

end CoordinatePolar

lemma integral_coordinatePolarDirection {S : Type*} [MeasurableSpace S] {n : ℕ}
    (μpos μneg : Fin n → Measure S) (i : Fin n) (φ : S → ℝ) :
    (∫ x, φ x * coordinatePolarDirection μpos μneg x i ∂coordinatePolarMeasure μpos μneg) =
      ∫ x, φ x * coordinateRNDensity μpos μneg x i ∂coordinateDominatingMeasure μpos μneg := by
  rw [coordinatePolarMeasure, integral_withDensity_eq_integral_toReal_smul
    (measurable_coordinateRNDensity μpos μneg).norm.ennreal_ofReal
    (Eventually.of_forall fun x => ENNReal.ofReal_lt_top)]
  apply integral_congr_ae
  apply Eventually.of_forall
  intro x
  have h := congrArg (fun v : EuclideanSpace ℝ (Fin n) => v i)
    (norm_smul_coordinatePolarDirection μpos μneg x)
  simp only [ENNReal.toReal_ofReal (norm_nonneg _), smul_eq_mul]
  change ‖coordinateRNDensity μpos μneg x‖ * coordinatePolarDirection μpos μneg x i =
    coordinateRNDensity μpos μneg x i at h
  rw [← h]
  ring

/-- Coordinate distributional identities for a measurable direction of unit norm almost
everywhere. Finiteness on compact sets and regularity of the measure are stated separately. -/
structure IsDistributionalPolarRepresentation {n : ℕ}
    (f : EuclideanSpace ℝ (Fin n) → ℝ) (U : Set (EuclideanSpace ℝ (Fin n)))
    (ρ : Measure U) (σ : U → EuclideanSpace ℝ (Fin n)) : Prop where
  measurable : Measurable σ
  norm_ae : ∀ᵐ x ∂ρ, ‖σ x‖ = 1
  test_eq : ∀ i (φ : C_c(EuclideanSpace ℝ (Fin n), ℝ)), ContDiff ℝ 1 φ → tsupport φ ⊆ U →
    -(∫ x in U, f x * fderiv ℝ φ x (EuclideanSpace.single i 1)) =
      ∫ x : U, φ x * σ x i ∂ρ

/-- The distributional derivative of a locally BV function admits a locally finite regular
measure and a measurable unit polar direction on the entire open domain. The pairing is
proved coordinatewise for all supported C¹ tests. Identifying this measure with the original
variation supremum on every open subset is the remaining part of blueprint `thm:polar`. -/
theorem exists_distributional_polar_representation {n : ℕ}
    {U : Set (EuclideanSpace ℝ (Fin n))} (hU : IsOpen U)
    {f : EuclideanSpace ℝ (Fin n) → ℝ} (hf : IsLocallyBVOn f U) :
    ∃ ρ : Measure U, ∃ σ : U → EuclideanSpace ℝ (Fin n),
      ρ.Regular ∧ IsFiniteMeasureOnCompacts ρ ∧ IsDistributionalPolarRepresentation f U ρ σ := by
  let := hU.locallyCompactSpace
  obtain ⟨μpos, μneg, hμ, hrep⟩ := exists_global_coordinateDerivative_measures hU hf
  let : ∀ i, IsFiniteMeasureOnCompacts (μpos i) := fun i => (hμ i).2.2.1
  let : ∀ i, IsFiniteMeasureOnCompacts (μneg i) := fun i => (hμ i).2.2.2
  refine ⟨coordinatePolarMeasure μpos μneg, coordinatePolarDirection μpos μneg,
    inferInstance, inferInstance, measurable_coordinatePolarDirection μpos μneg,
    norm_coordinatePolarDirection_ae μpos μneg, ?_⟩
  intro i φ hφ hsφ
  calc
    -(∫ x in U, f x * fderiv ℝ φ x (EuclideanSpace.single i 1)) =
        (∫ x : U, φ x ∂μpos i) - ∫ x : U, φ x ∂μneg i := hrep i φ hφ hsφ
    _ = ∫ x : U, φ x * coordinateRNDensity μpos μneg x i
        ∂coordinateDominatingMeasure μpos μneg :=
      integral_coordinateRNDensity μpos μneg i (restrictSupportedCC ⟨φ, hsφ⟩)
    _ = ∫ x : U, φ x * coordinatePolarDirection μpos μneg x i
        ∂coordinatePolarMeasure μpos μneg :=
      (integral_coordinatePolarDirection μpos μneg i (fun x : U => φ x)).symm

/-! ## The vector-field pairing and the upper variation bound -/

lemma tsupport_vectorComponent_subset {n : ℕ}
    (X : EuclideanSpace ℝ (Fin n) → EuclideanSpace ℝ (Fin n)) (i : Fin n) :
    tsupport (fun x => X x i) ⊆ tsupport X := by
  apply closure_mono
  intro x hx h
  exact hx (by change X x i = 0; rw [h]; rfl)

/-- A scalar component of a continuous compactly supported field. -/
noncomputable def vectorComponentCC {n : ℕ}
    (X : EuclideanSpace ℝ (Fin n) → EuclideanSpace ℝ (Fin n))
    (hX : Continuous X) (hcX : HasCompactSupport X) (i : Fin n) :
    C_c(EuclideanSpace ℝ (Fin n), ℝ) where
  toFun x := X x i
  continuous_toFun := (EuclideanSpace.proj i).continuous.comp hX
  hasCompactSupport' := hcX.of_isClosed_subset (isClosed_tsupport _)
    (tsupport_vectorComponent_subset X i)

lemma fderiv_vectorComponent {n : ℕ}
    {X : EuclideanSpace ℝ (Fin n) → EuclideanSpace ℝ (Fin n)}
    (hX : ContDiff ℝ 1 X) (i : Fin n) (x v : EuclideanSpace ℝ (Fin n)) :
    fderiv ℝ (fun y => X y i) x v = fderiv ℝ X x v i := by
  have h := ((EuclideanSpace.proj i).hasFDerivAt.comp x
    (hX.differentiable one_ne_zero x).hasFDerivAt).fderiv
  exact congrArg (fun A => A v) h

lemma integrable_mul_fderiv_component {n : ℕ}
    {U : Set (EuclideanSpace ℝ (Fin n))} {f : EuclideanSpace ℝ (Fin n) → ℝ}
    (hf : LocallyIntegrableOn f U)
    {X : EuclideanSpace ℝ (Fin n) → EuclideanSpace ℝ (Fin n)}
    (hX : ContDiff ℝ 1 X) (hcX : HasCompactSupport X) (hsX : tsupport X ⊆ U)
    (i j : Fin n) :
    Integrable (fun x => f x * fderiv ℝ X x (EuclideanSpace.single i 1) j) := by
  have hcont : Continuous (fun x => fderiv ℝ X x (EuclideanSpace.single i 1) j) := by
    have := hX.continuous_fderiv one_ne_zero
    fun_prop
  have hi := (hf.integrableOn_compact_subset hsX hcX).mul_continuousOn hcont.continuousOn hcX
  apply (integrableOn_iff_integrable_of_support_subset ?_).mp hi
  intro x hx
  by_contra hx'
  exact hx (by simp [fderiv_of_notMem_tsupport ℝ hx'])

lemma hasCompactSupport_restrict_field {n : ℕ}
    {U : Set (EuclideanSpace ℝ (Fin n))}
    {X : EuclideanSpace ℝ (Fin n) → EuclideanSpace ℝ (Fin n)}
    (hcX : HasCompactSupport X) (hsX : tsupport X ⊆ U) :
    HasCompactSupport (fun x : U => X x) := by
  have hK : IsCompact (Subtype.val ⁻¹' tsupport X : Set U) :=
    Topology.IsInducing.subtypeVal.isCompact_preimage' hcX (by simpa using hsX)
  apply hK.of_isClosed_subset (isClosed_tsupport _)
  exact continuous_subtype_val.closure_preimage_subset (Function.support X)

lemma IsDistributionalPolarRepresentation.integrable_component {n : ℕ}
    {U : Set (EuclideanSpace ℝ (Fin n))} {f : EuclideanSpace ℝ (Fin n) → ℝ}
    {ρ : Measure U} [IsFiniteMeasureOnCompacts ρ] {σ : U → EuclideanSpace ℝ (Fin n)}
    (hpolar : IsDistributionalPolarRepresentation f U ρ σ)
    {X : EuclideanSpace ℝ (Fin n) → EuclideanSpace ℝ (Fin n)}
    (hX : Continuous X) (hcX : HasCompactSupport X) (hsX : tsupport X ⊆ U) (i : Fin n) :
    Integrable (fun x : U => X x i * σ x i) ρ := by
  have hiX : Integrable (fun x : U => X x) ρ :=
    (hX.comp continuous_subtype_val).integrable_of_hasCompactSupport
      (hasCompactSupport_restrict_field hcX hsX)
  have hm : Measurable (fun x : U => X x i * σ x i) :=
    ((EuclideanSpace.proj i).continuous.comp (hX.comp continuous_subtype_val)).measurable.mul
      ((EuclideanSpace.proj (𝕜 := ℝ) i).measurable.comp hpolar.measurable)
  apply hiX.norm.mono' hm.aestronglyMeasurable
  filter_upwards [hpolar.norm_ae] with x hx
  calc
    ‖X x i * σ x i‖ = ‖X x i‖ * ‖σ x i‖ := norm_mul _ _
    _ ≤ ‖X x‖ * ‖σ x‖ := mul_le_mul (PiLp.norm_apply_le _ i) (PiLp.norm_apply_le _ i)
      (norm_nonneg _) (norm_nonneg _)
    _ = ‖X x‖ := by rw [hx, mul_one]

/-- The coordinate distributional identities assemble into the full vector-field identity. -/
theorem IsDistributionalPolarRepresentation.integral_divergence_eq {n : ℕ}
    {U : Set (EuclideanSpace ℝ (Fin n))} {f : EuclideanSpace ℝ (Fin n) → ℝ}
    {ρ : Measure U} [IsFiniteMeasureOnCompacts ρ] {σ : U → EuclideanSpace ℝ (Fin n)}
    (hpolar : IsDistributionalPolarRepresentation f U ρ σ) (hf : LocallyIntegrableOn f U)
    {X : EuclideanSpace ℝ (Fin n) → EuclideanSpace ℝ (Fin n)}
    (hX : ContDiff ℝ 1 X) (hcX : HasCompactSupport X) (hsX : tsupport X ⊆ U) :
    -(∫ x in U, f x * divergenceN X x) = ∫ x : U, inner ℝ (X x) (σ x) ∂ρ := by
  have hi (i : Fin n) :=
    (integrable_mul_fderiv_component hf hX hcX hsX i i).integrableOn (s := U)
  have hj (i : Fin n) := hpolar.integrable_component hX.continuous hcX hsX i
  have htest (i : Fin n) :
      -(∫ x in U, f x * fderiv ℝ X x (EuclideanSpace.single i 1) i) =
        ∫ x : U, X x i * σ x i ∂ρ := by
    have hφ : ContDiff ℝ 1 (fun x => X x i) :=
      (EuclideanSpace.proj (𝕜 := ℝ) i).contDiff.comp hX
    have h := hpolar.test_eq i (vectorComponentCC X hX.continuous hcX i) hφ
      ((tsupport_vectorComponent_subset X i).trans hsX)
    change -(∫ x in U, f x * fderiv ℝ (fun y => X y i) x (EuclideanSpace.single i 1)) =
      ∫ x : U, X x i * σ x i ∂ρ at h
    simpa only [fderiv_vectorComponent hX] using h
  simp only [divergenceN, Finset.mul_sum,
    integral_finsetSum Finset.univ (fun i _ => hi i)]
  rw [← Finset.sum_neg_distrib]
  simp_rw [htest]
  rw [← integral_finsetSum Finset.univ (fun i _ => hj i)]
  congr 1
  funext x
  simp only [PiLp.inner_apply, Real.inner_apply]

/-- An admissible test field pairs with the derivative by at most the polar mass of its
compact support. Only that compact mass needs to be finite. -/
theorem IsDistributionalPolarRepresentation.test_integral_le_support_measure {n : ℕ}
    {U : Set (EuclideanSpace ℝ (Fin n))} {f : EuclideanSpace ℝ (Fin n) → ℝ}
    {ρ : Measure U} [IsFiniteMeasureOnCompacts ρ] {σ : U → EuclideanSpace ℝ (Fin n)}
    (hpolar : IsDistributionalPolarRepresentation f U ρ σ) (hf : LocallyIntegrableOn f U)
    {X : EuclideanSpace ℝ (Fin n) → EuclideanSpace ℝ (Fin n)}
    (hX : IsVariationTestField U X) :
    ENNReal.ofReal (∫ x in U, f x * divergenceN X x) ≤ ρ (Subtype.val ⁻¹' tsupport X) := by
  let K : Set U := Subtype.val ⁻¹' tsupport X
  have hK : IsCompact K :=
    Topology.IsInducing.subtypeVal.isCompact_preimage' hX.2.1 (by simpa using hX.2.2.1)
  have hi : Integrable (K.indicator (fun _ => (1 : ℝ))) ρ :=
    (integrable_indicator_iff hK.measurableSet).mpr (integrableOn_const hK.measure_ne_top)
  have hb : ∀ᵐ (x : U) ∂ρ, ‖inner ℝ (X x) (σ x)‖ ≤ K.indicator (fun _ => (1 : ℝ)) x := by
    filter_upwards [hpolar.norm_ae] with x hxσ
    by_cases hx : x ∈ K
    · rw [indicator_of_mem hx]
      calc
        ‖inner ℝ (X x) (σ x)‖ ≤ ‖X x‖ * ‖σ x‖ := norm_inner_le_norm _ _
        _ = ‖X x‖ := by rw [hxσ, mul_one]
        _ ≤ 1 := hX.2.2.2 x
    · have hx' : (x : EuclideanSpace ℝ (Fin n)) ∉ tsupport X := hx
      rw [image_eq_zero_of_notMem_tsupport hx', inner_zero_left, norm_zero,
        indicator_of_notMem hx]
  have hJ : ‖∫ x : U, inner ℝ (X x) (σ x) ∂ρ‖ ≤ (ρ K).toReal := by
    simpa only [integral_indicator_const (1 : ℝ) hK.measurableSet,
      smul_eq_mul, mul_one, Measure.real] using norm_integral_le_of_norm_le hi hb
  have hI : ‖∫ x in U, f x * divergenceN X x‖ ≤ (ρ K).toReal := by
    rw [← norm_neg, hpolar.integral_divergence_eq hf hX.1 hX.2.1 hX.2.2.1]
    exact hJ
  calc
    ENNReal.ofReal (∫ x in U, f x * divergenceN X x) ≤
        ENNReal.ofReal ‖∫ x in U, f x * divergenceN X x‖ :=
      ENNReal.ofReal_le_ofReal (le_abs_self _)
    _ ≤ ENNReal.ofReal (ρ K).toReal := ENNReal.ofReal_le_ofReal hI
    _ = ρ K := ENNReal.ofReal_toReal hK.measure_ne_top

/-- The variation supremum is bounded above by the polar measure on every subregion.
The subregion may have infinite measure; no global finite-variation assumption is used. -/
theorem IsDistributionalPolarRepresentation.variation_le_measure {n : ℕ}
    {U O : Set (EuclideanSpace ℝ (Fin n))} (hU : IsOpen U) (hOU : O ⊆ U)
    {f : EuclideanSpace ℝ (Fin n) → ℝ}
    {ρ : Measure U} [IsFiniteMeasureOnCompacts ρ] {σ : U → EuclideanSpace ℝ (Fin n)}
    (hpolar : IsDistributionalPolarRepresentation f U ρ σ) (hf : LocallyIntegrableOn f U) :
    variation f O ≤ ρ (Subtype.val ⁻¹' O) := by
  apply iSup_le
  intro X
  apply iSup_le
  intro hX
  have hXU : IsVariationTestField U X := ⟨hX.1, hX.2.1, hX.2.2.1.trans hOU, hX.2.2.2⟩
  have hI : (∫ x in U, f x * divergenceN X x) = ∫ x in O, f x * divergenceN X x := by
    apply setIntegral_eq_of_subset_of_forall_sdiff_eq_zero hU.measurableSet hOU
    intro x hx
    rw [divergenceN_eq_zero_of_notMem_tsupport (fun h => hx.2 (hX.2.2.1 h)), mul_zero]
  rw [← hI]
  exact (hpolar.test_integral_le_support_measure hf hXU).trans
    (measure_mono (preimage_mono hX.2.2.1))

/-- Continuous compactly supported unit fields admit uniform smooth approximations with
the same unit bound and with all supports in one compact subset of the open domain. -/
theorem exists_smooth_unit_field_approximation {n : ℕ}
    {O : Set (EuclideanSpace ℝ (Fin n))} (hO : IsOpen O)
    {X : EuclideanSpace ℝ (Fin n) → EuclideanSpace ℝ (Fin n)}
    (hX : Continuous X) (hcX : HasCompactSupport X) (hsX : tsupport X ⊆ O)
    (hbX : ∀ x, ‖X x‖ ≤ 1) :
    ∃ K : Set (EuclideanSpace ℝ (Fin n)),
      ∃ Y : ℕ → EuclideanSpace ℝ (Fin n) → EuclideanSpace ℝ (Fin n),
        IsCompact K ∧ K ⊆ O ∧ tsupport X ⊆ K ∧
        (∀ j, IsSmoothVariationTestField O (Y j) ∧ tsupport (Y j) ⊆ K) ∧
        TendstoUniformly Y X atTop := by
  obtain ⟨δ, hδ, hδO⟩ := hcX.exists_cthickening_subset_open hO hsX
  let φ (j : ℕ) : ContDiffBump (0 : EuclideanSpace ℝ (Fin n)) :=
    ⟨(δ / ((j : ℝ) + 1)) / 2, δ / ((j : ℝ) + 1), by positivity,
      half_lt_self (by positivity)⟩
  have hφδ (j : ℕ) : (φ j).rOut ≤ δ :=
    div_le_self hδ.le (by have := Nat.cast_nonneg (α := ℝ) j; linarith)
  have hφlim : Tendsto (fun j => (φ j).rOut) atTop (𝓝 0) := by
    simpa only [mul_one_div, mul_zero] using
      (tendsto_one_div_add_atTop_nhds_zero_nat (𝕜 := ℝ)).const_mul δ
  let Y := fun j => mollifyTestField (φ j) X
  have hsY (j : ℕ) := mollifyTestField_support (X := X) (φ j) (hφδ j)
  refine ⟨cthickening δ (tsupport X), Y, hcX.cthickening, hδO,
    self_subset_cthickening _, ?_, ?_⟩
  · intro j
    refine ⟨⟨mollifyTestField_contDiff _ hX, ?_, (hsY j).trans hδO,
      mollifyTestField_norm_le _ hX hbX⟩, hsY j⟩
    exact (φ j).hasCompactSupport_normed.convolution (ContinuousLinearMap.lsmul ℝ ℝ) hcX
  · exact tendstoUniformly_mollifyTestField hφlim (hcX.uniformContinuous_of_continuous hX)

/-- Every continuous compactly supported unit field satisfies the variation lower-testing
inequality, by uniform smooth approximation and the polar vector-field identity. -/
theorem IsDistributionalPolarRepresentation.continuous_test_le_variation {n : ℕ}
    {U O : Set (EuclideanSpace ℝ (Fin n))} (hU : IsOpen U) (hO : IsOpen O) (hOU : O ⊆ U)
    {f : EuclideanSpace ℝ (Fin n) → ℝ}
    {ρ : Measure U} [IsFiniteMeasureOnCompacts ρ] {σ : U → EuclideanSpace ℝ (Fin n)}
    (hpolar : IsDistributionalPolarRepresentation f U ρ σ) (hf : LocallyIntegrableOn f U)
    {X : EuclideanSpace ℝ (Fin n) → EuclideanSpace ℝ (Fin n)}
    (hX : Continuous X) (hcX : HasCompactSupport X) (hsX : tsupport X ⊆ O)
    (hbX : ∀ x, ‖X x‖ ≤ 1) :
    ENNReal.ofReal (-(∫ x : U, inner ℝ (X x) (σ x) ∂ρ)) ≤ variation f O := by
  obtain ⟨K, Y, hK, hKO, _, hY, hlim⟩ :=
    exists_smooth_unit_field_approximation hO hX hcX hsX hbX
  let K' : Set U := Subtype.val ⁻¹' K
  have hK' : IsCompact K' :=
    Topology.IsInducing.subtypeVal.isCompact_preimage' hK (by simpa using hKO.trans hOU)
  have hi : Integrable (K'.indicator (fun _ => (1 : ℝ))) ρ :=
    (integrable_indicator_iff hK'.measurableSet).mpr (integrableOn_const hK'.measure_ne_top)
  have hconv : Tendsto (fun j => ∫ x : U, inner ℝ (Y j x) (σ x) ∂ρ) atTop
      (𝓝 (∫ x : U, inner ℝ (X x) (σ x) ∂ρ)) := by
    apply tendsto_integral_of_dominated_convergence (K'.indicator (fun _ => (1 : ℝ)))
    · intro j
      exact (((hY j).1.1.continuous.comp continuous_subtype_val).measurable.inner
        hpolar.measurable).aestronglyMeasurable
    · exact hi
    · intro j
      filter_upwards [hpolar.norm_ae] with x hxσ
      by_cases hx : x ∈ K'
      · rw [indicator_of_mem hx]
        calc
          ‖inner ℝ (Y j x) (σ x)‖ ≤ ‖Y j x‖ * ‖σ x‖ := norm_inner_le_norm _ _
          _ = ‖Y j x‖ := by rw [hxσ, mul_one]
          _ ≤ 1 := (hY j).1.2.2.2 x
      · have hx' : (x : EuclideanSpace ℝ (Fin n)) ∉ tsupport (Y j) :=
          fun h => hx ((hY j).2 h)
        rw [image_eq_zero_of_notMem_tsupport hx', inner_zero_left, norm_zero,
          indicator_of_notMem hx]
    · exact Eventually.of_forall fun x => (hlim.tendsto_at x).inner tendsto_const_nhds
  apply le_of_tendsto ((ENNReal.continuous_ofReal.tendsto _).comp hconv.neg)
  apply Eventually.of_forall
  intro j
  change ENNReal.ofReal (-(∫ x : U, inner ℝ (Y j x) (σ x) ∂ρ)) ≤ variation f O
  have hj := (hY j).1.toVariationTestField
  have hpair := hpolar.integral_divergence_eq hf hj.1 hj.2.1 (hj.2.2.1.trans hOU)
  rw [← hpair, neg_neg]
  have hI : (∫ x in U, f x * divergenceN (Y j) x) = ∫ x in O, f x * divergenceN (Y j) x := by
    apply setIntegral_eq_of_subset_of_forall_sdiff_eq_zero hU.measurableSet hOU
    intro x hx
    rw [divergenceN_eq_zero_of_notMem_tsupport (fun h => hx.2 (hj.2.2.1 h)), mul_zero]
  rw [hI]
  exact le_iSup_of_le (Y j) (le_iSup_of_le hj le_rfl)

/-! ## Recovering polar mass and the local vector derivative -/

section UnitBallTruncation
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

noncomputable def unitBallTruncation (y : E) : E := (max 1 ‖y‖)⁻¹ • y

lemma unitBallTruncation_eq_self {y : E} (hy : ‖y‖ ≤ 1) : unitBallTruncation y = y := by
  simp [unitBallTruncation, max_eq_left hy]

@[simp]
lemma unitBallTruncation_zero : unitBallTruncation (0 : E) = 0 := by
  simp [unitBallTruncation]

lemma continuous_unitBallTruncation : Continuous (unitBallTruncation : E → E) := by
  apply Continuous.smul _ continuous_id
  exact (continuous_const.max continuous_norm).inv₀ fun y => ne_of_gt (by positivity)

lemma norm_unitBallTruncation_le (y : E) : ‖unitBallTruncation y‖ ≤ 1 := by
  have hp : 0 < max 1 ‖y‖ := by positivity
  rw [unitBallTruncation, norm_smul, Real.norm_eq_abs, abs_of_pos (inv_pos.mpr hp)]
  calc
    (max 1 ‖y‖)⁻¹ * ‖y‖ ≤ (max 1 ‖y‖)⁻¹ * max 1 ‖y‖ :=
      mul_le_mul_of_nonneg_left (le_max_right _ _) (inv_nonneg.mpr hp.le)
    _ = 1 := inv_mul_cancel₀ hp.ne'

lemma norm_unitBallTruncation_sub_le {y q : E} (hq : ‖q‖ ≤ 1) :
    ‖unitBallTruncation y - q‖ ≤ 2 * ‖y - q‖ := by
  by_cases hy : ‖y‖ ≤ 1
  · rw [unitBallTruncation_eq_self hy]
    linarith [norm_nonneg (y - q)]
  · have hy1 : 1 < ‖y‖ := lt_of_not_ge hy
    have hyp : 0 < ‖y‖ := zero_lt_one.trans hy1
    have hi : ‖y‖⁻¹ ≤ 1 := (inv_le_one₀ hyp).mpr hy1.le
    have he : ‖unitBallTruncation y - y‖ = ‖y‖ - 1 := by
      rw [unitBallTruncation, max_eq_right hy1.le]
      conv_lhs => arg 1; rhs; rw [← one_smul ℝ y]
      rw [← sub_smul, norm_smul, Real.norm_eq_abs, abs_of_nonpos (sub_nonpos.mpr hi)]
      rw [neg_sub, sub_mul, one_mul, inv_mul_cancel₀ hyp.ne']
    calc
      ‖unitBallTruncation y - q‖ ≤ ‖unitBallTruncation y - y‖ + ‖y - q‖ :=
        norm_sub_le_norm_sub_add_norm_sub _ _ _
      _ ≤ 2 * ‖y - q‖ := by
        rw [he]
        have h := norm_sub_norm_le y q
        linarith

end UnitBallTruncation

set_option maxHeartbeats 800000 in
-- Combining L¹ density, truncation, and zero extension exceeds the default elaboration budget.
/-- L¹ approximation inside an open subregion by ambient continuous compactly supported
unit fields. The target is supported on a compact subset of that subregion. -/
theorem exists_continuous_unit_field_l1_approximation {n : ℕ}
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]
    {U O : Set (EuclideanSpace ℝ (Fin n))} (hU : IsOpen U) (hO : IsOpen O)
    {ρ : Measure U} [ρ.Regular]
    {K : Set U} (hK : IsCompact K) (hKO : Subtype.val '' K ⊆ O)
    {g : U → E} (hi : Integrable g ρ) (hb : ∀ᵐ x ∂ρ, ‖g x‖ ≤ 1)
    (hs : ∀ x ∉ K, g x = 0) {ε : ℝ} (hε : 0 < ε) :
    ∃ X : EuclideanSpace ℝ (Fin n) → E,
      Continuous X ∧ HasCompactSupport X ∧ tsupport X ⊆ O ∧
      (∀ x, ‖X x‖ ≤ 1) ∧ (∫ x : U, ‖g x - X x‖ ∂ρ) ≤ ε := by
  let : LocallyCompactSpace U := hU.locallyCompactSpace
  obtain ⟨G, hcG, herr, hG, hiG⟩ :=
    hi.exists_hasCompactSupport_integral_sub_le (half_pos hε)
  obtain ⟨φ, hφK, hcφ, hsφ, hbφ⟩ :=
    exists_continuousMap_one_of_isCompact_subset_isOpen
      (hK.image continuous_subtype_val) hO hKO
  let T : U → E := fun x => unitBallTruncation (G x)
  have hT : Continuous T := continuous_unitBallTruncation.comp hG
  have hcT : HasCompactSupport T := hcG.comp_left unitBallTruncation_zero
  let Z : EuclideanSpace ℝ (Fin n) → E := Subtype.val.extend T 0
  have hZ : Continuous Z := HasCompactSupport.continuous_extend_zero hU hT hcT
  have hZU (x : U) : Z x = T x := Subtype.val_injective.extend_apply T 0 x
  have hbZ (x : EuclideanSpace ℝ (Fin n)) : ‖Z x‖ ≤ 1 := by
    by_cases hx : x ∈ U
    · rw [show x = ((⟨x, hx⟩ : U) : EuclideanSpace ℝ (Fin n)) from rfl, hZU]
      exact norm_unitBallTruncation_le _
    · have he : ¬ ∃ a : U, (a : EuclideanSpace ℝ (Fin n)) = x := by
        rintro ⟨a, rfl⟩
        exact hx a.property
      simp only [Z, Function.extend_apply' T (0 : EuclideanSpace ℝ (Fin n) → E) x he,
        Pi.zero_apply, norm_zero]
      exact zero_le_one
  let X : EuclideanSpace ℝ (Fin n) → E := fun x => φ x • Z x
  have hX : Continuous X := φ.continuous.smul hZ
  have hcφ' : HasCompactSupport (φ : EuclideanSpace ℝ (Fin n) → ℝ) := hcφ
  have hcX : HasCompactSupport X := hcφ'.smul_right
  have hsX : tsupport X ⊆ O := (tsupport_smul_subset_left _ _).trans hsφ
  have hbX (x) : ‖X x‖ ≤ 1 := by
    calc
      ‖X x‖ = φ x * ‖Z x‖ := by
        change ‖φ x • Z x‖ = _
        rw [norm_smul, Real.norm_eq_abs, abs_of_nonneg (hbφ x).1]
      _ ≤ 1 * 1 := mul_le_mul (hbφ x).2 (hbZ x) (norm_nonneg _) zero_le_one
      _ = 1 := one_mul _
  refine ⟨X, hX, hcX, hsX, hbX, ?_⟩
  have hiX : Integrable (fun x : U => X x) ρ := by
    change Integrable (fun x : U => φ x • Z x) ρ
    simp_rw [hZU]
    exact ((φ.continuous.comp continuous_subtype_val).smul hT).integrable_of_hasCompactSupport
      hcT.smul_left
  have hpoint : ∀ᵐ x ∂ρ, ‖g x - X x‖ ≤ 2 * ‖g x - G x‖ := by
    filter_upwards [hb] with x hx
    have hφg : φ x • g x = g x := by
      by_cases hxK : x ∈ K
      · rw [hφK (mem_image_of_mem Subtype.val hxK)]
        exact one_smul ℝ _
      · rw [hs x hxK, smul_zero]
    calc
      ‖g x - X x‖ = ‖φ x • (g x - T x)‖ := by
        change ‖g x - φ x • Z x‖ = _
        rw [smul_sub, hφg, hZU]
      _ = φ x * ‖g x - T x‖ := by
        rw [norm_smul, Real.norm_eq_abs, abs_of_nonneg (hbφ x).1]
      _ ≤ ‖g x - T x‖ := by
        simpa only [one_mul] using mul_le_mul_of_nonneg_right (hbφ x).2 (norm_nonneg _)
      _ ≤ 2 * ‖g x - G x‖ := by
        simpa only [T, norm_sub_rev] using (norm_unitBallTruncation_sub_le (y := G x) hx)
  calc
    (∫ x : U, ‖g x - X x‖ ∂ρ) ≤ ∫ x : U, 2 * ‖g x - G x‖ ∂ρ :=
      integral_mono_ae (hi.sub hiX).norm ((hi.sub hiG).norm.const_mul 2) hpoint
    _ = 2 * ∫ x : U, ‖g x - G x‖ ∂ρ := integral_const_mul _ _
    _ ≤ ε := by linarith


/-- Pairing any integrable field with the polar direction remains integrable. -/
lemma IsDistributionalPolarRepresentation.integrable_inner {n : ℕ}
    {U : Set (EuclideanSpace ℝ (Fin n))} {f : EuclideanSpace ℝ (Fin n) → ℝ}
    {ρ : Measure U} {σ : U → EuclideanSpace ℝ (Fin n)}
    (hpolar : IsDistributionalPolarRepresentation f U ρ σ)
    {G : U → EuclideanSpace ℝ (Fin n)} (hG : Integrable G ρ) :
    Integrable (fun x => inner ℝ (G x) (σ x)) ρ := by
  apply hG.norm.mono'
    (hG.aestronglyMeasurable.aemeasurable.inner hpolar.measurable.aemeasurable).aestronglyMeasurable
  filter_upwards [hpolar.norm_ae] with x hx
  simpa only [hx, mul_one] using norm_inner_le_norm (G x) (σ x)

/-- Every compact polar mass inside an open subregion is bounded by variation there. -/
theorem IsDistributionalPolarRepresentation.compact_measure_le_variation {n : ℕ}
    {U O : Set (EuclideanSpace ℝ (Fin n))} (hU : IsOpen U) (hO : IsOpen O) (hOU : O ⊆ U)
    {f : EuclideanSpace ℝ (Fin n) → ℝ} {ρ : Measure U} [ρ.Regular]
    {σ : U → EuclideanSpace ℝ (Fin n)}
    (hpolar : IsDistributionalPolarRepresentation f U ρ σ) (hf : LocallyIntegrableOn f U)
    {K : Set U} (hK : IsCompact K) (hKO : Subtype.val '' K ⊆ O) :
    ρ K ≤ variation f O := by
  by_cases hv : variation f O = ∞
  · simp only [hv, le_top]
  rw [← ENNReal.ofReal_toReal hK.measure_ne_top]
  apply ENNReal.ofReal_le_of_le_toReal
  apply le_of_forall_pos_le_add
  intro ε hε
  let g : U → EuclideanSpace ℝ (Fin n) := K.indicator (fun x => -σ x)
  have hm : Measurable g := hpolar.measurable.neg.indicator hK.measurableSet
  have hg_norm : ∀ᵐ x ∂ρ, ‖g x‖ = K.indicator (fun _ => (1 : ℝ)) x := by
    filter_upwards [hpolar.norm_ae] with x hx
    by_cases hxK : x ∈ K <;> simp [g, hxK, hx]
  have hi1 : Integrable (K.indicator (fun _ => (1 : ℝ))) ρ :=
    (integrable_indicator_iff hK.measurableSet).mpr (integrableOn_const hK.measure_ne_top)
  have hi : Integrable g ρ := hi1.mono' hm.aestronglyMeasurable (hg_norm.mono fun _ h => h.le)
  have hb : ∀ᵐ x ∂ρ, ‖g x‖ ≤ 1 := by
    filter_upwards [hg_norm] with x hx
    rw [hx]
    by_cases hxK : x ∈ K <;> simp [hxK]
  have hs (x) (hx : x ∉ K) : g x = 0 := indicator_of_notMem hx _
  obtain ⟨X, hX, hcX, hsX, hbX, herr⟩ :=
    exists_continuous_unit_field_l1_approximation hU hO hK hKO hi hb hs hε
  have hiX : Integrable (fun x : U => X x) ρ :=
    (hX.comp continuous_subtype_val).integrable_of_hasCompactSupport
      (hasCompactSupport_restrict_field hcX (hsX.trans hOU))
  have hig := hpolar.integrable_inner hi
  have hiJ := hpolar.integrable_inner hiX
  have heq : (∫ x : U, inner ℝ (g x) (σ x) ∂ρ) = -(ρ K).toReal := by
    calc
      (∫ x : U, inner ℝ (g x) (σ x) ∂ρ) =
          ∫ x : U, K.indicator (fun _ => (-1 : ℝ)) x ∂ρ := by
        apply integral_congr_ae
        filter_upwards [hpolar.norm_ae] with x hx
        by_cases hxK : x ∈ K
        · simp [g, hxK, inner_neg_left, hx]
        · simp [g, hxK]
      _ = -(ρ K).toReal := by
        simp only [integral_indicator_const (-1 : ℝ) hK.measurableSet,
          smul_eq_mul, mul_neg_one, Measure.real]
  have hclose : ‖(∫ x : U, inner ℝ (g x) (σ x) ∂ρ) -
      ∫ x : U, inner ℝ (X x) (σ x) ∂ρ‖ ≤ ε := by
    calc
      _ = ‖∫ x : U, inner ℝ (g x - X x) (σ x) ∂ρ‖ := by
        rw [← integral_sub hig hiJ]
        congr 1
        apply integral_congr_ae
        exact Eventually.of_forall fun x => (inner_sub_left (g x) (X x) (σ x)).symm
      _ ≤ ∫ x : U, ‖g x - X x‖ ∂ρ := by
        apply norm_integral_le_of_norm_le (hi.sub hiX).norm
        filter_upwards [hpolar.norm_ae] with x hx
        simpa only [hx, mul_one, Pi.sub_apply] using norm_inner_le_norm (g x - X x) (σ x)
      _ ≤ ε := herr
  have htest := hpolar.continuous_test_le_variation hU hO hOU hf hX hcX hsX hbX
  have htest' := (ENNReal.ofReal_le_iff_le_toReal hv).mp htest
  rw [heq, Real.norm_eq_abs] at hclose
  have := (abs_le.mp hclose).1
  linarith

/-- Regularity turns the compact lower bounds into the full reverse inequality on open sets. -/
theorem IsDistributionalPolarRepresentation.measure_le_variation {n : ℕ}
    {U O : Set (EuclideanSpace ℝ (Fin n))} (hU : IsOpen U) (hO : IsOpen O) (hOU : O ⊆ U)
    {f : EuclideanSpace ℝ (Fin n) → ℝ} {ρ : Measure U} [ρ.Regular]
    {σ : U → EuclideanSpace ℝ (Fin n)}
    (hpolar : IsDistributionalPolarRepresentation f U ρ σ) (hf : LocallyIntegrableOn f U) :
    ρ (Subtype.val ⁻¹' O) ≤ variation f O := by
  rw [(hO.preimage continuous_subtype_val).measure_eq_iSup_isCompact ρ]
  apply iSup_le
  intro K
  apply iSup_le
  intro hKO
  apply iSup_le
  intro hK
  exact hpolar.compact_measure_le_variation hU hO hOU hf hK
    (by rintro _ ⟨x, hx, rfl⟩; exact hKO hx)

/-- The polar measure agrees with the defining BV variation on every open subregion,
including subregions with infinite measure. -/
theorem IsDistributionalPolarRepresentation.variation_eq_measure {n : ℕ}
    {U O : Set (EuclideanSpace ℝ (Fin n))} (hU : IsOpen U) (hO : IsOpen O) (hOU : O ⊆ U)
    {f : EuclideanSpace ℝ (Fin n) → ℝ} {ρ : Measure U} [ρ.Regular]
    {σ : U → EuclideanSpace ℝ (Fin n)}
    (hpolar : IsDistributionalPolarRepresentation f U ρ σ) (hf : LocallyIntegrableOn f U) :
    variation f O = ρ (Subtype.val ⁻¹' O) :=
  le_antisymm (hpolar.variation_le_measure hU hOU hf)
    (hpolar.measure_le_variation hU hO hOU hf)

/-- A locally BV function on an open domain has a distributional polar representation
whose measure is exactly the variation supremum on each open subregion. -/
theorem exists_polar_representation_with_variation {n : ℕ}
    {U : Set (EuclideanSpace ℝ (Fin n))} (hU : IsOpen U)
    {f : EuclideanSpace ℝ (Fin n) → ℝ} (hf : IsLocallyBVOn f U) :
    ∃ ρ : Measure U, ∃ σ : U → EuclideanSpace ℝ (Fin n),
      ρ.Regular ∧ IsDistributionalPolarRepresentation f U ρ σ ∧
      ∀ O, IsOpen O → O ⊆ U → variation f O = ρ (Subtype.val ⁻¹' O) := by
  obtain ⟨ρ, σ, hρ, _, hpolar⟩ := exists_distributional_polar_representation hU hf
  let : ρ.Regular := hρ
  exact ⟨ρ, σ, hρ, hpolar, fun O hO hOU => hpolar.variation_eq_measure hU hO hOU hf.1⟩


/-- The vector measure with density `σ` on a compact restriction of `ρ`. Integrability
on that restriction is established below; no global integrability is assumed. -/
noncomputable def polarVectorRestriction {n : ℕ} {S : Type*} [MeasurableSpace S]
    (ρ : Measure S) (σ : S → EuclideanSpace ℝ (Fin n)) (K : Set S) :
    VectorMeasure S (EuclideanSpace ℝ (Fin n)) := (ρ.restrict K).withDensityᵥ σ

lemma IsDistributionalPolarRepresentation.integrableOn_direction {n : ℕ}
    {U : Set (EuclideanSpace ℝ (Fin n))} {f : EuclideanSpace ℝ (Fin n) → ℝ}
    {ρ : Measure U} [IsFiniteMeasureOnCompacts ρ] {σ : U → EuclideanSpace ℝ (Fin n)}
    (hpolar : IsDistributionalPolarRepresentation f U ρ σ) {K : Set U} (hK : IsCompact K) :
    IntegrableOn σ K ρ := by
  let : IsFiniteMeasure (ρ.restrict K) := ⟨by
    simpa only [Measure.restrict_apply_univ] using (hK.measure_lt_top (μ := ρ))⟩
  apply Integrable.of_bound hpolar.measurable.aestronglyMeasurable.restrict 1
  filter_upwards [ae_restrict_of_ae hpolar.norm_ae] with x hx
  exact hx.le

/-- The total variation of each compact vector restriction is exactly the corresponding
restriction of the positive polar measure. -/
theorem IsDistributionalPolarRepresentation.variation_polarVectorRestriction {n : ℕ}
    {U : Set (EuclideanSpace ℝ (Fin n))} {f : EuclideanSpace ℝ (Fin n) → ℝ}
    {ρ : Measure U} [IsFiniteMeasureOnCompacts ρ] {σ : U → EuclideanSpace ℝ (Fin n)}
    (hpolar : IsDistributionalPolarRepresentation f U ρ σ) {K : Set U} (hK : IsCompact K) :
    (polarVectorRestriction ρ σ K).variation = ρ.restrict K := by
  rw [polarVectorRestriction, Measure.variation_withDensityᵥ (hpolar.integrableOn_direction hK)]
  calc
    _ = (ρ.restrict K).withDensity 1 := by
      apply withDensity_congr_ae
      filter_upwards [ae_restrict_of_ae hpolar.norm_ae] with x hx
      simp only [← ofReal_norm, hx, ENNReal.ofReal_one, Pi.one_apply]
    _ = ρ.restrict K := withDensity_one

/-- The compact vector restrictions agree on nested compact sets. -/
theorem IsDistributionalPolarRepresentation.polarVectorRestriction_restrict {n : ℕ}
    {U : Set (EuclideanSpace ℝ (Fin n))} {f : EuclideanSpace ℝ (Fin n) → ℝ}
    {ρ : Measure U} [IsFiniteMeasureOnCompacts ρ] {σ : U → EuclideanSpace ℝ (Fin n)}
    (hpolar : IsDistributionalPolarRepresentation f U ρ σ)
    {K L : Set U} (hK : IsCompact K) (hL : IsCompact L) (hKL : K ⊆ L) :
    (polarVectorRestriction ρ σ L).restrict K = polarVectorRestriction ρ σ K := by
  ext A hA
  rw [VectorMeasure.restrict_apply _ hK.measurableSet hA, polarVectorRestriction,
    withDensityᵥ_apply (hpolar.integrableOn_direction hL) (hA.inter hK.measurableSet),
    polarVectorRestriction, withDensityᵥ_apply (hpolar.integrableOn_direction hK) hA,
    Measure.restrict_restrict (hA.inter hK.measurableSet), Measure.restrict_restrict hA]
  rw [inter_assoc, inter_eq_left.mpr hKL]

/-- Polar decomposition on an open locally BV domain, including the genuine compatible
local vector measures, their total variations, and equality with the defining variation. -/
theorem polar_decomposition {n : ℕ} {U : Set (EuclideanSpace ℝ (Fin n))} (hU : IsOpen U)
    {f : EuclideanSpace ℝ (Fin n) → ℝ} (hf : IsLocallyBVOn f U) :
    ∃ ρ : Measure U, ∃ σ : U → EuclideanSpace ℝ (Fin n),
      ∃ D : Set U → VectorMeasure U (EuclideanSpace ℝ (Fin n)),
        ρ.Regular ∧ IsDistributionalPolarRepresentation f U ρ σ ∧
        (∀ O, IsOpen O → O ⊆ U → variation f O = ρ (Subtype.val ⁻¹' O)) ∧
        (∀ K, IsCompact K → D K = (ρ.restrict K).withDensityᵥ σ) ∧
        (∀ K, IsCompact K → (D K).variation = ρ.restrict K) ∧
        (∀ K L, IsCompact K → IsCompact L → K ⊆ L → (D L).restrict K = D K) := by
  obtain ⟨ρ, σ, hρ, hpolar, hvar⟩ := exists_polar_representation_with_variation hU hf
  let : ρ.Regular := hρ
  exact ⟨ρ, σ, polarVectorRestriction ρ σ, hρ, hpolar, hvar, fun _ _ => rfl,
    fun _ hK => hpolar.variation_polarVectorRestriction hK,
    fun _ _ hK hL hKL => hpolar.polarVectorRestriction_restrict hK hL hKL⟩

/-- Indicator functions of measurable sets with locally finite perimeter are locally BV
on every open subdomain, with no finite-volume assumption. -/
theorem HasLocallyFinitePerimeter.isLocallyBVOn_indicator {n : ℕ}
    {E : Set (EuclideanSpace ℝ (Fin n))} (hE : HasLocallyFinitePerimeter E)
    (hmE : NullMeasurableSet E volume) (U : Set (EuclideanSpace ℝ (Fin n))) :
    IsLocallyBVOn (E.indicator (fun _ => (1 : ℝ))) U := by
  exact ⟨(locallyIntegrable_indicator_one hmE).locallyIntegrableOn U,
    fun A hA hcA _ => hE A hA hcA⟩

/-- The outward normal is the negative polar direction. This records both the positive
boundary pairing and the negative sign of the derivative vector measure. -/
theorem exists_outward_perimeter_polar {n : ℕ}
    {E U : Set (EuclideanSpace ℝ (Fin n))} (hU : IsOpen U)
    (hE : HasLocallyFinitePerimeter E) (hmE : NullMeasurableSet E volume) :
    ∃ ρ : Measure U, ∃ ν : U → EuclideanSpace ℝ (Fin n),
      ρ.Regular ∧ Measurable ν ∧ (∀ᵐ x ∂ρ, ‖ν x‖ = 1) ∧
      IsDistributionalPolarRepresentation (E.indicator (fun _ => (1 : ℝ))) U ρ (-ν) ∧
      (∀ O, IsOpen O → O ⊆ U → perimeterIn E O = ρ (Subtype.val ⁻¹' O)) ∧
      (∀ K, IsCompact K →
        polarVectorRestriction ρ (-ν) K = -(ρ.restrict K).withDensityᵥ ν) ∧
      (∀ (X : EuclideanSpace ℝ (Fin n) → EuclideanSpace ℝ (Fin n)),
        ContDiff ℝ 1 X → HasCompactSupport X → tsupport X ⊆ U →
        (∫ x in U, E.indicator (fun _ => (1 : ℝ)) x * divergenceN X x) =
          ∫ x : U, inner ℝ (X x) (ν x) ∂ρ) := by
  have hf := hE.isLocallyBVOn_indicator hmE U
  obtain ⟨ρ, σ, hρ, hpolar, hvar⟩ := exists_polar_representation_with_variation hU hf
  let : ρ.Regular := hρ
  refine ⟨ρ, -σ, hρ, hpolar.measurable.neg, ?_, ?_, hvar, ?_, ?_⟩
  · simpa only [Pi.neg_apply, norm_neg] using hpolar.norm_ae
  · simpa only [neg_neg] using hpolar
  · intro K _
    exact withDensityᵥ_neg
  · intro X hX hcX hsX
    have h := hpolar.integral_divergence_eq hf.1 hX hcX hsX
    simpa only [Pi.neg_apply, inner_neg_right, integral_neg, neg_neg] using congrArg Neg.neg h

/-- Distributional polar measures agree when the represented functions agree almost
everywhere on the open domain. No finite global mass is required. -/
theorem IsDistributionalPolarRepresentation.measure_eq_of_ae_eq {n : ℕ}
    {U : Set (EuclideanSpace ℝ (Fin n))} (hU : IsOpen U)
    {f g : EuclideanSpace ℝ (Fin n) → ℝ}
    {ρ τ : Measure U} [ρ.Regular] [τ.Regular]
    {σ η : U → EuclideanSpace ℝ (Fin n)}
    (hpolar : IsDistributionalPolarRepresentation f U ρ σ)
    (hother : IsDistributionalPolarRepresentation g U τ η)
    (hf : LocallyIntegrableOn f U) (hg : LocallyIntegrableOn g U)
    (hfg : f =ᵐ[volume.restrict U] g) : ρ = τ := by
  apply Measure.OuterRegular.ext_isOpen
  intro V hV
  let O : Set (EuclideanSpace ℝ (Fin n)) := Subtype.val '' V
  have hO : IsOpen O := hU.isOpenEmbedding_subtypeVal.isOpenMap _ hV
  have hOU : O ⊆ U := by rintro _ ⟨x, _, rfl⟩; exact x.property
  have hpre : Subtype.val ⁻¹' O = V := preimage_image_eq _ Subtype.val_injective
  have heq : variation f O = variation g O :=
    variation_congr_ae O (ae_restrict_of_ae_restrict_of_subset hOU hfg)
  rw [hpolar.variation_eq_measure hU hO hOU hf,
    hother.variation_eq_measure hU hO hOU hg, hpre] at heq
  exact heq

/-- The regular measure in a distributional polar representation is unique. -/
theorem IsDistributionalPolarRepresentation.measure_unique {n : ℕ}
    {U : Set (EuclideanSpace ℝ (Fin n))} (hU : IsOpen U)
    {f : EuclideanSpace ℝ (Fin n) → ℝ}
    {ρ τ : Measure U} [ρ.Regular] [τ.Regular]
    {σ η : U → EuclideanSpace ℝ (Fin n)}
    (hpolar : IsDistributionalPolarRepresentation f U ρ σ)
    (hother : IsDistributionalPolarRepresentation f U τ η)
    (hf : LocallyIntegrableOn f U) : ρ = τ :=
  hpolar.measure_eq_of_ae_eq hU hother hf hf (EventuallyEq.refl _ _)

/-! ## Extended variation measures and perimeter locality -/

lemma variation_mono {n : ℕ} {f : EuclideanSpace ℝ (Fin n) → ℝ}
    {U V : Set (EuclideanSpace ℝ (Fin n))} (hV : MeasurableSet V) (hUV : U ⊆ V) :
    variation f U ≤ variation f V := by
  apply iSup_le
  intro X
  apply iSup_le
  intro hX
  have hXV : IsVariationTestField V X := ⟨hX.1, hX.2.1, hX.2.2.1.trans hUV, hX.2.2.2⟩
  have heq : (∫ x in V, f x * divergenceN X x) = ∫ x in U, f x * divergenceN X x := by
    apply setIntegral_eq_of_subset_of_forall_sdiff_eq_zero hV hUV
    intro x hx
    rw [divergenceN_eq_zero_of_notMem_tsupport (fun h => hx.2 (hX.2.2.1 h)), mul_zero]
  rw [← heq]
  exact le_iSup_of_le X (le_iSup_of_le hXV le_rfl)

@[simp]
lemma variation_empty {n : ℕ} (f : EuclideanSpace ℝ (Fin n) → ℝ) :
    variation f ∅ = 0 := by simp [variation]

set_option maxHeartbeats 800000 in
-- The manifold partition and Euclidean test-field interfaces require extra elaboration work.
/-- An admissible field splits into finitely many admissible fields subordinate to an
open cover, with every new support contained in the original compact support. -/
theorem exists_variationTestField_partition {n : ℕ} {ι : Type*}
    {U : Set (EuclideanSpace ℝ (Fin n))}
    {X : EuclideanSpace ℝ (Fin n) → EuclideanSpace ℝ (Fin n)}
    (hX : IsVariationTestField U X) (V : ι → Set (EuclideanSpace ℝ (Fin n)))
    (hV : ∀ i, IsOpen (V i)) (hcover : tsupport X ⊆ ⋃ i, V i) :
    ∃ s : Finset ι, ∃ Y : ι → EuclideanSpace ℝ (Fin n) → EuclideanSpace ℝ (Fin n),
      (∀ i, IsVariationTestField (V i) (Y i) ∧ tsupport (Y i) ⊆ tsupport X) ∧
      X = fun x => ∑ i ∈ s, Y i x := by
  classical
  obtain ⟨φ, hφ⟩ := SmoothPartitionOfUnity.exists_isSubordinate
    (I := 𝓘(ℝ, EuclideanSpace ℝ (Fin n))) (isClosed_tsupport X) V hV hcover
  let s := (φ.locallyFinite.finite_nonempty_inter_compact hX.2.1).toFinset
  let Y (i : ι) (x : EuclideanSpace ℝ (Fin n)) := φ i x • X x
  have hs (i : ι) : i ∈ s ↔ (Function.support (φ i) ∩ tsupport X).Nonempty :=
    Set.Finite.mem_toFinset _
  refine ⟨s, Y, ?_, ?_⟩
  · intro i
    have hsY : tsupport (Y i) ⊆ tsupport X := tsupport_smul_subset_right _ _
    have hcY : HasCompactSupport (Y i) :=
      hX.2.1.of_isClosed_subset (isClosed_tsupport _) hsY
    have hsV : tsupport (Y i) ⊆ V i :=
      (tsupport_smul_subset_left (fun x => φ i x) X).trans (hφ i)
    have hφi : ContDiff ℝ (⊤ : ℕ∞) (fun x => φ i x) := (φ i).contMDiff.contDiff
    refine ⟨⟨hφi.of_le (by decide) |>.smul hX.1, hcY, hsV, ?_⟩, hsY⟩
    · intro x
      calc
        ‖Y i x‖ = φ i x * ‖X x‖ := by
          change ‖φ i x • X x‖ = _
          rw [norm_smul, Real.norm_eq_abs, abs_of_nonneg (φ.nonneg i x)]
        _ ≤ 1 * 1 := mul_le_mul (φ.le_one i x) (hX.2.2.2 x) (norm_nonneg _) zero_le_one
        _ = 1 := one_mul _
  · funext x
    by_cases hx : x ∈ tsupport X
    · have hsum : ∑ i ∈ s, φ i x = 1 := by
        rw [← φ.sum_eq_one hx]
        symm
        apply finsum_eq_sum_of_support_subset
        intro i hi
        exact (hs i).mpr ⟨x, hi, hx⟩
      change X x = ∑ i ∈ s, φ i x • X x
      rw [← Finset.sum_smul, hsum, one_smul]
    · have hzero : X x = 0 := image_eq_zero_of_notMem_tsupport hx
      simp only [Y, hzero, smul_zero, Finset.sum_const_zero]


lemma divergenceN_finset_sum {n : ℕ} {ι : Type*} (s : Finset ι)
    {Y : ι → EuclideanSpace ℝ (Fin n) → EuclideanSpace ℝ (Fin n)}
    (hY : ∀ i ∈ s, ContDiff ℝ 1 (Y i)) (x : EuclideanSpace ℝ (Fin n)) :
    divergenceN (fun y => ∑ i ∈ s, Y i y) x = ∑ i ∈ s, divergenceN (Y i) x := by
  simp only [divergenceN, fderiv_fun_sum (fun i hi => (hY i hi).differentiable one_ne_zero x),
    sum_apply, WithLp.ofLp_sum, Finset.sum_apply]
  exact Finset.sum_comm

lemma ofReal_sum_le_sum {ι : Type*} (s : Finset ι) (a : ι → ℝ) :
    ENNReal.ofReal (∑ i ∈ s, a i) ≤ ∑ i ∈ s, ENNReal.ofReal (a i) := by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | @insert i s hi ih =>
    simp only [Finset.sum_insert hi]
    exact ENNReal.ofReal_add_le.trans (add_le_add le_rfl ih)

/-- Variation is bounded by the sum over any open cover, without a finite-variation
assumption. The partition is finite for each compactly supported test field. -/
theorem variation_le_tsum_open_cover {n : ℕ} {ι : Type*}
    {f : EuclideanSpace ℝ (Fin n) → ℝ} {U : Set (EuclideanSpace ℝ (Fin n))}
    (hf : LocallyIntegrableOn f U) (V : ι → Set (EuclideanSpace ℝ (Fin n)))
    (hV : ∀ i, IsOpen (V i)) (hcover : U ⊆ ⋃ i, V i) :
    variation f U ≤ ∑' i, variation f (V i) := by
  apply iSup_le
  intro X
  apply iSup_le
  intro hX
  obtain ⟨s, Y, hY, hsum⟩ := exists_variationTestField_partition hX V hV
    (hX.2.2.1.trans hcover)
  have hi (i : ι) : Integrable (fun x => f x * divergenceN (Y i) x) :=
    integrable_mul_divergenceN hf (hY i).1.1 (hY i).1.2.1 ((hY i).2.trans hX.2.2.1)
  have heq : (∫ x in U, f x * divergenceN X x) =
      ∑ i ∈ s, ∫ x in V i, f x * divergenceN (Y i) x := by
    rw [hsum]
    simp_rw [divergenceN_finset_sum s (fun i _ => (hY i).1.1), Finset.mul_sum]
    rw [integral_finsetSum s (fun i _ => (hi i).integrableOn (s := U))]
    apply Finset.sum_congr rfl
    intro i _
    have hUzero : (∫ x in U, f x * divergenceN (Y i) x) =
        ∫ x, f x * divergenceN (Y i) x := by
      apply setIntegral_eq_integral_of_forall_compl_eq_zero
      intro x hx
      rw [divergenceN_eq_zero_of_notMem_tsupport
        (fun h => hx (hX.2.2.1 ((hY i).2 h))), mul_zero]
    have hVzero : (∫ x in V i, f x * divergenceN (Y i) x) =
        ∫ x, f x * divergenceN (Y i) x := by
      apply setIntegral_eq_integral_of_forall_compl_eq_zero
      intro x hx
      rw [divergenceN_eq_zero_of_notMem_tsupport (fun h => hx ((hY i).1.2.2.1 h)), mul_zero]
    exact hUzero.trans hVzero.symm
  rw [heq]
  calc
    _ ≤ ∑ i ∈ s, ENNReal.ofReal (∫ x in V i, f x * divergenceN (Y i) x) :=
      ofReal_sum_le_sum _ _
    _ ≤ ∑ i ∈ s, variation f (V i) := Finset.sum_le_sum fun i _ =>
      le_iSup_of_le (Y i) (le_iSup_of_le (hY i).1 le_rfl)
    _ ≤ ∑' i, variation f (V i) := ENNReal.sum_le_tsum s


lemma isLocallyBVOn_of_variation_lt_top {n : ℕ}
    {U : Set (EuclideanSpace ℝ (Fin n))} (hU : IsOpen U)
    {f : EuclideanSpace ℝ (Fin n) → ℝ} (hf : LocallyIntegrableOn f U)
    (hfin : variation f U < ∞) : IsLocallyBVOn f U := by
  refine ⟨hf, fun A _ _ hA => ?_⟩
  exact (variation_mono hU.measurableSet (subset_closure.trans hA)).trans_lt hfin

/-- Disjoint open subregions are superadditive even when variation is infinite.
The finite case follows from the polar measure already constructed. -/
theorem variation_add_le_union {n : ℕ}
    {f : EuclideanSpace ℝ (Fin n) → ℝ} {A B : Set (EuclideanSpace ℝ (Fin n))}
    (hA : IsOpen A) (hB : IsOpen B) (hd : Disjoint A B)
    (hf : LocallyIntegrableOn f (A ∪ B)) :
    variation f A + variation f B ≤ variation f (A ∪ B) := by
  by_cases hfin : variation f (A ∪ B) = ∞
  · simp only [hfin, le_top]
  obtain ⟨ρ, σ, hρ, _, hvar⟩ := exists_polar_representation_with_variation (hA.union hB)
    (isLocallyBVOn_of_variation_lt_top (hA.union hB) hf (lt_top_iff_ne_top.mpr hfin))
  have hdis : Disjoint (Subtype.val ⁻¹' A : Set ↥(A ∪ B)) (Subtype.val ⁻¹' B) :=
    hd.preimage Subtype.val
  have hmB : MeasurableSet (Subtype.val ⁻¹' B : Set ↥(A ∪ B)) :=
    hB.measurableSet.preimage measurable_subtype_coe
  rw [hvar A hA subset_union_left, hvar B hB subset_union_right,
    hvar (A ∪ B) (hA.union hB) Subset.rfl, preimage_union, measure_union hdis hmB]

/-- The outer measure generated by variation on open sets. Its agreement on open sets
is proved for globally locally integrable functions. -/
noncomputable def variationOuterMeasure {n : ℕ} (f : EuclideanSpace ℝ (Fin n) → ℝ) :
    OuterMeasure (EuclideanSpace ℝ (Fin n)) := by
  classical
  exact OuterMeasure.ofFunction (fun A => if IsOpen A then variation f A else ∞)
    (by simp only [isOpen_empty, ↓reduceIte, variation_empty])

lemma variationOuterMeasure_open {n : ℕ} {f : EuclideanSpace ℝ (Fin n) → ℝ}
    (hf : LocallyIntegrable f) {U : Set (EuclideanSpace ℝ (Fin n))} (hU : IsOpen U) :
    variationOuterMeasure f U = variation f U := by
  classical
  apply le_antisymm
  · exact (OuterMeasure.ofFunction_le _).trans_eq (ite_eq_left hU)
  · rw [variationOuterMeasure, OuterMeasure.ofFunction_eq_iInf_mem _ _
      (P := IsOpen) (fun A hA => ite_eq_right hA)]
    refine le_iInf fun V => le_iInf fun hV => le_iInf fun hcover => ?_
    simp only [ite_eq_left (hV _)]
    exact variation_le_tsum_open_cover (hf.locallyIntegrableOn U) V hV hcover

lemma variationOuterMeasure_eq_iInf_open {n : ℕ} {f : EuclideanSpace ℝ (Fin n) → ℝ}
    (hf : LocallyIntegrable f) (A : Set (EuclideanSpace ℝ (Fin n))) :
    variationOuterMeasure f A =
      ⨅ (O : Set (EuclideanSpace ℝ (Fin n))) (_ : IsOpen O) (_ : A ⊆ O), variation f O := by
  classical
  apply le_antisymm
  · refine le_iInf fun O => le_iInf fun hO => le_iInf fun hAO => ?_
    exact ((variationOuterMeasure f).mono hAO).trans_eq (variationOuterMeasure_open hf hO)
  · rw [variationOuterMeasure, OuterMeasure.ofFunction_eq_iInf_mem _ _
      (P := IsOpen) (fun O hO => ite_eq_right hO)]
    refine le_iInf fun V => le_iInf fun hV => le_iInf fun hcover => ?_
    simp only [ite_eq_left (hV _)]
    calc
      _ ≤ variation f (⋃ i, V i) := iInf_le_of_le (⋃ i, V i)
        (iInf_le_of_le (isOpen_iUnion hV) (iInf_le _ hcover))
      _ ≤ ∑' i, variation f (V i) :=
        variation_le_tsum_open_cover (hf.locallyIntegrableOn _) V hV Subset.rfl


lemma disjoint_closure_of_areSeparated {n : ℕ}
    {s t : Set (EuclideanSpace ℝ (Fin n))} (h : AreSeparated s t) :
    Disjoint (closure s) (closure t) := by
  obtain ⟨r, hr, hst⟩ := h
  have hleft (y) (hy : y ∈ t) : closure s ⊆ {x | r ≤ edist x y} :=
    closure_minimal (fun x hx => hst x hx y hy)
      (isClosed_le continuous_const (continuous_id.edist continuous_const))
  have hright (x) (hx : x ∈ closure s) : closure t ⊆ {y | r ≤ edist x y} :=
    closure_minimal (fun y hy => hleft y hy hx)
      (isClosed_le continuous_const (continuous_const.edist continuous_id))
  apply Set.disjoint_left.mpr
  intro x hx hy
  have hz := hright x hx hy
  exact hr (by simpa only [mem_ofPred_eq, edist_self, nonpos_iff_eq_zero] using hz)

/-- The outer extension of variation is metric, and hence all Borel sets are measurable. -/
theorem variationOuterMeasure_isMetric {n : ℕ} {f : EuclideanSpace ℝ (Fin n) → ℝ}
    (hf : LocallyIntegrable f) : (variationOuterMeasure f).IsMetric := by
  intro s t hsep
  apply le_antisymm (measure_union_le s t)
  rw [variationOuterMeasure_eq_iInf_open hf (s ∪ t)]
  refine le_iInf fun O => le_iInf fun hO => le_iInf fun hstO => ?_
  obtain ⟨A, B, hA, hB, hsA, htB, hd⟩ :=
    normal_separation isClosed_closure isClosed_closure (disjoint_closure_of_areSeparated hsep)
  have hs : s ⊆ O ∩ A := fun x hx => ⟨hstO (Or.inl hx), hsA (subset_closure hx)⟩
  have ht : t ⊆ O ∩ B := fun x hx => ⟨hstO (Or.inr hx), htB (subset_closure hx)⟩
  calc
    _ ≤ variation f (O ∩ A) + variation f (O ∩ B) := add_le_add
      (((variationOuterMeasure f).mono hs).trans_eq (variationOuterMeasure_open hf (hO.inter hA)))
      (((variationOuterMeasure f).mono ht).trans_eq (variationOuterMeasure_open hf (hO.inter hB)))
    _ ≤ variation f ((O ∩ A) ∪ (O ∩ B)) :=
      variation_add_le_union (hO.inter hA) (hO.inter hB)
        (hd.mono inter_subset_right inter_subset_right) (hf.locallyIntegrableOn _)
    _ ≤ variation f O := variation_mono hO.measurableSet
      (union_subset inter_subset_left inter_subset_left)

/-- The Borel variation measure of a locally integrable function, without a locally finite
variation assumption. It can take infinite values on every neighborhood of a point. -/
noncomputable def variationMeasure {n : ℕ} (f : EuclideanSpace ℝ (Fin n) → ℝ)
    (hf : LocallyIntegrable f) : Measure (EuclideanSpace ℝ (Fin n)) :=
  (variationOuterMeasure f).toMeasure (variationOuterMeasure_isMetric hf).le_caratheodory

theorem variationMeasure_open {n : ℕ} {f : EuclideanSpace ℝ (Fin n) → ℝ}
    (hf : LocallyIntegrable f) {U : Set (EuclideanSpace ℝ (Fin n))} (hU : IsOpen U) :
    variationMeasure f hf U = variation f U := by
  rw [variationMeasure, toMeasure_apply _ _ hU.measurableSet, variationOuterMeasure_open hf hU]

/-- Every Lebesgue-measurable set has a Borel perimeter measure agreeing with the defining
variation on all open sets, even without locally finite perimeter. -/
theorem exists_perimeter_measure {n : ℕ} {E : Set (EuclideanSpace ℝ (Fin n))}
    (hE : NullMeasurableSet E volume) :
    ∃ μ : Measure (EuclideanSpace ℝ (Fin n)), ∀ O, IsOpen O → perimeterIn E O = μ O := by
  let hf := locallyIntegrable_indicator_one hE
  exact ⟨variationMeasure _ hf, fun _ hO => (variationMeasure_open hf hO).symm⟩


/-- Perimeter vanishes on a measurable region disjoint from the set. -/
lemma perimeterIn_eq_zero_of_disjoint {n : ℕ}
    {E O : Set (EuclideanSpace ℝ (Fin n))} (hO : MeasurableSet O) (hd : Disjoint E O) :
    perimeterIn E O = 0 := by
  have heq : E.indicator (fun _ => (1 : ℝ)) =ᵐ[volume.restrict O] fun _ => 0 := by
    filter_upwards [ae_restrict_mem hO] with x hx
    exact indicator_of_notMem (fun he => Set.disjoint_left.mp hd he hx) _
  rw [perimeterIn, variation_congr_ae O heq]
  simp [variation]

/-- Any perimeter measure with the correct open-set values is supported on the closure
of the set, including in the absence of locally finite perimeter. -/
lemma perimeter_measure_compl_eq_zero {n : ℕ}
    {E A : Set (EuclideanSpace ℝ (Fin n))} {μ : Measure (EuclideanSpace ℝ (Fin n))}
    (hμ : ∀ O, IsOpen O → perimeterIn E O = μ O) (hEA : closure E ⊆ A) : μ Aᶜ = 0 := by
  apply measure_mono_null (compl_subset_compl.mpr hEA)
  rw [← hμ (closure E)ᶜ isClosed_closure.isOpen_compl]
  apply perimeterIn_eq_zero_of_disjoint isClosed_closure.measurableSet.compl
  exact Set.disjoint_left.mpr fun x hx hx' => hx' (subset_closure hx)

/-- An open neighborhood of the closure carries the entire perimeter. -/
theorem perimeterN_eq_perimeterIn_of_closure_subset {n : ℕ}
    {E A : Set (EuclideanSpace ℝ (Fin n))} (hE : NullMeasurableSet E volume)
    (hA : IsOpen A) (hEA : closure E ⊆ A) : perimeterN E = perimeterIn E A := by
  obtain ⟨μ, hμ⟩ := exists_perimeter_measure hE
  change perimeterIn E univ = perimeterIn E A
  rw [hμ univ isOpen_univ, hμ A hA]
  have h := measure_add_measure_compl (μ := μ) hA.measurableSet
  rw [perimeter_measure_compl_eq_zero hμ hEA, add_zero] at h
  exact h.symm

lemma perimeterIn_union_eq_left_of_disjoint {n : ℕ}
    {E F O : Set (EuclideanSpace ℝ (Fin n))} (hO : MeasurableSet O) (hd : Disjoint F O) :
    perimeterIn (E ∪ F) O = perimeterIn E O := by
  apply perimeterIn_congr_ae
  filter_upwards [ae_restrict_mem hO] with x hx
  have hxF : x ∉ F := fun hf => Set.disjoint_left.mp hd hf hx
  change (x ∈ E ∪ F) = (x ∈ E)
  simp only [mem_union, hxF, or_false]

/-- Sets separated by a positive distance have additive perimeter. This includes infinite
perimeters and therefore implies the finite-perimeter statement in the blueprint. -/
theorem perimeterN_union_of_areSeparated {n : ℕ}
    {E F : Set (EuclideanSpace ℝ (Fin n))} (hE : NullMeasurableSet E volume)
    (hF : NullMeasurableSet F volume) (hsep : AreSeparated E F) :
    perimeterN (E ∪ F) = perimeterN E + perimeterN F := by
  obtain ⟨A, B, hA, hB, hEA, hFB, hd⟩ :=
    normal_separation isClosed_closure isClosed_closure (disjoint_closure_of_areSeparated hsep)
  have hEFAB : closure (E ∪ F) ⊆ A ∪ B := by
    rw [closure_union]
    exact union_subset_union hEA hFB
  have hlocalA : perimeterIn (E ∪ F) A = perimeterIn E A :=
    perimeterIn_union_eq_left_of_disjoint hA.measurableSet
      (hd.symm.mono (subset_closure.trans hFB) Subset.rfl)
  have hlocalB : perimeterIn (E ∪ F) B = perimeterIn F B := by
    rw [union_comm]
    exact perimeterIn_union_eq_left_of_disjoint hB.measurableSet
      (hd.mono (subset_closure.trans hEA) Subset.rfl)
  obtain ⟨μ, hμ⟩ := exists_perimeter_measure (hE.union hF)
  calc
    perimeterN (E ∪ F) = perimeterIn (E ∪ F) (A ∪ B) :=
      perimeterN_eq_perimeterIn_of_closure_subset (hE.union hF) (hA.union hB) hEFAB
    _ = μ (A ∪ B) := hμ _ (hA.union hB)
    _ = μ A + μ B := measure_union hd hB.measurableSet
    _ = perimeterIn E A + perimeterIn F B := by rw [← hμ A hA, ← hμ B hB, hlocalA, hlocalB]
    _ = perimeterN E + perimeterN F := by
      rw [← perimeterN_eq_perimeterIn_of_closure_subset hE hA hEA,
        ← perimeterN_eq_perimeterIn_of_closure_subset hF hB hFB]

end LiquidDrop

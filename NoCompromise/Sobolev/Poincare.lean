import NoCompromise.BV.ZeroVariation
import NoCompromise.BV.Compactness
import NoCompromise.BV.Algebra
import NoCompromise.Sobolev.Extension
import NoCompromise.Sobolev.BV
import Mathlib.MeasureTheory.Integral.Average

/-!
# The compactness argument for BV Poincaré inequalities

This module isolates the strong-L¹ compactness input, proves it from a quantitative
BV extension, and derives the mean-zero L¹ Poincaré estimate by contradiction.
-/

noncomputable section

open MeasureTheory Filter Metric Set
open scoped ENNReal Topology

namespace LiquidDrop

set_option maxSynthPendingDepth 8

/-- Strong L¹ sequential compactness for uniformly bounded BV functions on a fixed domain. -/
def HasBVCompactness {n : ℕ} (D : Set (EuclideanSpace ℝ (Fin n))) : Prop :=
  ∀ f : ℕ → EuclideanSpace ℝ (Fin n) → ℝ, (∀ j, IsBVOn (f j) D) →
    ∀ B : ℝ, 0 ≤ B →
      (∀ j, (∫ x in D, |f j x|) + (variation (f j) D).toReal ≤ B) →
      ∃ g : EuclideanSpace ℝ (Fin n) → ℝ, ∃ σ : ℕ → ℕ,
        StrictMono σ ∧ IntegrableOn g D ∧
          Tendsto (fun j => ∫ x in D, |f (σ j) x - g x|) atTop (𝓝 0)

/-- Ordinary L¹ convergence implies convergence of integrals for any measure. -/
lemma tendsto_integral_of_integral_norm_sub_tendsto_zero {α : Type*} [MeasurableSpace α]
    {μ : Measure α} {f : ℕ → α → ℝ} {g : α → ℝ}
    (hf : ∀ j, Integrable (f j) μ) (hg : Integrable g μ)
    (ht : Tendsto (fun j => ∫ x, |f j x - g x| ∂μ) atTop (𝓝 0)) :
    Tendsto (fun j => ∫ x, f j x ∂μ) atTop (𝓝 (∫ x, g x ∂μ)) := by
  apply tendsto_iff_norm_sub_tendsto_zero.mpr
  refine squeeze_zero (fun _ => norm_nonneg _) (fun j => ?_) ht
  rw [← integral_sub (hf j) hg]
  simpa only [Real.norm_eq_abs] using norm_integral_le_integral_norm (fun x => f j x - g x)

/-- Ordinary L¹ convergence implies convergence of the L¹ norms. -/
lemma tendsto_integral_abs_of_integral_abs_sub_tendsto_zero {α : Type*} [MeasurableSpace α]
    {μ : Measure α} {f : ℕ → α → ℝ} {g : α → ℝ}
    (hf : ∀ j, Integrable (f j) μ) (hg : Integrable g μ)
    (ht : Tendsto (fun j => ∫ x, |f j x - g x| ∂μ) atTop (𝓝 0)) :
    Tendsto (fun j => ∫ x, |f j x| ∂μ) atTop (𝓝 (∫ x, |g x| ∂μ)) := by
  apply tendsto_integral_of_integral_norm_sub_tendsto_zero (fun j => (hf j).abs) hg.abs
  apply squeeze_zero (fun _ => integral_nonneg fun _ => abs_nonneg _) (fun j => ?_) ht
  exact integral_mono ((hf j).abs.sub hg.abs).abs ((hf j).sub hg).abs
    (fun x => abs_abs_sub_abs_le_abs_sub _ _)

/-- Bounded extension to whole-space BV implies strong L¹ compactness on a bounded domain.
Linearity and support control are unnecessary for this compactness consequence. -/
theorem hasBVCompactness_of_bounded_extension {n : ℕ}
    {D : Set (EuclideanSpace ℝ (Fin n))} (hD : MeasurableSet D)
    (hbD : Bornology.IsBounded D) {C : ℝ} (hC : 0 ≤ C)
    (hext : ∀ f : EuclideanSpace ℝ (Fin n) → ℝ, IsBVOn f D →
      ∃ F : EuclideanSpace ℝ (Fin n) → ℝ, IsBVOn F univ ∧
        F =ᵐ[volume.restrict D] f ∧
        (∫ x, |F x|) + (variation F univ).toReal ≤
          C * ((∫ x in D, |f x|) + (variation f D).toReal)) :
    HasBVCompactness D := by
  intro f hf B hB hbound
  choose F hF hFeq hFbound using fun j => hext (f j) (hf j)
  have hbound' (j) : (∫ x, |F j x|) + (variation (F j) univ).toReal ≤ C * B :=
    (hFbound j).trans (mul_le_mul_of_nonneg_left (hbound j) hC)
  have hL (j) : (∫ x in univ, |F j x|) ≤ C * B := by
    simp only [setIntegral_univ]
    linarith [hbound' j, ENNReal.toReal_nonneg (a := variation (F j) univ)]
  have hV (j) : (variation (F j) univ).toReal ≤ C * B := by
    have hnonneg : 0 ≤ ∫ x, |F j x| := integral_nonneg fun x => abs_nonneg (F j x)
    linarith [hbound' j]
  obtain ⟨g, σ, hσ, hig, ht⟩ := exists_subseq_l1_of_bv_bounds isOpen_univ hD
    hbD.isCompact_closure (subset_univ _) F hF (mul_nonneg hC hB) hL hV
  refine ⟨g, σ, hσ, hig, ?_⟩
  convert ht using 1
  ext j
  exact integral_congr_ae ((hFeq (σ j)).symm.sub EventuallyEq.rfl |>.fun_comp abs)

/-- A mean-zero, unit-L¹ BV sequence with variation tending to zero contradicts compactness
and connectedness. This is the normalization argument underlying BV Poincaré. -/
theorem not_exists_normalized_bv_sequence_of_compactness {n : ℕ}
    {D : Set (EuclideanSpace ℝ (Fin n))} (hD : IsOpen D) (hcD : IsPreconnected D)
    (hcompact : HasBVCompactness D)
    (f : ℕ → EuclideanSpace ℝ (Fin n) → ℝ) (hf : ∀ j, IsBVOn (f j) D)
    (hmean : ∀ j, (∫ x in D, f j x) = 0)
    (hnorm : ∀ j, (∫ x in D, |f j x|) = 1)
    (hvarbound : ∀ j, (variation (f j) D).toReal ≤ 1)
    (hvarlim : Tendsto (fun j => (variation (f j) D).toReal) atTop (𝓝 0)) : False := by
  obtain ⟨g, σ, hσ, hig, ht⟩ := hcompact f hf 2 (by norm_num)
    (fun j => by rw [hnorm j]; linarith [hvarbound j])
  have hmeanlim := tendsto_integral_of_integral_norm_sub_tendsto_zero
    (fun j => (hf (σ j)).1) hig ht
  have hnormlim := tendsto_integral_abs_of_integral_abs_sub_tendsto_zero
    (fun j => (hf (σ j)).1) hig ht
  simp_rw [hmean] at hmeanlim
  simp_rw [hnorm] at hnormlim
  have hmean0 : (∫ x in D, g x) = 0 := tendsto_nhds_unique hmeanlim tendsto_const_nhds
  have hnorm1 : (∫ x in D, |g x|) = 1 := tendsto_nhds_unique hnormlim tendsto_const_nhds
  have hlocal (K : Set (EuclideanSpace ℝ (Fin n))) (_hK : IsCompact K) (hKD : K ⊆ D) :
      Tendsto (fun j => ∫ x in K, |f (σ j) x - g x|) atTop (𝓝 0) := by
    apply squeeze_zero (fun _ => integral_nonneg fun _ => abs_nonneg _) (fun j => ?_) ht
    exact setIntegral_mono_set ((hf (σ j)).1.sub hig).abs
      (Eventually.of_forall fun _ => abs_nonneg _) (Eventually.of_forall hKD)
  have hlsc := variation_le_liminf_of_locally_l1 hD
    (fun j => (hf (σ j)).1.locallyIntegrableOn) hig.locallyIntegrableOn hlocal
  have htvar := ENNReal.continuous_ofReal.continuousAt.tendsto.comp
    (hvarlim.comp hσ.tendsto_atTop)
  simp only [ENNReal.ofReal_zero] at htvar
  have htvar' : Tendsto (fun j => variation (f (σ j)) D) atTop (𝓝 0) := by
    convert htvar using 1
    ext j
    exact (ENNReal.ofReal_toReal (hf (σ j)).2.ne).symm
  have hz : variation g D = 0 := le_antisymm (hlsc.trans_eq htvar'.liminf_eq) bot_le
  obtain ⟨c, hc⟩ := ae_eq_const_of_variation_eq_zero hD hcD hig.locallyIntegrableOn hz
  have heq : (∫ x in D, |g x|) = |∫ x in D, g x| := by
    have hcabs : (fun x => |g x|) =ᵐ[volume.restrict D] fun _ => |c| := hc.fun_comp abs
    rw [integral_congr_ae hcabs, integral_congr_ae hc]
    simp only [integral_const, smul_eq_mul, abs_mul, abs_of_nonneg measureReal_nonneg]
  rw [hmean0, hnorm1] at heq
  norm_num at heq

/-- Strong L¹ BV compactness and connectedness give the mean-zero L¹ Poincaré estimate. -/
theorem exists_bv_poincare_mean_zero_of_compactness {n : ℕ}
    {D : Set (EuclideanSpace ℝ (Fin n))} (hD : IsOpen D) (hcD : IsPreconnected D)
    (hcompact : HasBVCompactness D) :
    ∃ C : ℝ, 0 < C ∧ ∀ f : EuclideanSpace ℝ (Fin n) → ℝ,
      IsBVOn f D → (∫ x in D, f x) = 0 →
        (∫ x in D, |f x|) ≤ C * (variation f D).toReal := by
  classical
  by_contra! h
  have hbad (j : ℕ) := h ((j : ℝ) + 1) (by positivity)
  choose f hf hmean hbad using hbad
  let N (j : ℕ) := ∫ x in D, |f j x|
  have hN (j) : 0 < N j := by
    have hv : 0 ≤ ((j : ℝ) + 1) * (variation (f j) D).toReal := by positivity
    exact hv.trans_lt (hbad j)
  let g (j : ℕ) (x : EuclideanSpace ℝ (Fin n)) := (N j)⁻¹ * f j x
  have hg (j) : IsBVOn (g j) D := (hf j).const_mul _
  have hmean' (j) : (∫ x in D, g j x) = 0 := by
    simp only [g, integral_const_mul, hmean j, mul_zero]
  have hnorm (j) : (∫ x in D, |g j x|) = 1 := by
    simp only [g, abs_mul, abs_inv, abs_of_pos (hN j), integral_const_mul]
    exact inv_mul_cancel₀ (hN j).ne'
  have hvar (j) : (variation (g j) D).toReal < 1 / ((j : ℝ) + 1) := by
    rw [show g j = fun x => (N j)⁻¹ * f j x from rfl, variation_const_mul,
      ENNReal.toReal_mul, ENNReal.toReal_ofReal (abs_nonneg _), abs_inv, abs_of_pos (hN j)]
    rw [inv_mul_eq_div, div_lt_div_iff₀ (hN j) (by positivity)]
    simpa only [one_mul, mul_comm] using hbad j
  have hvarbound (j) : (variation (g j) D).toReal ≤ 1 := by
    apply (hvar j).le.trans
    exact div_le_self (by norm_num) (by norm_num)
  have hvarlim : Tendsto (fun j => (variation (g j) D).toReal) atTop (𝓝 0) := by
    exact squeeze_zero (fun _ => ENNReal.toReal_nonneg) (fun j => (hvar j).le)
      (tendsto_one_div_add_atTop_nhds_zero_nat (𝕜 := ℝ))
  exact not_exists_normalized_bv_sequence_of_compactness hD hcD hcompact g hg
    hmean' hnorm hvarbound hvarlim

/-- Subtracting a constant leaves variation unchanged. -/
theorem variation_sub_const {n : ℕ}
    {D : Set (EuclideanSpace ℝ (Fin n))} {f : EuclideanSpace ℝ (Fin n) → ℝ}
    (hf : LocallyIntegrableOn f D) (c : ℝ) :
    variation (fun x => f x - c) D = variation f D := by
  unfold variation
  congr 1
  funext X
  congr 1
  funext hX
  have hi := (integrable_mul_divergenceN hf hX.1 hX.2.1 hX.2.2.1).integrableOn (s := D)
  have hid := (integrable_divergenceN hX.1 hX.2.1).integrableOn (s := D)
  have hzero : (∫ x in D, divergenceN X x) = 0 := by
    rw [setIntegral_eq_integral_of_forall_compl_eq_zero]
    · exact integral_divergenceN_eq_zero hX.1 hX.2.1
    · intro x hx
      exact divergenceN_eq_zero_of_notMem_tsupport (fun h => hx (hX.2.2.1 h))
  simp_rw [sub_mul]
  rw [integral_sub hi (hid.const_mul c), integral_const_mul, hzero, mul_zero, sub_zero]

/-- Centering by the domain average converts the mean-zero estimate into L¹ BV Poincaré. -/
theorem exists_bv_poincare_l1_of_compactness {n : ℕ}
    {D : Set (EuclideanSpace ℝ (Fin n))} (hD : IsOpen D) (hcD : IsPreconnected D)
    (hvol : volume D ≠ ∞) (hcompact : HasBVCompactness D) :
    ∃ C : ℝ, 0 < C ∧ ∀ f : EuclideanSpace ℝ (Fin n) → ℝ, IsBVOn f D →
      (∫ x in D, |f x - ⨍ y in D, f y|) ≤ C * (variation f D).toReal := by
  obtain ⟨C, hC, hb⟩ := exists_bv_poincare_mean_zero_of_compactness hD hcD hcompact
  refine ⟨C, hC, fun f hf => ?_⟩
  have hv := variation_sub_const hf.1.locallyIntegrableOn (⨍ y in D, f y)
  have hg : IsBVOn (fun x => f x - ⨍ y in D, f y) D :=
    ⟨hf.1.sub (integrableOn_const hvol), by rw [hv]; exact hf.2⟩
  have h := hb (fun x => f x - ⨍ y in D, f y) hg (setAverage_sub_setAverage hvol f)
  rwa [hv] at h

/-- Bounded Lipschitz domains have strong L¹ sequential BV compactness. -/
theorem hasBVCompactness_of_lipschitzBoundary {n : ℕ}
    {D : Set (EuclideanSpace ℝ (Fin n))} (hD : IsOpen D)
    (hbD : Bornology.IsBounded D) (hL : HasLipschitzBoundary D) :
    HasBVCompactness D := by
  obtain ⟨T, K, C, _, hC, hT⟩ := exists_bv_extension_linearMap hD hbD hL
  apply hasBVCompactness_of_bounded_extension hD.measurableSet hbD hC
  intro f hf
  have h := hT f hf
  refine ⟨T f, h.1, ae_restrict_of_forall_mem hD.measurableSet h.2.1, ?_⟩
  simpa only [Real.norm_eq_abs] using h.2.2.2

/-- The L¹ clause of blueprint BV Poincaré, in arbitrary finite dimension. -/
theorem bv_poincare_l1 {n : ℕ}
    {D : Set (EuclideanSpace ℝ (Fin n))} (hD : IsOpen D) (hcD : IsPreconnected D)
    (hbD : Bornology.IsBounded D) (hL : HasLipschitzBoundary D) :
    ∃ C : ℝ, 0 < C ∧ ∀ f : EuclideanSpace ℝ (Fin n) → ℝ, IsBVOn f D →
      (∫ x in D, |f x - ⨍ y in D, f y|) ≤ C * (variation f D).toReal :=
  exists_bv_poincare_l1_of_compactness hD hcD hbD.measure_lt_top.ne
    (hasBVCompactness_of_lipschitzBoundary hD hbD hL)

/-- A whole-space BV embedding upgrades the L¹ Poincaré inequality on bounded connected
Lipschitz domains to the same exponent. The final two-dimensional and three-dimensional
statements below instantiate the proved whole-space embeddings. -/
theorem bv_poincare_of_bv_embedding {n : ℕ} {p : ℝ≥0∞}
    (hsob : ∀ F : EuclideanSpace ℝ (Fin n) → ℝ, IsBVOn F univ →
      MemLp F p volume ∧ eLpNorm F p volume ≤ variation F univ)
    {D : Set (EuclideanSpace ℝ (Fin n))} (hD : IsOpen D) (hcD : IsPreconnected D)
    (hbD : Bornology.IsBounded D) (hL : HasLipschitzBoundary D) :
    ∃ C : ℝ, 0 < C ∧ ∀ f : EuclideanSpace ℝ (Fin n) → ℝ, IsBVOn f D →
      (∫ x in D, |f x - ⨍ y in D, f y|) ≤ C * (variation f D).toReal ∧
      MemLp (fun x => f x - ⨍ y in D, f y) p (volume.restrict D) ∧
      lpNorm (fun x => f x - ⨍ y in D, f y) p (volume.restrict D) ≤
        C * (variation f D).toReal := by
  obtain ⟨A, hA, hP⟩ := bv_poincare_l1 hD hcD hbD hL
  obtain ⟨T, K, B, _, hB, hT⟩ := exists_bv_extension_linearMap hD hbD hL
  refine ⟨A + B * (A + 1), by nlinarith, fun f hf => ?_⟩
  let g := fun x => f x - ⨍ y in D, f y
  have hv : variation g D = variation f D := variation_sub_const hf.1.locallyIntegrableOn _
  have hg : IsBVOn g D :=
    ⟨hf.1.sub (integrableOn_const hbD.measure_lt_top.ne), by rw [hv]; exact hf.2⟩
  have hTg := hT g hg
  have hnorm : (∫ x in D, |g x|) ≤ A * (variation f D).toReal := hP f hf
  have hnonneg : 0 ≤ B * (A + 1) := mul_nonneg hB (by linarith)
  refine ⟨hnorm.trans (mul_le_mul_of_nonneg_right (by linarith) ENNReal.toReal_nonneg), ?_⟩
  have heq : T g =ᵐ[volume.restrict D] g :=
    ae_restrict_of_forall_mem hD.measurableSet hTg.2.1
  obtain ⟨hmem, hSob⟩ := hsob (T g) hTg.1
  have hmemD : MemLp g p (volume.restrict D) := MemLp.ae_eq heq (hmem.restrict D)
  refine ⟨hmemD, ?_⟩
  have hel : eLpNorm g p (volume.restrict D) ≤ variation (T g) univ := by
    rw [← eLpNorm_congr_ae heq]
    exact (eLpNorm_mono_measure _ Measure.restrict_le_self).trans hSob
  have hreal : lpNorm g p (volume.restrict D) ≤ (variation (T g) univ).toReal := by
    simpa only [toReal_eLpNorm] using ENNReal.toReal_mono hTg.1.2.ne hel
  have hext : (∫ x, |T g x|) + (variation (T g) univ).toReal ≤
      B * ((∫ x in D, |g x|) + (variation f D).toReal) := by
    simpa only [Real.norm_eq_abs, hv] using hTg.2.2.2
  have hnonnegT : 0 ≤ ∫ x, |T g x| := integral_nonneg fun _ => abs_nonneg _
  have hvar : (variation (T g) univ).toReal ≤
      B * (A + 1) * (variation f D).toReal := by
    have := mul_le_mul_of_nonneg_left
      (add_le_add_right hnorm (variation f D).toReal) hB
    nlinarith
  apply hreal.trans (hvar.trans ?_)
  exact mul_le_mul_of_nonneg_right (by linarith) ENNReal.toReal_nonneg

/-- Blueprint `thm:bv-poincare` in dimension three: a common constant controls both L¹
and L³ᐟ² deviations from the average, with actual L³ᐟ² membership. -/
theorem bv_poincare_three
    {D : Set (EuclideanSpace ℝ (Fin 3))} (hD : IsOpen D) (hcD : IsPreconnected D)
    (hbD : Bornology.IsBounded D) (hL : HasLipschitzBoundary D) :
    ∃ C : ℝ, 0 < C ∧ ∀ f : EuclideanSpace ℝ (Fin 3) → ℝ, IsBVOn f D →
      (∫ x in D, |f x - ⨍ y in D, f y|) ≤ C * (variation f D).toReal ∧
      MemLp (fun x => f x - ⨍ y in D, f y) (3 / 2) (volume.restrict D) ∧
      lpNorm (fun x => f x - ⨍ y in D, f y) (3 / 2) (volume.restrict D) ≤
        C * (variation f D).toReal :=
  bv_poincare_of_bv_embedding
    (fun _ hF => ⟨(memLp_and_bv_sobolev_three hF).1, bv_sobolev_three hF⟩) hD hcD hbD hL

/-- Blueprint `thm:bv-poincare` in dimension two: a common constant controls both L¹
and L² deviations from the average, with actual L² membership. -/
theorem bv_poincare_two
    {D : Set (EuclideanSpace ℝ (Fin 2))} (hD : IsOpen D) (hcD : IsPreconnected D)
    (hbD : Bornology.IsBounded D) (hL : HasLipschitzBoundary D) :
    ∃ C : ℝ, 0 < C ∧ ∀ f : EuclideanSpace ℝ (Fin 2) → ℝ, IsBVOn f D →
      (∫ x in D, |f x - ⨍ y in D, f y|) ≤ C * (variation f D).toReal ∧
      MemLp (fun x => f x - ⨍ y in D, f y) 2 (volume.restrict D) ∧
      lpNorm (fun x => f x - ⨍ y in D, f y) 2 (volume.restrict D) ≤
        C * (variation f D).toReal :=
  bv_poincare_of_bv_embedding (fun _ hF => bv_sobolev_two hF) hD hcD hbD hL

end LiquidDrop

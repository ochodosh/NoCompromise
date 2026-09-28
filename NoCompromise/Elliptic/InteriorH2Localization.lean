import NoCompromise.Elliptic.InteriorH2Global

/-!
# Localization of the distributional Poisson equation

The product rule below is proved by compact test functions and the existing weak
gradient pairing. It introduces no regularity assumption beyond those already constructed.
-/

noncomputable section

open MeasureTheory Filter Metric Set InnerProductSpace
open scoped NNReal ENNReal Topology Gradient Convolution

namespace LiquidDrop

set_option maxSynthPendingDepth 8

/-- Compact smooth localization of a distributional Poisson equation, with its
actual source including the two first-derivative product terms. -/
theorem HasDistributionalLaplacianOn.mul_compact_cutoff {n : ℕ}
    {U : Set (EuclideanSpace ℝ (Fin n))}
    {u f η : EuclideanSpace ℝ (Fin n) → ℝ}
    {G : EuclideanSpace ℝ (Fin n) → EuclideanSpace ℝ (Fin n)}
    (h : HasDistributionalLaplacianOn u f U) (hG : HasWeakGradientOn u G U)
    (hη : ContDiff ℝ (⊤ : ℕ∞) η) (hcη : HasCompactSupport η) (hsη : tsupport η ⊆ U) :
    HasDistributionalLaplacianOn (fun x => η x * u x)
      (fun x => η x * f x + laplacianN η x * u x +
        2 * inner ℝ (gradient η x) (G x)) univ := by
  have hη1 : ContDiff ℝ 1 η := hη.of_le (by simp)
  have hη2 : ContDiff ℝ 2 η := hη.of_le (by simp)
  have hgrad : ContDiff ℝ 1 (gradient η) := contDiff_gradient_of_contDiff_succ hη2
  have hcgrad : HasCompactSupport (gradient η) :=
    hcη.of_isClosed_subset (isClosed_tsupport _) (tsupport_gradient_subset η)
  have hsgrad := (tsupport_gradient_subset η).trans hsη
  have hclap : HasCompactSupport (laplacianN η) :=
    hcη.of_isClosed_subset (isClosed_tsupport _) (tsupport_laplacianN_subset η)
  have hslap := (tsupport_laplacianN_subset η).trans hsη
  have hiu := integrable_mul_compact_factor h.locallyIntegrable_function hη.continuous hcη hsη
  have hif := integrable_mul_compact_factor h.locallyIntegrable_source hη.continuous hcη hsη
  have hiulap := integrable_mul_compact_factor h.locallyIntegrable_function
    (continuous_laplacianN hη2) hclap hslap
  have hiG := integrable_inner_compact_factor_on hG.locallyIntegrable_gradient
    hgrad.continuous hcgrad hsgrad
  refine ⟨hiu.locallyIntegrable.locallyIntegrableOn univ,
    ((hif.add hiulap).add (hiG.const_mul 2)).locallyIntegrable.locallyIntegrableOn univ, ?_⟩
  intro φ hφ hcφ _
  have hφ1 : ContDiff ℝ 1 φ := hφ.of_le (by simp)
  have hφ2 : ContDiff ℝ 2 φ := hφ.of_le (by simp)
  let X (x : EuclideanSpace ℝ (Fin n)) : EuclideanSpace ℝ (Fin n) := φ x • gradient η x
  have hX : ContDiff ℝ 1 X := hφ1.smul hgrad
  have hcX : HasCompactSupport X := hcgrad.smul_left (f := φ)
  have hsX : tsupport X ⊆ U := (tsupport_smul_subset_right φ (gradient η)).trans hsgrad
  let A (x : EuclideanSpace ℝ (Fin n)) := (η x * laplacianN φ x) * u x
  let B (x : EuclideanSpace ℝ (Fin n)) := (φ x * laplacianN η x) * u x
  let C (x : EuclideanSpace ℝ (Fin n)) :=
    inner ℝ (gradient φ x) (gradient η x) * u x
  let D (x : EuclideanSpace ℝ (Fin n)) := (η x * φ x) * f x
  let Q (x : EuclideanSpace ℝ (Fin n)) := inner ℝ (X x) (G x)
  have hiA : Integrable A := integrable_mul_compact_factor h.locallyIntegrable_function
    (hη.continuous.mul (continuous_laplacianN hφ2)) hcη.mul_right
    (tsupport_mul_subset_left.trans hsη)
  have hiB : Integrable B := integrable_mul_compact_factor h.locallyIntegrable_function
    (hφ.continuous.mul (continuous_laplacianN hη2)) (hclap.mul_left (f := φ))
    (tsupport_mul_subset_right.trans hslap)
  have hiD : Integrable D := integrable_mul_compact_factor h.locallyIntegrable_source
    (hη.continuous.mul hφ.continuous) (hcη.mul_right (f' := φ))
    (tsupport_mul_subset_left.trans hsη)
  have hiQ : Integrable Q := integrable_inner_compact_factor_on
    hG.locallyIntegrable_gradient hX.continuous hcX hsX
  have hdiv (x : EuclideanSpace ℝ (Fin n)) :
      divergenceN X x = φ x * laplacianN η x + inner ℝ (gradient φ x) (gradient η x) := by
    rw [show divergenceN X x = _ from divergenceN_smul hφ1 hgrad x,
      ← laplacianN_eq_divergenceN_gradient hη2]
  have hBC : (fun x => u x * divergenceN X x) = fun x => B x + C x := by
    funext x
    rw [hdiv]
    dsimp [B, C]
    ring
  have hiC : Integrable C := by
    have hd := integrable_mul_divergenceN h.locallyIntegrable_function hX hcX hsX
    have he : C = fun x => u x * divergenceN X x - B x := by
      funext x
      rw [hdiv]
      dsimp [B, C]
      ring
    rw [he]
    exact hd.sub hiB
  have htest := h.test_eq (fun x => η x * φ x) (hη.mul hφ) hcη.mul_right
    (tsupport_mul_subset_left.trans hsη)
  have hsprod : tsupport (fun x => η x * φ x) ⊆ U := tsupport_mul_subset_left.trans hsη
  have hleft : (∫ x in U, u x * laplacianN (fun y => η y * φ y) x) =
      ∫ x, u x * laplacianN (fun y => η y * φ y) x :=
    setIntegral_eq_integral_of_forall_compl_eq_zero fun x hx => by
      rw [image_eq_zero_of_notMem_tsupport
        (fun ht => hx (hsprod ((tsupport_laplacianN_subset _) ht))), mul_zero]
  have hright : (∫ x in U, f x * (η x * φ x)) = ∫ x, D x := by
    rw [setIntegral_eq_integral_of_forall_compl_eq_zero
      (fun x hx => by rw [image_eq_zero_of_notMem_tsupport (fun ht => hx (hsη ht))]; simp)]
    apply integral_congr_ae
    exact Eventually.of_forall fun x => by dsimp [D]; ring
  rw [hleft, hright] at htest
  have hABC : (fun x => u x * laplacianN (fun y => η y * φ y) x) =
      fun x => A x + B x + 2 * C x := by
    funext x
    rw [laplacianN_mul hφ2 hη2, real_inner_comm]
    dsimp [A, B, C]
    ring
  rw [hABC, integral_add (f := fun x => A x + B x) (g := fun x => 2 * C x)
    (hiA.add hiB) (hiC.const_mul 2), integral_add hiA hiB, integral_const_mul] at htest
  have hweak := hG.integral_divergence_eq hX hcX hsX
  rw [setIntegral_eq_integral_of_forall_compl_eq_zero
    (fun x hx => by rw [divergenceN_eq_zero_of_notMem_tsupport
      (fun ht => hx (hsX ht)), mul_zero])] at hweak
  rw [setIntegral_eq_integral_of_forall_compl_eq_zero
    (fun x hx => by rw [image_eq_zero_of_notMem_tsupport (fun ht => hx (hsX ht)),
      inner_zero_left])] at hweak
  change -(∫ x, u x * divergenceN X x) = ∫ x, Q x at hweak
  rw [hBC, integral_add hiB hiC] at hweak
  simp only [setIntegral_univ]
  have hAeq : (fun x => (η x * u x) * laplacianN φ x) = A := by
    funext x
    dsimp [A]
    ring
  have hReq : (fun x => (η x * f x + laplacianN η x * u x +
      2 * inner ℝ (gradient η x) (G x)) * φ x) = fun x => D x + B x + 2 * Q x := by
    funext x
    simp only [D, B, Q, X, real_inner_smul_left]
    ring
  rw [hAeq, hReq, integral_add (f := fun x => D x + B x) (g := fun x => 2 * Q x)
    (hiD.add hiB) (hiQ.const_mul 2), integral_add hiD hiB, integral_const_mul]
  linarith only [htest, hweak]

lemma poisson_lpNorm_le_of_eLpNorm_le {α E F : Type*} [MeasurableSpace α]
    [NormedAddCommGroup E] [NormedAddCommGroup F] {μ ν : Measure α}
    {g : α → E} {f : α → F} (hg : MemLp g 2 μ) (hf : MemLp f 2 ν)
    {C : ℝ} (hC : 0 ≤ C)
    (hbound : eLpNorm g 2 μ ≤ ENNReal.ofReal C * eLpNorm f 2 ν) :
    lpNorm g 2 μ ≤ C * lpNorm f 2 ν := by
  rw [← toReal_eLpNorm, ← toReal_eLpNorm]
  have hfin : ENNReal.ofReal C * eLpNorm f 2 ν ≠ ∞ :=
    ENNReal.mul_ne_top ENNReal.ofReal_ne_top hf.eLpNorm_ne_top
  simpa only [ENNReal.toReal_mul, ENNReal.toReal_ofReal hC] using
    ENNReal.toReal_mono hfin hbound

/-- Compactly supported bounded vector coefficients pair with local L² fields
into global scalar L², with the expected coefficient bound. -/
lemma poisson_memLp_inner_supported {n : ℕ}
    {U : Set (EuclideanSpace ℝ (Fin n))} (hU : MeasurableSet U)
    {G X : EuclideanSpace ℝ (Fin n) → EuclideanSpace ℝ (Fin n)}
    (hG : MemLp G 2 (volume.restrict U)) (hX : Continuous X) (hsX : tsupport X ⊆ U)
    {B : ℝ} (hB : 0 ≤ B) (hbX : ∀ x, ‖X x‖ ≤ B) :
    MemLp (fun x => inner ℝ (X x) (G x)) 2 volume ∧
      lpNorm (fun x => inner ℝ (X x) (G x)) 2 volume ≤ B * lpNorm G 2 (volume.restrict U) := by
  have hG0 := (memLp_indicator_iff_restrict hU).mpr hG
  have heq : (fun x => inner ℝ (X x) (G x)) =
      fun x => inner ℝ (X x) (U.indicator G x) := by
    funext x
    by_cases hx : x ∈ U
    · rw [indicator_of_mem hx]
    · rw [image_eq_zero_of_notMem_tsupport (fun ht => hx (hsX ht))]
      simp only [inner_zero_left]
  rw [heq]
  have hb (x : EuclideanSpace ℝ (Fin n)) :
      ‖inner ℝ (X x) (U.indicator G x)‖ ≤ B * ‖U.indicator G x‖ :=
    (norm_inner_le_norm _ _).trans
      (mul_le_mul_of_nonneg_right (hbX x) (norm_nonneg _))
  refine ⟨hG0.of_le_mul (hX.aestronglyMeasurable.inner hG0.aestronglyMeasurable)
    (Eventually.of_forall hb), ?_⟩
  have h := poisson_lpNorm_le_mul_of_norm_le hG0 hB hb
  rw [← toReal_eLpNorm (f := U.indicator G), eLpNorm_indicator_eq_eLpNorm_restrict hU,
    toReal_eLpNorm] at h
  exact h

/-- The localized Poisson source belongs to L² with an explicit cutoff bound. -/
theorem poisson_cutoff_source_memLp_and_bound {n : ℕ}
    {U : Set (EuclideanSpace ℝ (Fin n))} (hU : MeasurableSet U)
    {u f η : EuclideanSpace ℝ (Fin n) → ℝ}
    {G : EuclideanSpace ℝ (Fin n) → EuclideanSpace ℝ (Fin n)}
    (hu : MemLp u 2 (volume.restrict U)) (hf : MemLp f 2 (volume.restrict U))
    (hG : MemLp G 2 (volume.restrict U))
    (hη : ContDiff ℝ (⊤ : ℕ∞) η) (hsη : tsupport η ⊆ U)
    {A B C : ℝ} (hA : 0 ≤ A) (hB : 0 ≤ B) (hC : 0 ≤ C)
    (hbη : ∀ x, ‖η x‖ ≤ A) (hbgrad : ∀ x, ‖gradient η x‖ ≤ B)
    (hblap : ∀ x, ‖laplacianN η x‖ ≤ C) :
    MemLp (fun x => η x * f x + laplacianN η x * u x +
      2 * inner ℝ (gradient η x) (G x)) 2 volume ∧
      lpNorm (fun x => η x * f x + laplacianN η x * u x +
        2 * inner ℝ (gradient η x) (G x)) 2 volume ≤
        A * lpNorm f 2 (volume.restrict U) + C * lpNorm u 2 (volume.restrict U) +
          2 * B * lpNorm G 2 (volume.restrict U) := by
  let q₁ (x : EuclideanSpace ℝ (Fin n)) := η x * f x
  let q₂ (x : EuclideanSpace ℝ (Fin n)) := laplacianN η x * u x
  let q₃ (x : EuclideanSpace ℝ (Fin n)) := inner ℝ (gradient η x) (G x)
  have h₁ := memLp_smul_supported_scalar hU hf hη.continuous hsη hbη
  have h₂ := memLp_smul_supported_scalar hU hu
    (continuous_laplacianN (hη.of_le (by simp))) ((tsupport_laplacianN_subset η).trans hsη) hblap
  have h₃ := poisson_memLp_inner_supported hU hG
    (continuous_gradient_of_contDiff (hη.of_le (by simp)))
    ((tsupport_gradient_subset η).trans hsη) hB hbgrad
  have hm₁ : MemLp q₁ 2 volume := h₁.1
  have hm₂ : MemLp q₂ 2 volume := h₂.1
  have hm₃ : MemLp q₃ 2 volume := h₃.1
  have hb₁ : lpNorm q₁ 2 volume ≤ A * lpNorm f 2 (volume.restrict U) :=
    poisson_lpNorm_le_of_eLpNorm_le hm₁ hf hA h₁.2
  have hb₂ : lpNorm q₂ 2 volume ≤ C * lpNorm u 2 (volume.restrict U) :=
    poisson_lpNorm_le_of_eLpNorm_le hm₂ hu hC h₂.2
  refine ⟨(hm₁.add hm₂).add (hm₃.const_mul 2), ?_⟩
  have hbadd := lpNorm_add_le (hm₁.add hm₂) (g := (2 : ℝ) • q₃) (by norm_num)
  have hbadd' := lpNorm_add_le hm₁ (g := q₂) (by norm_num)
  have hsmul : lpNorm ((2 : ℝ) • q₃) 2 volume = 2 * lpNorm q₃ 2 volume := by
    rw [lpNorm_const_smul]
    norm_num
  rw [hsmul] at hbadd
  change lpNorm (q₁ + q₂ + (2 : ℝ) • q₃) 2 volume ≤ _
  have hb₃ : lpNorm q₃ 2 volume ≤ B * lpNorm G 2 (volume.restrict U) := h₃.2
  linarith only [hbadd, hbadd', hb₁, hb₂, hb₃]

end LiquidDrop

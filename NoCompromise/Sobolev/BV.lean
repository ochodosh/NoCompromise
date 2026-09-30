module

public import NoCompromise.BV.StrictApprox
public import Mathlib.MeasureTheory.Integral.MeanInequalities
public import Mathlib.Analysis.Calculus.Deriv.Pi
public import Mathlib.MeasureTheory.Integral.IntegralEqImproper
public import Mathlib.MeasureTheory.Constructions.Pi
public import Mathlib.MeasureTheory.Function.LpSeminorm.LpNorm
public import Mathlib.Analysis.MeanInequalities
public import Mathlib.MeasureTheory.Function.ConvergenceInMeasure
public import Mathlib.MeasureTheory.Function.LpSpace.Complete
public import Mathlib.MeasureTheory.Function.LpSeminorm.Indicator
public import Mathlib.MeasureTheory.VectorMeasure.Variation.SignedMeasure

@[expose] public section

/-!
# BV Sobolev inequalities

The smooth anisotropic estimates in dimensions two and three are derived from
the fundamental theorem of calculus, Tonelli, and Cauchy–Schwarz. No Sobolev
inequality is used as a premise. Strict approximation and Fatou prove the 3D BV
bound. In the plane, coordinatewise mollification estimates and compact cutoffs
prove the sharper bound involving the actual coordinate derivative measures.
-/

open MeasureTheory Filter Metric Set InnerProductSpace
open scoped NNReal ENNReal Topology Gradient Pointwise Convolution
namespace LiquidDrop
set_option maxSynthPendingDepth 8


/-- Three successive applications of Cauchy–Schwarz to functions each missing
one coordinate. This is the integral estimate used in the smooth 3D Sobolev proof. -/
theorem coordinate_lintegral_three {X Y Z : Type*}
    [MeasurableSpace X] [MeasurableSpace Y] [MeasurableSpace Z]
    {μ : Measure X} {ν : Measure Y} {ρ : Measure Z} [SFinite ν] [SFinite ρ]
    (A : Y → Z → ℝ≥0∞) (B : X → Z → ℝ≥0∞) (C : X → Y → ℝ≥0∞)
    (hA : Measurable (Function.uncurry A)) (hB : Measurable (Function.uncurry B))
    (hC : Measurable (Function.uncurry C)) :
    (∫⁻ x, ∫⁻ y, ∫⁻ z, A y z ^ (1 / 2 : ℝ) * B x z ^ (1 / 2 : ℝ) *
      C x y ^ (1 / 2 : ℝ) ∂ρ ∂ν ∂μ) ≤
      (∫⁻ y, ∫⁻ z, A y z ∂ρ ∂ν) ^ (1 / 2 : ℝ) *
      (∫⁻ x, ∫⁻ z, B x z ∂ρ ∂μ) ^ (1 / 2 : ℝ) *
      (∫⁻ x, ∫⁻ y, C x y ∂ν ∂μ) ^ (1 / 2 : ℝ) := by
  have hAs (y) : Measurable (A y) := hA.comp (measurable_const.prodMk measurable_id)
  have hBs (x) : Measurable (B x) := hB.comp (measurable_const.prodMk measurable_id)
  have hCs (x) : Measurable (C x) := hC.comp (measurable_const.prodMk measurable_id)
  have hAm : Measurable (fun y => ∫⁻ z, A y z ∂ρ) := hA.lintegral_prod_right
  have hBm : Measurable (fun x => ∫⁻ z, B x z ∂ρ) := hB.lintegral_prod_right
  have hz (x y) :
      (∫⁻ z, A y z ^ (1 / 2 : ℝ) * B x z ^ (1 / 2 : ℝ) * C x y ^ (1 / 2 : ℝ) ∂ρ) ≤
        (∫⁻ z, A y z ∂ρ) ^ (1 / 2 : ℝ) * (∫⁻ z, B x z ∂ρ) ^ (1 / 2 : ℝ) *
          C x y ^ (1 / 2 : ℝ) := by
    rw [lintegral_mul_const (f := fun z => A y z ^ (1 / 2 : ℝ) * B x z ^ (1 / 2 : ℝ))
      _ (((hAs y).pow_const _).mul ((hBs x).pow_const _))]
    exact mul_le_mul' (ENNReal.lintegral_mul_norm_pow_le (hAs y).aemeasurable
      (hBs x).aemeasurable (by norm_num) (by norm_num) (by norm_num)) le_rfl
  have hy (x) :
      (∫⁻ y, (∫⁻ z, A y z ∂ρ) ^ (1 / 2 : ℝ) * (∫⁻ z, B x z ∂ρ) ^ (1 / 2 : ℝ) *
        C x y ^ (1 / 2 : ℝ) ∂ν) ≤
      (∫⁻ y, ∫⁻ z, A y z ∂ρ ∂ν) ^ (1 / 2 : ℝ) *
        ((∫⁻ z, B x z ∂ρ) ^ (1 / 2 : ℝ) * (∫⁻ y, C x y ∂ν) ^ (1 / 2 : ℝ)) := by
    calc
      _ = (∫⁻ y, (∫⁻ z, A y z ∂ρ) ^ (1 / 2 : ℝ) * C x y ^ (1 / 2 : ℝ) ∂ν) *
          (∫⁻ z, B x z ∂ρ) ^ (1 / 2 : ℝ) := by
        rw [← lintegral_mul_const (f := fun y =>
          (∫⁻ z, A y z ∂ρ) ^ (1 / 2 : ℝ) * C x y ^ (1 / 2 : ℝ))
          _ ((hAm.pow_const _).mul ((hCs x).pow_const _))]
        apply lintegral_congr
        intro y
        ring
      _ ≤ ((∫⁻ y, ∫⁻ z, A y z ∂ρ ∂ν) ^ (1 / 2 : ℝ) *
          (∫⁻ y, C x y ∂ν) ^ (1 / 2 : ℝ)) * (∫⁻ z, B x z ∂ρ) ^ (1 / 2 : ℝ) :=
        mul_le_mul' (ENNReal.lintegral_mul_norm_pow_le hAm.aemeasurable
          (hCs x).aemeasurable (by norm_num) (by norm_num) (by norm_num)) le_rfl
      _ = _ := by ring
  calc
    _ ≤ ∫⁻ x, ∫⁻ y, (∫⁻ z, A y z ∂ρ) ^ (1 / 2 : ℝ) *
        (∫⁻ z, B x z ∂ρ) ^ (1 / 2 : ℝ) * C x y ^ (1 / 2 : ℝ) ∂ν ∂μ :=
      lintegral_mono fun x => lintegral_mono fun y => hz x y
    _ ≤ ∫⁻ x, (∫⁻ y, ∫⁻ z, A y z ∂ρ ∂ν) ^ (1 / 2 : ℝ) *
        ((∫⁻ z, B x z ∂ρ) ^ (1 / 2 : ℝ) * (∫⁻ y, C x y ∂ν) ^ (1 / 2 : ℝ)) ∂μ :=
      lintegral_mono hy
    _ ≤ _ := by
      rw [lintegral_const_mul (f := fun x => (∫⁻ z, B x z ∂ρ) ^ (1 / 2 : ℝ) *
        (∫⁻ y, C x y ∂ν) ^ (1 / 2 : ℝ))
        _ ((hBm.pow_const _).mul ((hC.lintegral_prod_right).pow_const _))]
      exact (mul_le_mul' le_rfl (ENNReal.lintegral_mul_norm_pow_le hBm.aemeasurable
        (hC.lintegral_prod_right).aemeasurable (by norm_num) (by norm_num) (by norm_num))).trans_eq
          (mul_assoc _ _ _).symm


/-- The derivative in a standard Euclidean coordinate direction. -/
noncomputable def coordinateDerivative {n : ℕ} (f : EuclideanSpace ℝ (Fin n) → ℝ)
    (i : Fin n) (x : EuclideanSpace ℝ (Fin n)) : ℝ :=
  fderiv ℝ f x (PiLp.single 2 i 1)

lemma continuous_coordinateDerivative {n : ℕ} {f : EuclideanSpace ℝ (Fin n) → ℝ}
    (hf : ContDiff ℝ 1 f) (i : Fin n) : Continuous (coordinateDerivative f i) :=
  (hf.continuous_fderiv one_ne_zero).clm_apply continuous_const

lemma hasCompactSupport_coordinateDerivative {n : ℕ} {f : EuclideanSpace ℝ (Fin n) → ℝ}
    (hf : HasCompactSupport f) (i : Fin n) : HasCompactSupport (coordinateDerivative f i) :=
  hf.fderiv_apply ℝ (PiLp.single 2 i 1)


/-- The fundamental theorem of calculus on a full coordinate line. -/
theorem enorm_le_lintegral_coordinateDerivative {n : ℕ}
    {f : EuclideanSpace ℝ (Fin n) → ℝ} (hf : ContDiff ℝ 1 f) (hc : HasCompactSupport f)
    (i : Fin n) (x : EuclideanSpace ℝ (Fin n)) :
    ‖f x‖ₑ ≤ ∫⁻ t : ℝ, ‖coordinateDerivative f i (x + (t - x i) • PiLp.single 2 i 1)‖ₑ := by
  let e : EuclideanSpace ℝ (Fin n) := PiLp.single 2 i 1
  let γ (t : ℝ) := x + (t - x i) • e
  have hγ : ContDiff ℝ 1 γ :=
    contDiff_const.add ((contDiff_id.sub contDiff_const).smul contDiff_const)
  have hγiso : Isometry γ := Isometry.of_dist_eq fun s t => by
    rw [dist_eq_norm, dist_eq_norm]
    have heq : γ s - γ t = (s - t) • e := by dsimp [γ]; module
    rw [heq, norm_smul]
    simp [e, PiLp.norm_single]
  have hcf : HasCompactSupport (f ∘ γ) := hc.comp_isClosedEmbedding hγiso.isClosedEmbedding
  have hd (t : ℝ) : deriv (f ∘ γ) t = coordinateDerivative f i (γ t) := by
    have ht : HasDerivAt γ e t := by
      simpa only [one_smul, id_eq, γ] using
        (((hasDerivAt_id t).sub_const (x i)).smul_const e).const_add x
    exact ((hf.differentiable one_ne_zero).differentiableAt.hasFDerivAt.comp_hasDerivAt t ht).deriv
  calc
    _ = ‖(f ∘ γ) (x i)‖ₑ := by simp [γ]
    _ ≤ ∫⁻ t in Iic (x i), ‖deriv (f ∘ γ) t‖ₑ :=
      HasCompactSupport.enorm_le_lintegral_Ici_deriv (hf.comp hγ) hcf _
    _ ≤ ∫⁻ t, ‖deriv (f ∘ γ) t‖ₑ := lintegral_mono' Measure.restrict_le_self le_rfl
    _ = _ := by simp only [hd, γ, e]


/-- The coordinate identification between a triple product and Euclidean three-space. -/
noncomputable def triplePointEquiv : (ℝ × (ℝ × ℝ)) ≃L[ℝ] EuclideanSpace ℝ (Fin 3) :=
  LinearEquiv.toContinuousLinearEquiv
    { toFun := fun p => WithLp.toLp 2 ![p.1, p.2.1, p.2.2]
      invFun := fun x => (x 0, x 1, x 2)
      left_inv := by intro p; rcases p with ⟨x, y, z⟩; rfl
      right_inv := by intro x; apply PiLp.ext; intro i; fin_cases i <;> rfl
      map_add' := by intro p q; apply PiLp.ext; intro i; fin_cases i <;> rfl
      map_smul' := by intro r p; apply PiLp.ext; intro i; fin_cases i <;> rfl }

lemma triplePointEquiv_apply (x y z : ℝ) :
    triplePointEquiv (x, y, z) = WithLp.toLp 2 ![x, y, z] := rfl

lemma triplePointEquiv_symm_apply (x : EuclideanSpace ℝ (Fin 3)) :
    triplePointEquiv.symm x = (x 0, x 1, x 2) := rfl

lemma measurePreserving_triplePointEquiv_symm : MeasurePreserving triplePointEquiv.symm := by
  have h := ((MeasurePreserving.id (volume : Measure ℝ)).prod
    (volume_preserving_finTwoArrow ℝ)).comp
      ((volume_preserving_piFinSuccAbove (fun _ : Fin 3 => ℝ) 0).comp
        (PiLp.volume_preserving_ofLp (Fin 3)))
  convert h using 1 <;> rfl

lemma measurePreserving_triplePointEquiv : MeasurePreserving triplePointEquiv := by
  exact MeasurePreserving.symm triplePointEquiv.symm.toHomeomorph.toMeasurableEquiv
    measurePreserving_triplePointEquiv_symm

lemma lintegral_euclidean_three (F : EuclideanSpace ℝ (Fin 3) → ℝ≥0∞)
    (hF : Measurable F) :
    (∫⁻ p, F p) = ∫⁻ x : ℝ, ∫⁻ y : ℝ, ∫⁻ z : ℝ, F (triplePointEquiv (x, y, z)) := by
  calc
    _ = ∫⁻ p : ℝ × (ℝ × ℝ), F (triplePointEquiv p) :=
      (measurePreserving_triplePointEquiv.lintegral_comp hF).symm
    _ = ∫⁻ x : ℝ, ∫⁻ p : ℝ × ℝ, F (triplePointEquiv (x, p)) :=
      lintegral_prod _ (hF.comp triplePointEquiv.continuous.measurable).aemeasurable
    _ = _ := by
      apply lintegral_congr
      intro x
      exact lintegral_prod _ ((hF.comp triplePointEquiv.continuous.measurable).comp
        (measurable_const.prodMk measurable_id)).aemeasurable


lemma triplePointEquiv_replace_zero (x y z t : ℝ) :
    triplePointEquiv (x, y, z) + (t - (triplePointEquiv (x, y, z)) 0) •
      PiLp.single 2 (0 : Fin 3) 1 = triplePointEquiv (t, y, z) := by
  apply PiLp.ext
  intro i
  fin_cases i <;> simp [triplePointEquiv_apply]

lemma triplePointEquiv_replace_one (x y z t : ℝ) :
    triplePointEquiv (x, y, z) + (t - (triplePointEquiv (x, y, z)) 1) •
      PiLp.single 2 (1 : Fin 3) 1 = triplePointEquiv (x, t, z) := by
  apply PiLp.ext
  intro i
  fin_cases i <;> simp [triplePointEquiv_apply]

lemma triplePointEquiv_replace_two (x y z t : ℝ) :
    triplePointEquiv (x, y, z) + (t - (triplePointEquiv (x, y, z)) 2) •
      PiLp.single 2 (2 : Fin 3) 1 = triplePointEquiv (x, y, t) := by
  apply PiLp.ext
  intro i
  fin_cases i <;> simp [triplePointEquiv_apply]

lemma lintegral_three_cycle (F : ℝ → ℝ → ℝ → ℝ≥0∞)
    (hF : Measurable (fun p : ℝ × (ℝ × ℝ) => F p.1 p.2.1 p.2.2)) :
    (∫⁻ y, ∫⁻ z, ∫⁻ x, F x y z) = ∫⁻ x, ∫⁻ y, ∫⁻ z, F x y z := by
  have hswap : Measurable (fun p : (ℝ × ℝ) × ℝ => F p.2 p.1.1 p.1.2) :=
    hF.comp measurable_swap
  calc
    _ = ∫⁻ p : ℝ × ℝ, ∫⁻ x, F x p.1 p.2 :=
      (lintegral_prod _ hswap.lintegral_prod_right.aemeasurable).symm
    _ = ∫⁻ x, ∫⁻ p : ℝ × ℝ, F x p.1 p.2 := lintegral_lintegral_swap hswap.aemeasurable
    _ = _ := by
      apply lintegral_congr
      intro x
      exact lintegral_prod _ (hF.comp (measurable_const.prodMk measurable_id)).aemeasurable

lemma lintegral_three_swap_last (F : ℝ → ℝ → ℝ → ℝ≥0∞)
    (hF : Measurable (fun p : ℝ × (ℝ × ℝ) => F p.1 p.2.1 p.2.2)) :
    (∫⁻ x, ∫⁻ z, ∫⁻ y, F x y z) = ∫⁻ x, ∫⁻ y, ∫⁻ z, F x y z := by
  apply lintegral_congr
  intro x
  exact lintegral_lintegral_swap
    ((hF.comp (measurable_const.prodMk measurable_id)).comp measurable_swap).aemeasurable

/-- The anisotropic integral form of the smooth three-dimensional Sobolev inequality. -/
theorem smooth_gn_three_lintegral {f : EuclideanSpace ℝ (Fin 3) → ℝ}
    (hf : ContDiff ℝ 1 f) (hc : HasCompactSupport f) :
    (∫⁻ x, ‖f x‖ₑ ^ (3 / 2 : ℝ)) ≤
      (∫⁻ x, ‖coordinateDerivative f 0 x‖ₑ) ^ (1 / 2 : ℝ) *
      (∫⁻ x, ‖coordinateDerivative f 1 x‖ₑ) ^ (1 / 2 : ℝ) *
      (∫⁻ x, ‖coordinateDerivative f 2 x‖ₑ) ^ (1 / 2 : ℝ) := by
  let D (i : Fin 3) (x y z : ℝ) := ‖coordinateDerivative f i (triplePointEquiv (x, y, z))‖ₑ
  have hD (i : Fin 3) : Measurable (fun p : ℝ × (ℝ × ℝ) => D i p.1 p.2.1 p.2.2) :=
    ((continuous_coordinateDerivative hf i).comp triplePointEquiv.continuous).enorm.measurable
  let A (y z : ℝ) := ∫⁻ x, D 0 x y z
  let B (x z : ℝ) := ∫⁻ y, D 1 x y z
  let C (x y : ℝ) := ∫⁻ z, D 2 x y z
  have hA : Measurable (Function.uncurry A) :=
    ((hD 0).comp measurable_swap).lintegral_prod_right'
  have hB : Measurable (Function.uncurry B) :=
    ((hD 1).comp (measurable_fst.fst.prodMk
      (measurable_snd.prodMk measurable_fst.snd))).lintegral_prod_right'
  have hC : Measurable (Function.uncurry C) :=
    ((hD 2).comp (measurable_fst.fst.prodMk
      (measurable_fst.snd.prodMk measurable_snd))).lintegral_prod_right'
  have h0 (x y z) : ‖f (triplePointEquiv (x, y, z))‖ₑ ≤ A y z := by
    simpa only [triplePointEquiv_replace_zero] using
      enorm_le_lintegral_coordinateDerivative hf hc 0 (triplePointEquiv (x, y, z))
  have h1 (x y z) : ‖f (triplePointEquiv (x, y, z))‖ₑ ≤ B x z := by
    simpa only [triplePointEquiv_replace_one] using
      enorm_le_lintegral_coordinateDerivative hf hc 1 (triplePointEquiv (x, y, z))
  have h2 (x y z) : ‖f (triplePointEquiv (x, y, z))‖ₑ ≤ C x y := by
    simpa only [triplePointEquiv_replace_two] using
      enorm_le_lintegral_coordinateDerivative hf hc 2 (triplePointEquiv (x, y, z))
  have hpoint (x y z : ℝ) : ‖f (triplePointEquiv (x, y, z))‖ₑ ^ (3 / 2 : ℝ) ≤
      A y z ^ (1 / 2 : ℝ) * B x z ^ (1 / 2 : ℝ) * C x y ^ (1 / 2 : ℝ) := by
    have he (a : ℝ≥0∞) : a ^ (3 / 2 : ℝ) =
        a ^ (1 / 2 : ℝ) * a ^ (1 / 2 : ℝ) * a ^ (1 / 2 : ℝ) := by
      rw [← ENNReal.rpow_add_of_nonneg _ _ (by norm_num) (by norm_num),
        ← ENNReal.rpow_add_of_nonneg _ _ (by norm_num) (by norm_num)]
      norm_num
    rw [he]
    exact mul_le_mul' (mul_le_mul' (ENNReal.rpow_le_rpow (h0 x y z) (by norm_num))
      (ENNReal.rpow_le_rpow (h1 x y z) (by norm_num)))
      (ENNReal.rpow_le_rpow (h2 x y z) (by norm_num))
  have hmarg (i : Fin 3) : (∫⁻ x, ∫⁻ y, ∫⁻ z, D i x y z) =
      ∫⁻ p, ‖coordinateDerivative f i p‖ₑ :=
    (lintegral_euclidean_three _ (continuous_coordinateDerivative hf i).enorm.measurable).symm
  calc
    _ = ∫⁻ x, ∫⁻ y, ∫⁻ z, ‖f (triplePointEquiv (x, y, z))‖ₑ ^ (3 / 2 : ℝ) :=
      lintegral_euclidean_three _ (hf.continuous.enorm.measurable.pow_const _)
    _ ≤ ∫⁻ x, ∫⁻ y, ∫⁻ z,
        A y z ^ (1 / 2 : ℝ) * B x z ^ (1 / 2 : ℝ) * C x y ^ (1 / 2 : ℝ) :=
      lintegral_mono fun x => lintegral_mono fun y => lintegral_mono fun z => hpoint x y z
    _ ≤ (∫⁻ y, ∫⁻ z, A y z) ^ (1 / 2 : ℝ) * (∫⁻ x, ∫⁻ z, B x z) ^ (1 / 2 : ℝ) *
        (∫⁻ x, ∫⁻ y, C x y) ^ (1 / 2 : ℝ) := coordinate_lintegral_three A B C hA hB hC
    _ = _ := by
      change (∫⁻ y, ∫⁻ z, ∫⁻ x, D 0 x y z) ^ (1 / 2 : ℝ) *
        (∫⁻ x, ∫⁻ z, ∫⁻ y, D 1 x y z) ^ (1 / 2 : ℝ) *
        (∫⁻ x, ∫⁻ y, ∫⁻ z, D 2 x y z) ^ (1 / 2 : ℝ) = _
      rw [lintegral_three_cycle _ (hD 0), lintegral_three_swap_last _ (hD 1), hmarg, hmarg, hmarg]

/-- The smooth 3D anisotropic Sobolev bound with constant one, in extended norms. -/
theorem smooth_gn_three_eLpNorm {f : EuclideanSpace ℝ (Fin 3) → ℝ}
    (hf : ContDiff ℝ 1 f) (hc : HasCompactSupport f) :
    eLpNorm f (3 / 2) volume ≤
      (eLpNorm (coordinateDerivative f 0) 1 volume) ^ (1 / 3 : ℝ) *
      (eLpNorm (coordinateDerivative f 1) 1 volume) ^ (1 / 3 : ℝ) *
      (eLpNorm (coordinateDerivative f 2) 1 volume) ^ (1 / 3 : ℝ) := by
  have hr := ENNReal.rpow_le_rpow (smooth_gn_three_lintegral hf hc)
    (by norm_num : (0 : ℝ) ≤ 2 / 3)
  rw [ENNReal.mul_rpow_of_nonneg _ _ (by norm_num : (0 : ℝ) ≤ 2 / 3),
    ENNReal.mul_rpow_of_nonneg _ _ (by norm_num : (0 : ℝ) ≤ 2 / 3)] at hr
  simp only [← ENNReal.rpow_mul] at hr
  norm_num only at hr
  rw [eLpNorm_eq_lintegral_rpow_enorm_toReal (by norm_num : (3 / 2 : ℝ≥0∞) ≠ 0)
    (by finiteness : (3 / 2 : ℝ≥0∞) ≠ ∞) hf.continuous.aestronglyMeasurable]
  norm_num only [ENNReal.toReal_div, ENNReal.toReal_ofNat]
  simpa only [eLpNorm_one_eq_lintegral_enorm
    (continuous_coordinateDerivative hf _).aestronglyMeasurable] using hr

/-- Blueprint `lem:GN-smooth`, with C = 1. -/
theorem smooth_gagliardo_nirenberg_three {f : EuclideanSpace ℝ (Fin 3) → ℝ}
    (hf : ContDiff ℝ 1 f) (hc : HasCompactSupport f) :
    lpNorm f (3 / 2) volume ≤
        (lpNorm (coordinateDerivative f 0) 1 volume) ^ (1 / 3 : ℝ) *
        (lpNorm (coordinateDerivative f 1) 1 volume) ^ (1 / 3 : ℝ) *
        (lpNorm (coordinateDerivative f 2) 1 volume) ^ (1 / 3 : ℝ) ∧
      (lpNorm (coordinateDerivative f 0) 1 volume) ^ (1 / 3 : ℝ) *
        (lpNorm (coordinateDerivative f 1) 1 volume) ^ (1 / 3 : ℝ) *
        (lpNorm (coordinateDerivative f 2) 1 volume) ^ (1 / 3 : ℝ) ≤
      (1 / 3 : ℝ) * (lpNorm (coordinateDerivative f 0) 1 volume +
        lpNorm (coordinateDerivative f 1) 1 volume +
        lpNorm (coordinateDerivative f 2) 1 volume) := by
  have hi (i : Fin 3) : Integrable (coordinateDerivative f i) :=
    (continuous_coordinateDerivative hf i).integrable_of_hasCompactSupport
      (hasCompactSupport_coordinateDerivative hc i)
  have hfin (i : Fin 3) : eLpNorm (coordinateDerivative f i) 1 volume < ∞ :=
    ((memLp_one_iff_integrable).mpr (hi i)).eLpNorm_lt_top
  constructor
  · have ht : (eLpNorm (coordinateDerivative f 0) 1 volume) ^ (1 / 3 : ℝ) *
        (eLpNorm (coordinateDerivative f 1) 1 volume) ^ (1 / 3 : ℝ) *
        (eLpNorm (coordinateDerivative f 2) 1 volume) ^ (1 / 3 : ℝ) < ∞ :=
      ENNReal.mul_lt_top (ENNReal.mul_lt_top
        (ENNReal.rpow_lt_top_of_nonneg (by norm_num) (hfin 0).ne)
        (ENNReal.rpow_lt_top_of_nonneg (by norm_num) (hfin 1).ne))
        (ENNReal.rpow_lt_top_of_nonneg (by norm_num) (hfin 2).ne)
    have hr := ENNReal.toReal_mono ht.ne (smooth_gn_three_eLpNorm hf hc)
    simpa only [ENNReal.toReal_mul, ← ENNReal.toReal_rpow, toReal_eLpNorm] using hr
  · have h := Real.geom_mean_le_arith_mean3_weighted
      (by norm_num : (0 : ℝ) ≤ 1 / 3) (by norm_num : (0 : ℝ) ≤ 1 / 3)
      (by norm_num : (0 : ℝ) ≤ 1 / 3)
      (lpNorm_nonneg (f := coordinateDerivative f 0) (p := 1) (μ := volume))
      (lpNorm_nonneg (f := coordinateDerivative f 1) (p := 1) (μ := volume))
      (lpNorm_nonneg (f := coordinateDerivative f 2) (p := 1) (μ := volume)) (by norm_num)
    convert h using 1; ring

lemma coordinateDerivative_eq_gradient_apply {n : ℕ}
    (f : EuclideanSpace ℝ (Fin n) → ℝ) (i : Fin n) (x : EuclideanSpace ℝ (Fin n)) :
    coordinateDerivative f i x = gradient f x i := by
  exact (gradient_apply_eq_fderiv_single f x i).symm

/-- The isotropic smooth Sobolev estimate, with constant one. -/
theorem smooth_sobolev_three {f : EuclideanSpace ℝ (Fin 3) → ℝ}
    (hf : ContDiff ℝ 1 f) (hc : HasCompactSupport f) :
    eLpNorm f (3 / 2) volume ≤ ∫⁻ x, ‖gradient f x‖ₑ := by
  have hb (i : Fin 3) : eLpNorm (coordinateDerivative f i) 1 volume ≤
      ∫⁻ x, ‖gradient f x‖ₑ := by
    rw [eLpNorm_one_eq_lintegral_enorm (continuous_coordinateDerivative hf i).aestronglyMeasurable]
    apply lintegral_mono
    intro x
    change ‖coordinateDerivative f i x‖ₑ ≤ ‖gradient f x‖ₑ
    rw [coordinateDerivative_eq_gradient_apply]
    exact PiLp.enorm_apply_le _ _
  calc
    _ ≤ _ := smooth_gn_three_eLpNorm hf hc
    _ ≤ (∫⁻ x, ‖gradient f x‖ₑ) ^ (1 / 3 : ℝ) *
        (∫⁻ x, ‖gradient f x‖ₑ) ^ (1 / 3 : ℝ) *
        (∫⁻ x, ‖gradient f x‖ₑ) ^ (1 / 3 : ℝ) :=
      mul_le_mul' (mul_le_mul' (ENNReal.rpow_le_rpow (hb 0) (by norm_num))
        (ENNReal.rpow_le_rpow (hb 1) (by norm_num)))
        (ENNReal.rpow_le_rpow (hb 2) (by norm_num))
    _ = _ := by
      rw [← ENNReal.rpow_add_of_nonneg _ _ (by norm_num) (by norm_num),
        ← ENNReal.rpow_add_of_nonneg _ _ (by norm_num) (by norm_num)]
      norm_num

/-- Blueprint `thm:bv-sobolev`: the extended L³ᐟ² norm is bounded by total variation. -/
theorem bv_sobolev_three {f : EuclideanSpace ℝ (Fin 3) → ℝ}
    (hf : IsBVOn f univ) : eLpNorm f (3 / 2) volume ≤ variation f univ := by
  obtain ⟨g, hg, hL1, hgrad⟩ := strict_approximation_univ hf
  have hif : Integrable f := integrableOn_univ.mp hf.1
  have hL1' : Tendsto (fun j => eLpNorm (g j - f) 1 volume) atTop (𝓝 0) := by
    have he := ENNReal.continuous_ofReal.continuousAt.tendsto.comp hL1
    simp only [ENNReal.ofReal_zero] at he
    convert he using 1
    ext j
    rw [eLpNorm_one_eq_lintegral_enorm ((hg j).2.2.1.sub hif).1,
      ← ofReal_integral_norm_eq_lintegral_enorm ((hg j).2.2.1.sub hif)]
    rfl
  obtain ⟨σ, hσ, hae⟩ := (tendstoInMeasure_of_tendsto_eLpNorm one_ne_zero
    hL1').exists_seq_tendsto_ae
  have hfatou := Lp.eLpNorm_lim_le_liminf_eLpNorm
    (fun j => (hg (σ j)).2.2.1.1) f hif.1 hae (p := (3 / 2 : ℝ≥0∞))
  have hb (j) : eLpNorm (g (σ j)) (3 / 2) volume ≤
      ENNReal.ofReal (∫ x, ‖gradient (g (σ j)) x‖) := by
    rw [ofReal_integral_norm_eq_lintegral_enorm (hg (σ j)).2.2.2]
    exact smooth_sobolev_three ((hg (σ j)).1.of_le (by simp)) (hg (σ j)).2.1
  have hlim : Tendsto (fun j => ENNReal.ofReal (∫ x, ‖gradient (g (σ j)) x‖)) atTop
      (𝓝 (variation f univ)) := by
    have he := ENNReal.continuous_ofReal.continuousAt.tendsto.comp (hgrad.comp hσ.tendsto_atTop)
    simpa only [ENNReal.ofReal_toReal hf.2.ne, Function.comp_def] using he
  exact hfatou.trans ((liminf_le_liminf (Eventually.of_forall hb)).trans_eq hlim.liminf_eq)

/-- Global BV functions in three dimensions belong to L³ᐟ², with the ordinary norm bound. -/
theorem memLp_and_bv_sobolev_three {f : EuclideanSpace ℝ (Fin 3) → ℝ}
    (hf : IsBVOn f univ) :
    MemLp f (3 / 2) volume ∧ lpNorm f (3 / 2) volume ≤ (variation f univ).toReal := by
  have hb := bv_sobolev_three hf
  refine ⟨hb.trans_lt hf.2, ?_⟩
  simpa only [toReal_eLpNorm] using ENNReal.toReal_mono hf.2.ne hb

/-- The finite-volume, finite-perimeter consequence of blueprint `thm:bv-sobolev`.
Lebesgue measurability suffices; no boundedness assumption is needed. -/
theorem volume_rpow_two_thirds_le_perimeterN {E : Set (EuclideanSpace ℝ (Fin 3))}
    (hE : NullMeasurableSet E volume) (hvol : volume E < ∞) (hper : HasFinitePerimeter E) :
    volume E ^ (2 / 3 : ℝ) ≤ perimeterN E := by
  have hi : Integrable (E.indicator (fun _ => (1 : ℝ))) :=
    (integrableOn_const hvol.ne).integrable_indicator₀ hE
  have hb := bv_sobolev_three ⟨hi.integrableOn, hper⟩
  rw [eLpNorm_indicator_const₀ hE (by norm_num : (3 / 2 : ℝ≥0∞) ≠ 0)
    (by finiteness : (3 / 2 : ℝ≥0∞) ≠ ∞)] at hb
  norm_num only [enorm_one, one_mul, ENNReal.toReal_div, ENNReal.toReal_ofNat] at hb
  exact hb

/-- The same estimate for the unchanged showcase perimeter. -/
theorem volume_rpow_two_thirds_le_perimeter {E : Set AmbientSpace}
    (hE : NullMeasurableSet E volume) (hvol : volume E < ∞) (hper : perimeter E < ∞) :
    volume E ^ (2 / 3 : ℝ) ≤ perimeter E := by
  have heq := perimeterN_eq_perimeter E hE
  rw [← heq] at hper ⊢
  exact volume_rpow_two_thirds_le_perimeterN hE hvol hper


/-! ## Planar smooth Sobolev inequalities -/

noncomputable def pairPointEquiv : (ℝ × ℝ) ≃L[ℝ] EuclideanSpace ℝ (Fin 2) :=
  LinearEquiv.toContinuousLinearEquiv
    { toFun := fun p => WithLp.toLp 2 ![p.1, p.2]
      invFun := fun x => (x 0, x 1)
      left_inv := by intro p; rcases p with ⟨x, y⟩; rfl
      right_inv := by intro x; apply PiLp.ext; intro i; fin_cases i <;> rfl
      map_add' := by intro p q; apply PiLp.ext; intro i; fin_cases i <;> rfl
      map_smul' := by intro r p; apply PiLp.ext; intro i; fin_cases i <;> rfl }

lemma pairPointEquiv_apply (x y : ℝ) :
    pairPointEquiv (x, y) = WithLp.toLp 2 ![x, y] := rfl

lemma measurePreserving_pairPointEquiv_symm : MeasurePreserving pairPointEquiv.symm := by
  have h := (volume_preserving_finTwoArrow ℝ).comp (PiLp.volume_preserving_ofLp (Fin 2))
  convert h using 1 <;> rfl

lemma measurePreserving_pairPointEquiv : MeasurePreserving pairPointEquiv :=
  MeasurePreserving.symm pairPointEquiv.symm.toHomeomorph.toMeasurableEquiv
    measurePreserving_pairPointEquiv_symm

lemma lintegral_euclidean_two (F : EuclideanSpace ℝ (Fin 2) → ℝ≥0∞)
    (hF : Measurable F) :
    (∫⁻ p, F p) = ∫⁻ x : ℝ, ∫⁻ y : ℝ, F (pairPointEquiv (x, y)) := by
  calc
    _ = ∫⁻ p : ℝ × ℝ, F (pairPointEquiv p) :=
      (measurePreserving_pairPointEquiv.lintegral_comp hF).symm
    _ = _ := lintegral_prod _ (hF.comp pairPointEquiv.continuous.measurable).aemeasurable

lemma pairPointEquiv_replace_zero (x y t : ℝ) :
    pairPointEquiv (x, y) + (t - (pairPointEquiv (x, y)) 0) •
      PiLp.single 2 (0 : Fin 2) 1 = pairPointEquiv (t, y) := by
  apply PiLp.ext
  intro i
  fin_cases i <;> simp [pairPointEquiv_apply]

lemma pairPointEquiv_replace_one (x y t : ℝ) :
    pairPointEquiv (x, y) + (t - (pairPointEquiv (x, y)) 1) •
      PiLp.single 2 (1 : Fin 2) 1 = pairPointEquiv (x, t) := by
  apply PiLp.ext
  intro i
  fin_cases i <;> simp [pairPointEquiv_apply]

/-- The smooth planar coordinate-product inequality. -/
theorem smooth_planar_sobolev_sq {f : EuclideanSpace ℝ (Fin 2) → ℝ}
    (hf : ContDiff ℝ 1 f) (hc : HasCompactSupport f) :
    eLpNorm f 2 volume ^ 2 ≤ eLpNorm (coordinateDerivative f 0) 1 volume *
      eLpNorm (coordinateDerivative f 1) 1 volume := by
  let D (i : Fin 2) (x y : ℝ) := ‖coordinateDerivative f i (pairPointEquiv (x, y))‖ₑ
  have hD (i) : Measurable (Function.uncurry (D i)) :=
    (continuous_coordinateDerivative hf i).enorm.measurable.comp
      pairPointEquiv.continuous.measurable
  let A (y : ℝ) := ∫⁻ x, D 0 x y
  let B (x : ℝ) := ∫⁻ y, D 1 x y
  have hA : Measurable A := (hD 0).lintegral_prod_left
  have hB : Measurable B := (hD 1).lintegral_prod_right
  have hpoint (x y : ℝ) : ‖f (pairPointEquiv (x, y))‖ₑ ^ 2 ≤ A y * B x := by
    have h0 : ‖f (pairPointEquiv (x, y))‖ₑ ≤ A y := by
      simpa only [pairPointEquiv_replace_zero] using
        enorm_le_lintegral_coordinateDerivative hf hc (0 : Fin 2) (pairPointEquiv (x, y))
    have h1 : ‖f (pairPointEquiv (x, y))‖ₑ ≤ B x := by
      simpa only [pairPointEquiv_replace_one] using
        enorm_le_lintegral_coordinateDerivative hf hc (1 : Fin 2) (pairPointEquiv (x, y))
    simpa only [pow_two] using mul_le_mul' h0 h1
  have hsq : eLpNorm f 2 volume ^ 2 = ∫⁻ x, ‖f x‖ₑ ^ 2 := by
    simpa only [ENNReal.coe_ofNat, NNReal.coe_ofNat, ENNReal.rpow_two] using
      eLpNorm_nnreal_pow_eq_lintegral (f := f) (μ := volume) (p := (2 : ℝ≥0)) (by norm_num)
        hf.continuous.aestronglyMeasurable
  rw [hsq, lintegral_euclidean_two _ (hf.continuous.enorm.measurable.pow_const 2)]
  calc
    _ ≤ ∫⁻ x, ∫⁻ y, A y * B x :=
      lintegral_mono fun x => lintegral_mono fun y => hpoint x y
    _ = (∫⁻ y, A y) * ∫⁻ x, B x := by
      simp_rw [lintegral_mul_const (f := A) _ hA]
      exact lintegral_const_mul _ hB
    _ = _ := by
      have h0 : (∫⁻ y, A y) = ∫⁻ x, ‖coordinateDerivative f 0 x‖ₑ := by
        change (∫⁻ y, ∫⁻ x, D 0 x y) = _
        rw [← lintegral_lintegral_swap (hD 0).aemeasurable]
        exact (lintegral_euclidean_two _
          (continuous_coordinateDerivative hf 0).enorm.measurable).symm
      have h1 : (∫⁻ x, B x) = ∫⁻ x, ‖coordinateDerivative f 1 x‖ₑ :=
        (lintegral_euclidean_two _ (continuous_coordinateDerivative hf 1).enorm.measurable).symm
      rw [h0, h1,
        eLpNorm_one_eq_lintegral_enorm (continuous_coordinateDerivative hf 0).aestronglyMeasurable,
        eLpNorm_one_eq_lintegral_enorm (continuous_coordinateDerivative hf 1).aestronglyMeasurable]

/-- The square-root form, suitable for taking BV limits. -/
theorem smooth_planar_sobolev_eLpNorm {f : EuclideanSpace ℝ (Fin 2) → ℝ}
    (hf : ContDiff ℝ 1 f) (hc : HasCompactSupport f) :
    eLpNorm f 2 volume ≤ eLpNorm (coordinateDerivative f 0) 1 volume ^ (1 / 2 : ℝ) *
      eLpNorm (coordinateDerivative f 1) 1 volume ^ (1 / 2 : ℝ) := by
  have h := ENNReal.rpow_le_rpow (smooth_planar_sobolev_sq hf hc)
    (by norm_num : (0 : ℝ) ≤ 1 / 2)
  rw [← ENNReal.rpow_two, ← ENNReal.rpow_mul] at h
  norm_num only at h
  simpa only [ENNReal.rpow_one,
    ENNReal.mul_rpow_of_nonneg _ _ (by norm_num : (0 : ℝ) ≤ 1 / 2)] using h

/-- Both ordinary-norm inequalities in the smooth clause of `lem:planar-sobolev-L2`. -/
theorem smooth_planar_sobolev {f : EuclideanSpace ℝ (Fin 2) → ℝ}
    (hf : ContDiff ℝ 1 f) (hc : HasCompactSupport f) :
    lpNorm f 2 volume ^ 2 ≤ lpNorm (coordinateDerivative f 0) 1 volume *
        lpNorm (coordinateDerivative f 1) 1 volume ∧
      lpNorm f 2 volume ≤ (1 / 2 : ℝ) *
        (lpNorm (coordinateDerivative f 0) 1 volume +
        lpNorm (coordinateDerivative f 1) 1 volume) := by
  have hi (i : Fin 2) : Integrable (coordinateDerivative f i) :=
    (continuous_coordinateDerivative hf i).integrable_of_hasCompactSupport
      (hasCompactSupport_coordinateDerivative hc i)
  have ht (i : Fin 2) := ((memLp_one_iff_integrable).mpr (hi i)).eLpNorm_lt_top
  have hs := ENNReal.toReal_mono (ENNReal.mul_lt_top (ht 0) (ht 1)).ne
    (smooth_planar_sobolev_sq hf hc)
  simp only [ENNReal.toReal_pow, ENNReal.toReal_mul, toReal_eLpNorm] at hs
  refine ⟨hs, ?_⟩
  have hn := lpNorm_nonneg (f := f) (p := 2) (μ := volume)
  have h0 := lpNorm_nonneg (f := coordinateDerivative f 0) (p := 1) (μ := volume)
  have h1 := lpNorm_nonneg (f := coordinateDerivative f 1) (p := 1) (μ := volume)
  nlinarith [sq_nonneg (lpNorm (coordinateDerivative f 0) 1 volume -
    lpNorm (coordinateDerivative f 1) 1 volume)]


/-! ## Coordinate derivative measures and approximation -/

/-- A coordinate of a globally integrable polar derivative density, as a genuine signed measure. -/
noncomputable def polarCoordinateDerivative {n : ℕ} {S : Type*} [MeasurableSpace S]
    (ρ : Measure S) (σ : S → EuclideanSpace ℝ (Fin n)) (i : Fin n) : SignedMeasure S :=
  ρ.withDensityᵥ (fun y => σ y i)

lemma variation_polarCoordinateDerivative {n : ℕ} {S : Type*} [MeasurableSpace S]
    {ρ : Measure S} {σ : S → EuclideanSpace ℝ (Fin n)} (hσ : Integrable σ ρ) (i : Fin n) :
    (polarCoordinateDerivative ρ σ i).variation = ρ.withDensity (fun y => ‖σ y i‖ₑ) := by
  exact Measure.variation_withDensityᵥ ((EuclideanSpace.proj (𝕜 := ℝ) i).integrable_comp hσ)

lemma variation_polarCoordinateDerivative_univ {n : ℕ} {S : Type*} [MeasurableSpace S]
    {ρ : Measure S} {σ : S → EuclideanSpace ℝ (Fin n)} (hσ : Integrable σ ρ) (i : Fin n) :
    (polarCoordinateDerivative ρ σ i).variation univ = ∫⁻ y, ‖σ y i‖ₑ ∂ρ := by
  rw [variation_polarCoordinateDerivative hσ, withDensity_apply _ MeasurableSet.univ]
  simp only [setLIntegral_univ]

lemma polarCoordinateDerivative_apply {n : ℕ} {S : Type*} [MeasurableSpace S]
    {ρ : Measure S} {σ : S → EuclideanSpace ℝ (Fin n)} (hσ : Integrable σ ρ)
    (i : Fin n) {A : Set S} (hA : MeasurableSet A) :
    polarCoordinateDerivative ρ σ i A = ∫ y in A, σ y i ∂ρ :=
  withDensityᵥ_apply ((EuclideanSpace.proj (𝕜 := ℝ) i).integrable_comp hσ) hA

/-- The exact coordinatewise L¹ mollification bound from the polar derivative measure. -/
theorem IsDistributionalPolarRepresentation.integral_coordinateDerivative_bump_convolution_le
    {n : ℕ} {f : EuclideanSpace ℝ (Fin n) → ℝ}
    {ρ : Measure (univ : Set (EuclideanSpace ℝ (Fin n)))} [IsFiniteMeasure ρ]
    {σ : ↑(univ : Set (EuclideanSpace ℝ (Fin n))) → EuclideanSpace ℝ (Fin n)}
    (hpolar : IsDistributionalPolarRepresentation f univ ρ σ)
    (hf : LocallyIntegrable f) (φ : ContDiffBump (0 : EuclideanSpace ℝ (Fin n))) (i : Fin n) :
    Integrable (coordinateDerivative (φ.normed volume ⋆[ContinuousLinearMap.lsmul ℝ ℝ] f) i) ∧
      (∫ x, ‖coordinateDerivative (φ.normed volume ⋆[ContinuousLinearMap.lsmul ℝ ℝ] f) i x‖) ≤
        ∫ y, ‖σ y i‖ ∂ρ := by
  have hiσ : Integrable σ ρ := Integrable.of_bound hpolar.measurable.aestronglyMeasurable 1
    (hpolar.norm_ae.mono fun _ hx => hx.le)
  have hi : Integrable (fun y => σ y i) ρ := (EuclideanSpace.proj (𝕜 := ℝ) i).integrable_comp hiσ
  have hgrad (x : EuclideanSpace ℝ (Fin n)) := hpolar.gradient_convolution_eq hf
    (φ.contDiff_normed (μ := volume)) φ.hasCompactSupport_normed x
  have hderiv (x) : coordinateDerivative
      (φ.normed volume ⋆[ContinuousLinearMap.lsmul ℝ ℝ] f) i x =
      ∫ y, φ.normed volume (x - y) • σ y i ∂ρ := by
    rw [coordinateDerivative_eq_gradient_apply, hgrad]
    have hk : Integrable (fun y : ↑(univ : Set (EuclideanSpace ℝ (Fin n))) =>
        φ.normed volume (x - y) • σ y) ρ :=
      hpolar.integrable_smul_compact_factor
        (φ.continuous_normed.comp (continuous_const.sub continuous_id))
        (φ.hasCompactSupport_normed.comp_homeomorph (Homeomorph.subLeft x)) (subset_univ _)
    rw [eval_integral_piLp hk.eval_piLp]
    simp only [PiLp.smul_apply]
  have hp := integrable_measure_convolution_integrand measurable_subtype_coe
    φ.integrable_normed φ.continuous_normed hi
  have hb := integral_norm_measure_convolution_le measurable_subtype_coe
    φ.integrable_normed φ.continuous_normed φ.nonneg_normed hi
  refine ⟨?_, ?_⟩
  · simpa only [← hderiv] using hp.integral_prod_left
  · simpa only [← hderiv, φ.integral_normed, one_mul] using hb


lemma integrable_coordinateDerivative_of_gradient {n : ℕ}
    {f : EuclideanSpace ℝ (Fin n) → ℝ} (hf : Integrable (gradient f)) (i : Fin n) :
    Integrable (coordinateDerivative f i) := by
  have h := (EuclideanSpace.proj (𝕜 := ℝ) i).integrable_comp hf
  change Integrable (fun x => gradient f x i) at h
  simpa only [← coordinateDerivative_eq_gradient_apply] using h

lemma integral_norm_coordinateDerivative_le_add_gradient_error {n : ℕ}
    {f g : EuclideanSpace ℝ (Fin n) → ℝ}
    (hf : Integrable (gradient f)) (hg : Integrable (gradient g)) (i : Fin n) :
    (∫ x, ‖coordinateDerivative f i x‖) ≤ (∫ x, ‖coordinateDerivative g i x‖) +
      ∫ x, ‖gradient f x - gradient g x‖ := by
  have hfi := integrable_coordinateDerivative_of_gradient hf i
  have hgi := integrable_coordinateDerivative_of_gradient hg i
  have hb := abs_integral_norm_sub_le_integral_norm_sub hfi hgi
  have hdiff : (∫ x, ‖coordinateDerivative f i x - coordinateDerivative g i x‖) ≤
      ∫ x, ‖gradient f x - gradient g x‖ := by
    apply integral_mono (hfi.sub hgi).norm (hf.sub hg).norm
    intro x
    change ‖coordinateDerivative f i x - coordinateDerivative g i x‖ ≤
      ‖gradient f x - gradient g x‖
    simpa only [coordinateDerivative_eq_gradient_apply, ← PiLp.sub_apply] using
      PiLp.norm_apply_le (gradient f x - gradient g x) i
  have hl := le_abs_self ((∫ x, ‖coordinateDerivative f i x‖) -
    ∫ x, ‖coordinateDerivative g i x‖)
  linarith

/-- Mollification followed by compact cutoffs preserves each derivative mass up to
an error tending to zero. This uses full-gradient L¹ cutoff errors, not coordinatewise
strict convergence. -/
theorem IsDistributionalPolarRepresentation.exists_smooth_compact_coordinate_approximation
    {n : ℕ} {f : EuclideanSpace ℝ (Fin n) → ℝ}
    {ρ : Measure (univ : Set (EuclideanSpace ℝ (Fin n)))} [IsFiniteMeasure ρ]
    {σ : ↑(univ : Set (EuclideanSpace ℝ (Fin n))) → EuclideanSpace ℝ (Fin n)}
    (hpolar : IsDistributionalPolarRepresentation f univ ρ σ) (hf : Integrable f) :
    ∃ g : ℕ → EuclideanSpace ℝ (Fin n) → ℝ,
      (∀ j, ContDiff ℝ (⊤ : ℕ∞) (g j) ∧ HasCompactSupport (g j) ∧ Integrable (g j) ∧
        Integrable (gradient (g j))) ∧
      Tendsto (fun j => ∫ x, ‖g j x - f x‖) atTop (𝓝 0) ∧
      ∀ j i, (∫ x, ‖coordinateDerivative (g j) i x‖) ≤
        (∫ y, ‖σ y i‖ ∂ρ) + ((j : ℝ) + 1)⁻¹ := by
  let φ (j : ℕ) : ContDiffBump (0 : EuclideanSpace ℝ (Fin n)) :=
    ⟨((j : ℝ) + 1)⁻¹ / 2, ((j : ℝ) + 1)⁻¹, by positivity,
      half_lt_self (by positivity)⟩
  have hφlim : Tendsto (fun j => (φ j).rOut) atTop (𝓝 0) := by
    simpa only [one_div] using tendsto_one_div_add_atTop_nhds_zero_nat (𝕜 := ℝ)
  let h (j : ℕ) := (φ j).normed volume ⋆[ContinuousLinearMap.lsmul ℝ ℝ] f
  have hh (j) : ContDiff ℝ (⊤ : ℕ∞) (h j) :=
    (φ j).hasCompactSupport_normed.contDiff_convolution_left _
      (φ j).contDiff_normed hf.locallyIntegrable
  have hih (j) : Integrable (h j) := (φ j).integrable_normed.integrable_convolution _ hf
  have hiσ : Integrable σ ρ := Integrable.of_bound hpolar.measurable.aestronglyMeasurable 1
    (hpolar.norm_ae.mono fun _ hx => hx.le)
  have hihg (j) : Integrable (gradient (h j)) := by
    have hprod := integrable_measure_convolution_integrand measurable_subtype_coe
      (φ j).integrable_normed (φ j).continuous_normed hiσ
    have hgrad (x) := hpolar.gradient_convolution_eq hf.locallyIntegrable
      ((φ j).contDiff_normed (μ := volume)) (φ j).hasCompactSupport_normed x
    simpa only [← hgrad] using hprod.integral_prod_left
  have hbound (j i) : (∫ x, ‖coordinateDerivative (h j) i x‖) ≤ ∫ y, ‖σ y i‖ ∂ρ :=
    (hpolar.integral_coordinateDerivative_bump_convolution_le hf.locallyIntegrable (φ j) i).2
  have happrox (j) := exists_smooth_compact_gradient_approximation (hh j) (hih j) (hihg j)
    (ε := ((j : ℝ) + 1)⁻¹) (by positivity)
  choose g hg hcg hig higg hfgerr hgraderr using happrox
  refine ⟨g, fun j => ⟨hg j, hcg j, hig j, higg j⟩, ?_, ?_⟩
  · have hb (j) : (∫ x, ‖g j x - f x‖) ≤
        ((j : ℝ) + 1)⁻¹ + ∫ x, ‖h j x - f x‖ := by
      calc
        _ ≤ (∫ x, ‖g j x - h j x‖) + ∫ x, ‖h j x - f x‖ := by
          have hadd := integral_add ((hig j).sub (hih j)).norm ((hih j).sub hf).norm
          simp only [Pi.sub_apply] at hadd
          rw [← hadd]
          apply integral_mono ((hig j).sub hf).norm
            (((hig j).sub (hih j)).norm.add ((hih j).sub hf).norm)
          exact fun x => by
            simpa only [dist_eq_norm, Pi.sub_apply, Pi.add_apply] using
              dist_triangle (g j x) (h j x) (f x)
        _ ≤ _ := add_le_add (hfgerr j).le le_rfl
    apply squeeze_zero (fun _ => integral_nonneg fun _ => norm_nonneg _) hb
    simpa only [zero_add] using hφlim.add (tendsto_integral_norm_bump_convolution_sub hf hφlim)
  · intro j i
    exact (integral_norm_coordinateDerivative_le_add_gradient_error (higg j) (hihg j) i).trans
      (add_le_add (hbound j i) (hgraderr j).le)

/-- Fatou with a convergent sequence of norm bounds and ordinary L¹ convergence. -/
theorem eLpNorm_le_of_l1_convergence_and_tendsto_bound {α F : Type*}
    [MeasurableSpace α] [NormedAddCommGroup F] {μ : Measure α}
    {g : ℕ → α → F} {f : α → F} {p : ℝ≥0∞}
    (hg : ∀ j, Integrable (g j) μ) (hf : Integrable f μ)
    (ht : Tendsto (fun j => ∫ x, ‖g j x - f x‖ ∂μ) atTop (𝓝 0))
    {C : ℕ → ℝ≥0∞} {c : ℝ≥0∞} (hb : ∀ j, eLpNorm (g j) p μ ≤ C j)
    (hC : Tendsto C atTop (𝓝 c)) : eLpNorm f p μ ≤ c := by
  have ht1 : Tendsto (fun j => eLpNorm (g j - f) 1 μ) atTop (𝓝 0) := by
    have he := ENNReal.continuous_ofReal.continuousAt.tendsto.comp ht
    simp only [ENNReal.ofReal_zero] at he
    convert he using 1
    ext j
    rw [eLpNorm_one_eq_lintegral_enorm ((hg j).sub hf).1,
      ← ofReal_integral_norm_eq_lintegral_enorm ((hg j).sub hf)]
    rfl
  obtain ⟨σ, hσ, hae⟩ := (tendstoInMeasure_of_tendsto_eLpNorm one_ne_zero
    ht1).exists_seq_tendsto_ae
  have hfatou := Lp.eLpNorm_lim_le_liminf_eLpNorm (fun j => (hg (σ j)).1) f hf.1 hae (p := p)
  exact hfatou.trans ((liminf_le_liminf (Eventually.of_forall fun j => hb (σ j))).trans_eq
    (hC.comp hσ.tendsto_atTop).liminf_eq)

/-- The scalar derivative measure is the coordinate projection of the full vector measure. -/
lemma polarCoordinateDerivative_eq_mapRange {n : ℕ} {S : Type*} [MeasurableSpace S]
    {ρ : Measure S} {σ : S → EuclideanSpace ℝ (Fin n)} (hσ : Integrable σ ρ) (i : Fin n) :
    polarCoordinateDerivative ρ σ i = (ρ.withDensityᵥ σ).mapRange
      (EuclideanSpace.proj (𝕜 := ℝ) i).toAddMonoidHom (EuclideanSpace.proj i).continuous := by
  ext A hA
  rw [polarCoordinateDerivative_apply hσ i hA]
  change (∫ y in A, σ y i ∂ρ) = (ρ.withDensityᵥ σ A) i
  rw [withDensityᵥ_apply hσ hA]
  exact (eval_integral_piLp hσ.integrableOn.eval_piLp i).symm

/-- The coordinate derivative mass uses the usual Hahn–Jordan total variation. -/
lemma totalVariation_polarCoordinateDerivative {n : ℕ} {S : Type*} [MeasurableSpace S]
    {ρ : Measure S} {σ : S → EuclideanSpace ℝ (Fin n)} (hσ : Integrable σ ρ) (i : Fin n) :
    (polarCoordinateDerivative ρ σ i).totalVariation =
      ρ.withDensity (fun y => ‖σ y i‖ₑ) := by
  rw [SignedMeasure.totalVariation_eq_variation, variation_polarCoordinateDerivative hσ]


/-! ## Planar BV Sobolev inequalities -/

/-- Each coordinate derivative mass is bounded by the full polar mass. -/
lemma IsDistributionalPolarRepresentation.coordinate_mass_le
    {n : ℕ} {U : Set (EuclideanSpace ℝ (Fin n))} {f : EuclideanSpace ℝ (Fin n) → ℝ}
    {ρ : Measure U} [IsFiniteMeasure ρ] {σ : U → EuclideanSpace ℝ (Fin n)}
    (hpolar : IsDistributionalPolarRepresentation f U ρ σ) (i : Fin n) :
    (polarCoordinateDerivative ρ σ i).variation univ ≤ ρ univ := by
  have hiσ : Integrable σ ρ := Integrable.of_bound hpolar.measurable.aestronglyMeasurable 1
    (hpolar.norm_ae.mono fun _ hx => hx.le)
  rw [variation_polarCoordinateDerivative_univ hiσ]
  calc
    _ ≤ ∫⁻ _ : U, (1 : ℝ≥0∞) ∂ρ := by
      apply lintegral_mono_ae
      filter_upwards [hpolar.norm_ae] with y hy
      change ‖σ y i‖ₑ ≤ 1
      calc
        _ ≤ ‖σ y‖ₑ := PiLp.enorm_apply_le _ _
        _ = 1 := by rw [← ofReal_norm, hy]; simp
    _ = _ := by simp

/-- The extended planar BV norm bound with the actual coordinate derivative masses. -/
theorem IsDistributionalPolarRepresentation.planar_sobolev_eLpNorm
    {f : EuclideanSpace ℝ (Fin 2) → ℝ}
    {ρ : Measure (univ : Set (EuclideanSpace ℝ (Fin 2)))} [IsFiniteMeasure ρ]
    {σ : ↑(univ : Set (EuclideanSpace ℝ (Fin 2))) → EuclideanSpace ℝ (Fin 2)}
    (hpolar : IsDistributionalPolarRepresentation f univ ρ σ) (hf : Integrable f) :
    eLpNorm f 2 volume ≤
      (polarCoordinateDerivative ρ σ 0).variation univ ^ (1 / 2 : ℝ) *
      (polarCoordinateDerivative ρ σ 1).variation univ ^ (1 / 2 : ℝ) := by
  have hiσ : Integrable σ ρ := Integrable.of_bound hpolar.measurable.aestronglyMeasurable 1
    (hpolar.norm_ae.mono fun _ hx => hx.le)
  let c (i : Fin 2) := ∫ y, ‖σ y i‖ ∂ρ
  have hc (i) : ENNReal.ofReal (c i) = (polarCoordinateDerivative ρ σ i).variation univ := by
    rw [variation_polarCoordinateDerivative_univ hiσ]
    exact ofReal_integral_norm_eq_lintegral_enorm
      ((EuclideanSpace.proj (𝕜 := ℝ) i).integrable_comp hiσ)
  rw [← hc 0, ← hc 1]
  obtain ⟨g, hg, ht, hb⟩ := hpolar.exists_smooth_compact_coordinate_approximation hf
  let C (j : ℕ) (i : Fin 2) := ENNReal.ofReal (c i + ((j : ℝ) + 1)⁻¹)
  have he : Tendsto (fun j : ℕ => ((j : ℝ) + 1)⁻¹) atTop (𝓝 0) := by
    simpa only [one_div] using tendsto_one_div_add_atTop_nhds_zero_nat (𝕜 := ℝ)
  have hC (i) : Tendsto (fun j => C j i) atTop (𝓝 (ENNReal.ofReal (c i))) := by
    simpa only [C, add_zero, Function.comp_def] using
      ENNReal.continuous_ofReal.continuousAt.tendsto.comp (tendsto_const_nhds.add he)
  have hCr (i) : Tendsto (fun j => C j i ^ (1 / 2 : ℝ)) atTop
      (𝓝 (ENNReal.ofReal (c i) ^ (1 / 2 : ℝ))) :=
    (ENNReal.continuous_rpow_const (y := (1 / 2 : ℝ))).continuousAt.tendsto.comp (hC i)
  have hCf (i) : ENNReal.ofReal (c i) ^ (1 / 2 : ℝ) ≠ ∞ :=
    (ENNReal.rpow_lt_top_of_nonneg (by norm_num) ENNReal.ofReal_ne_top).ne
  apply eLpNorm_le_of_l1_convergence_and_tendsto_bound (fun j => (hg j).2.2.1) hf ht
    (C := fun j => C j 0 ^ (1 / 2 : ℝ) * C j 1 ^ (1 / 2 : ℝ))
  · intro j
    have hb' (i) : eLpNorm (coordinateDerivative (g j) i) 1 volume ≤ C j i := by
      rw [eLpNorm_one_eq_lintegral_enorm
          (integrable_coordinateDerivative_of_gradient (hg j).2.2.2 i).1,
        ← ofReal_integral_norm_eq_lintegral_enorm
          (integrable_coordinateDerivative_of_gradient (hg j).2.2.2 i)]
      exact ENNReal.ofReal_le_ofReal (hb j i)
    exact (smooth_planar_sobolev_eLpNorm ((hg j).1.of_le (by simp)) (hg j).2.1).trans
      (mul_le_mul' (ENNReal.rpow_le_rpow (hb' 0) (by norm_num))
        (ENNReal.rpow_le_rpow (hb' 1) (by norm_num)))
  · exact ENNReal.Tendsto.mul (hCr 0) (Or.inr (hCf 1)) (hCr 1) (Or.inr (hCf 0))

/-- The full coordinatewise BV inequalities for any finite polar representation. -/
theorem IsDistributionalPolarRepresentation.planar_sobolev
    {f : EuclideanSpace ℝ (Fin 2) → ℝ}
    {ρ : Measure (univ : Set (EuclideanSpace ℝ (Fin 2)))} [IsFiniteMeasure ρ]
    {σ : ↑(univ : Set (EuclideanSpace ℝ (Fin 2))) → EuclideanSpace ℝ (Fin 2)}
    (hpolar : IsDistributionalPolarRepresentation f univ ρ σ) (hf : Integrable f) :
    MemLp f 2 volume ∧
      lpNorm f 2 volume ^ 2 ≤
        ((polarCoordinateDerivative ρ σ 0).variation univ).toReal *
        ((polarCoordinateDerivative ρ σ 1).variation univ).toReal ∧
      lpNorm f 2 volume ≤ (1 / 2 : ℝ) *
        (((polarCoordinateDerivative ρ σ 0).variation univ).toReal +
        ((polarCoordinateDerivative ρ σ 1).variation univ).toReal) ∧
      (1 / 2 : ℝ) *
        (((polarCoordinateDerivative ρ σ 0).variation univ).toReal +
        ((polarCoordinateDerivative ρ σ 1).variation univ).toReal) ≤ (ρ univ).toReal := by
  let m (i : Fin 2) := (polarCoordinateDerivative ρ σ i).variation univ
  have hm (i) : m i < ∞ := (hpolar.coordinate_mass_le i).trans_lt (measure_lt_top ρ univ)
  have hb := hpolar.planar_sobolev_eLpNorm hf
  have hfin : m 0 ^ (1 / 2 : ℝ) * m 1 ^ (1 / 2 : ℝ) < ∞ :=
    ENNReal.mul_lt_top (ENNReal.rpow_lt_top_of_nonneg (by norm_num) (hm 0).ne)
      (ENNReal.rpow_lt_top_of_nonneg (by norm_num) (hm 1).ne)
  have hs : eLpNorm f 2 volume ^ 2 ≤ m 0 * m 1 := by
    have he (x : ℝ≥0∞) : (x ^ (1 / 2 : ℝ)) ^ 2 = x := by
      rw [← ENNReal.rpow_two (x ^ (1 / 2 : ℝ)), ← ENNReal.rpow_mul]
      norm_num
    simpa only [mul_pow, he] using pow_le_pow_left' hb 2
  have hsr := ENNReal.toReal_mono (ENNReal.mul_lt_top (hm 0) (hm 1)).ne hs
  simp only [ENNReal.toReal_pow, ENNReal.toReal_mul, toReal_eLpNorm] at hsr
  have h0 := ENNReal.toReal_nonneg (a := m 0)
  have h1 := ENNReal.toReal_nonneg (a := m 1)
  refine ⟨hb.trans_lt hfin, hsr, ?_, ?_⟩
  · have hn := lpNorm_nonneg (f := f) (p := 2) (μ := volume)
    change lpNorm f 2 volume ≤ (1 / 2 : ℝ) * ((m 0).toReal + (m 1).toReal)
    nlinarith [sq_nonneg ((m 0).toReal - (m 1).toReal)]
  · have h0b := ENNReal.toReal_mono (measure_lt_top ρ univ).ne (hpolar.coordinate_mass_le 0)
    have h1b := ENNReal.toReal_mono (measure_lt_top ρ univ).ne (hpolar.coordinate_mass_le 1)
    linarith


/-- Blueprint `lem:planar-sobolev-L2`, BV clause. The coordinate derivative measures
come from an actual polar representation with full mass equal to variation. -/
theorem bv_planar_sobolev {f : EuclideanSpace ℝ (Fin 2) → ℝ} (hf : IsBVOn f univ) :
    ∃ ρ : Measure (univ : Set (EuclideanSpace ℝ (Fin 2))),
    ∃ σ : ↑(univ : Set (EuclideanSpace ℝ (Fin 2))) → EuclideanSpace ℝ (Fin 2),
      ρ.Regular ∧ IsFiniteMeasure ρ ∧ IsDistributionalPolarRepresentation f univ ρ σ ∧
      variation f univ = ρ univ ∧ MemLp f 2 volume ∧
      lpNorm f 2 volume ^ 2 ≤
        ((polarCoordinateDerivative ρ σ 0).variation univ).toReal *
        ((polarCoordinateDerivative ρ σ 1).variation univ).toReal ∧
      lpNorm f 2 volume ≤ (1 / 2 : ℝ) *
        (((polarCoordinateDerivative ρ σ 0).variation univ).toReal +
        ((polarCoordinateDerivative ρ σ 1).variation univ).toReal) ∧
      (1 / 2 : ℝ) *
        (((polarCoordinateDerivative ρ σ 0).variation univ).toReal +
        ((polarCoordinateDerivative ρ σ 1).variation univ).toReal) ≤
          (variation f univ).toReal := by
  have hif := integrableOn_univ.mp hf.1
  obtain ⟨ρ, σ, hρ, hpolar, hvar⟩ := exists_polar_representation_with_variation isOpen_univ
    (isLocallyBVOn_of_variation_lt_top isOpen_univ (hif.locallyIntegrable.locallyIntegrableOn univ)
      hf.2)
  have hmass : variation f univ = ρ univ := by
    simpa only [preimage_univ] using hvar univ isOpen_univ (Subset.rfl)
  let hfin : IsFiniteMeasure ρ := ⟨by rw [← hmass]; exact hf.2⟩
  obtain ⟨hL2, hprod, hsum, hbound⟩ := hpolar.planar_sobolev hif
  exact ⟨ρ, σ, hρ, hfin, hpolar, hmass, hL2, hprod, hsum, by simpa only [hmass] using hbound⟩

/-- The isotropic planar BV embedding, with constant one and genuine L² membership. -/
theorem bv_sobolev_two {f : EuclideanSpace ℝ (Fin 2) → ℝ} (hf : IsBVOn f univ) :
    MemLp f 2 volume ∧ eLpNorm f 2 volume ≤ variation f univ := by
  obtain ⟨ρ, σ, _, _, _, _, hL2, _, hsum, hvar⟩ := bv_planar_sobolev hf
  refine ⟨hL2, (ENNReal.toReal_le_toReal hL2.eLpNorm_ne_top hf.2.ne).mp ?_⟩
  rw [toReal_eLpNorm]
  exact hsum.trans hvar

end LiquidDrop

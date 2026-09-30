module

public import NoCompromise.Stationary.Bootstrap
public import NoCompromise.Elliptic.Quasilinear

@[expose] public section

/-! The minimal-surface flux: smoothness, its quadratic form, and uniform derivative bounds. -/

noncomputable section
open Metric InnerProductSpace
open scoped RealInnerProductSpace

namespace LiquidDrop

/-- The minimal-surface flux in the two graph variables. -/
def mcFlux (p : EuclideanSpace ℝ (Fin 2)) : EuclideanSpace ℝ (Fin 2) :=
  (Real.sqrt (1 + ‖p‖ ^ 2))⁻¹ • p

/-- The graph flux is real analytic, hence smooth, including at zero gradient. -/
theorem contDiff_mcFlux : ContDiff ℝ ⊤ mcFlux := by
  have hs : ContDiff ℝ ⊤ (fun p : EuclideanSpace ℝ (Fin 2) =>
      Real.sqrt (1 + ‖p‖ ^ 2)) :=
    (contDiff_const.add (contDiff_norm_sq ℝ)).sqrt fun p =>
      (by positivity : (1 + ‖p‖ ^ 2 : ℝ) ≠ 0)
  exact (hs.inv (fun p => by positivity)).smul contDiff_id

/-- The derivative of the flux has exactly the minimal-surface quadratic form. -/
theorem mcFlux_fderiv_inner (p ξ : EuclideanSpace ℝ (Fin 2)) :
    inner ℝ (fderiv ℝ mcFlux p ξ) ξ = mcQuadratic p ξ := by
  have hb : (1 + ‖p‖ ^ 2 : ℝ) ≠ 0 := by positivity
  have hs : Real.sqrt (1 + ‖p‖ ^ 2) ≠ 0 := by positivity
  have hd := ((hasDerivAt_inv hs).comp_hasFDerivAt p
    (((hasStrictFDerivAt_norm_sq p).hasFDerivAt.const_add 1).sqrt hb)).smul
    (hasFDerivAt_id p)
  rw [show fderiv ℝ mcFlux p = _ from hd.fderiv]
  simp [ContinuousLinearMap.smulRight_apply, inner_add_left, inner_smul_left, mcQuadratic]
  field_simp
  ring

/-- Ellipticity and both derivative bounds on any closed gradient ball.
The operator bound is enlarged so that it also dominates the ellipticity constant. -/
theorem mcFlux_uniform_bounds {M : ℝ} (hM : 0 ≤ M) :
    ∃ lam cap B : ℝ, 0 < lam ∧ lam ≤ cap ∧ 0 ≤ B ∧
      (∀ p ∈ closedBall (0 : EuclideanSpace ℝ (Fin 2)) M,
        ‖fderiv ℝ mcFlux p‖ ≤ cap) ∧
      (∀ p ∈ closedBall (0 : EuclideanSpace ℝ (Fin 2)) M,
        ‖fderiv ℝ (fderiv ℝ mcFlux) p‖ ≤ B) ∧
      (∀ p ∈ closedBall (0 : EuclideanSpace ℝ (Fin 2)) M, ∀ ξ,
        lam * ‖ξ‖ ^ 2 ≤ inner ℝ (fderiv ℝ mcFlux p ξ) ξ) := by
  obtain ⟨lam, hlam, hell⟩ := mcCoefficient_elliptic hM
  have hd : ContDiff ℝ 1 (fderiv ℝ mcFlux) :=
    contDiff_mcFlux.fderiv_right (by simp)
  obtain ⟨cap, hcap⟩ :=
    (isCompact_closedBall (0 : EuclideanSpace ℝ (Fin 2)) M).exists_bound_of_continuousOn
      hd.continuous.continuousOn
  obtain ⟨B, hB⟩ :=
    (isCompact_closedBall (0 : EuclideanSpace ℝ (Fin 2)) M).exists_bound_of_continuousOn
      (hd.continuous_fderiv one_ne_zero).continuousOn
  refine ⟨lam, max lam cap, max 0 B, hlam, le_max_left _ _, le_max_left _ _,
    fun p hp => (hcap p hp).trans (le_max_right _ _),
    fun p hp => (hB p hp).trans (le_max_right _ _), ?_⟩
  intro p hp ξ
  rw [mcFlux_fderiv_inner]
  exact hell p (mem_closedBall_zero_iff.mp hp) ξ


open MeasureTheory

/-- Passing from the Fréchet derivative to the gradient preserves the Hölder seminorm. -/
lemma mc_gradient_holderSeminorm_eq {a : ℝ}
    (f : EuclideanSpace ℝ (Fin 2) → ℝ) (U : Set (EuclideanSpace ℝ (Fin 2))) :
    holderSeminorm a (gradient f) U = holderSeminorm a (fderiv ℝ f) U := by
  have he (x y : EuclideanSpace ℝ (Fin 2)) :
      ‖gradient f x - gradient f y‖ = ‖fderiv ℝ f x - fderiv ℝ f y‖ := by
    rw [← toDual_gradient (f := f) (x := x), ← toDual_gradient (f := f) (x := y),
      ← map_sub, LinearIsometryEquiv.norm_map]
  simp only [holderSeminorm, he]

/-- The unit-ball interior C²,α estimate for the weak prescribed-mean-curvature equation. -/
theorem mc_graph_C2_holder_unit {a : ℝ} (ha : 0 < a) (ha1 : a < 1)
    {f G : EuclideanSpace ℝ (Fin 2) → ℝ}
    (hf : HasC1HolderOn a f (ball 0 1))
    (hG : HasFiniteHolderNormOn a G (ball 0 1))
    (he : ∀ φ : EuclideanSpace ℝ (Fin 2) → ℝ,
      ContDiff ℝ (⊤ : ℕ∞) φ → HasCompactSupport φ → tsupport φ ⊆ ball 0 1 →
      (∫ y, inner ℝ (gradient f y) (gradient φ y) /
        Real.sqrt (1 + ‖gradient f y‖ ^ 2)) = ∫ y, G y * φ y) :
    HasC2HolderOn a f (ball 0 (1 / 2)) := by
  have hneg : HasFiniteHolderNormOn a (-G) (ball 0 1) := by
    constructor
    · simpa only [Pi.neg_apply, norm_neg] using hG.uniform_bounded
    · simpa only [Pi.neg_apply, neg_sub_neg, norm_sub_rev] using hG.seminorm_bounded
  have hM := hf.derivative_holder.norm_nonneg
  have hH := hf.derivative_holder.seminorm_nonneg
  obtain ⟨lam, cap, B, hlam, hlamcap, hB, hcap, hb, hell⟩ := mcFlux_uniform_bounds hM
  obtain ⟨C, hC, hS⟩ := quasilinear_schauder (n := 2) (by norm_num) (by norm_num)
    ha ha1 hlam hlamcap hM hB hneg.norm_nonneg hH
  have hgrad : ∀ x ∈ ball (0 : EuclideanSpace ℝ (Fin 2)) 1,
      ‖gradient f x‖ ≤ holderNorm a (fderiv ℝ f) (ball 0 1) := by
    intro x hx
    simpa only [gradient, LinearIsometryEquiv.norm_map] using
      hf.derivative_holder.nondiv_norm_le hx
  have hweak : IsWeakQuasilinearEquationOn mcFlux f (-G) (ball 0 1) := by
    intro φ hφ hcφ hsφ
    calc
      (∫ y, inner ℝ (mcFlux (gradient f y)) (gradient φ y)) =
          ∫ y, inner ℝ (gradient f y) (gradient φ y) /
            Real.sqrt (1 + ‖gradient f y‖ ^ 2) := by
        congr 1
        funext y
        simp [mcFlux, div_eq_mul_inv, mul_comm]
      _ = ∫ y, G y * φ y := he φ hφ hcφ hsφ
      _ = -(∫ y, φ y * (-G) y) := by
        simp [mul_comm, integral_neg]
  exact (hS mcFlux f (-G) (contDiff_mcFlux.of_le (by simp)) hf hneg le_rfl
    hgrad (le_of_eq (mc_gradient_holderSeminorm_eq f (ball 0 1)))
    hcap hb hell hweak).2.2.1

end LiquidDrop

import NoCompromise.Stationary.BootstrapC2Chart
import NoCompromise.Elliptic.NondivSchauder

/-!
# The C³ interior bootstrap for the prescribed-mean-curvature graph equation

Blueprint `prop:bootstrap-C3`, on the unit ball. Classical differentiation of
the weak equation supplies the scalar-source linearized equation. Smooth
composition gives C¹,α coefficients, and the nondivergence Schauder theorem
upgrades every actual coordinate derivative to C²,α on the half ball.
-/

noncomputable section
open MeasureTheory Filter Metric Set InnerProductSpace
open scoped ENNReal Topology Gradient RealInnerProductSpace
namespace LiquidDrop

/-- Blueprint `prop:bootstrap-C3`: differentiation of the gradient commutes with
constant directional differentiation for a C² scalar function. -/
lemma bootstrap_gradient_fderiv {n : ℕ} {f : EuclideanSpace ℝ (Fin n) → ℝ}
    {x : EuclideanSpace ℝ (Fin n)} (hf : ContDiffAt ℝ 2 f x)
    (v : EuclideanSpace ℝ (Fin n)) :
    gradient (fun y => fderiv ℝ f y v) x = fderiv ℝ (gradient f) x v := by
  have hd : DifferentiableAt ℝ (fderiv ℝ f) x :=
    (hf.fderiv_right (by norm_num : (1 : WithTop ℕ∞) + 1 ≤ 2)).differentiableAt one_ne_zero
  have hg : DifferentiableAt ℝ (gradient f) x :=
    (toDual ℝ (EuclideanSpace ℝ (Fin n))).symm.differentiableAt.comp x hd
  have hdual := (toDual ℝ (EuclideanSpace ℝ (Fin n))).toContinuousLinearEquiv.hasFDerivAt.comp x
    hg.hasFDerivAt
  have he : (toDual ℝ (EuclideanSpace ℝ (Fin n))).toContinuousLinearEquiv ∘ gradient f =
      fderiv ℝ f := funext fun _ => toDual_gradient
  rw [he] at hdual
  apply ext_inner_right ℝ
  intro w
  rw [inner_gradient_left, fderiv_clm_apply hd (differentiableAt_const v)]
  simp only [fderiv_fun_const, Pi.zero_apply, ContinuousLinearMap.comp_zero, zero_add,
    ContinuousLinearMap.flip_apply]
  have hs := hf.isSymmSndFDerivAt (by norm_num) w v
  rw [hs, hdual.fderiv]
  rfl

/-- Blueprint `prop:bootstrap-C3`: local integration by parts for a C¹ vector
field against a compactly supported C¹ field, in a constant direction. -/
lemma bootstrap_integral_inner_fderiv {n : ℕ}
    {F X : EuclideanSpace ℝ (Fin n) → EuclideanSpace ℝ (Fin n)}
    {U : Set (EuclideanSpace ℝ (Fin n))} (hU : IsOpen U)
    (hF : ContDiffOn ℝ 1 F U) (hX : ContDiff ℝ 1 X)
    (hcX : HasCompactSupport X) (hsX : tsupport X ⊆ U)
    (v : EuclideanSpace ℝ (Fin n)) :
    (∫ x, inner ℝ (F x) (fderiv ℝ X x v)) =
      -(∫ x, inner ℝ (fderiv ℝ F x v) (X x)) := by
  have hDF : ContinuousOn (fun x => fderiv ℝ F x v) U :=
    (hF.continuousOn_fderiv_of_isOpen hU le_rfl).clm_apply continuousOn_const
  have hDX : Continuous (fun x => fderiv ℝ X x v) :=
    (hX.continuous_fderiv one_ne_zero).clm_apply continuous_const
  have hi₁ : Integrable (fun x => inner ℝ (fderiv ℝ F x v) (X x)) := by
    simpa only [real_inner_comm] using integrable_inner_compact_factor_on
      (hDF.locallyIntegrableOn hU.measurableSet) hX.continuous hcX hsX
  have hi₂ : Integrable (fun x => inner ℝ (F x) (fderiv ℝ X x v)) := by
    simpa only [real_inner_comm] using integrable_inner_compact_factor_on
      (hF.continuousOn.locallyIntegrableOn hU.measurableSet) hDX
      (hcX.fderiv_apply ℝ v) ((tsupport_fderiv_apply_subset ℝ v).trans hsX)
  have hi₃ : Integrable (fun x => inner ℝ (F x) (X x)) := by
    simpa only [real_inner_comm] using integrable_inner_compact_factor_on
      (hF.continuousOn.locallyIntegrableOn hU.measurableSet) hX.continuous hcX hsX
  exact integral_bilinear_fderiv_right_eq_neg_left_of_integrable (B := innerSL ℝ)
    hi₁ hi₂ hi₃
    (fun x hx => (hF.contDiffAt (hU.mem_nhds (hsX hx))).differentiableAt one_ne_zero)
    (fun x _ => hX.differentiable one_ne_zero x)

/-- Blueprint `prop:bootstrap-C3`: local scalar integration by parts with a
compactly supported C¹ test function. -/
lemma bootstrap_integral_mul_fderiv {n : ℕ}
    {G φ : EuclideanSpace ℝ (Fin n) → ℝ}
    {U : Set (EuclideanSpace ℝ (Fin n))} (hU : IsOpen U)
    (hG : ContDiffOn ℝ 1 G U) (hφ : ContDiff ℝ 1 φ)
    (hcφ : HasCompactSupport φ) (hsφ : tsupport φ ⊆ U)
    (v : EuclideanSpace ℝ (Fin n)) :
    (∫ x, G x * fderiv ℝ φ x v) = -(∫ x, fderiv ℝ G x v * φ x) := by
  have hi₁ : Integrable (fun x => fderiv ℝ G x v * φ x) := by
    simpa only [mul_comm] using integrable_mul_compact_factor_on
      (((hG.continuousOn_fderiv_of_isOpen hU le_rfl).clm_apply
        continuousOn_const).locallyIntegrableOn hU.measurableSet) hφ.continuous hcφ hsφ
  have hi₂ : Integrable (fun x => G x * fderiv ℝ φ x v) := by
    simpa only [mul_comm] using integrable_mul_compact_factor_on
      (hG.continuousOn.locallyIntegrableOn hU.measurableSet)
      ((hφ.continuous_fderiv one_ne_zero).clm_apply continuous_const)
      (hcφ.fderiv_apply ℝ v) ((tsupport_fderiv_apply_subset ℝ v).trans hsφ)
  have hi₃ : Integrable (fun x => G x * φ x) := by
    simpa only [mul_comm] using integrable_mul_compact_factor_on
      (hG.continuousOn.locallyIntegrableOn hU.measurableSet) hφ.continuous hcφ hsφ
  exact integral_mul_fderiv_eq_neg_fderiv_mul_of_integrable hi₁ hi₂ hi₃
    (fun x hx => (hG.contDiffAt (hU.mem_nhds (hsφ hx))).differentiableAt one_ne_zero)
    (fun x _ => hφ.differentiable one_ne_zero x)

/-- Blueprint `prop:bootstrap-C3`: the differentiated divergence-form equation
on the entire unit ball. Its scalar right-hand side is the positive derivative
of G in the integral convention used by the graph equation. -/
theorem mc_graph_differentiated_weak_unit
    {f G : EuclideanSpace ℝ (Fin 2) → ℝ}
    (hf : ContDiffOn ℝ 2 f (ball 0 1))
    (hG : ContDiffOn ℝ 1 G (ball 0 1))
    (he : ∀ φ : EuclideanSpace ℝ (Fin 2) → ℝ,
      ContDiff ℝ (⊤ : ℕ∞) φ → HasCompactSupport φ → tsupport φ ⊆ ball 0 1 →
      (∫ y, inner ℝ (gradient f y) (gradient φ y) /
        Real.sqrt (1 + ‖gradient f y‖ ^ 2)) = ∫ y, G y * φ y)
    (v : EuclideanSpace ℝ (Fin 2))
    {φ : EuclideanSpace ℝ (Fin 2) → ℝ}
    (hφ : ContDiff ℝ (⊤ : ℕ∞) φ) (hcφ : HasCompactSupport φ)
    (hsφ : tsupport φ ⊆ ball 0 1) :
    (∫ x, inner ℝ (fderiv ℝ mcFlux (gradient f x)
      (gradient (fun y => fderiv ℝ f y v) x)) (gradient φ x)) =
      ∫ x, fderiv ℝ G x v * φ x := by
  have hgrad : ContDiffOn ℝ 1 (gradient f) (ball 0 1) :=
    (toDual ℝ (EuclideanSpace ℝ (Fin 2))).symm.contDiff.comp_contDiffOn
      (hf.fderiv_of_isOpen isOpen_ball (by norm_num))
  have hflux : ContDiffOn ℝ 1 (fun x => mcFlux (gradient f x)) (ball 0 1) :=
    (contDiff_mcFlux.of_le (by simp)).comp_contDiffOn hgrad
  have hgradφ : ContDiff ℝ 1 (gradient φ) :=
    (toDual ℝ (EuclideanSpace ℝ (Fin 2))).symm.contDiff.comp
      (hφ.fderiv_right (by simp))
  have hcgradφ : HasCompactSupport (gradient φ) :=
    hcφ.of_isClosed_subset (isClosed_tsupport _) (tsupport_gradient_subset φ)
  have htest := he (fun y => fderiv ℝ φ y v)
    ((hφ.fderiv_right (by simp)).clm_apply contDiff_const)
    (hcφ.fderiv_apply ℝ v) ((tsupport_fderiv_apply_subset ℝ v).trans hsφ)
  have heq : (∫ x, inner ℝ (mcFlux (gradient f x))
      (fderiv ℝ (gradient φ) x v)) = ∫ x, G x * fderiv ℝ φ x v := by
    convert htest using 1
    congr 1
    funext x
    rw [bootstrap_gradient_fderiv (hφ.contDiffAt.of_le (by simp))]
    simp only [mcFlux, real_inner_smul_left, div_eq_mul_inv]
    ring
  rw [bootstrap_integral_inner_fderiv isOpen_ball hflux hgradφ hcgradφ
    ((tsupport_gradient_subset φ).trans hsφ) v,
    bootstrap_integral_mul_fderiv isOpen_ball hG (hφ.of_le (by simp)) hcφ hsφ v] at heq
  have hchain : (∫ x, inner ℝ (fderiv ℝ (fun y => mcFlux (gradient f y)) x v)
      (gradient φ x)) =
      ∫ x, inner ℝ (fderiv ℝ mcFlux (gradient f x)
        (gradient (fun y => fderiv ℝ f y v) x)) (gradient φ x) := by
    apply integral_congr_ae
    exact Eventually.of_forall fun x => by
      dsimp only
      by_cases hx : x ∈ ball (0 : EuclideanSpace ℝ (Fin 2)) 1
      · rw [bootstrap_gradient_fderiv (hf.contDiffAt (isOpen_ball.mem_nhds hx))]
        change inner ℝ (fderiv ℝ (mcFlux ∘ gradient f) x v) (gradient φ x) = _
        rw [fderiv_comp x (contDiff_mcFlux.differentiable (by simp) _)
          ((hgrad.contDiffAt (isOpen_ball.mem_nhds hx)).differentiableAt one_ne_zero)]
        rfl
      · rw [gradient_eq_zero_of_notMem_tsupport (fun h => hx (hsφ h))]
        simp
  rw [hchain] at heq
  exact neg_injective heq

/-- Blueprint `prop:bootstrap-C3`: a globally C¹ map preserves finite Hölder
norms of maps with bounded range in a finite-dimensional (proper) space. -/
lemma bootstrap_holder_comp_smooth {E F H : Type*}
    [NormedAddCommGroup E] [NormedAddCommGroup F] [NormedSpace ℝ F] [ProperSpace F]
    [NormedAddCommGroup H] [NormedSpace ℝ H]
    {a : ℝ} {u : E → F} {U : Set E} (hu : HasFiniteHolderNormOn a u U)
    {P : F → H} (hP : ContDiff ℝ 1 P) :
    HasFiniteHolderNormOn a (fun x => P (u x)) U := by
  let R := holderNorm a u U
  have hm (x) (hx : x ∈ U) : u x ∈ closedBall (0 : F) R :=
    mem_closedBall_zero_iff.mpr (hu.nondiv_norm_le hx)
  obtain ⟨B, hB⟩ := (isCompact_closedBall (0 : F) R).exists_bound_of_continuousOn
    hP.continuous.continuousOn
  obtain ⟨L, hL⟩ := (isCompact_closedBall (0 : F) R).exists_bound_of_continuousOn
    (hP.continuous_fderiv one_ne_zero).continuousOn
  apply (quasilinear_holder_of_modulus (le_max_left 0 B)
    (mul_nonneg (le_max_left 0 L) hu.seminorm_nonneg) ?_ ?_).1
  · intro x hx
    exact (hB _ (hm x hx)).trans (le_max_right _ _)
  · intro x hx y hy
    have hlip := (convex_closedBall (0 : F) R).norm_image_sub_le_of_norm_fderiv_le
      (fun z _ => hP.differentiable one_ne_zero z)
      (fun z hz => (hL z hz).trans (le_max_right 0 L)) (hm y hy) (hm x hx)
    calc
      ‖P (u x) - P (u y)‖ ≤ max 0 L * ‖u x - u y‖ := hlip
      _ ≤ max 0 L * (holderSeminorm a u U * ‖x - y‖ ^ a) :=
        mul_le_mul_of_nonneg_left (hu.nondiv_norm_sub_le hx hy) (le_max_left _ _)
      _ = (max 0 L * holderSeminorm a u U) * dist x y ^ a := by
        rw [dist_eq_norm, mul_assoc]

/-- Blueprint `prop:bootstrap-C3`: smooth composition preserves C¹,α on an
open set when the inner map has bounded range in a proper normed space. -/
lemma bootstrap_c1Holder_comp_smooth {E F H : Type*}
    [NormedAddCommGroup E] [NormedSpace ℝ E]
    [NormedAddCommGroup F] [NormedSpace ℝ F] [ProperSpace F]
    [NormedAddCommGroup H] [NormedSpace ℝ H]
    {a : ℝ} {u : E → F} {U : Set E} (hU : IsOpen U) (hu : HasC1HolderOn a u U)
    {P : F → H} (hP : ContDiff ℝ 2 P) :
    HasC1HolderOn a (fun x => P (u x)) U := by
  have hDP : ContDiff ℝ 1 (fderiv ℝ P) := hP.fderiv_right (by norm_num)
  have hcomp := (nondiv_holder_bilinear
    (bootstrap_holder_comp_smooth hu.function_holder hDP) hu.derivative_holder
    (ContinuousLinearMap.compL ℝ E F H)).1
  refine ⟨(hP.of_le (by norm_num)).comp_contDiffOn hu.contDiff,
    bootstrap_holder_comp_smooth hu.function_holder (hP.of_le (by norm_num)), ?_⟩
  apply (nondiv_holder_congr (g := fun x => (fderiv ℝ P (u x)).comp (fderiv ℝ u x)) ?_).1.mpr
    hcomp
  intro x hx
  exact ((hP.differentiable (by norm_num) (u x)).hasFDerivAt.comp x
    ((hu.contDiff.contDiffAt (hU.mem_nhds hx)).differentiableAt one_ne_zero).hasFDerivAt).fderiv

/-- Blueprint `prop:bootstrap-C3`: the first Fréchet derivative of C²,α data
is C¹,α on the same open set. -/
lemma bootstrap_fderiv_c1Holder {n : ℕ} {a : ℝ}
    {f : EuclideanSpace ℝ (Fin n) → ℝ} {U : Set (EuclideanSpace ℝ (Fin n))}
    (hU : IsOpen U) (hf : HasC2HolderOn a f U) :
    HasC1HolderOn a (fderiv ℝ f) U :=
  ⟨hf.contDiff.fderiv_of_isOpen hU (by norm_num), hf.derivative_holder, hf.hessian_holder⟩

/-- Blueprint `prop:bootstrap-C3`: the differentiated graph equation in the
repo's nondivergence convention, with drift div A and source -∂ᵥG. -/
theorem mc_graph_nondivergence_weak_unit
    {f G : EuclideanSpace ℝ (Fin 2) → ℝ}
    (hf : ContDiffOn ℝ 2 f (ball 0 1))
    (hG : ContDiffOn ℝ 1 G (ball 0 1))
    (he : ∀ φ : EuclideanSpace ℝ (Fin 2) → ℝ,
      ContDiff ℝ (⊤ : ℕ∞) φ → HasCompactSupport φ → tsupport φ ⊆ ball 0 1 →
      (∫ y, inner ℝ (gradient f y) (gradient φ y) /
        Real.sqrt (1 + ‖gradient f y‖ ^ 2)) = ∫ y, G y * φ y)
    (v : EuclideanSpace ℝ (Fin 2)) :
    IsWeakNondivergenceEquationOn (fun x => fderiv ℝ mcFlux (gradient f x))
      (nondivCoefficientDivergence (fun x => fderiv ℝ mcFlux (gradient f x)))
      (fun x => fderiv ℝ f x v) (fun x => -(fderiv ℝ G x v)) (ball 0 1) := by
  have hgrad : ContDiffOn ℝ 1 (gradient f) (ball 0 1) :=
    (toDual ℝ (EuclideanSpace ℝ (Fin 2))).symm.contDiff.comp_contDiffOn
      (hf.fderiv_of_isOpen isOpen_ball (by norm_num))
  have hA : ContDiffOn ℝ 1 (fun x => fderiv ℝ mcFlux (gradient f x)) (ball 0 1) :=
    (contDiff_mcFlux.fderiv_right (by simp)).comp_contDiffOn hgrad
  apply (isWeakNondivergenceEquationOn_iff_divergence isOpen_ball hA
    (continuousOn_nondivCoefficientDivergence isOpen_ball hA)
    ((hf.fderiv_of_isOpen isOpen_ball (by norm_num : (1 : WithTop ℕ∞) + 1 ≤ 2)).clm_apply
      contDiffOn_const)
    (((hG.continuousOn_fderiv_of_isOpen isOpen_ball le_rfl).clm_apply
      continuousOn_const).neg)).mpr
  intro φ hφ hcφ hsφ
  simpa only [nondivDivergenceSource, sub_self, inner_zero_left, add_zero,
    Pi.neg_apply, mul_neg, integral_neg, neg_neg, mul_comm] using
    mc_graph_differentiated_weak_unit hf hG he v hφ hcφ hsφ

/-- Blueprint `prop:bootstrap-C3`: C² regularity of all coordinate derivatives
upgrades a C¹ function to C³ on the same open set. -/
lemma bootstrap_contDiff_three_of_coordinate_derivatives {n : ℕ}
    {f : EuclideanSpace ℝ (Fin n) → ℝ} {U : Set (EuclideanSpace ℝ (Fin n))}
    (hU : IsOpen U) (hf : ContDiffOn ℝ 1 f U)
    (hD : ∀ i : Fin n, ContDiffOn ℝ 2
      (fun x => fderiv ℝ f x (EuclideanSpace.single i 1)) U) :
    ContDiffOn ℝ 3 f U := by
  have hDf : ContDiffOn ℝ 2 (fderiv ℝ f) U := by
    apply contDiffOn_clm_apply.mpr
    intro v
    have he : (fun x => fderiv ℝ f x v) =
        fun x => ∑ i : Fin n, v i * fderiv ℝ f x (EuclideanSpace.single i 1) := by
      funext x
      calc
        fderiv ℝ f x v = fderiv ℝ f x (∑ i : Fin n, v i • EuclideanSpace.single i 1) := by
          rw [nondiv_euclidean_sum_single]
        _ = _ := by simp only [map_sum, map_smul, smul_eq_mul]
    rw [he]
    exact ContDiffOn.sum (fun i _ => contDiffOn_const.mul (hD i))
  rw [show (3 : WithTop ℕ∞) = 2 + 1 by norm_num, contDiffOn_succ_iff_fderiv_of_isOpen hU]
  exact ⟨hf.differentiableOn one_ne_zero, by simp, hDf⟩

/-- Blueprint `prop:bootstrap-C3`: C²,α graph data and C¹,α prescribed mean
curvature give C³ regularity and C²,α coordinate derivatives on the half ball. -/
theorem mc_graph_C3_unit {a : ℝ} (ha : 0 < a) (ha1 : a < 1)
    {f G : EuclideanSpace ℝ (Fin 2) → ℝ}
    (hf : HasC2HolderOn a f (ball 0 1))
    (hG : HasC1HolderOn a G (ball 0 1))
    (he : ∀ φ : EuclideanSpace ℝ (Fin 2) → ℝ,
      ContDiff ℝ (⊤ : ℕ∞) φ → HasCompactSupport φ → tsupport φ ⊆ ball 0 1 →
      (∫ y, inner ℝ (gradient f y) (gradient φ y) /
        Real.sqrt (1 + ‖gradient f y‖ ^ 2)) = ∫ y, G y * φ y) :
    ContDiffOn ℝ 3 f (ball 0 (1 / 2)) ∧
      ∀ k : Fin 2, HasC2HolderOn a
        (fun x => fderiv ℝ f x (EuclideanSpace.single k 1)) (ball 0 (1 / 2)) := by
  have hDf := bootstrap_fderiv_c1Holder isOpen_ball hf
  have hgrad : HasC1HolderOn a (gradient f) (ball 0 1) :=
    bootstrap_c1Holder_comp_smooth isOpen_ball hDf
      (toDual ℝ (EuclideanSpace ℝ (Fin 2))).symm.contDiff
  let A := fun x => fderiv ℝ mcFlux (gradient f x)
  let b := nondivCoefficientDivergence A
  have hA : HasC1HolderOn a A (ball 0 1) :=
    bootstrap_c1Holder_comp_smooth isOpen_ball hgrad
      (contDiff_mcFlux.fderiv_right (by simp))
  have hb : HasFiniteHolderNormOn a b (ball 0 1) :=
    (nondivCoefficientDivergence_holder hA).1
  let M := max (nondivC1HolderNorm a A (ball 0 1)) (holderNorm a b (ball 0 1))
  have hM : 0 ≤ M := hA.norm_nonneg.trans (le_max_left _ _)
  have hgradmem (x) (hx : x ∈ ball (0 : EuclideanSpace ℝ (Fin 2)) 1) :
      gradient f x ∈ closedBall 0 (holderNorm a (fderiv ℝ f) (ball 0 1)) := by
    apply mem_closedBall_zero_iff.mpr
    simpa only [gradient, LinearIsometryEquiv.norm_map] using
      hf.derivative_holder.nondiv_norm_le hx
  obtain ⟨lam, cap, B, hlam, hlamcap, _, hcap, _, hell⟩ :=
    mcFlux_uniform_bounds hf.derivative_holder.norm_nonneg
  obtain ⟨C, _, hS⟩ := nondiv_schauder (n := 2) (by norm_num) (by norm_num)
    ha ha1 hlam hlamcap hM
  have hreg (k : Fin 2) : HasC2HolderOn a
      (fun x => fderiv ℝ f x (EuclideanSpace.single k 1)) (ball 0 (1 / 2)) := by
    have hw : HasC1HolderOn a
        (fun x => fderiv ℝ f x (EuclideanSpace.single k 1)) (ball 0 1) :=
      bootstrap_c1Holder_comp_smooth isOpen_ball hDf
        (ContinuousLinearMap.apply ℝ ℝ (EuclideanSpace.single k 1)).contDiff
    have hsource : HasFiniteHolderNormOn a
        (fun x => -(fderiv ℝ G x (EuclideanSpace.single k 1))) (ball 0 1) := by
      simpa only [neg_apply, ContinuousLinearMap.apply_apply] using
        (nondiv_holder_comp_clm hG.derivative_holder
          (-(ContinuousLinearMap.apply ℝ ℝ (EuclideanSpace.single k 1)))).1
    exact (hS A b _ _ hA hb hw hsource (le_max_left _ _) (le_max_right _ _)
      (fun x hx => hcap _ (hgradmem x hx))
      (fun x hx v => by simpa only [real_inner_comm] using hell _ (hgradmem x hx) v)
      (mc_graph_nondivergence_weak_unit hf.contDiff hG.contDiff he
        (EuclideanSpace.single k 1))).1
  refine ⟨bootstrap_contDiff_three_of_coordinate_derivatives isOpen_ball ?_
    (fun k => (hreg k).contDiff), hreg⟩
  exact (hf.contDiff.of_le (by norm_num : (1 : WithTop ℕ∞) ≤ 2)).mono
    (ball_subset_ball (by norm_num : (1 / 2 : ℝ) ≤ 1))

end LiquidDrop

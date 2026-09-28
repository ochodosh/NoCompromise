import NoCompromise.Elliptic.ClassicalKernelW11
import NoCompromise.Sobolev.W11VectorAssembly

/-! # Compact C¹ vector fields divided by reciprocal distance are W¹,¹ -/

noncomputable section
open MeasureTheory Set Filter Metric InnerProductSpace
open scoped ENNReal Topology Gradient
namespace LiquidDrop
set_option maxSynthPendingDepth 8

def classicalNewtonFieldDerivative (X : AmbientSpace → AmbientSpace)
    (y x : AmbientSpace) : AmbientSpace →L[ℝ] AmbientSpace :=
  (innerSL ℝ (classicalNewtonGradient (x - y))).smulRight (X x) +
    ‖x - y‖⁻¹ • fderiv ℝ X x

lemma classicalNewtonFieldDerivative_adjoint {X : AmbientSpace → AmbientSpace}
    (hX : ContDiff ℝ 1 X) (y x : AmbientSpace) (i : Fin 3) :
    (classicalNewtonFieldDerivative X y x).adjoint (EuclideanSpace.single i 1) =
      X x i • classicalNewtonGradient (x - y) +
        ‖x - y‖⁻¹ • gradient (fun z => X z i) x := by
  apply ext_inner_right ℝ
  intro v
  rw [ContinuousLinearMap.adjoint_inner_left, inner_add_left, real_inner_smul_left,
    real_inner_smul_left, gradient_component_eq_adjoint (hX.differentiable one_ne_zero x),
    ContinuousLinearMap.adjoint_inner_left]
  simp only [classicalNewtonFieldDerivative, add_apply,
    ContinuousLinearMap.smulRight_apply, smul_apply, inner_add_right,
    inner_smul_right, EuclideanSpace.inner_single_left, map_one, one_mul,
    innerSL_apply_apply]
  ring

theorem hasW11VectorGradientOn_newton_field {X : AmbientSpace → AmbientSpace}
    (hX : ContDiff ℝ 1 X) (hcX : HasCompactSupport X) (y : AmbientSpace) :
    HasW11VectorGradientOn (fun x => ‖x - y‖⁻¹ • X x)
      (classicalNewtonFieldDerivative X y) univ := by
  obtain ⟨R, _, hsR⟩ := hcX.isBounded.subset_ball_lt 0 (0 : AmbientSpace)
  have hk := hasW11GradientOn_reciprocal_distance isOpen_ball isBounded_ball y
    (D := ball 0 R)
  have hmG : Measurable (fun x => classicalNewtonGradient (x - y)) := by
    unfold classicalNewtonGradient
    fun_prop
  have hmJ : AEStronglyMeasurable (classicalNewtonFieldDerivative X y) volume := by
    unfold classicalNewtonFieldDerivative
    have hmG' : AEStronglyMeasurable (fun x => classicalNewtonGradient (x - y)) volume :=
      hmG.aestronglyMeasurable
    have hL := Continuous.comp_aestronglyMeasurable
      (ContinuousLinearMap.smulRightL ℝ AmbientSpace AmbientSpace).continuous
      ((innerSL ℝ).continuous.comp_aestronglyMeasurable hmG')
    have hA := (continuous_fst.clm_apply continuous_snd).comp_aestronglyMeasurable
      (hL.prodMk hX.continuous.aestronglyMeasurable)
    have hm : Measurable (fun x : AmbientSpace => ‖x - y‖⁻¹) := by fun_prop
    exact hA.add (hm.aestronglyMeasurable.smul
      (hX.continuous_fderiv one_ne_zero).aestronglyMeasurable)
  apply hasW11VectorGradientOn_of_components (by simpa only [Measure.restrict_univ] using hmJ)
  intro i
  have hXi : ContDiff ℝ 1 (fun x => X x i) := by
    exact (EuclideanSpace.proj i).contDiff.comp hX
  have hsXi : tsupport (fun x => X x i) ⊆ tsupport X := by
    apply closure_mono
    intro x hx hzero
    exact hx (by change X x i = 0; rw [hzero]; rfl)
  have hcXi : HasCompactSupport (fun x => X x i) :=
    hcX.of_isClosed_subset (isClosed_tsupport _) hsXi
  have hw := hk.toHasWeakGradientOn.w11_mul_compact_cutoff hXi hcXi (hsXi.trans hsR)
  apply hw.congr_ae
  · exact Eventually.of_forall fun x => by simp only [PiLp.smul_apply, smul_eq_mul, mul_comm]
  · exact Eventually.of_forall fun x => (classicalNewtonFieldDerivative_adjoint hX y x i).symm

lemma HasW11VectorGradientOn.mono {n : ℕ}
    {Z : EuclideanSpace ℝ (Fin n) → EuclideanSpace ℝ (Fin n)}
    {J : EuclideanSpace ℝ (Fin n) → EuclideanSpace ℝ (Fin n) →L[ℝ]
      EuclideanSpace ℝ (Fin n)}
    {U V : Set (EuclideanSpace ℝ (Fin n))} (h : HasW11VectorGradientOn Z J U)
    (hVU : V ⊆ U) : HasW11VectorGradientOn Z J V :=
  ⟨h.integrable_function.mono_set hVU, h.integrable_gradient.mono_set hVU,
    fun i => (h.weak_component i).mono hVU⟩

end LiquidDrop

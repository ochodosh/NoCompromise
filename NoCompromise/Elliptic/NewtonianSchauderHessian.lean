import NoCompromise.Elliptic.NewtonianSchauderLimit
import NoCompromise.Energy.SignedPotentialRegularity

/-!
# Classical identification of the Newtonian Hessian

The normalized signed potential has an actual C¹ derivative. Differentiation
under the integral for its smooth regularizations, followed by locally uniform
Hessian convergence, identifies its second derivative with the compensated
Hessian integral. No differentiability of the source is assumed.
-/

noncomputable section
open MeasureTheory Filter Metric Set InnerProductSpace
open scoped NNReal ENNReal Topology Gradient RealInnerProductSpace
namespace LiquidDrop
set_option maxSynthPendingDepth 8
local notation "E₃" => EuclideanSpace ℝ (Fin 3)
local notation "D₃" => E₃ →L[ℝ] ℝ
local notation "H₃" => E₃ →L[ℝ] D₃

lemma schauder_linear_eq_sum {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]
    (L : E₃ →L[ℝ] F) :
    L = ∑ i : Fin 3, (innerSL ℝ (EuclideanSpace.single i 1)).smulRight
      (L (EuclideanSpace.single i 1)) := by
  ext v
  have he := (EuclideanSpace.basisFun (Fin 3) ℝ).sum_repr v
  simp only [EuclideanSpace.basisFun_repr, EuclideanSpace.basisFun_apply] at he
  conv_lhs => rw [← he]
  simp only [map_sum, map_smul, _root_.sum_apply, ContinuousLinearMap.smulRight_apply,
    innerSL_apply_apply, EuclideanSpace.inner_single_left, conj_trivial, one_mul]

/-- The rank-one bilinear coordinate form. -/
def schauderCoordinateBilinear (i j : Fin 3) : H₃ :=
  (innerSL ℝ (EuclideanSpace.single i 1)).smulRight (innerSL ℝ (EuclideanSpace.single j 1))

lemma schauder_bilinear_eq_sum (L : H₃) :
    L = ∑ i : Fin 3, ∑ j : Fin 3,
      L (EuclideanSpace.single i 1) (EuclideanSpace.single j 1) •
        schauderCoordinateBilinear i j := by
  ext v w
  have hv := (EuclideanSpace.basisFun (Fin 3) ℝ).sum_repr v
  have hw := (EuclideanSpace.basisFun (Fin 3) ℝ).sum_repr w
  simp only [EuclideanSpace.basisFun_repr, EuclideanSpace.basisFun_apply] at hv hw
  conv_lhs => rw [← hv, ← hw]
  simp only [map_sum, map_smul, _root_.sum_apply, smul_apply, smul_eq_mul,
    schauderCoordinateBilinear, ContinuousLinearMap.smulRight_apply, innerSL_apply_apply,
    EuclideanSpace.inner_single_left, conj_trivial, one_mul]
  simp_rw [Finset.mul_sum]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro i _
  apply Finset.sum_congr rfl
  intro j _
  ring

/-- The continuous bilinear map represented by the compensated entries. -/
def schauderHessianCandidateMap (f : E₃ → ℝ) (x : E₃) : H₃ :=
  ∑ i : Fin 3, ∑ j : Fin 3, schauderHessianCandidate i j f x • schauderCoordinateBilinear i j

lemma schauderHessianCandidateMap_apply_basis (f : E₃ → ℝ) (x : E₃) (i j : Fin 3) :
    schauderHessianCandidateMap f x (EuclideanSpace.single i 1) (EuclideanSpace.single j 1) =
      schauderHessianCandidate i j f x := by
  simp [schauderHessianCandidateMap, schauderCoordinateBilinear,
    EuclideanSpace.inner_single_left, PiLp.single_apply]

lemma continuous_schauderHessianCandidateMap {α A : ℝ} (hα : 0 < α) (hα1 : α < 1)
    (hA : 0 ≤ A) {f : E₃ → ℝ} (hf : Measurable f) (hi : Integrable f)
    (hinc : ∀ x y, ‖f x - f y‖ ≤ A * ‖x - y‖ ^ α) :
    Continuous (schauderHessianCandidateMap f) := by
  apply continuous_finsetSum
  intro i _
  apply continuous_finsetSum
  intro j _
  exact (continuous_schauderHessianCandidate hα hα1 hA hf hi hinc i j).smul continuous_const

/-- The signed potential with the convention `ΔP = f`. -/
def schauderPotential (f : E₃ → ℝ) (x : E₃) : ℝ :=
  -(4 * Real.pi)⁻¹ * scalarNewtonianPotential f x

/-- Its already constructed genuine first derivative. -/
def schauderPotentialDerivative (f : E₃ → ℝ) (x : E₃) : D₃ :=
  -(4 * Real.pi)⁻¹ • scalarNewtonianPotentialDerivative f x

lemma hasFDerivAt_schauderPotential {f : E₃ → ℝ} {B : ℝ}
    (hf : AEStronglyMeasurable f volume) (hcf : HasCompactSupport f)
    (hB : ∀ x, ‖f x‖ ≤ B) (x : E₃) :
    HasFDerivAt (schauderPotential f) (schauderPotentialDerivative f x) x :=
  (hasFDerivAt_scalarNewtonianPotential hf hcf hB x).const_mul (-(4 * Real.pi)⁻¹)

lemma schauderRegularizedDerivative_eq (ε : ℝ) (x : E₃) :
    schauderRegularizedDerivative ε x = -(4 * Real.pi)⁻¹ • regularizedNewtonDerivative ε x := by
  simp only [schauderRegularizedDerivative, regularizedNewtonDerivative, smul_smul, neg_mul_neg]

lemma continuous_schauderRegularizedDerivative {ε : ℝ} (hε : 0 < ε) :
    Continuous (schauderRegularizedDerivative ε) :=
  (show Differentiable ℝ (schauderRegularizedDerivative ε) from
    fun x => (hasFDerivAt_schauderRegularizedDerivative hε x).differentiableAt).continuous

lemma continuous_schauderRegularizedHessian {ε : ℝ} (hε : 0 < ε) :
    Continuous (schauderRegularizedHessian ε) := by
  have he : fderiv ℝ (fderiv ℝ (schauderRegularizedKernel ε)) = schauderRegularizedHessian ε :=
    funext (fderiv_two_schauderRegularizedKernel hε)
  rw [← he]
  exact ((contDiff_schauderRegularizedKernel hε).fderiv_right
    (m := 1) (by simp)).continuous_fderiv (by norm_num)

lemma norm_schauderRegularizedHessian_le_uniform {ε : ℝ} (hε : 0 < ε) (x : E₃) :
    ‖schauderRegularizedHessian ε x‖ ≤ Real.pi⁻¹ * (ε ^ 3)⁻¹ :=
  (norm_schauderRegularizedHessian_le hε x).trans
    (mul_le_mul_of_nonneg_left (inv_anti₀ (by positivity)
      (pow_le_pow_left₀ hε.le (regularizedNewton_sqrt_bounds hε x).2.2 3)) (by positivity))

/-- The first derivative of the smooth signed potential approximation. -/
def schauderRegularizedPotentialDerivative (ε : ℝ) (f : E₃ → ℝ) (x : E₃) : D₃ :=
  ∫ y, f y • schauderRegularizedDerivative ε (x - y)

lemma schauderRegularizedPotentialDerivative_eq (ε : ℝ) (f : E₃ → ℝ) (x : E₃) :
    schauderRegularizedPotentialDerivative ε f x =
      -(4 * Real.pi)⁻¹ • regularizedScalarNewtonPotentialDerivative ε f x := by
  simp only [schauderRegularizedPotentialDerivative, schauderRegularizedDerivative_eq,
    regularizedScalarNewtonPotentialDerivative]
  simp_rw [smul_comm (f _) (-(4 * Real.pi)⁻¹), integral_smul]

/-- The actual Hessian convolution as a continuous bilinear map. -/
def schauderRegularizedHessianMap (ε : ℝ) (f : E₃ → ℝ) (x : E₃) : H₃ :=
  ∫ y, f y • schauderRegularizedHessian ε (x - y)

lemma integrable_schauderRegularizedHessianMap {ε : ℝ} (hε : 0 < ε)
    {f : E₃ → ℝ} (hf : Integrable f) (x : E₃) :
    Integrable (fun y => f y • schauderRegularizedHessian ε (x - y)) := by
  apply (hf.norm.mul_const (Real.pi⁻¹ * (ε ^ 3)⁻¹)).mono'
    (hf.aestronglyMeasurable.smul ((continuous_schauderRegularizedHessian hε).comp
      (continuous_const.sub continuous_id)).aestronglyMeasurable)
  exact Eventually.of_forall fun y => by
    change ‖f y • schauderRegularizedHessian ε (x - y)‖ ≤ _
    rw [norm_smul]
    exact mul_le_mul_of_nonneg_left
      (norm_schauderRegularizedHessian_le_uniform hε _) (norm_nonneg _)

lemma hasFDerivAt_schauderRegularizedPotentialDerivative {ε : ℝ} (hε : 0 < ε)
    {f : E₃ → ℝ} (hf : Integrable f) (x : E₃) :
    HasFDerivAt (schauderRegularizedPotentialDerivative ε f)
      (schauderRegularizedHessianMap ε f x) x := by
  have hi : Integrable (fun y => f y • schauderRegularizedDerivative ε (x - y)) := by
    apply ((integrable_regularizedScalarNewtonPotentialDerivative_integrand hε hf x).smul
      (-(4 * Real.pi)⁻¹)).congr
    exact Eventually.of_forall fun y => by
      change -(4 * Real.pi)⁻¹ • (f y • regularizedNewtonDerivative ε (x - y)) = _
      simp only [schauderRegularizedDerivative_eq]
      exact smul_comm _ _ _
  unfold schauderRegularizedPotentialDerivative schauderRegularizedHessianMap
  apply hasFDerivAt_integral_of_dominated_of_fderiv_le (s := univ)
    (F' := fun a y => f y • schauderRegularizedHessian ε (a - y))
    (bound := fun y => ‖f y‖ * (Real.pi⁻¹ * (ε ^ 3)⁻¹)) univ_mem
  · exact Eventually.of_forall fun a => hf.aestronglyMeasurable.smul
      (((continuous_schauderRegularizedDerivative hε).comp
        (continuous_const.sub continuous_id)).aestronglyMeasurable)
  · exact hi
  · exact (integrable_schauderRegularizedHessianMap hε hf x).aestronglyMeasurable
  · exact Eventually.of_forall fun y a _ => by
      rw [norm_smul]
      exact mul_le_mul_of_nonneg_left
        (norm_schauderRegularizedHessian_le_uniform hε _) (norm_nonneg _)
  · exact hf.norm.mul_const _
  · exact Eventually.of_forall fun y a _ => by
      simpa only [ContinuousLinearMap.comp_id, Function.comp_def, id_eq, Pi.smul_apply] using!
        ((hasFDerivAt_schauderRegularizedDerivative hε (a - y)).comp a
          ((hasFDerivAt_id a).sub_const y)).const_smul (f y)

lemma schauderRegularizedHessianMap_apply_basis {ε : ℝ} (hε : 0 < ε)
    {f : E₃ → ℝ} (hf : Integrable f) (x : E₃) (i j : Fin 3) :
    schauderRegularizedHessianMap ε f x (EuclideanSpace.single i 1) (EuclideanSpace.single j 1) =
      schauderRegularizedHessianConvolution ε i j f x := by
  have hi := integrable_schauderRegularizedHessianMap hε hf x
  rw [schauderRegularizedHessianMap, ContinuousLinearMap.integral_apply hi]
  have hi1 : Integrable (fun y =>
      (f y • schauderRegularizedHessian ε (x - y)) (EuclideanSpace.single i 1)) :=
    (ContinuousLinearMap.apply ℝ D₃ (EuclideanSpace.single i 1)).integrable_comp hi
  rw [ContinuousLinearMap.integral_apply hi1]
  change (∫ y, f y * schauderRegularizedHessianEntry ε i j (x - y)) = _
  have h := integral_sub_left_eq_self
    (fun y => f y * schauderRegularizedHessianEntry ε i j (x - y)) volume x
  simpa only [sub_sub_cancel, mul_comm, schauderRegularizedHessianConvolution] using h.symm

lemma schauderRegularizedHessianMap_eq_sum {ε : ℝ} (hε : 0 < ε)
    {f : E₃ → ℝ} (hf : Integrable f) (x : E₃) :
    schauderRegularizedHessianMap ε f x = ∑ i : Fin 3, ∑ j : Fin 3,
      schauderRegularizedHessianConvolution ε i j f x • schauderCoordinateBilinear i j := by
  rw [schauder_bilinear_eq_sum (schauderRegularizedHessianMap ε f x)]
  simp_rw [schauderRegularizedHessianMap_apply_basis hε hf]

lemma schauder_uniform_sum {ι F : Type*} [Fintype ι] [NormedAddCommGroup F]
    {g : ι → ℕ → E₃ → F} {f : ι → E₃ → F} {U : Set E₃}
    (h : ∀ i, TendstoUniformlyOn (g i) (f i) atTop U) :
    TendstoUniformlyOn (fun k x => ∑ i, g i k x) (fun x => ∑ i, f i x) atTop U := by
  classical
  have hs (s : Finset ι) :
      TendstoUniformlyOn (fun k x => ∑ i ∈ s, g i k x) (fun x => ∑ i ∈ s, f i x) atTop U := by
    induction s using Finset.induction_on with
    | empty =>
      simp only [Finset.sum_empty]
      exact tendsto_const_nhds.tendstoUniformlyOn_const U
    | @insert i s his ih =>
      simpa only [Finset.sum_insert his, Pi.add_apply] using! (h i).add ih
  exact hs Finset.univ

lemma tendstoUniformlyOn_schauderRegularizedHessianMap {α A B : ℝ}
    (hα : 0 < α) (hA : 0 ≤ A) (hB : 0 ≤ B) {ε : ℕ → ℝ}
    (hε : Tendsto ε atTop (𝓝 0)) (hεpos : ∀ k, 0 < ε k)
    {f : E₃ → ℝ} (hf : Measurable f) (hcf : HasCompactSupport f)
    (hfb : ∀ x, ‖f x‖ ≤ B) (hinc : ∀ x y, ‖f x - f y‖ ≤ A * ‖x - y‖ ^ α) (S : ℝ) :
    TendstoUniformlyOn (fun k => schauderRegularizedHessianMap (ε k) f)
      (schauderHessianCandidateMap f) atTop (ball 0 S) := by
  have hi := integrable_scalarDensity_of_bounded_compact hf.aestronglyMeasurable hcf hfb
  change TendstoUniformlyOn (fun k x => schauderRegularizedHessianMap (ε k) f x)
    (fun x => schauderHessianCandidateMap f x) atTop (ball 0 S)
  simp_rw [schauderRegularizedHessianMap_eq_sum (hεpos _) hi, schauderHessianCandidateMap]
  apply schauder_uniform_sum
  intro i
  apply schauder_uniform_sum
  intro j
  let T : ℝ →L[ℝ] H₃ := (1 : ℝ →L[ℝ] ℝ).smulRight (schauderCoordinateBilinear i j)
  have h := T.uniformContinuous.comp_tendstoUniformlyOn
    (tendstoUniformlyOn_schauderRegularizedHessianConvolution
      hα hA hB hε hεpos hf hcf hfb hinc S i j)
  simpa [T] using! h

/-- The compensated bilinear integral is the actual derivative of the potential's
first derivative, obtained from genuine smooth approximations. -/
theorem hasFDerivAt_schauderPotentialDerivative {α A B : ℝ}
    (hα : 0 < α) (hA : 0 ≤ A) (hB : 0 ≤ B) {f : E₃ → ℝ}
    (hf : Measurable f) (hcf : HasCompactSupport f) (hfb : ∀ x, ‖f x‖ ≤ B)
    (hinc : ∀ x y, ‖f x - f y‖ ≤ A * ‖x - y‖ ^ α) (x : E₃) :
    HasFDerivAt (schauderPotentialDerivative f) (schauderHessianCandidateMap f x) x := by
  let ε (k : ℕ) : ℝ := 1 / ((k : ℝ) + 1)
  have hε : Tendsto ε atTop (𝓝 0) := tendsto_one_div_add_atTop_nhds_zero_nat
  have hεpos (k : ℕ) : 0 < ε k := by dsimp [ε]; positivity
  have hi := integrable_scalarDensity_of_bounded_compact hf.aestronglyMeasurable hcf hfb
  apply hasFDerivAt_of_tendstoUniformlyOn (s := ball 0 (‖x‖ + 1)) isOpen_ball
    (tendstoUniformlyOn_schauderRegularizedHessianMap
      hα hA hB hε hεpos hf hcf hfb hinc (‖x‖ + 1))
  · exact fun k y _ => hasFDerivAt_schauderRegularizedPotentialDerivative (hεpos k) hi y
  · intro y hy
    have h := (tendstoUniformlyOn_regularizedScalarNewtonPotentialDerivative hε hεpos
      hf.aestronglyMeasurable hcf hfb (‖x‖ + 1)).tendsto_at hy
    simpa only [schauderRegularizedPotentialDerivative_eq, schauderPotentialDerivative] using
      h.const_smul (-(4 * Real.pi)⁻¹)
  · simp only [mem_ball, dist_zero_right]
    linarith

/-- A bounded compactly supported Hölder source has a genuinely C² signed
Newtonian potential, with no derivative assumption on the source. -/
theorem contDiff_two_schauderPotential {α A B : ℝ} (hα : 0 < α) (hα1 : α < 1)
    (hA : 0 ≤ A) (hB : 0 ≤ B) {f : E₃ → ℝ} (hf : Measurable f) (hcf : HasCompactSupport f)
    (hfb : ∀ x, ‖f x‖ ≤ B) (hinc : ∀ x y, ‖f x - f y‖ ≤ A * ‖x - y‖ ^ α) :
    ContDiff ℝ 2 (schauderPotential f) := by
  have hi := integrable_scalarDensity_of_bounded_compact hf.aestronglyMeasurable hcf hfb
  apply (contDiff_succ_iff_hasFDerivAt (n := 1)).mpr
  refine ⟨schauderPotentialDerivative f, ?_, hasFDerivAt_schauderPotential
    hf.aestronglyMeasurable hcf hfb⟩
  apply contDiff_one_iff_hasFDerivAt.mpr
  exact ⟨schauderHessianCandidateMap f,
    continuous_schauderHessianCandidateMap hα hα1 hA hf hi hinc,
    hasFDerivAt_schauderPotentialDerivative hα hA hB hf hcf hfb hinc⟩

lemma fderiv_two_schauderPotential {α A B : ℝ} (hα : 0 < α)
    (hA : 0 ≤ A) (hB : 0 ≤ B) {f : E₃ → ℝ} (hf : Measurable f) (hcf : HasCompactSupport f)
    (hfb : ∀ x, ‖f x‖ ≤ B) (hinc : ∀ x y, ‖f x - f y‖ ≤ A * ‖x - y‖ ^ α) (x : E₃) :
    fderiv ℝ (fderiv ℝ (schauderPotential f)) x = schauderHessianCandidateMap f x := by
  have he : fderiv ℝ (schauderPotential f) = schauderPotentialDerivative f :=
    funext fun y => (hasFDerivAt_schauderPotential hf.aestronglyMeasurable hcf hfb y).fderiv
  rw [he, (hasFDerivAt_schauderPotentialDerivative hα hA hB hf hcf hfb hinc x).fderiv]

end LiquidDrop

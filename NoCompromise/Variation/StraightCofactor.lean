module

public import NoCompromise.Variation.StraightDiffeo
public import NoCompromise.Variation.Piola
public import Mathlib.LinearAlgebra.Matrix.Trace
public import Mathlib.Topology.Instances.Matrix

@[expose] public section

/-!
# Uniform expansions for straight perturbations

The cofactor and determinant expansions are exact polynomial identities. Their
norm remainders yield uniform quadratic bounds for bounded derivatives and unit
normals, hence the uniform first-order surface Jacobian formula.
-/

noncomputable section

open Set Filter MeasureTheory Matrix
open scoped Topology NNReal RealInnerProductSpace

namespace LiquidDrop

set_option maxSynthPendingDepth 8

local notation "E₃" => EuclideanSpace ℝ (Fin 3)
local notation "L₃" => E₃ →L[ℝ] E₃

lemma standardMatrix3_injective : Function.Injective standardMatrix3 := by
  intro A B h
  have hL : A.toLinearMap = B.toLinearMap := Matrix.toEuclideanLin.symm.injective h
  exact ContinuousLinearMap.ext fun x => LinearMap.congr_fun hL x

@[simp] lemma standardMatrix3_id : standardMatrix3 (ContinuousLinearMap.id ℝ E₃) = 1 := by
  ext i j
  simp [standardMatrix3_apply, Matrix.one_apply, PiLp.single_apply]

@[simp] lemma standardMatrix3_add (A B : L₃) :
    standardMatrix3 (A + B) = standardMatrix3 A + standardMatrix3 B := by
  ext i j
  simp [standardMatrix3_apply]

@[simp] lemma standardMatrix3_sub (A B : L₃) :
    standardMatrix3 (A - B) = standardMatrix3 A - standardMatrix3 B := by
  ext i j
  simp [standardMatrix3_apply]

@[simp] lemma standardMatrix3_smul (t : ℝ) (A : L₃) :
    standardMatrix3 (t • A) = t • standardMatrix3 A := by
  ext i j
  simp [standardMatrix3_apply]

/-- Exact cofactor polynomial in dimension three. -/
lemma adjugate_transpose_one_add_smul_three (A : Matrix (Fin 3) (Fin 3) ℝ) (t : ℝ) :
    (1 + t • A).adjugate.transpose =
      1 + t • (A.trace • 1 - A.transpose) + t ^ 2 • A.adjugate.transpose := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [Matrix.adjugate_fin_three, Matrix.trace, Fin.sum_univ_three] <;> ring

/-- Exact determinant polynomial in dimension three. -/
lemma det_one_add_smul_three (A : Matrix (Fin 3) (Fin 3) ℝ) (t : ℝ) :
    (1 + t • A).det = 1 + t * A.trace + t ^ 2 * A.adjugate.transpose.trace + t ^ 3 * A.det := by
  simp [Matrix.det_fin_three, Matrix.adjugate_fin_three, Matrix.trace, Fin.sum_univ_three]
  ring

/-- Linear cofactor term, with transpose expressed intrinsically as the real adjoint. -/
def cofactorLinearTerm3 (A : L₃) : L₃ :=
  (standardMatrix3 A).trace • ContinuousLinearMap.id ℝ E₃ - A.adjoint

lemma cofactor3_id_add_smul (A : L₃) (t : ℝ) :
    cofactor3 (ContinuousLinearMap.id ℝ E₃ + t • A) =
      ContinuousLinearMap.id ℝ E₃ + t • cofactorLinearTerm3 A + t ^ 2 • cofactor3 A := by
  apply standardMatrix3_injective
  simp only [standardMatrix3_cofactor3, standardMatrix3_add, standardMatrix3_id,
    standardMatrix3_smul, cofactorLinearTerm3, standardMatrix3_sub, standardMatrix3_adjoint]
  exact adjugate_transpose_one_add_smul_three _ _

lemma det_id_add_smul_three (A : L₃) (t : ℝ) :
    (ContinuousLinearMap.id ℝ E₃ + t • A).det =
      1 + t * (standardMatrix3 A).trace + t ^ 2 * (standardMatrix3 (cofactor3 A)).trace +
        t ^ 3 * A.det := by
  rw [← standardMatrix3_det, standardMatrix3_add, standardMatrix3_id, standardMatrix3_smul,
    det_one_add_smul_three, standardMatrix3_cofactor3, standardMatrix3_det]

lemma standardMatrix3_fderiv_trace (X : E₃ → E₃) (x : E₃) :
    (standardMatrix3 (fderiv ℝ X x)).trace = divergenceN X x := rfl

/-- Exact cofactor expansion for the derivative of the actual straight perturbation. -/
lemma cofactor3_fderiv_straightPerturbation {X : E₃ → E₃} {x : E₃}
    (hX : DifferentiableAt ℝ X x) (t : ℝ) :
    cofactor3 (fderiv ℝ (straightPerturbation X t) x) =
      ContinuousLinearMap.id ℝ E₃ + t •
        (divergenceN X x • ContinuousLinearMap.id ℝ E₃ - (fderiv ℝ X x).adjoint) +
      t ^ 2 • cofactor3 (fderiv ℝ X x) := by
  rw [fderiv_straightPerturbation hX t, cofactor3_id_add_smul]
  rfl

/-- Exact determinant expansion for the derivative of the actual straight perturbation. -/
lemma det_fderiv_straightPerturbation {X : E₃ → E₃} {x : E₃}
    (hX : DifferentiableAt ℝ X x) (t : ℝ) :
    (fderiv ℝ (straightPerturbation X t) x).det =
      1 + t * divergenceN X x + t ^ 2 * (standardMatrix3 (cofactor3 (fderiv ℝ X x))).trace +
        t ^ 3 * (fderiv ℝ X x).det := by
  rw [fderiv_straightPerturbation hX t, det_id_add_smul_three, standardMatrix3_fderiv_trace]

/-- A uniform quadratic estimate for the norm at every unit vector. -/
lemma abs_norm_add_sub_one_sub_inner_le_sq {E : Type*} [NormedAddCommGroup E]
    [InnerProductSpace ℝ E] {ν : E} (hν : ‖ν‖ = 1) (w : E) :
    |‖ν + w‖ - 1 - inner ℝ ν w| ≤ ‖w‖ ^ 2 := by
  have hs := norm_add_sq_real ν w
  rw [hν] at hs
  have hlow := real_inner_le_norm ν (ν + w)
  simp only [inner_add_right, real_inner_self_eq_norm_sq, hν, one_pow, one_mul] at hlow
  rw [abs_of_nonneg (by linarith)]
  nlinarith [sq_nonneg (‖ν + w‖ - 1), sq_nonneg ‖w‖]

/-- The cofactor linear term paired with a unit normal is tangential divergence. -/
lemma inner_cofactorLinearTerm3 (A : L₃) {ν : E₃} (hν : ‖ν‖ = 1) :
    inner ℝ ν (cofactorLinearTerm3 A ν) =
      (standardMatrix3 A).trace - inner ℝ ν (A ν) := by
  simp only [cofactorLinearTerm3, _root_.sub_apply, _root_.smul_apply,
    ContinuousLinearMap.id_apply, inner_sub_right, real_inner_smul_right,
    real_inner_self_eq_norm_sq, hν, one_pow, mul_one]
  rw [A.adjoint_inner_right, real_inner_comm]

/-- The cofactor error after its linear term is exactly quadratic. -/
lemma norm_cofactor3_id_add_smul_remainder (A : L₃) (t : ℝ) :
    ‖cofactor3 (ContinuousLinearMap.id ℝ E₃ + t • A) -
      (ContinuousLinearMap.id ℝ E₃ + t • cofactorLinearTerm3 A)‖ = t ^ 2 * ‖cofactor3 A‖ := by
  rw [cofactor3_id_add_smul, add_sub_cancel_left, norm_smul,
    Real.norm_of_nonneg (sq_nonneg t)]

/-- The determinant's quadratic error, uniformly for `|t| ≤ 1`. -/
lemma abs_det_id_add_smul_remainder_le (A : L₃) {t : ℝ} (ht : |t| ≤ 1) :
    |(ContinuousLinearMap.id ℝ E₃ + t • A).det - 1 - t * (standardMatrix3 A).trace| ≤
      t ^ 2 * (|(standardMatrix3 (cofactor3 A)).trace| + |A.det|) := by
  rw [det_id_add_smul_three]
  have heq : 1 + t * (standardMatrix3 A).trace +
      t ^ 2 * (standardMatrix3 (cofactor3 A)).trace + t ^ 3 * A.det - 1 -
      t * (standardMatrix3 A).trace =
      t ^ 2 * ((standardMatrix3 (cofactor3 A)).trace + t * A.det) := by ring
  rw [heq, abs_mul, abs_of_nonneg (sq_nonneg t)]
  apply mul_le_mul_of_nonneg_left _ (sq_nonneg t)
  calc
    _ ≤ |(standardMatrix3 (cofactor3 A)).trace| + |t * A.det| := abs_add_le _ _
    _ ≤ _ := by rw [abs_mul]; nlinarith [abs_nonneg A.det]

/-- A quantitative surface-Jacobian expansion, uniform in the unit normal. -/
lemma abs_norm_cofactor3_id_add_smul_remainder_le (A : L₃) {t : ℝ} (ht : |t| ≤ 1)
    {ν : E₃} (hν : ‖ν‖ = 1) :
    |‖cofactor3 (ContinuousLinearMap.id ℝ E₃ + t • A) ν‖ - 1 -
      t * ((standardMatrix3 A).trace - inner ℝ ν (A ν))| ≤
      t ^ 2 * ((‖cofactorLinearTerm3 A‖ + ‖cofactor3 A‖) ^ 2 + ‖cofactor3 A‖) := by
  let w := t • cofactorLinearTerm3 A ν + t ^ 2 • cofactor3 A ν
  have hb : ‖cofactorLinearTerm3 A ν‖ ≤ ‖cofactorLinearTerm3 A‖ := by
    simpa only [hν, mul_one] using (cofactorLinearTerm3 A).le_opNorm ν
  have hc : ‖cofactor3 A ν‖ ≤ ‖cofactor3 A‖ := by
    simpa only [hν, mul_one] using (cofactor3 A).le_opNorm ν
  have htsq : t ^ 2 ≤ |t| := by
    nlinarith [sq_abs t, mul_nonneg (abs_nonneg t) (sub_nonneg.mpr ht)]
  have hw : ‖w‖ ≤ |t| * (‖cofactorLinearTerm3 A‖ + ‖cofactor3 A‖) := by
    calc
      _ ≤ ‖t • cofactorLinearTerm3 A ν‖ + ‖t ^ 2 • cofactor3 A ν‖ := norm_add_le _ _
      _ = |t| * ‖cofactorLinearTerm3 A ν‖ + t ^ 2 * ‖cofactor3 A ν‖ := by
        rw [norm_smul, norm_smul, Real.norm_eq_abs, Real.norm_of_nonneg (sq_nonneg t)]
      _ ≤ |t| * ‖cofactorLinearTerm3 A‖ + t ^ 2 * ‖cofactor3 A‖ := by gcongr
      _ ≤ _ := by nlinarith [mul_le_mul_of_nonneg_right htsq (norm_nonneg (cofactor3 A))]
  have hinner : |inner ℝ ν (cofactor3 A ν)| ≤ ‖cofactor3 A‖ := by
    calc
      _ ≤ ‖cofactor3 A ν‖ := by
        simpa only [hν, one_mul] using (abs_real_inner_le_norm ν (cofactor3 A ν))
      _ ≤ _ := hc
  have hnorm := abs_norm_add_sub_one_sub_inner_le_sq hν w
  have heq : cofactor3 (ContinuousLinearMap.id ℝ E₃ + t • A) ν = ν + w := by
    simp [cofactor3_id_add_smul, w, add_assoc]
  have hi : inner ℝ ν w = t * ((standardMatrix3 A).trace - inner ℝ ν (A ν)) +
      t ^ 2 * inner ℝ ν (cofactor3 A ν) := by
    simp only [w, inner_add_right, real_inner_smul_right, inner_cofactorLinearTerm3 A hν]
  rw [heq]
  calc
    _ = |(‖ν + w‖ - 1 - inner ℝ ν w) + t ^ 2 * inner ℝ ν (cofactor3 A ν)| := by
      congr 1
      linarith [hi]
    _ ≤ |‖ν + w‖ - 1 - inner ℝ ν w| + |t ^ 2 * inner ℝ ν (cofactor3 A ν)| := abs_add_le _ _
    _ ≤ ‖w‖ ^ 2 + t ^ 2 * ‖cofactor3 A‖ := by
      rw [abs_mul, abs_of_nonneg (sq_nonneg t)]
      gcongr
    _ ≤ (|t| * (‖cofactorLinearTerm3 A‖ + ‖cofactor3 A‖)) ^ 2 +
        t ^ 2 * ‖cofactor3 A‖ := by gcongr
    _ = _ := by rw [mul_pow, sq_abs]; ring

/-- The standard coordinate map as a linear equivalence. -/
def standardMatrix3Equiv : L₃ ≃ₗ[ℝ] Matrix (Fin 3) (Fin 3) ℝ :=
  (LinearMap.toContinuousLinearMap : (E₃ →ₗ[ℝ] E₃) ≃ₗ[ℝ] L₃).symm.trans
    Matrix.toEuclideanLin.symm

lemma continuous_standardMatrix3 : Continuous standardMatrix3 :=
  standardMatrix3Equiv.toContinuousLinearEquiv.continuous

lemma continuous_cofactor3 : Continuous cofactor3 := by
  exact standardMatrix3Equiv.symm.toContinuousLinearEquiv.continuous.comp
    continuous_standardMatrix3.matrix_adjugate.matrix_transpose

lemma continuous_cofactorLinearTerm3 : Continuous cofactorLinearTerm3 := by
  exact (continuous_standardMatrix3.matrix_trace.smul continuous_const).sub
    ContinuousLinearMap.adjoint.continuous

/-- On every bounded operator ball, all three quadratic remainder coefficients have
one finite common bound. -/
lemma exists_uniform_straight_remainder_bound (M : ℝ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ A : L₃, ‖A‖ ≤ M →
      ‖cofactor3 A‖ ≤ C ∧
      |(standardMatrix3 (cofactor3 A)).trace| + |A.det| ≤ C ∧
      (‖cofactorLinearTerm3 A‖ + ‖cofactor3 A‖) ^ 2 + ‖cofactor3 A‖ ≤ C := by
  let R (A : L₃) := ‖cofactor3 A‖ + |(standardMatrix3 (cofactor3 A)).trace| + |A.det| +
    (‖cofactorLinearTerm3 A‖ + ‖cofactor3 A‖) ^ 2
  have hR : Continuous R := by
    exact ((continuous_cofactor3.norm.add
      (continuous_standardMatrix3.comp continuous_cofactor3).matrix_trace.abs).add
      ContinuousLinearMap.continuous_det.abs).add
      ((continuous_cofactorLinearTerm3.norm.add continuous_cofactor3.norm).pow 2)
  obtain ⟨C, hC⟩ := (isCompact_closedBall (0 : L₃) M).exists_bound_of_continuousOn hR.continuousOn
  refine ⟨max C 0, le_max_right _ _, fun A hA => ?_⟩
  have hRA := hC A (by simpa only [Metric.mem_closedBall, dist_zero_right] using hA)
  have hRpos : 0 ≤ R A := by dsimp [R]; positivity
  rw [Real.norm_of_nonneg hRpos] at hRA
  have hCM := le_max_left C 0
  dsimp [R] at hRA
  constructor
  · nlinarith [abs_nonneg ((standardMatrix3 (cofactor3 A)).trace), abs_nonneg A.det,
      sq_nonneg (‖cofactorLinearTerm3 A‖ + ‖cofactor3 A‖)]
  constructor
  · nlinarith [norm_nonneg (cofactor3 A), sq_nonneg (‖cofactorLinearTerm3 A‖ + ‖cofactor3 A‖)]
  · nlinarith [abs_nonneg ((standardMatrix3 (cofactor3 A)).trace), abs_nonneg A.det]

/-- Uniform quadratic remainders for every operator in a bounded ball and every unit normal. -/
theorem uniform_straight_expansion_on_operator_ball (M : ℝ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ A : L₃, ‖A‖ ≤ M → ∀ t : ℝ, |t| ≤ 1 →
      ‖cofactor3 (ContinuousLinearMap.id ℝ E₃ + t • A) -
        (ContinuousLinearMap.id ℝ E₃ + t • cofactorLinearTerm3 A)‖ ≤ C * t ^ 2 ∧
      |(ContinuousLinearMap.id ℝ E₃ + t • A).det - 1 - t * (standardMatrix3 A).trace| ≤
        C * t ^ 2 ∧
      ∀ ν : E₃, ‖ν‖ = 1 →
        |‖cofactor3 (ContinuousLinearMap.id ℝ E₃ + t • A) ν‖ - 1 -
          t * ((standardMatrix3 A).trace - inner ℝ ν (A ν))| ≤ C * t ^ 2 := by
  obtain ⟨C, hC, hbound⟩ := exists_uniform_straight_remainder_bound M
  refine ⟨C, hC, fun A hA t ht => ?_⟩
  obtain ⟨hc, hd, hj⟩ := hbound A hA
  have hmul (a : ℝ) (ha : a ≤ C) : t ^ 2 * a ≤ C * t ^ 2 := by
    nlinarith [mul_le_mul_of_nonneg_left ha (sq_nonneg t)]
  refine ⟨?_, (abs_det_id_add_smul_remainder_le A ht).trans (hmul _ hd), ?_⟩
  · rw [norm_cofactor3_id_add_smul_remainder]
    exact hmul _ hc
  · intro ν hν
    exact (abs_norm_cofactor3_id_add_smul_remainder_le A ht hν).trans (hmul _ hj)

/-- Blueprint `lem:straight-cofactor`: the cofactor, determinant, and unit-normal
Jacobian all have quadratic remainders with one constant, uniform over all positions. -/
theorem exists_uniform_straight_cofactor_expansion {X : E₃ → E₃}
    (hXC : ContDiff ℝ 1 X) (hXc : HasCompactSupport X) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ t : ℝ, |t| ≤ 1 → ∀ x : E₃,
      ‖cofactor3 (fderiv ℝ (straightPerturbation X t) x) -
        (ContinuousLinearMap.id ℝ E₃ + t •
          (divergenceN X x • ContinuousLinearMap.id ℝ E₃ - (fderiv ℝ X x).adjoint))‖ ≤
        C * t ^ 2 ∧
      |(fderiv ℝ (straightPerturbation X t) x).det - 1 - t * divergenceN X x| ≤ C * t ^ 2 ∧
      ∀ ν : E₃, ‖ν‖ = 1 →
        |‖cofactor3 (fderiv ℝ (straightPerturbation X t) x) ν‖ - 1 -
          t * (divergenceN X x - inner ℝ ν (fderiv ℝ X x ν))| ≤ C * t ^ 2 := by
  obtain ⟨C, hC, hbound⟩ :=
    uniform_straight_expansion_on_operator_ball ‖straightDerivativeField hXC hXc‖
  refine ⟨C, hC, fun t ht x => ?_⟩
  simpa only [fderiv_straightPerturbation (hXC.differentiable (by simp) x) t,
    cofactorLinearTerm3, standardMatrix3_fderiv_trace] using
    hbound (fderiv ℝ X x) (norm_fderiv_le_straightDerivativeField hXC hXc x) t ht

/-- The same bound for the actual Jacobian on a normal plane in any isometric coordinates. -/
theorem exists_uniform_straight_plane_jacobian_expansion {X : E₃ → E₃}
    (hXC : ContDiff ℝ 1 X) (hXc : HasCompactSupport X) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ t : ℝ, |t| ≤ 1 → ∀ x ν : E₃, ‖ν‖ = 1 →
      ∀ e : EuclideanSpace ℝ (Fin 2) ≃ₗᵢ[ℝ] (ℝ ∙ ν)ᗮ,
        |jacobian2Linear ((fderiv ℝ (straightPerturbation X t) x).comp
          (normalPlaneInclusion ν e).toContinuousLinearMap) - 1 -
            t * (divergenceN X x - inner ℝ ν (fderiv ℝ X x ν))| ≤ C * t ^ 2 := by
  obtain ⟨C, hC, hbound⟩ := exists_uniform_straight_cofactor_expansion hXC hXc
  refine ⟨C, hC, fun t ht x ν hν e => ?_⟩
  rw [jacobian2Linear_normalPlane _ hν e]
  exact (hbound t ht x).2.2 ν hν

/-- The first-order plane-Jacobian error is `o(t)` uniformly in position, unit normal,
and isometric coordinates on the plane. The quantifiers make the uniformity explicit. -/
theorem straight_plane_jacobian_uniform_littleO {X : E₃ → E₃}
    (hXC : ContDiff ℝ 1 X) (hXc : HasCompactSupport X) :
    ∀ ε : ℝ, 0 < ε → ∃ δ : ℝ, 0 < δ ∧ ∀ t : ℝ, |t| < δ →
      ∀ x ν : E₃, ‖ν‖ = 1 → ∀ e : EuclideanSpace ℝ (Fin 2) ≃ₗᵢ[ℝ] (ℝ ∙ ν)ᗮ,
        |jacobian2Linear ((fderiv ℝ (straightPerturbation X t) x).comp
          (normalPlaneInclusion ν e).toContinuousLinearMap) - 1 -
            t * (divergenceN X x - inner ℝ ν (fderiv ℝ X x ν))| ≤ ε * |t| := by
  obtain ⟨C, hC, hbound⟩ := exists_uniform_straight_plane_jacobian_expansion hXC hXc
  intro ε hε
  refine ⟨min 1 (ε / (C + 1)), lt_min zero_lt_one (div_pos hε (by linarith)), ?_⟩
  intro t ht x ν hν e
  have ht1 : |t| ≤ 1 := (ht.trans_le (min_le_left _ _)).le
  have htε : |t| * (C + 1) < ε :=
    (lt_div_iff₀ (by linarith : 0 < C + 1)).mp (ht.trans_le (min_le_right _ _))
  apply (hbound t ht1 x ν hν e).trans
  have hmul := mul_le_mul_of_nonneg_right htε.le (abs_nonneg t)
  nlinarith [sq_abs t, sq_nonneg t]

end LiquidDrop

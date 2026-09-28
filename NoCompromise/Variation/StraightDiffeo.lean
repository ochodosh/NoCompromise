import NoCompromise.Conventions
import Mathlib.Analysis.Calculus.ContDiff.RCLike
import Mathlib.Analysis.Calculus.ContDiff.Operations
import Mathlib.Analysis.Calculus.InverseFunctionTheorem.ApproximatesLinearOn
import Mathlib.Analysis.SpecificLimits.Normed
import Mathlib.Topology.ContinuousMap.BoundedCompactlySupported

/-!
# Straight perturbations are global diffeomorphisms

For a Lipschitz vector field `X`, the map `x ↦ x + t • X x` is a global
homeomorphism when `|t|` times its Lipschitz constant is smaller than one.
A continuously differentiable field gives a continuously differentiable inverse.
The compactly supported three-dimensional specialization matches the blueprint.
-/

noncomputable section

open Set Function
open scoped NNReal Topology

namespace LiquidDrop

set_option maxSynthPendingDepth 8

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

/-- The straight perturbation by a vector field. -/
def straightPerturbation (X : E → E) (t : ℝ) (x : E) : E := x + t • X x

@[simp] lemma straightPerturbation_zero (X : E → E) : straightPerturbation X 0 = id := by
  funext x
  simp [straightPerturbation]

/-- A straight perturbation agrees with the identity wherever the field vanishes. -/
lemma straightPerturbation_eq_self {X : E → E} (t : ℝ) {x : E} (hx : X x = 0) :
    straightPerturbation X t x = x := by simp [straightPerturbation, hx]

lemma straightPerturbation_eq_self_of_notMem_tsupport (X : E → E) (t : ℝ) {x : E}
    (hx : x ∉ tsupport X) : straightPerturbation X t x = x :=
  straightPerturbation_eq_self t (image_eq_zero_of_notMem_tsupport hx)

/-- The sharp lower distance estimate. -/
lemma norm_sub_straightPerturbation_ge {X : E → E} {L : ℝ≥0} (hX : LipschitzWith L X)
    (t : ℝ) (x y : E) :
    (1 - |t| * L) * ‖x - y‖ ≤ ‖straightPerturbation X t x - straightPerturbation X t y‖ := by
  have heq : straightPerturbation X t x - straightPerturbation X t y =
      (x - y) + t • (X x - X y) := by simp only [straightPerturbation, smul_sub]; abel
  rw [heq]
  have htri := norm_sub_norm_le (x - y) (-t • (X x - X y))
  have hbound := hX.norm_sub_le x y
  simp only [neg_smul, norm_neg, norm_smul, Real.norm_eq_abs, sub_neg_eq_add] at htri
  nlinarith [mul_le_mul_of_nonneg_left hbound (abs_nonneg t)]

/-- The perturbation differs from the identity by a map with Lipschitz constant `|t| L`. -/
lemma straightPerturbation_approximatesLinearOn {X : E → E} {L : ℝ≥0}
    (hX : LipschitzWith L X) (t : ℝ) :
    ApproximatesLinearOn (straightPerturbation X t) (ContinuousLinearMap.id ℝ E)
      univ (‖t‖₊ * L) := by
  intro x _ y _
  have heq : straightPerturbation X t x - straightPerturbation X t y - (x - y) =
      t • (X x - X y) := by simp only [straightPerturbation, smul_sub]; abel
  simp only [ContinuousLinearMap.id_apply, heq, norm_smul, NNReal.coe_mul,
    coe_nnnorm, Real.norm_eq_abs]
  exact (mul_le_mul_of_nonneg_left (hX.norm_sub_le x y) (abs_nonneg t)).trans_eq
    (mul_assoc _ _ _).symm

lemma lipschitzWith_straightPerturbation {X : E → E} {L : ℝ≥0}
    (hX : LipschitzWith L X) (t : ℝ) :
    LipschitzWith (1 + ‖t‖₊ * L) (straightPerturbation X t) := by
  apply LipschitzWith.of_dist_le_mul
  intro x y
  rw [dist_eq_norm, dist_eq_norm]
  have heq : straightPerturbation X t x - straightPerturbation X t y =
      (x - y) + t • (X x - X y) := by simp only [straightPerturbation, smul_sub]; abel
  rw [heq]
  calc
    _ ≤ ‖x - y‖ + ‖t • (X x - X y)‖ := norm_add_le _ _
    _ ≤ ‖x - y‖ + |t| * (L * ‖x - y‖) := by
      rw [norm_smul, Real.norm_eq_abs]
      gcongr
      exact hX.norm_sub_le x y
    _ = _ := by simp only [NNReal.coe_add, NNReal.coe_one, NNReal.coe_mul,
      coe_nnnorm, Real.norm_eq_abs]; ring

/-- The lower distance estimate in inverse Lipschitz form. -/
lemma antilipschitzWith_straightPerturbation {X : E → E} {L : ℝ≥0}
    (hX : LipschitzWith L X) {t : ℝ} (ht : |t| * L < 1) :
    AntilipschitzWith (1 - ‖t‖₊ * L)⁻¹ (straightPerturbation X t) := by
  have hsmall : ‖t‖₊ * L ≤ 1 := by
    apply NNReal.coe_le_coe.mp
    simpa only [NNReal.coe_mul, NNReal.coe_one, coe_nnnorm, Real.norm_eq_abs] using ht.le
  apply AntilipschitzWith.of_le_mul_dist
  intro x y
  simp only [dist_eq_norm, NNReal.coe_inv, NNReal.coe_sub hsmall, NNReal.coe_one,
    NNReal.coe_mul, coe_nnnorm, Real.norm_eq_abs]
  exact (le_inv_mul_iff₀ (sub_pos.mpr ht)).mpr (norm_sub_straightPerturbation_ge hX t x y)

lemma hasFDerivAt_straightPerturbation {X : E → E} {x : E} {X' : E →L[ℝ] E}
    (hX : HasFDerivAt X X' x) (t : ℝ) :
    HasFDerivAt (straightPerturbation X t) (ContinuousLinearMap.id ℝ E + t • X') x :=
  (hasFDerivAt_id x).add (hX.const_smul t)

lemma fderiv_straightPerturbation {X : E → E} {x : E} (hX : DifferentiableAt ℝ X x)
    (t : ℝ) : fderiv ℝ (straightPerturbation X t) x =
      ContinuousLinearMap.id ℝ E + t • fderiv ℝ X x :=
  (hasFDerivAt_straightPerturbation hX.hasFDerivAt t).fderiv

lemma contDiff_straightPerturbation {X : E → E} {n : WithTop ℕ∞}
    (hX : ContDiff ℝ n X) (t : ℝ) : ContDiff ℝ n (straightPerturbation X t) :=
  contDiff_id.add (hX.const_smul t)

section Complete

variable [CompleteSpace E] [Nontrivial E]

/-- The global homeomorphism associated with a small straight perturbation.
Surjectivity follows from the contraction argument in `ApproximatesLinearOn`. -/
def straightPerturbationHomeomorph {X : E → E} {L : ℝ≥0} (hX : LipschitzWith L X)
    {t : ℝ} (ht : |t| * L < 1) : E ≃ₜ E :=
  (straightPerturbation_approximatesLinearOn hX t).toHomeomorph
    (f' := ContinuousLinearEquiv.refl ℝ E) (straightPerturbation X t) (.inr (by
      have h : ‖t‖₊ * L < 1 := by
        apply NNReal.coe_lt_coe.mp
        simpa only [NNReal.coe_mul, NNReal.coe_one, coe_nnnorm, Real.norm_eq_abs] using ht
      simpa using h))

@[simp] lemma straightPerturbationHomeomorph_apply {X : E → E} {L : ℝ≥0}
    (hX : LipschitzWith L X) {t : ℝ} (ht : |t| * L < 1) (x : E) :
    straightPerturbationHomeomorph hX ht x = straightPerturbation X t x := rfl

lemma straightPerturbation_bijective {X : E → E} {L : ℝ≥0} (hX : LipschitzWith L X)
    {t : ℝ} (ht : |t| * L < 1) : Bijective (straightPerturbation X t) :=
  (straightPerturbationHomeomorph hX ht).bijective

/-- The inverse has Lipschitz constant at most `(1 - |t| L)⁻¹`. -/
lemma lipschitzWith_symm_straightPerturbationHomeomorph {X : E → E} {L : ℝ≥0}
    (hX : LipschitzWith L X) {t : ℝ} (ht : |t| * L < 1) :
    LipschitzWith (1 - ‖t‖₊ * L)⁻¹ (straightPerturbationHomeomorph hX ht).symm :=
  (antilipschitzWith_straightPerturbation hX ht).to_rightInverse
    (straightPerturbationHomeomorph hX ht).apply_symm_apply

lemma symm_straightPerturbationHomeomorph_eq_self_of_notMem_tsupport
    {X : E → E} {L : ℝ≥0} (hX : LipschitzWith L X) {t : ℝ} (ht : |t| * L < 1)
    {x : E} (hx : x ∉ tsupport X) : (straightPerturbationHomeomorph hX ht).symm x = x := by
  have hfix : straightPerturbationHomeomorph hX ht x = x :=
    straightPerturbation_eq_self_of_notMem_tsupport X t hx
  calc
    _ = (straightPerturbationHomeomorph hX ht).symm
        (straightPerturbationHomeomorph hX ht x) := by rw [hfix]
    _ = x := (straightPerturbationHomeomorph hX ht).symm_apply_apply x

omit [Nontrivial E] in
/-- Neumann's series makes the derivative of a small straight perturbation invertible. -/
lemma isUnit_straightPerturbation_derivative {X : E → E} {L : ℝ≥0}
    (hX : LipschitzWith L X) {t : ℝ} (ht : |t| * L < 1) (x : E) :
    IsUnit (ContinuousLinearMap.id ℝ E + t • fderiv ℝ X x) := by
  have hnorm : ‖-(t • fderiv ℝ X x)‖ < 1 := by
    rw [norm_neg, norm_smul, Real.norm_eq_abs]
    exact (mul_le_mul_of_nonneg_left (norm_fderiv_le_of_lipschitz ℝ hX)
      (abs_nonneg t)).trans_lt ht
  convert! isUnit_one_sub_of_norm_lt_one hnorm using 1
  · simp [ContinuousLinearMap.one_def]

/-- The derivative regarded as a continuous linear equivalence. -/
def straightPerturbationDerivativeEquiv {X : E → E} {L : ℝ≥0} (hX : LipschitzWith L X)
    {t : ℝ} (ht : |t| * L < 1) (x : E) : E ≃L[ℝ] E :=
  ContinuousLinearEquiv.ofUnit (isUnit_straightPerturbation_derivative hX ht x).unit

omit [Nontrivial E] in
@[simp] lemma coe_straightPerturbationDerivativeEquiv {X : E → E} {L : ℝ≥0}
    (hX : LipschitzWith L X) {t : ℝ} (ht : |t| * L < 1) (x : E) :
    (straightPerturbationDerivativeEquiv hX ht x : E →L[ℝ] E) =
      ContinuousLinearMap.id ℝ E + t • fderiv ℝ X x :=
  (isUnit_straightPerturbation_derivative hX ht x).unit_spec

/-- The inverse of a small `Cⁿ` straight perturbation is `Cⁿ`. -/
lemma contDiff_symm_straightPerturbationHomeomorph {X : E → E} {L : ℝ≥0}
    (hX : LipschitzWith L X) {n : WithTop ℕ∞} (hXC : ContDiff ℝ n X) (hn : n ≠ 0)
    {t : ℝ} (ht : |t| * L < 1) :
    ContDiff ℝ n (straightPerturbationHomeomorph hX ht).symm := by
  apply (straightPerturbationHomeomorph hX ht).contDiff_symm
    (f₀' := straightPerturbationDerivativeEquiv hX ht)
  · intro x
    change HasFDerivAt (straightPerturbation X t)
      (straightPerturbationDerivativeEquiv hX ht x : E →L[ℝ] E) x
    rw [coe_straightPerturbationDerivativeEquiv]
    exact hasFDerivAt_straightPerturbation ((hXC.differentiable hn) x).hasFDerivAt t
  · exact contDiff_straightPerturbation hXC t

/-- The derivative of the inverse is the inverse of `I + t DX` at the inverse image. -/
lemma hasFDerivAt_symm_straightPerturbationHomeomorph {X : E → E} {L : ℝ≥0}
    (hX : LipschitzWith L X) (hXD : Differentiable ℝ X) {t : ℝ} (ht : |t| * L < 1)
    (y : E) :
    HasFDerivAt (straightPerturbationHomeomorph hX ht).symm
      ((straightPerturbationDerivativeEquiv hX ht
        ((straightPerturbationHomeomorph hX ht).symm y)).symm : E →L[ℝ] E) y := by
  apply (straightPerturbationHomeomorph hX ht).toOpenPartialHomeomorph.hasFDerivAt_symm
    (f' := straightPerturbationDerivativeEquiv hX ht
      ((straightPerturbationHomeomorph hX ht).symm y)) (mem_univ y)
  rw [coe_straightPerturbationDerivativeEquiv]
  exact hasFDerivAt_straightPerturbation (hXD _).hasFDerivAt t

/-- A diffeomorphism statement with the actual map and both regularity claims explicit. -/
theorem straightPerturbation_diffeomorphism {X : E → E} {L : ℝ≥0}
    (hX : LipschitzWith L X) (hXC : ContDiff ℝ 1 X) {t : ℝ} (ht : |t| * L < 1) :
    ∃ F : E ≃ₜ E, (∀ x, F x = straightPerturbation X t x) ∧
      ContDiff ℝ 1 F ∧ ContDiff ℝ 1 F.symm ∧
      ∀ x, fderiv ℝ F x = ContinuousLinearMap.id ℝ E + t • fderiv ℝ X x ∧
        IsUnit (fderiv ℝ F x) := by
  refine ⟨straightPerturbationHomeomorph hX ht, fun _ => rfl,
    contDiff_straightPerturbation hXC t,
    contDiff_symm_straightPerturbationHomeomorph hX hXC (by simp) ht, ?_⟩
  intro x
  change fderiv ℝ (straightPerturbation X t) x = _ ∧
    IsUnit (fderiv ℝ (straightPerturbation X t) x)
  rw [fderiv_straightPerturbation (hXC.differentiable (by simp) x) t]
  exact ⟨rfl, isUnit_straightPerturbation_derivative hX ht x⟩

/-- The same theorem from a uniform derivative bound, via the mean value theorem. -/
theorem straightPerturbation_diffeomorphism_of_fderiv_bound {X : E → E} {L : ℝ≥0}
    (hXC : ContDiff ℝ 1 X) (hL : ∀ x, ‖fderiv ℝ X x‖ ≤ L)
    {t : ℝ} (ht : |t| * L < 1) :
    ∃ F : E ≃ₜ E, (∀ x, F x = straightPerturbation X t x) ∧
      ContDiff ℝ 1 F ∧ ContDiff ℝ 1 F.symm ∧
      ∀ x, fderiv ℝ F x = ContinuousLinearMap.id ℝ E + t • fderiv ℝ X x ∧
        IsUnit (fderiv ℝ F x) := by
  apply straightPerturbation_diffeomorphism (L := L) ?_ hXC ht
  exact lipschitzWith_of_nnnorm_fderiv_le (hXC.differentiable (by simp))
    (fun x => NNReal.coe_le_coe.mp (hL x))

end Complete

/-- The continuous derivative of a compactly supported `C¹` field, with its true sup norm. -/
def straightDerivativeField {X : E → E} (hXC : ContDiff ℝ 1 X) (hXc : HasCompactSupport X) :
    BoundedContinuousFunction E (E →L[ℝ] E) :=
  ofCompactSupport (fderiv ℝ X) (hXC.continuous_fderiv (by simp)) (hXc.fderiv ℝ)

@[simp] lemma straightDerivativeField_apply {X : E → E} (hXC : ContDiff ℝ 1 X)
    (hXc : HasCompactSupport X) (x : E) : straightDerivativeField hXC hXc x = fderiv ℝ X x := rfl

lemma norm_fderiv_le_straightDerivativeField {X : E → E} (hXC : ContDiff ℝ 1 X)
    (hXc : HasCompactSupport X) (x : E) :
    ‖fderiv ℝ X x‖ ≤ ‖straightDerivativeField hXC hXc‖ :=
  (straightDerivativeField hXC hXc).norm_coe_le_norm x

/-- A compactly supported `C¹` field is Lipschitz with constant `‖DX‖∞`. -/
lemma lipschitzWith_straightDerivativeField {X : E → E} (hXC : ContDiff ℝ 1 X)
    (hXc : HasCompactSupport X) : LipschitzWith ‖straightDerivativeField hXC hXc‖₊ X :=
  lipschitzWith_of_nnnorm_fderiv_le (hXC.differentiable (by simp))
    (fun x => NNReal.coe_le_coe.mp (norm_fderiv_le_straightDerivativeField hXC hXc x))

/-- The blueprint's three-dimensional compactly supported straight diffeomorphism,
using exactly the uniform norm of its continuous derivative. -/
theorem straightPerturbation_compactlySupported_diffeomorphism
    {X : EuclideanSpace ℝ (Fin 3) → EuclideanSpace ℝ (Fin 3)}
    (hXC : ContDiff ℝ 1 X) (hXc : HasCompactSupport X) {t : ℝ}
    (ht : |t| * ‖straightDerivativeField hXC hXc‖ < 1) :
    ∃ F : EuclideanSpace ℝ (Fin 3) ≃ₜ EuclideanSpace ℝ (Fin 3),
      (∀ x, F x = straightPerturbation X t x) ∧ ContDiff ℝ 1 F ∧ ContDiff ℝ 1 F.symm ∧
      (∀ x, fderiv ℝ F x = ContinuousLinearMap.id ℝ (EuclideanSpace ℝ (Fin 3)) +
        t • fderiv ℝ X x ∧ IsUnit (fderiv ℝ F x)) ∧
      (∀ x y, (1 - |t| * ‖straightDerivativeField hXC hXc‖) * ‖x - y‖ ≤ ‖F x - F y‖) ∧
      (∀ x ∉ tsupport X, F x = x ∧ F.symm x = x) := by
  let hX := lipschitzWith_straightDerivativeField hXC hXc
  obtain ⟨F, hF, hFC, hFiC, hFD⟩ := straightPerturbation_diffeomorphism hX hXC ht
  refine ⟨F, hF, hFC, hFiC, hFD, ?_, ?_⟩
  · intro x y
    rw [hF x, hF y]
    exact norm_sub_straightPerturbation_ge hX t x y
  · intro x hx
    have hfix : F x = x := (hF x).trans (straightPerturbation_eq_self_of_notMem_tsupport X t hx)
    refine ⟨hfix, ?_⟩
    calc
      F.symm x = F.symm (F x) := by rw [hfix]
      _ = x := F.symm_apply_apply x

end LiquidDrop

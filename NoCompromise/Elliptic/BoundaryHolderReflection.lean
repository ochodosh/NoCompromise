import NoCompromise.Elliptic.FrozenDecayLinear

/-!
# Reflection adapted to a frozen elliptic operator

The reflection fixes the boundary hyperplane and preserves the symmetric part
of the coefficient. No symmetry of the original coefficient is assumed.
-/

noncomputable section
open MeasureTheory Filter Metric Set InnerProductSpace
open scoped ENNReal NNReal Topology Gradient RealInnerProductSpace
namespace LiquidDrop

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]

/-- The oblique reflection associated with the frozen coefficient and a normal. -/
def boundaryFrozenReflection (A : E →L[ℝ] E) (n : E) : E →L[ℝ] E :=
  ContinuousLinearMap.id ℝ E -
    (2 / inner ℝ (frozenSymmetricPart A n) n) •
      ((innerSL ℝ n).smulRight (frozenSymmetricPart A n))

lemma boundaryFrozenReflection_apply (A : E →L[ℝ] E) (n x : E) :
    boundaryFrozenReflection A n x = x -
      (2 / inner ℝ (frozenSymmetricPart A n) n * inner ℝ n x) •
        frozenSymmetricPart A n := by
  simp [boundaryFrozenReflection, smul_smul]

lemma boundaryFrozenReflection_normal (A : E →L[ℝ] E) (n x : E)
    (hn : inner ℝ (frozenSymmetricPart A n) n ≠ 0) :
    inner ℝ n (boundaryFrozenReflection A n x) = -inner ℝ n x := by
  rw [boundaryFrozenReflection_apply, inner_sub_right, real_inner_smul_right,
    real_inner_comm n (frozenSymmetricPart A n)]
  field_simp [hn, real_inner_comm (frozenSymmetricPart A n) n]
  ring

lemma boundaryFrozenReflection_involutive (A : E →L[ℝ] E) (n : E)
    (hn : inner ℝ (frozenSymmetricPart A n) n ≠ 0) :
    Function.Involutive (boundaryFrozenReflection A n) := by
  intro x
  rw [boundaryFrozenReflection_apply, boundaryFrozenReflection_normal A n x hn,
    boundaryFrozenReflection_apply]
  module

lemma boundaryFrozenReflection_eq_self (A : E →L[ℝ] E) (n x : E)
    (hx : inner ℝ n x = 0) : boundaryFrozenReflection A n x = x := by
  simp [boundaryFrozenReflection_apply, hx]

lemma boundaryFrozenReflection_adjoint_apply (A : E →L[ℝ] E) (n x : E) :
    (boundaryFrozenReflection A n).adjoint x = x -
      (2 / inner ℝ (frozenSymmetricPart A n) n * inner ℝ (frozenSymmetricPart A n) x) • n := by
  apply ext_inner_left ℝ
  intro y
  rw [ContinuousLinearMap.adjoint_inner_right, boundaryFrozenReflection_apply]
  simp only [inner_sub_left, inner_sub_right, real_inner_smul_left, real_inner_smul_right]
  rw [real_inner_comm y n]
  ring

lemma boundaryFrozenReflection_intertwine (A : E →L[ℝ] E) (n x : E) :
    boundaryFrozenReflection A n (frozenSymmetricPart A x) =
      frozenSymmetricPart A ((boundaryFrozenReflection A n).adjoint x) := by
  rw [boundaryFrozenReflection_apply, boundaryFrozenReflection_adjoint_apply,
    map_sub, map_smul]
  have hs : inner ℝ (frozenSymmetricPart A n) x =
      inner ℝ n (frozenSymmetricPart A x) := frozenSymmetricPart_isSymmetric A n x
  rw [hs]

lemma boundaryFrozenReflection_preserves (A : E →L[ℝ] E) (n : E)
    (hn : inner ℝ (frozenSymmetricPart A n) n ≠ 0) :
    (boundaryFrozenReflection A n).comp ((frozenSymmetricPart A).comp
      (boundaryFrozenReflection A n).adjoint) = frozenSymmetricPart A := by
  ext x
  change boundaryFrozenReflection A n
    (frozenSymmetricPart A ((boundaryFrozenReflection A n).adjoint x)) = _
  rw [← boundaryFrozenReflection_intertwine]
  exact boundaryFrozenReflection_involutive A n hn _

/-- The adapted reflection is its own inverse as a continuous linear equivalence. -/
def boundaryFrozenReflectionEquiv (A : E →L[ℝ] E) (n : E)
    (hn : inner ℝ (frozenSymmetricPart A n) n ≠ 0) : E ≃L[ℝ] E :=
  { LinearEquiv.ofInvolutive (boundaryFrozenReflection A n).toLinearMap
      (boundaryFrozenReflection_involutive A n hn) with
    continuous_toFun := (boundaryFrozenReflection A n).continuous
    continuous_invFun := (boundaryFrozenReflection A n).continuous }

lemma boundaryFrozenReflectionEquiv_apply (A : E →L[ℝ] E) (n : E)
    (hn : inner ℝ (frozenSymmetricPart A n) n ≠ 0) (x : E) :
    boundaryFrozenReflectionEquiv A n hn x = boundaryFrozenReflection A n x := rfl

lemma boundaryFrozenReflectionEquiv_symm (A : E →L[ℝ] E) (n : E)
    (hn : inner ℝ (frozenSymmetricPart A n) n ≠ 0) :
    (boundaryFrozenReflectionEquiv A n hn).symm = boundaryFrozenReflectionEquiv A n hn := by
  ext x
  rfl

lemma boundaryFrozenReflection_det_abs [FiniteDimensional ℝ E]
    (A : E →L[ℝ] E) (n : E)
    (hn : inner ℝ (frozenSymmetricPart A n) n ≠ 0) :
    |LinearMap.det (boundaryFrozenReflection A n).toLinearMap| = 1 := by
  have hh : (boundaryFrozenReflection A n).toLinearMap.comp
      (boundaryFrozenReflection A n).toLinearMap = LinearMap.id := by
    ext x
    exact boundaryFrozenReflection_involutive A n hn x
  have hd := congrArg LinearMap.det hh
  rw [LinearMap.det_comp, LinearMap.det_id] at hd
  have ha := sq_abs (LinearMap.det (boundaryFrozenReflection A n).toLinearMap)
  nlinarith [abs_nonneg (LinearMap.det (boundaryFrozenReflection A n).toLinearMap)]

/-- The reflection and its inverse have a bound depending only on ellipticity. -/
lemma norm_boundaryFrozenReflection_le (A : E →L[ℝ] E) (n : E)
    (hn : ‖n‖ = 1) {lam cap : ℝ} (hlam : 0 < lam) (hcap : 0 ≤ cap)
    (hell : ∀ x, lam * ‖x‖ ^ 2 ≤ inner ℝ (A x) x) (hb : ‖A‖ ≤ cap) :
    ‖boundaryFrozenReflection A n‖ ≤ 1 + 2 * cap / lam := by
  have hβ : lam ≤ inner ℝ (frozenSymmetricPart A n) n := by
    rw [frozenSymmetricPart_inner]
    simpa [hn] using hell n
  have hβp : 0 < inner ℝ (frozenSymmetricPart A n) n := hlam.trans_le hβ
  have hSn : ‖frozenSymmetricPart A n‖ ≤ cap := by
    simpa [hn] using (frozenSymmetricPart A).le_opNorm n |>.trans
      (mul_le_mul_of_nonneg_right ((norm_frozenSymmetricPart_le A).trans hb) (norm_nonneg n))
  have hdiv : 2 / inner ℝ (frozenSymmetricPart A n) n ≤ 2 / lam :=
    div_le_div_of_nonneg_left (by norm_num) hlam hβ
  apply ContinuousLinearMap.opNorm_le_bound _ (by positivity)
  intro x
  have hi : |inner ℝ n x| ≤ ‖x‖ := by simpa [hn] using abs_real_inner_le_norm n x
  calc
    ‖boundaryFrozenReflection A n x‖ ≤ ‖x‖ +
        ‖(2 / inner ℝ (frozenSymmetricPart A n) n * inner ℝ n x) •
          frozenSymmetricPart A n‖ := by
      rw [boundaryFrozenReflection_apply]
      exact norm_sub_le _ _
    _ = ‖x‖ + (2 / inner ℝ (frozenSymmetricPart A n) n * |inner ℝ n x|) *
        ‖frozenSymmetricPart A n‖ := by
      rw [norm_smul, Real.norm_eq_abs, abs_mul, abs_of_pos (div_pos (by norm_num) hβp)]
    _ ≤ ‖x‖ + (2 / lam * ‖x‖) * cap := by
      gcongr
    _ = (1 + 2 * cap / lam) * ‖x‖ := by ring

lemma boundaryFrozenReflection_preimage_upper (A : E →L[ℝ] E) (n : E)
    (hn : inner ℝ (frozenSymmetricPart A n) n ≠ 0) :
    boundaryFrozenReflection A n ⁻¹' {x | 0 < inner ℝ n x} =
      {x | inner ℝ n x < 0} := by
  ext x
  simp only [mem_preimage, mem_ofPred_eq, boundaryFrozenReflection_normal A n x hn,
    neg_pos]

lemma boundaryFrozenReflection_preimage_lower (A : E →L[ℝ] E) (n : E)
    (hn : inner ℝ (frozenSymmetricPart A n) n ≠ 0) :
    boundaryFrozenReflection A n ⁻¹' {x | inner ℝ n x < 0} =
      {x | 0 < inner ℝ n x} := by
  ext x
  simp only [mem_preimage, mem_ofPred_eq, boundaryFrozenReflection_normal A n x hn,
    neg_lt_zero]

lemma boundaryFrozenReflection_inner (A : E →L[ℝ] E) (n x y : E)
    (hn : inner ℝ (frozenSymmetricPart A n) n ≠ 0) :
    inner ℝ (frozenSymmetricPart A ((boundaryFrozenReflection A n).adjoint x))
      ((boundaryFrozenReflection A n).adjoint y) =
        inner ℝ (frozenSymmetricPart A x) y := by
  rw [ContinuousLinearMap.adjoint_inner_right]
  have h := congrArg (fun B : E →L[ℝ] E => B x)
    (boundaryFrozenReflection_preserves A n hn)
  change boundaryFrozenReflection A n
    (frozenSymmetricPart A ((boundaryFrozenReflection A n).adjoint x)) = _ at h
  rw [h]

lemma boundaryFrozenReflection_measurePreserving {m : ℕ}
    (A : EuclideanSpace ℝ (Fin m) →L[ℝ] EuclideanSpace ℝ (Fin m))
    (n : EuclideanSpace ℝ (Fin m))
    (hn : inner ℝ (frozenSymmetricPart A n) n ≠ 0) :
    MeasurePreserving (boundaryFrozenReflection A n) volume volume := by
  refine ⟨(boundaryFrozenReflection A n).continuous.measurable, ?_⟩
  have hd := boundaryFrozenReflection_det_abs A n hn
  have hne : LinearMap.det (boundaryFrozenReflection A n).toLinearMap ≠ 0 := by
    intro he
    simp [he] at hd
  have hm := Measure.map_linearMap_addHaar_eq_smul_addHaar volume hne
  change Measure.map (boundaryFrozenReflection A n) volume = _ at hm
  simpa only [abs_inv, hd, inv_one, ENNReal.ofReal_one, one_smul] using hm

end LiquidDrop

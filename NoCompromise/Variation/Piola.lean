import NoCompromise.Area.Cofactor
import NoCompromise.BV.Defs
import Mathlib.Analysis.Calculus.FDeriv.Symmetric
import Mathlib.Analysis.Calculus.FDeriv.WithLp

/-!
# The local Piola identity

With the standard derivative matrix (output coordinates index rows) and
`cofactor3 = adjugate.transpose`, the divergence-free fields are the rows of
`cofactor3 (fderiv ℝ Φ)`, equivalently the columns of its transpose. The divergence
is the existing `divergenceN` convention. All analytic conclusions require only
local `C²` regularity; the open-domain endpoint uses `ContDiffOn ℝ 2`.

The proof expands the three-by-three minors and cancels mixed second derivatives.
The algebraic identity `DΦ * (cof DΦ)ᵀ = det(DΦ) I` needs no regularity or
invertibility assumption.
-/

noncomputable section

open Module Matrix
open scoped RealInnerProductSpace

namespace LiquidDrop

/-- Standard matrix entries are the coordinates of the images of standard basis vectors. -/
lemma standardMatrix3_apply
    (L : EuclideanSpace ℝ (Fin 3) →L[ℝ] EuclideanSpace ℝ (Fin 3)) (i j : Fin 3) :
    standardMatrix3 L i j = L (EuclideanSpace.single j (1 : ℝ)) i := rfl

/-- The standard matrix determinant is the linear-map determinant. -/
lemma standardMatrix3_det
    (L : EuclideanSpace ℝ (Fin 3) →L[ℝ] EuclideanSpace ℝ (Fin 3)) :
    (standardMatrix3 L).det = L.det := by
  exact LinearMap.det_toMatrix (EuclideanSpace.basisFun (Fin 3) ℝ).toBasis L.toLinearMap

/-- For real Euclidean spaces, the adjoint matrix is the transpose. -/
lemma standardMatrix3_adjoint
    (L : EuclideanSpace ℝ (Fin 3) →L[ℝ] EuclideanSpace ℝ (Fin 3)) :
    standardMatrix3 L.adjoint = (standardMatrix3 L).transpose := by
  ext i j
  simp only [standardMatrix3_apply, Matrix.transpose_apply]
  calc
    _ = inner ℝ (EuclideanSpace.single i (1 : ℝ))
        (L.adjoint (EuclideanSpace.single j (1 : ℝ))) := by
      simp [EuclideanSpace.inner_single_left]
    _ = inner ℝ (L (EuclideanSpace.single i (1 : ℝ)))
        (EuclideanSpace.single j (1 : ℝ)) := L.adjoint_inner_right _ _
    _ = _ := by simp [EuclideanSpace.inner_single_right]

/-- The algebraic Piola identity, including for singular maps. -/
lemma mul_cofactor3_transpose
    (L : EuclideanSpace ℝ (Fin 3) →L[ℝ] EuclideanSpace ℝ (Fin 3)) :
    standardMatrix3 L * (standardMatrix3 (cofactor3 L)).transpose =
      L.det • (1 : Matrix (Fin 3) (Fin 3) ℝ) := by
  rw [standardMatrix3_cofactor3, Matrix.transpose_transpose, Matrix.mul_adjugate,
    standardMatrix3_det]

/-- The algebraic Piola identity in continuous-linear-map form. -/
lemma comp_cofactor3_adjoint
    (L : EuclideanSpace ℝ (Fin 3) →L[ℝ] EuclideanSpace ℝ (Fin 3)) :
    L.comp (cofactor3 L).adjoint = L.det • ContinuousLinearMap.id ℝ _ := by
  suffices h : (L.comp (cofactor3 L).adjoint).toLinearMap =
      (L.det • ContinuousLinearMap.id ℝ _).toLinearMap by
    exact ContinuousLinearMap.ext (fun x => LinearMap.congr_fun h x)
  apply Matrix.toEuclideanLin.symm.injective
  change (Matrix.toLpLin 2 2).symm
    (L.toLinearMap.comp (cofactor3 L).adjoint.toLinearMap) =
      (Matrix.toLpLin 2 2).symm (L.det • LinearMap.id)
  rw [Matrix.toLpLin_symm_comp]
  change standardMatrix3 L * standardMatrix3 (cofactor3 L).adjoint = _
  rw [standardMatrix3_adjoint, mul_cofactor3_transpose]
  simp [map_smul, Matrix.toLpLin_symm_id]

/-- Differentiating an entry of the derivative matrix extracts a second derivative. -/
lemma hasFDerivAt_derivativeEntry3
    {Φ : EuclideanSpace ℝ (Fin 3) → EuclideanSpace ℝ (Fin 3)}
    {x : EuclideanSpace ℝ (Fin 3)} (hΦ : ContDiffAt ℝ 2 Φ x) (i j : Fin 3) :
    HasFDerivAt (fun y => standardMatrix3 (fderiv ℝ Φ y) i j)
      ((EuclideanSpace.proj i).comp
        ((fderiv ℝ (fderiv ℝ Φ) x).flip (EuclideanSpace.single j (1 : ℝ)))) x := by
  have hD : DifferentiableAt ℝ (fderiv ℝ Φ) x :=
    (hΦ.fderiv_right (m := 1) (by norm_num)).differentiableAt one_ne_zero
  have h := (EuclideanSpace.proj i).hasFDerivAt.comp x
    (hD.hasFDerivAt.clm_apply (hasFDerivAt_const (EuclideanSpace.single j (1 : ℝ)) x))
  simpa [Function.comp_def, standardMatrix3_apply] using h

/-- Local `C²` regularity gives equality of mixed coordinate derivatives. -/
lemma derivativeEntry3_mixed_eq
    {Φ : EuclideanSpace ℝ (Fin 3) → EuclideanSpace ℝ (Fin 3)}
    {x : EuclideanSpace ℝ (Fin 3)} (hΦ : ContDiffAt ℝ 2 Φ x) (i j k : Fin 3) :
    fderiv ℝ (fun y => standardMatrix3 (fderiv ℝ Φ y) i j) x
        (EuclideanSpace.single k (1 : ℝ)) =
      fderiv ℝ (fun y => standardMatrix3 (fderiv ℝ Φ y) i k) x
        (EuclideanSpace.single j (1 : ℝ)) := by
  rw [(hasFDerivAt_derivativeEntry3 hΦ i j).fderiv,
    (hasFDerivAt_derivativeEntry3 hΦ i k).fderiv]
  change (fderiv ℝ (fderiv ℝ Φ) x (EuclideanSpace.single k (1 : ℝ))
      (EuclideanSpace.single j (1 : ℝ))) i =
    (fderiv ℝ (fderiv ℝ Φ) x (EuclideanSpace.single j (1 : ℝ))
      (EuclideanSpace.single k (1 : ℝ))) i
  rw [(hΦ.isSymmSndFDerivAt (by norm_num)).eq]

/-- Polynomial cancellation of the cofactor row divergence under mixed-partial symmetry. -/
lemma sum_fderiv_adjugate_transpose_eq_zero
    {M : EuclideanSpace ℝ (Fin 3) → Matrix (Fin 3) (Fin 3) ℝ}
    {x : EuclideanSpace ℝ (Fin 3)}
    (hM : ∀ i j, DifferentiableAt ℝ (fun y => M y i j) x)
    (hsymm : ∀ i j k,
      fderiv ℝ (fun y => M y i j) x (EuclideanSpace.single k (1 : ℝ)) =
      fderiv ℝ (fun y => M y i k) x (EuclideanSpace.single j (1 : ℝ)))
    (i : Fin 3) :
    ∑ j, fderiv ℝ (fun y => (M y).adjugate.transpose i j) x
      (EuclideanSpace.single j (1 : ℝ)) = 0 := by
  fin_cases i <;>
    simp only [Fin.sum_univ_three, Matrix.transpose_apply, Matrix.adjugate_fin_three,
      Matrix.of_apply, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two,
      Matrix.cons_val_zero', Matrix.cons_val_succ',
      Matrix.head_cons, Matrix.tail_cons] <;>
    change EuclideanSpace ℝ (Fin 3) → Fin 3 → Fin 3 → ℝ at M <;>
    simp (disch := fun_prop) only [fderiv_fun_sub, fderiv_fun_mul, fderiv_fun_add,
      fderiv_fun_neg, _root_.add_apply, _root_.sub_apply,
      _root_.smul_apply, _root_.neg_apply, smul_eq_mul] <;>
    simp only [hsymm _ (1 : Fin 3) 0, hsymm _ (2 : Fin 3) 0, hsymm _ (2 : Fin 3) 1] <;>
    ring

/-- The coordinate form of the divergence-free cofactor rows. -/
lemma piola_cofactor_row_sum
    {Φ : EuclideanSpace ℝ (Fin 3) → EuclideanSpace ℝ (Fin 3)}
    {x : EuclideanSpace ℝ (Fin 3)} (hΦ : ContDiffAt ℝ 2 Φ x) (i : Fin 3) :
    ∑ j, fderiv ℝ (fun y => standardMatrix3 (cofactor3 (fderiv ℝ Φ y)) i j) x
      (EuclideanSpace.single j (1 : ℝ)) = 0 := by
  simp only [standardMatrix3_cofactor3]
  exact sum_fderiv_adjugate_transpose_eq_zero
    (fun i j => (hasFDerivAt_derivativeEntry3 hΦ i j).differentiableAt)
    (derivativeEntry3_mixed_eq hΦ) i

/-- Each adjugate entry is a polynomial in the original matrix entries. -/
lemma differentiableAt_adjugate_entry3
    {M : EuclideanSpace ℝ (Fin 3) → Matrix (Fin 3) (Fin 3) ℝ}
    {x : EuclideanSpace ℝ (Fin 3)}
    (hM : ∀ i j, DifferentiableAt ℝ (fun y => M y i j) x) (i j : Fin 3) :
    DifferentiableAt ℝ (fun y => (M y).adjugate i j) x := by
  fin_cases i <;> fin_cases j <;>
    simp only [Matrix.adjugate_fin_three, Matrix.of_apply,
      Matrix.cons_val_zero', Matrix.cons_val_succ'] <;>
    change EuclideanSpace ℝ (Fin 3) → Fin 3 → Fin 3 → ℝ at M <;>
    fun_prop

/-- Row `i` of the cofactor field, regarded as a Euclidean vector field. -/
def piolaRow (Φ : EuclideanSpace ℝ (Fin 3) → EuclideanSpace ℝ (Fin 3))
    (i : Fin 3) (x : EuclideanSpace ℝ (Fin 3)) : EuclideanSpace ℝ (Fin 3) :=
  (cofactor3 (fderiv ℝ Φ x)).adjoint (EuclideanSpace.single i (1 : ℝ))

/-- The row convention is explicit at each coordinate. -/
lemma piolaRow_apply (Φ : EuclideanSpace ℝ (Fin 3) → EuclideanSpace ℝ (Fin 3))
    (i j : Fin 3) (x : EuclideanSpace ℝ (Fin 3)) :
    piolaRow Φ i x j = standardMatrix3 (cofactor3 (fderiv ℝ Φ x)) i j := by
  have h := congrArg (fun M : Matrix (Fin 3) (Fin 3) ℝ => M j i)
    (standardMatrix3_adjoint (cofactor3 (fderiv ℝ Φ x)))
  simpa only [standardMatrix3_apply, Matrix.transpose_apply, piolaRow] using h

/-- The cofactor rows are differentiable wherever the map is locally `C²`. -/
lemma differentiableAt_piolaRow
    {Φ : EuclideanSpace ℝ (Fin 3) → EuclideanSpace ℝ (Fin 3)}
    {x : EuclideanSpace ℝ (Fin 3)} (hΦ : ContDiffAt ℝ 2 Φ x) (i : Fin 3) :
    DifferentiableAt ℝ (piolaRow Φ i) x := by
  apply (differentiableAt_piLp (𝕜 := ℝ) (p := 2)).2
  intro j
  simp only [piolaRow_apply, standardMatrix3_cofactor3, Matrix.transpose_apply]
  exact differentiableAt_adjugate_entry3
    (fun i j => (hasFDerivAt_derivativeEntry3 hΦ i j).differentiableAt) j i

/-- Divergence is the sum of the matching scalar coordinate partial derivatives. -/
lemma divergenceN_eq_sum_fderiv_coord
    {X : EuclideanSpace ℝ (Fin 3) → EuclideanSpace ℝ (Fin 3)}
    {x : EuclideanSpace ℝ (Fin 3)} (hX : DifferentiableAt ℝ X x) :
    divergenceN X x = ∑ j, fderiv ℝ (fun y => X y j) x
      (EuclideanSpace.single j (1 : ℝ)) := by
  apply Finset.sum_congr rfl
  intro j _
  have h := (EuclideanSpace.proj j).hasFDerivAt.comp x hX.hasFDerivAt
  change HasFDerivAt (fun y => X y j) _ x at h
  rw [h.fderiv]
  rfl

/-- Pointwise Piola identity: each row of the cofactor is divergence-free. -/
lemma piola_divergence_row_at
    {Φ : EuclideanSpace ℝ (Fin 3) → EuclideanSpace ℝ (Fin 3)}
    {x : EuclideanSpace ℝ (Fin 3)} (hΦ : ContDiffAt ℝ 2 Φ x) (i : Fin 3) :
    divergenceN (piolaRow Φ i) x = 0 := by
  rw [divergenceN_eq_sum_fderiv_coord (differentiableAt_piolaRow hΦ i)]
  simpa only [piolaRow_apply] using piola_cofactor_row_sum hΦ i

/-- Piola identity on an open domain under local `C²` regularity. -/
lemma piola_divergence_row_on
    {Φ : EuclideanSpace ℝ (Fin 3) → EuclideanSpace ℝ (Fin 3)}
    {U : Set (EuclideanSpace ℝ (Fin 3))} (hU : IsOpen U) (hΦ : ContDiffOn ℝ 2 Φ U)
    {x : EuclideanSpace ℝ (Fin 3)} (hx : x ∈ U) (i : Fin 3) :
    divergenceN (piolaRow Φ i) x = 0 :=
  piola_divergence_row_at (hΦ.contDiffAt (hU.mem_nhds hx)) i

end LiquidDrop

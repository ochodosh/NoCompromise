import NoCompromise.Variation.Piola

/-!
# The Piola identity is not symmetric in the two index slots

`NoCompromise.Variation.Piola` proves that the **rows** of the cofactor matrix
`cof DΦ = standardMatrix3 (cofactor3 (fderiv ℝ Φ ·))` are divergence free, i.e.
`∑ j, ∂_j (cof DΦ) i j = 0`. The blueprint statement `lem:piola` instead asserts
that the rows of the *transpose* `(cof DΦ)ᵀ = adj (DΦ)` are divergence free,
i.e. `∑ j, ∂_j (cof DΦ) j i = 0`. That statement is false.

This file exhibits the explicit counterexample
`Φ x = (x 0 + (x 2) ^ 2, x 1, x 2)`, a smooth (indeed polynomial) map with
`det DΦ ≡ 1`. Its cofactor matrix is

```
cof DΦ = !![1, 0, 0; 0, 1, 0; -2 * x 2, 0, 1]
```

whose rows are visibly divergence free, while column `0` — the first row of
`(cof DΦ)ᵀ = adj (DΦ)` — is `(1, 0, -2 * x 2)`, with divergence `-2`.

So the correct form of the first clause of `lem:piola` is `div (cof DΦ) = 0`
row-wise (equivalently: the *columns* of `(cof DΦ)ᵀ` are divergence free),
which is exactly `piola_divergence_row_at`.
-/

noncomputable section

open Module Matrix

namespace LiquidDrop

namespace PiolaCounterexample

/-- The shear `Φ x = (x 0 + (x 2) ^ 2, x 1, x 2)`. It is a polynomial diffeomorphism
of `ℝ³` with unit Jacobian. -/
def shearMap (x : EuclideanSpace ℝ (Fin 3)) : EuclideanSpace ℝ (Fin 3) :=
  WithLp.toLp 2 ![x 0 + (x 2) ^ 2, x 1, x 2]

/-- A coordinate-free description of the shear: it is the identity plus a
`(x 2) ^ 2`-multiple of the first basis vector. -/
lemma shearMap_eq (x : EuclideanSpace ℝ (Fin 3)) :
    shearMap x = x + (x 2) ^ 2 • EuclideanSpace.single (0 : Fin 3) (1 : ℝ) := by
  ext i
  fin_cases i <;>
    simp [shearMap]

/-- The shear is smooth. -/
lemma contDiff_shearMap : ContDiff ℝ ⊤ shearMap := by
  have hproj : ContDiff ℝ ⊤ (fun x : EuclideanSpace ℝ (Fin 3) => x 2) :=
    (EuclideanSpace.proj (𝕜 := ℝ) (2 : Fin 3)).contDiff
  have : ContDiff ℝ ⊤ (fun x : EuclideanSpace ℝ (Fin 3) =>
      x + (x 2) ^ 2 • EuclideanSpace.single (0 : Fin 3) (1 : ℝ)) :=
    contDiff_id.add ((hproj.pow 2).smul contDiff_const)
  have hfun : shearMap = fun x : EuclideanSpace ℝ (Fin 3) =>
      x + (x 2) ^ 2 • EuclideanSpace.single (0 : Fin 3) (1 : ℝ) := funext shearMap_eq
  rw [hfun]
  exact this

/-- The shear is `C²`. -/
lemma contDiff_two_shearMap : ContDiff ℝ 2 shearMap :=
  contDiff_shearMap.of_le (by exact_mod_cast le_top)

/-- The Fréchet derivative of the shear, in closed form. -/
lemma hasFDerivAt_shearMap (x : EuclideanSpace ℝ (Fin 3)) :
    HasFDerivAt shearMap
      (ContinuousLinearMap.id ℝ (EuclideanSpace ℝ (Fin 3)) +
        ((2 * x 2) • EuclideanSpace.proj (𝕜 := ℝ) (2 : Fin 3)).smulRight
          (EuclideanSpace.single (0 : Fin 3) (1 : ℝ))) x := by
  have hproj : HasFDerivAt (fun y : EuclideanSpace ℝ (Fin 3) => y 2)
      (EuclideanSpace.proj (𝕜 := ℝ) (2 : Fin 3)) x :=
    (EuclideanSpace.proj (𝕜 := ℝ) (2 : Fin 3)).hasFDerivAt
  have hsq : HasFDerivAt (fun y : EuclideanSpace ℝ (Fin 3) => (y 2) ^ 2)
      ((2 * x 2) • EuclideanSpace.proj (𝕜 := ℝ) (2 : Fin 3)) x := by
    simpa [smul_smul, mul_comm] using hproj.pow 2
  have := (hasFDerivAt_id x).add
    (hsq.smul_const (EuclideanSpace.single (0 : Fin 3) (1 : ℝ)))
  have hfun : shearMap = fun x : EuclideanSpace ℝ (Fin 3) =>
      x + (x 2) ^ 2 • EuclideanSpace.single (0 : Fin 3) (1 : ℝ) := funext shearMap_eq
  rw [hfun]
  exact this

/-- The derivative matrix of the shear. -/
lemma standardMatrix3_fderiv_shearMap (x : EuclideanSpace ℝ (Fin 3)) :
    standardMatrix3 (fderiv ℝ shearMap x) =
      !![1, 0, 2 * x 2; 0, 1, 0; 0, 0, 1] := by
  rw [(hasFDerivAt_shearMap x).fderiv]
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [standardMatrix3_apply]

/-- The cofactor matrix of the shear. Note that all three of its **rows**
`(1,0,0)`, `(0,1,0)`, `(-2 x₂, 0, 1)` are divergence free, while its first
**column** `(1, 0, -2 x₂)` is not. -/
lemma standardMatrix3_cofactor3_fderiv_shearMap (x : EuclideanSpace ℝ (Fin 3)) :
    standardMatrix3 (cofactor3 (fderiv ℝ shearMap x)) =
      !![1, 0, 0; 0, 1, 0; -(2 * x 2), 0, 1] := by
  rw [standardMatrix3_cofactor3, standardMatrix3_fderiv_shearMap]
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [Matrix.adjugate_fin_three]

/-- The `(j, 0)` entries of the cofactor matrix, as explicit scalar functions. -/
lemma cofactorColumn_zero (j : Fin 3) (x : EuclideanSpace ℝ (Fin 3)) :
    standardMatrix3 (cofactor3 (fderiv ℝ shearMap x)) j 0 =
      (if j = 2 then -(2 * x 2) else if j = 0 then 1 else 0) := by
  rw [standardMatrix3_cofactor3_fderiv_shearMap]
  fin_cases j <;> simp

/-- The divergence of the first **column** of the cofactor matrix of the shear
equals `-2` at every point: the transposed Piola identity fails. -/
theorem sum_fderiv_cofactor_column_shearMap (x : EuclideanSpace ℝ (Fin 3)) :
    ∑ j, fderiv ℝ (fun y => standardMatrix3 (cofactor3 (fderiv ℝ shearMap y)) j 0) x
      (EuclideanSpace.single j (1 : ℝ)) = -2 := by
  have hlast : fderiv ℝ
      (fun y => standardMatrix3 (cofactor3 (fderiv ℝ shearMap y)) (2 : Fin 3) 0) x
      (EuclideanSpace.single (2 : Fin 3) (1 : ℝ)) = -2 := by
    have hfun : (fun y : EuclideanSpace ℝ (Fin 3) =>
        standardMatrix3 (cofactor3 (fderiv ℝ shearMap y)) (2 : Fin 3) 0) =
        fun y : EuclideanSpace ℝ (Fin 3) => (-2 : ℝ) * y 2 := by
      funext y
      rw [cofactorColumn_zero]
      norm_num
    have hproj : HasFDerivAt (fun y : EuclideanSpace ℝ (Fin 3) => y 2)
        (EuclideanSpace.proj (𝕜 := ℝ) (2 : Fin 3)) x :=
      (EuclideanSpace.proj (𝕜 := ℝ) (2 : Fin 3)).hasFDerivAt
    rw [hfun, (hproj.const_mul (-2 : ℝ)).fderiv]
    simp
  have hconst : ∀ j : Fin 3, j ≠ 2 →
      fderiv ℝ (fun y => standardMatrix3 (cofactor3 (fderiv ℝ shearMap y)) j 0) x
        (EuclideanSpace.single j (1 : ℝ)) = 0 := by
    intro j hj
    have hfun : (fun y : EuclideanSpace ℝ (Fin 3) =>
        standardMatrix3 (cofactor3 (fderiv ℝ shearMap y)) j 0) =
        fun _ : EuclideanSpace ℝ (Fin 3) => (if j = 0 then 1 else 0 : ℝ) := by
      funext y
      rw [cofactorColumn_zero, if_neg hj]
    rw [hfun]
    simp
  rw [Fin.sum_univ_three, hconst 0 (by decide), hconst 1 (by decide), hlast]
  ring

/-- **The blueprint's first clause, as literally stated, is false.**

There is a `C²` map `Φ : ℝ³ → ℝ³`, an index `i` and a point `x` at which the
row divergence of the *transposed* cofactor matrix `(cof DΦ)ᵀ = adj (DΦ)` is
nonzero. Compare `piola_cofactor_row_sum`, whose index order is `i j` rather
than `j i`. -/
theorem not_piola_transpose_row :
    ∃ (Φ : EuclideanSpace ℝ (Fin 3) → EuclideanSpace ℝ (Fin 3)) (i : Fin 3)
      (x : EuclideanSpace ℝ (Fin 3)),
      ContDiff ℝ 2 Φ ∧
      ∑ j, fderiv ℝ (fun y => standardMatrix3 (cofactor3 (fderiv ℝ Φ y)) j i) x
        (EuclideanSpace.single j (1 : ℝ)) ≠ 0 := by
  refine ⟨shearMap, 0, 0, contDiff_two_shearMap, ?_⟩
  rw [sum_fderiv_cofactor_column_shearMap]
  norm_num

/-- The same failure, phrased through `piolaRow` and `divergenceN`: the vector
field whose coordinates are the first *column* of the cofactor matrix is not
divergence free. -/
theorem not_divergence_cofactor_column :
    ∃ (Φ : EuclideanSpace ℝ (Fin 3) → EuclideanSpace ℝ (Fin 3)) (i : Fin 3)
      (x : EuclideanSpace ℝ (Fin 3)),
      ContDiff ℝ 2 Φ ∧
      divergenceN
        (fun y => WithLp.toLp 2
          (fun j => standardMatrix3 (cofactor3 (fderiv ℝ Φ y)) j i)) x ≠ 0 := by
  refine ⟨shearMap, 0, 0, contDiff_two_shearMap, ?_⟩
  have hdiff : DifferentiableAt ℝ
      (fun y : EuclideanSpace ℝ (Fin 3) => WithLp.toLp 2
        (fun j => standardMatrix3 (cofactor3 (fderiv ℝ shearMap y)) j (0 : Fin 3)))
      (0 : EuclideanSpace ℝ (Fin 3)) := by
    refine (differentiableAt_piLp (𝕜 := ℝ) (p := 2)).2 fun j => ?_
    have hfun : (fun y : EuclideanSpace ℝ (Fin 3) => (WithLp.toLp 2
        (fun k => standardMatrix3 (cofactor3 (fderiv ℝ shearMap y)) k (0 : Fin 3))) j) =
        fun y : EuclideanSpace ℝ (Fin 3) =>
          (if j = 2 then -(2 : ℝ) * y 2 else if j = 0 then 1 else 0) := by
      funext y
      have := cofactorColumn_zero j y
      simp only [this]
      split_ifs <;> ring
    rw [hfun]
    by_cases hj : j = 2
    · simp only [hj, if_true]
      exact (((EuclideanSpace.proj (𝕜 := ℝ) (2 : Fin 3)).differentiableAt).const_mul _)
    · simp only [hj, if_false]
      exact differentiableAt_const _
  rw [divergenceN_eq_sum_fderiv_coord hdiff]
  have hcongr : ∀ j : Fin 3,
      fderiv ℝ (fun y : EuclideanSpace ℝ (Fin 3) => (WithLp.toLp 2
        (fun k => standardMatrix3 (cofactor3 (fderiv ℝ shearMap y)) k (0 : Fin 3))) j)
        (0 : EuclideanSpace ℝ (Fin 3)) =
      fderiv ℝ (fun y : EuclideanSpace ℝ (Fin 3) =>
        standardMatrix3 (cofactor3 (fderiv ℝ shearMap y)) j (0 : Fin 3))
        (0 : EuclideanSpace ℝ (Fin 3)) := by
    intro j; rfl
  simp only [hcongr]
  rw [sum_fderiv_cofactor_column_shearMap]
  norm_num

/-- The positive companion: for the very same map, the genuine Piola identity
`piola_divergence_row_at` does hold — every **row** of the cofactor matrix is
divergence free. This is the precise asymmetry between the two index orders. -/
theorem divergence_piolaRow_shearMap (i : Fin 3) (x : EuclideanSpace ℝ (Fin 3)) :
    divergenceN (piolaRow shearMap i) x = 0 :=
  piola_divergence_row_at (contDiff_two_shearMap.contDiffAt) i

/-- And the coordinate form of the positive statement, for the same map. -/
theorem sum_fderiv_cofactor_row_shearMap (i : Fin 3) (x : EuclideanSpace ℝ (Fin 3)) :
    ∑ j, fderiv ℝ (fun y => standardMatrix3 (cofactor3 (fderiv ℝ shearMap y)) i j) x
      (EuclideanSpace.single j (1 : ℝ)) = 0 :=
  piola_cofactor_row_sum (contDiff_two_shearMap.contDiffAt) i

end PiolaCounterexample

end LiquidDrop


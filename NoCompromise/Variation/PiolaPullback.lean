import NoCompromise.Variation.Piola
import NoCompromise.BV.StrictApprox
import NoCompromise.DeGiorgi.Structure
import Mathlib.MeasureTheory.Function.Jacobian
import Mathlib.Analysis.Calculus.ContDiff.WithLp


/-!
# Piola pullback and the C² transport pairing

The cofactor pullback has divergence det(DΦ) times the pulled-back divergence.
The proof combines the cofactor-row Piola identity with the chain and product
rules. A fixed orientation sign gives the integrated identity; for global C²
homeomorphisms it yields the reduced-boundary cofactor pairing via Gauss--Green.
This is the C² pairing step of transport, not the final C¹ measure theorem.
-/

noncomputable section
open Set Filter MeasureTheory
open scoped Topology Gradient
namespace LiquidDrop

/-- The cofactor pullback of an ambient vector field. -/
def piolaPullback (Φ X : AmbientSpace → AmbientSpace) (x : AmbientSpace) : AmbientSpace :=
  (cofactor3 (fderiv ℝ Φ x)).adjoint (X (Φ x))

lemma piolaPullback_eq_sum (Φ X : AmbientSpace → AmbientSpace) :
    piolaPullback Φ X = fun x => ∑ i, (X (Φ x)) i • piolaRow Φ i x := by
  funext x
  have h := (EuclideanSpace.basisFun (Fin 3) ℝ).sum_repr (X (Φ x))
  simp only [EuclideanSpace.basisFun_repr, EuclideanSpace.basisFun_apply] at h
  unfold piolaPullback
  nth_rw 1 [← h]
  rw [map_sum]
  simp only [map_smul, piolaRow]

lemma divergenceN_fun_sum_at {ι : Type*} [Fintype ι]
    {X : ι → AmbientSpace → AmbientSpace} {x : AmbientSpace}
    (hX : ∀ i, DifferentiableAt ℝ (X i) x) :
    divergenceN (fun y => ∑ i, X i y) x = ∑ i, divergenceN (X i) x := by
  simp only [divergenceN, fderiv_fun_sum (fun i _ => hX i),
    _root_.sum_apply, WithLp.ofLp_sum, Finset.sum_apply]
  exact Finset.sum_comm

/-- Piola's product identity, under local C² regularity of the coordinate map.
Invertibility is unnecessary for this pointwise identity. -/
theorem divergenceN_piolaPullback_at {Φ X : AmbientSpace → AmbientSpace}
    {x : AmbientSpace} (hΦ : ContDiffAt ℝ 2 Φ x)
    (hX : DifferentiableAt ℝ X (Φ x)) :
    divergenceN (piolaPullback Φ X) x =
      (fderiv ℝ Φ x).det * divergenceN X (Φ x) := by
  have hΦd := hΦ.differentiableAt (by norm_num : (2 : WithTop ℕ∞) ≠ 0)
  have hc (i : Fin 3) : DifferentiableAt ℝ (fun y => X (Φ y) i) x := by
    exact (differentiableAt_piLp (𝕜 := ℝ) (p := 2)).mp (hX.comp x hΦd) i
  rw [piolaPullback_eq_sum, divergenceN_fun_sum_at
    (X := fun i y => X (Φ y) i • piolaRow Φ i y)
    (fun i => (hc i).smul (differentiableAt_piolaRow hΦ i))]
  simp_rw [divergenceN_smul_of_differentiableAt (hc _) (differentiableAt_piolaRow hΦ _),
    piola_divergence_row_at hΦ, mul_zero, zero_add, inner_gradient_left]
  have hder (i : Fin 3) : fderiv ℝ (fun y => X (Φ y) i) x =
      (EuclideanSpace.proj i).comp ((fderiv ℝ X (Φ x)).comp (fderiv ℝ Φ x)) := by
    exact ((EuclideanSpace.proj i).hasFDerivAt.comp x
      (hX.hasFDerivAt.comp x hΦd.hasFDerivAt)).fderiv
  simp_rw [hder, ContinuousLinearMap.comp_apply, piolaRow]
  have hid := comp_cofactor3_adjoint (fderiv ℝ Φ x)
  have heq (i : Fin 3) : fderiv ℝ Φ x
      ((cofactor3 (fderiv ℝ Φ x)).adjoint (EuclideanSpace.single i 1)) =
      (fderiv ℝ Φ x).det • EuclideanSpace.single i 1 := by
    exact congrArg (fun L : AmbientSpace →L[ℝ] AmbientSpace => L (EuclideanSpace.single i 1)) hid
  simp_rw [heq, map_smul]
  simp only [smul_eq_mul, divergenceN, Finset.mul_sum]
  rfl

/-- The integrated Piola identity on a Borel set with a fixed determinant sign. -/
theorem integral_image_divergence_eq_piolaPullback
    {Φ X : AmbientSpace → AmbientSpace} {E : Set AmbientSpace} (hE : MeasurableSet E)
    (hΦ : ∀ x ∈ E, ContDiffAt ℝ 2 Φ x) (hinj : InjOn Φ E)
    (hX : ∀ x ∈ E, DifferentiableAt ℝ X (Φ x)) {s : ℝ}
    (hsgn : ∀ x ∈ E, |(fderiv ℝ Φ x).det| = s * (fderiv ℝ Φ x).det) :
    (∫ y in Φ '' E, divergenceN X y) = s * ∫ x in E, divergenceN (piolaPullback Φ X) x := by
  rw [integral_image_eq_integral_abs_det_fderiv_smul volume hE
    (fun x hx => ((hΦ x hx).differentiableAt (by norm_num)).hasFDerivAt.hasFDerivWithinAt)
    hinj (divergenceN X), ← integral_const_mul]
  apply setIntegral_congr_fun hE
  intro x hx
  dsimp only
  rw [smul_eq_mul, hsgn x hx, divergenceN_piolaPullback_at (hΦ x hx) (hX x hx), mul_assoc]

lemma contDiff_adjugate_entry3
    {M : AmbientSpace → Matrix (Fin 3) (Fin 3) ℝ} {k : WithTop ℕ∞}
    (hM : ∀ i j, ContDiff ℝ k (fun y => M y i j)) (i j : Fin 3) :
    ContDiff ℝ k (fun y => (M y).adjugate i j) := by
  fin_cases i <;> fin_cases j <;>
    simp only [Matrix.adjugate_fin_three, Matrix.of_apply,
      Matrix.cons_val_zero', Matrix.cons_val_succ'] <;>
    change AmbientSpace → Fin 3 → Fin 3 → ℝ at M <;>
    fun_prop

lemma contDiff_piolaRow {Φ : AmbientSpace → AmbientSpace} (hΦ : ContDiff ℝ 2 Φ)
    (i : Fin 3) : ContDiff ℝ 1 (piolaRow Φ i) := by
  have hD : ContDiff ℝ 1 (fderiv ℝ Φ) := hΦ.fderiv_right (by norm_num)
  have hM (i j : Fin 3) : ContDiff ℝ 1
      (fun y => standardMatrix3 (fderiv ℝ Φ y) i j) := by
    simp only [standardMatrix3_apply]
    fun_prop
  apply (contDiff_piLp (𝕜 := ℝ) (p := 2)).2
  intro j
  simp only [piolaRow_apply, standardMatrix3_cofactor3, Matrix.transpose_apply]
  exact contDiff_adjugate_entry3 hM j i

/-- A C² change of variables pulls C¹ fields back to C¹ fields. -/
theorem contDiff_piolaPullback {Φ X : AmbientSpace → AmbientSpace}
    (hΦ : ContDiff ℝ 2 Φ) (hX : ContDiff ℝ 1 X) : ContDiff ℝ 1 (piolaPullback Φ X) := by
  rw [piolaPullback_eq_sum]
  apply ContDiff.sum
  intro i _
  have hcomp := hX.comp (hΦ.of_le (by norm_num : (1 : WithTop ℕ∞) ≤ 2))
  have hi := (contDiff_piLp (𝕜 := ℝ) (p := 2)).mp hcomp i
  simpa only [Pi.smul_apply] using! hi.smul (contDiff_piolaRow hΦ i)

/-- Compact support is preserved by pullback along a global homeomorphism. -/
theorem hasCompactSupport_piolaPullback (Φ : AmbientSpace ≃ₜ AmbientSpace)
    {X : AmbientSpace → AmbientSpace} (hX : HasCompactSupport X) :
    HasCompactSupport (piolaPullback Φ X) := by
  apply (hX.comp_homeomorph Φ).mono
  intro x hx
  apply Function.mem_support.mpr
  intro hzero
  apply hx
  simp only [piolaPullback, Function.comp_apply] at hzero ⊢
  rw [hzero, map_zero]

/-- The C² transport pairing with the actual reduced-boundary area measure. -/
theorem integral_image_divergence_eq_reducedBoundary_cofactor
    (Φ : AmbientSpace ≃ₜ AmbientSpace) (hΦ : ContDiff ℝ 2 Φ)
    {E : Set AmbientSpace} (hE : HasLocallyFinitePerimeter E) (hmE : MeasurableSet E)
    {X : AmbientSpace → AmbientSpace} (hX : ContDiff ℝ 1 X) (hcX : HasCompactSupport X)
    {s : ℝ} (hsgn : ∀ x ∈ E, |(fderiv ℝ Φ x).det| = s * (fderiv ℝ Φ x).det) :
    (∫ y in Φ '' E, divergenceN X y) =
      s * ∫ x in reducedBoundary E hE hmE.nullMeasurableSet,
        inner ℝ (X (Φ x))
          (cofactor3 (fderiv ℝ Φ x) (reducedNormal E hE hmE.nullMeasurableSet x))
        ∂hausdorffMeasure2 3 := by
  rw [integral_image_divergence_eq_piolaPullback hmE (fun x _ => hΦ.contDiffAt)
    Φ.injective.injOn (fun x _ => hX.differentiable one_ne_zero (Φ x)) hsgn,
    gauss_green E hE hmE.nullMeasurableSet (piolaPullback Φ X)
      (contDiff_piolaPullback hΦ hX) (hasCompactSupport_piolaPullback Φ hcX)]
  congr 1
  apply setIntegral_congr_fun (measurableSet_reducedBoundary E hE hmE.nullMeasurableSet)
  intro x _
  exact (cofactor3 (fderiv ℝ Φ x)).adjoint_inner_left _ _

end LiquidDrop

module

public import NoCompromise.Elliptic.BoundaryNeumann
public import NoCompromise.Area.Graph

@[expose] public section

/-!
# The explicit lift of an inhomogeneous conormal datum

Here the cutoff is identically one: `q(x) = x₃ h(x') / b(x')`, where
`b(x') = A₃₃(x',0)`.  The lemmas below establish the pointwise flat-face
cancellation in the first paragraph of blueprint `thm:boundary-neumann`.
-/

noncomputable section
open MeasureTheory Filter Metric Set InnerProductSpace
open scoped ENNReal NNReal Topology Gradient RealInnerProductSpace
namespace LiquidDrop

lemma boundary_neumann_graphBase_eq_append (y : EuclideanSpace ℝ (Fin 2)) :
    graphBaseEmbedding y = graphAppendN y 0 := by
  ext i
  fin_cases i <;> simp [graphAppendN, graphBaseN]

lemma boundary_neumann_projection_base (y : EuclideanSpace ℝ (Fin 2)) :
    graphProjectionN 2 (graphBaseEmbedding y) = y := by
  rw [boundary_neumann_graphBase_eq_append, graphProjectionN_append]

/-- The normal-normal coefficient on the flat face; no symmetry is assumed. -/
def boundaryNeumannNormalCoefficient
    (A : EuclideanSpace ℝ (Fin 3) → EuclideanSpace ℝ (Fin 3) →L[ℝ]
      EuclideanSpace ℝ (Fin 3)) (y : EuclideanSpace ℝ (Fin 2)) : ℝ :=
  inner ℝ (A (graphBaseEmbedding y) (EuclideanSpace.single (Fin.last 2) 1))
    (EuclideanSpace.single (Fin.last 2) 1)

lemma boundaryNeumannNormalCoefficient_eq
    (A : EuclideanSpace ℝ (Fin 3) → EuclideanSpace ℝ (Fin 3) →L[ℝ]
      EuclideanSpace ℝ (Fin 3)) (y : EuclideanSpace ℝ (Fin 2)) :
    boundaryNeumannNormalCoefficient A y =
      A (graphBaseEmbedding y) (EuclideanSpace.single (Fin.last 2) 1) (Fin.last 2) := by
  simp [boundaryNeumannNormalCoefficient, EuclideanSpace.inner_single_right]

lemma boundaryNeumannNormalCoefficient_ge {lam : ℝ}
    {A : EuclideanSpace ℝ (Fin 3) → EuclideanSpace ℝ (Fin 3) →L[ℝ]
      EuclideanSpace ℝ (Fin 3)} {y : EuclideanSpace ℝ (Fin 2)}
    (hell : ∀ ξ, lam * ‖ξ‖ ^ 2 ≤ inner ℝ (A (graphBaseEmbedding y) ξ) ξ) :
    lam ≤ boundaryNeumannNormalCoefficient A y := by
  simpa [boundaryNeumannNormalCoefficient] using
    hell (EuclideanSpace.single (Fin.last 2) 1)

/-- The uncut lift, with an explicit denominator function on the base. -/
def boundaryNeumannLift (h b : EuclideanSpace ℝ (Fin 2) → ℝ)
    (x : EuclideanSpace ℝ (Fin 3)) : ℝ :=
  x (Fin.last 2) * (h (graphProjectionN 2 x) / b (graphProjectionN 2 x))

lemma boundaryNeumannLift_eq_zero (h b : EuclideanSpace ℝ (Fin 2) → ℝ)
    {x : EuclideanSpace ℝ (Fin 3)} (hx : x (Fin.last 2) = 0) :
    boundaryNeumannLift h b x = 0 := by
  simp only [boundaryNeumannLift, hx, zero_mul]

lemma boundaryNeumannLift_contDiffOn {h b : EuclideanSpace ℝ (Fin 2) → ℝ}
    {U : Set (EuclideanSpace ℝ (Fin 2))}
    (hh : ContDiffOn ℝ 1 h U) (hb : ContDiffOn ℝ 1 b U)
    (hb0 : ∀ y ∈ U, b y ≠ 0) :
    ContDiffOn ℝ 1 (boundaryNeumannLift h b) ((graphProjectionN 2) ⁻¹' U) := by
  exact (EuclideanSpace.proj (Fin.last 2)).contDiff.contDiffOn.mul
    ((hh.div hb hb0).comp (graphProjectionN 2).contDiff.contDiffOn (fun _ hx => hx))

/-- At a flat point only the derivative of the normal coordinate survives. -/
lemma boundaryNeumannLift_gradient_flat {h b : EuclideanSpace ℝ (Fin 2) → ℝ}
    {x : EuclideanSpace ℝ (Fin 3)} (hx : x (Fin.last 2) = 0)
    (hh : DifferentiableAt ℝ h (graphProjectionN 2 x))
    (hb : DifferentiableAt ℝ b (graphProjectionN 2 x))
    (hb0 : b (graphProjectionN 2 x) ≠ 0) :
    gradient (boundaryNeumannLift h b) x =
      (h (graphProjectionN 2 x) / b (graphProjectionN 2 x)) •
        EuclideanSpace.single (Fin.last 2) 1 := by
  have hquot : DifferentiableAt ℝ (fun y => h y / b y) (graphProjectionN 2 x) := by
    simpa only [div_eq_mul_inv, Pi.mul_def, Pi.inv_def] using hh.mul (hb.inv hb0)
  have hd := hquot.comp x (graphProjectionN 2).differentiableAt
  have hq := (EuclideanSpace.proj (Fin.last 2)).hasFDerivAt.mul hd.hasFDerivAt
  ext i
  rw [gradient_apply_eq_fderiv_single]
  change fderiv ℝ (fun y => y (Fin.last 2) *
    (h (graphProjectionN 2 y) / b (graphProjectionN 2 y))) x
      (EuclideanSpace.single i 1) = _
  have he := hq.fderiv
  simp only [Pi.mul_def, Function.comp_def, EuclideanSpace.coe_proj] at he
  change fderiv ℝ (fun y => y (Fin.last 2) *
    (h (graphProjectionN 2 y) / b (graphProjectionN 2 y))) x = _ at he
  rw [he, hx, zero_smul, zero_add]
  by_cases hi : i = Fin.last 2
  · subst i
    simp
  · simp only [smul_apply, EuclideanSpace.coe_proj,
      PiLp.smul_apply, PiLp.single_apply, hi, Ne.symm hi, ite_false, smul_eq_mul, mul_zero]

/-- The lift has the prescribed inward-coordinate conormal on the flat face. -/
lemma boundaryNeumannLift_conormal
    {A : EuclideanSpace ℝ (Fin 3) → EuclideanSpace ℝ (Fin 3) →L[ℝ]
      EuclideanSpace ℝ (Fin 3)} {h : EuclideanSpace ℝ (Fin 2) → ℝ}
    {y : EuclideanSpace ℝ (Fin 2)}
    (hh : DifferentiableAt ℝ h y)
    (hb : DifferentiableAt ℝ (boundaryNeumannNormalCoefficient A) y)
    (hb0 : boundaryNeumannNormalCoefficient A y ≠ 0) :
    A (graphBaseEmbedding y)
      (gradient (boundaryNeumannLift h (boundaryNeumannNormalCoefficient A))
        (graphBaseEmbedding y)) (Fin.last 2) = h y := by
  have hp := boundary_neumann_projection_base y
  rw [boundaryNeumannLift_gradient_flat (by simp : graphBaseEmbedding y (Fin.last 2) = 0)
    (hp.symm ▸ hh) (hp.symm ▸ hb) (hp.symm ▸ hb0), hp,
    map_smul, PiLp.smul_apply, smul_eq_mul,
    ← boundaryNeumannNormalCoefficient_eq]
  exact div_mul_cancel₀ _ hb0

/-- The vertical primitive used to convert the interior source to a flux. -/
def boundaryNeumannPrimitive (f : EuclideanSpace ℝ (Fin 3) → ℝ)
    (x : EuclideanSpace ℝ (Fin 3)) : EuclideanSpace ℝ (Fin 3) :=
  (∫ t in (0 : ℝ)..x (Fin.last 2), f (graphAppendN (graphProjectionN 2 x) t)) •
    EuclideanSpace.single (Fin.last 2) 1

lemma boundaryNeumannPrimitive_flat (f : EuclideanSpace ℝ (Fin 3) → ℝ)
    {x : EuclideanSpace ℝ (Fin 3)} (hx : x (Fin.last 2) = 0) :
    boundaryNeumannPrimitive f x = 0 := by
  simp only [boundaryNeumannPrimitive, hx, intervalIntegral.integral_same, zero_smul]

/-- The datum to which homogeneous conormal regularity will be applied. -/
def boundaryNeumannInhomDatum
    (A : EuclideanSpace ℝ (Fin 3) → EuclideanSpace ℝ (Fin 3) →L[ℝ]
      EuclideanSpace ℝ (Fin 3)) (f : EuclideanSpace ℝ (Fin 3) → ℝ)
    (h : EuclideanSpace ℝ (Fin 2) → ℝ) (x : EuclideanSpace ℝ (Fin 3)) :
    EuclideanSpace ℝ (Fin 3) :=
  boundaryNeumannPrimitive f x +
    h (graphProjectionN 2 x) • EuclideanSpace.single (Fin.last 2) 1 -
      A x (gradient (boundaryNeumannLift h (boundaryNeumannNormalCoefficient A)) x)

lemma boundaryNeumannInhomDatum_flat
    {A : EuclideanSpace ℝ (Fin 3) → EuclideanSpace ℝ (Fin 3) →L[ℝ]
      EuclideanSpace ℝ (Fin 3)} (f : EuclideanSpace ℝ (Fin 3) → ℝ)
    {h : EuclideanSpace ℝ (Fin 2) → ℝ} {y : EuclideanSpace ℝ (Fin 2)}
    (hh : DifferentiableAt ℝ h y)
    (hb : DifferentiableAt ℝ (boundaryNeumannNormalCoefficient A) y)
    (hb0 : boundaryNeumannNormalCoefficient A y ≠ 0) :
    boundaryNeumannInhomDatum A f h (graphBaseEmbedding y) (Fin.last 2) = 0 := by
  rw [boundaryNeumannInhomDatum,
    boundaryNeumannPrimitive_flat f (by simp), zero_add,
    PiLp.sub_apply, boundaryNeumannLift_conormal hh hb hb0,
    boundary_neumann_projection_base]
  simp

/-- Ellipticity makes the denominator nonzero at every flat point under consideration. -/
lemma boundaryNeumannInhomDatum_flat_of_elliptic {lam : ℝ} (hlam : 0 < lam)
    {A : EuclideanSpace ℝ (Fin 3) → EuclideanSpace ℝ (Fin 3) →L[ℝ]
      EuclideanSpace ℝ (Fin 3)} (f : EuclideanSpace ℝ (Fin 3) → ℝ)
    {h : EuclideanSpace ℝ (Fin 2) → ℝ} {x : EuclideanSpace ℝ (Fin 3)}
    (hx : x (Fin.last 2) = 0)
    (hell : ∀ ξ, lam * ‖ξ‖ ^ 2 ≤ inner ℝ (A x ξ) ξ)
    (hh : DifferentiableAt ℝ h (graphProjectionN 2 x))
    (hb : DifferentiableAt ℝ (boundaryNeumannNormalCoefficient A) (graphProjectionN 2 x)) :
    boundaryNeumannInhomDatum A f h x (Fin.last 2) = 0 := by
  have he : graphBaseEmbedding (graphProjectionN 2 x) = x := by
    rw [boundary_neumann_graphBase_eq_append, ← hx, graphAppendN_projection]
  have hpos : 0 < boundaryNeumannNormalCoefficient A (graphProjectionN 2 x) :=
    hlam.trans_le (boundaryNeumannNormalCoefficient_ge (by rwa [he]))
  have hz := boundaryNeumannInhomDatum_flat f hh hb hpos.ne'
  rwa [he] at hz

/-- The lift terms cancel identically in the reduced flux, before integration. -/
lemma boundaryNeumannInhomDatum_flux
    (A : EuclideanSpace ℝ (Fin 3) → EuclideanSpace ℝ (Fin 3) →L[ℝ]
      EuclideanSpace ℝ (Fin 3)) (f : EuclideanSpace ℝ (Fin 3) → ℝ)
    (h : EuclideanSpace ℝ (Fin 2) → ℝ)
    (F : EuclideanSpace ℝ (Fin 3) → EuclideanSpace ℝ (Fin 3))
    (x : EuclideanSpace ℝ (Fin 3)) :
    A x (F x - gradient (boundaryNeumannLift h (boundaryNeumannNormalCoefficient A)) x) -
        boundaryNeumannInhomDatum A f h x =
      A x (F x) - boundaryNeumannPrimitive f x -
        h (graphProjectionN 2 x) • EuclideanSpace.single (Fin.last 2) 1 := by
  rw [map_sub, boundaryNeumannInhomDatum]
  abel

end LiquidDrop

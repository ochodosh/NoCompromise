module

public import NoCompromise.Elliptic.InteriorH2Mollification

@[expose] public section

/-!
# Pointwise calculus vocabulary for chapter 31 (`CapacitaryK`)

Design (recorded for the chapter):

* The Laplacian is the repository's `LiquidDrop.laplacianN`, the sum of second
  coordinate derivatives `∂ᵢ∂ᵢ` in the standard orthonormal basis of `ℝ³`, where
  `∂ᵢ f x = fderiv ℝ f x (EuclideanSpace.single i 1)` (`poissonCoordinateDerivative`).
  This is the same operator used by `HasDistributionalLaplacianOn`.
* The Hessian is the directional second derivative
  `D²u(X, Y) = D_X (D_Y u)`, i.e. `fderiv ℝ (fun y ↦ fderiv ℝ u y Y) x X`
  (`dirHess`). Its coordinate matrix is `hess u x i j = ∂ᵢ∂ⱼu`.
* `w := |∇u|` (`gradNorm`, blueprint `not:w`) and `w_ε := (w² + ε²)^{1/2}`
  (`gradNormEps`).
* `|D²u|² = ∑ᵢⱼ (∂ᵢ∂ⱼu)²` (`hessNormSq`), `(D²u ∇u)ᵢ = ∑ⱼ ∂ᵢ∂ⱼu ∂ⱼu`
  (`hessGrad`), `|D²u ∇u|² = ∑ᵢ (D²u ∇u)ᵢ²` (`hessGradNormSq`).
* Level-set geometry (convention `conv:level-orientation`): on `{w > 0}` the
  unit normal is `ν := -∇u / |∇u|` (`unitNormal`), outward for `{u ≥ t}`; the
  second fundamental form is `A(X, Y) := ⟪D_X ν, Y⟫` (`secondFF`), and
  `H := div_Σ ν = div ν - ⟪D_ν ν, ν⟫` (`meanCurv`), the tangential divergence.
  A round sphere, e.g. the levels of `1/r`, has `H > 0`.
-/

noncomputable section
open MeasureTheory Filter Metric Set InnerProductSpace
open scoped NNReal ENNReal Topology Gradient RealInnerProductSpace

namespace LiquidDrop
namespace CapacitaryK

/-- The ambient Euclidean space `ℝ³`. -/
abbrev E3 := EuclideanSpace ℝ (Fin 3)

/-- The `i`-th standard basis vector of `ℝ³`. -/
abbrev basisVec (i : Fin 3) : E3 := EuclideanSpace.single i 1

/-- `w := |∇u|`, the length of the gradient (blueprint notation `not:w`). -/
def gradNorm (u : E3 → ℝ) (x : E3) : ℝ := ‖gradient u x‖

/-- The regularised gradient length `w_ε := (w² + ε²)^{1/2}`. -/
def gradNormEps (ε : ℝ) (u : E3 → ℝ) (x : E3) : ℝ :=
  Real.sqrt ((gradNorm u x) ^ 2 + ε ^ 2)

/-- The directional Hessian `D²u(X, Y) = D_X (D_Y u)` at `x`. -/
def dirHess (u : E3 → ℝ) (x X Y : E3) : ℝ :=
  fderiv ℝ (fun y => fderiv ℝ u y Y) x X

/-- The `(i, j)` entry `∂ᵢ∂ⱼu` of the Hessian in the standard basis. -/
def hess (u : E3 → ℝ) (x : E3) (i j : Fin 3) : ℝ :=
  poissonCoordinateDerivative i (poissonCoordinateDerivative j u) x

/-- `|D²u|²`, the squared Hilbert-Schmidt norm of the Hessian. -/
def hessNormSq (u : E3 → ℝ) (x : E3) : ℝ := ∑ i, ∑ j, (hess u x i j) ^ 2

/-- The `i`-th coordinate of `D²u ∇u`. -/
def hessGrad (u : E3 → ℝ) (x : E3) (i : Fin 3) : ℝ :=
  ∑ j, hess u x i j * gradient u x j

/-- `|D²u ∇u|²`. -/
def hessGradNormSq (u : E3 → ℝ) (x : E3) : ℝ := ∑ i, (hessGrad u x i) ^ 2

/-- The unit normal `ν := -∇u / |∇u|` of the level sets (convention
`conv:level-orientation`); it is the outward normal of `{u ≥ t}` where `w > 0`. -/
def unitNormal (u : E3 → ℝ) (y : E3) : E3 := -((gradNorm u y)⁻¹ • gradient u y)

/-- The second fundamental form `A(X, Y) := ⟪D_X ν, Y⟫` of the level set through `x`. -/
def secondFF (u : E3 → ℝ) (x X Y : E3) : ℝ :=
  ⟪fderiv ℝ (unitNormal u) x X, Y⟫

/-- The mean curvature `H := div_Σ ν = div ν - ⟪D_ν ν, ν⟫` of the level set through `x`. -/
def meanCurv (u : E3 → ℝ) (x : E3) : ℝ :=
  (∑ i, secondFF u x (basisVec i) (basisVec i)) -
    secondFF u x (unitNormal u x) (unitNormal u x)

lemma hess_eq_dirHess (u : E3 → ℝ) (x : E3) (i j : Fin 3) :
    hess u x i j = dirHess u x (basisVec i) (basisVec j) := rfl

lemma gradient_apply_eq_fderiv_basisVec (u : E3 → ℝ) (x : E3) (i : Fin 3) :
    gradient u x i = fderiv ℝ u x (basisVec i) :=
  gradient_apply_eq_fderiv_single u x i

lemma gradNorm_nonneg (u : E3 → ℝ) (x : E3) : 0 ≤ gradNorm u x := norm_nonneg _

lemma gradNorm_sq (u : E3 → ℝ) (x : E3) :
    (gradNorm u x) ^ 2 = ∑ i, (gradient u x i) ^ 2 := by
  rw [gradNorm, EuclideanSpace.norm_eq]
  rw [Real.sq_sqrt (Finset.sum_nonneg fun i _ => by positivity)]
  exact Finset.sum_congr rfl fun i _ => by rw [Real.norm_eq_abs, sq_abs]

lemma gradNormEps_pos {ε : ℝ} (hε : 0 < ε) (u : E3 → ℝ) (x : E3) :
    0 < gradNormEps ε u x := by
  have : (0:ℝ) < (gradNorm u x) ^ 2 + ε ^ 2 := by positivity
  simpa [gradNormEps] using Real.sqrt_pos.mpr this

lemma sq_gradNormEps (ε : ℝ) (u : E3 → ℝ) (x : E3) :
    (gradNormEps ε u x) ^ 2 = (gradNorm u x) ^ 2 + ε ^ 2 := by
  have : (0:ℝ) ≤ (gradNorm u x) ^ 2 + ε ^ 2 := by positivity
  simpa [gradNormEps] using Real.sq_sqrt this

/-- At `ε = 0` the regularisation is `w` itself. -/
lemma gradNormEps_zero (u : E3 → ℝ) : gradNormEps 0 u = gradNorm u := by
  funext x
  simp [gradNormEps, Real.sqrt_sq (gradNorm_nonneg u x)]

end CapacitaryK
end LiquidDrop

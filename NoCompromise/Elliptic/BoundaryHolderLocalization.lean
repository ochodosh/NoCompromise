module

public import NoCompromise.Elliptic.BoundaryHolderTrace
public import NoCompromise.Elliptic.CampanatoGrowthComparison
public import NoCompromise.Sobolev.LipschitzDomains

@[expose] public section

/-!
# Localization of a zero-trace half-ball solution

A fixed interior cutoff produces the genuine zero extension on the entire
space. It agrees with the original function and gradient on the smaller upper
ball; its weak gradient vanishes throughout the lower halfspace.
-/

noncomputable section
open MeasureTheory Filter Metric Set InnerProductSpace
open scoped ENNReal NNReal Topology Gradient RealInnerProductSpace
namespace LiquidDrop

/-- A fixed cutoff, equal to one on the ball of radius 1/64. -/
def boundaryHolderBump : ContDiffBump (0 : EuclideanSpace ℝ (Fin 3)) :=
  ⟨1 / 64, 1 / 32, by norm_num, by norm_num⟩

lemma boundaryHolderBump_eq_one {x : EuclideanSpace ℝ (Fin 3)}
    (hx : x ∈ ball 0 (1 / 64 : ℝ)) : boundaryHolderBump x = 1 :=
  boundaryHolderBump.one_of_mem_closedBall (ball_subset_closedBall hx)

lemma gradient_boundaryHolderBump_eq_zero {x : EuclideanSpace ℝ (Fin 3)}
    (hx : x ∈ ball 0 (1 / 64 : ℝ)) : gradient boundaryHolderBump x = 0 := by
  have he := boundaryHolderBump.eventuallyEq_one_of_mem_ball hx
  ext i
  rw [gradient_apply_eq_fderiv_single, he.fderiv_eq]
  simp

lemma boundaryHolderBump_support : tsupport boundaryHolderBump ⊆
    coordinateCube 3 (1 / 16 : ℝ) := by
  intro x hx i
  have hx' : ‖x‖ ≤ (1 / 32 : ℝ) := by
    rw [boundaryHolderBump.tsupport_eq] at hx
    change dist x 0 ≤ (1 / 32 : ℝ) at hx
    simpa only [dist_zero_right] using hx
  have hi : |x i| ≤ ‖x‖ := PiLp.norm_apply_le x i
  linarith

lemma boundary_holder_halfCube_subset : coordinateHalfCube (Fin.last 2) (1 / 8 : ℝ) ⊆
    ball (0 : EuclideanSpace ℝ (Fin 3)) 1 ∩ {x | 0 < x (Fin.last 2)} := by
  intro x hx
  refine ⟨?_, hx.2⟩
  have hh := norm_le_succ_card_mul_of_mem_coordinateCube (by norm_num : 0 ≤ (1 / 8 : ℝ)) hx.1
  change dist x 0 < 1
  rw [dist_zero_right]
  norm_num at hh
  linarith

lemma boundary_holder_cube_subset : coordinateCube 3 (1 / 8 : ℝ) ⊆
    ball (0 : EuclideanSpace ℝ (Fin 3)) 1 := by
  intro x hx
  have hh := norm_le_succ_card_mul_of_mem_coordinateCube (by norm_num : 0 ≤ (1 / 8 : ℝ)) hx
  change dist x 0 < 1
  rw [dist_zero_right]
  norm_num at hh
  linarith

/-- The explicit localized zero extension of the scalar function. -/
def boundaryHolderZeroFunction (f : EuclideanSpace ℝ (Fin 3) → ℝ) :
    EuclideanSpace ℝ (Fin 3) → ℝ :=
  {x | 0 < x (Fin.last 2)}.indicator (fun x => boundaryHolderBump x * f x)

/-- The explicit weak gradient of the localized zero extension. -/
def boundaryHolderZeroGradient (f : EuclideanSpace ℝ (Fin 3) → ℝ)
    (G : EuclideanSpace ℝ (Fin 3) → EuclideanSpace ℝ (Fin 3)) :
    EuclideanSpace ℝ (Fin 3) → EuclideanSpace ℝ (Fin 3) :=
  {x | 0 < x (Fin.last 2)}.indicator
    (fun x => boundaryHolderBump x • G x + f x • gradient boundaryHolderBump x)

lemma boundaryHolderZeroFunction_eq (f : EuclideanSpace ℝ (Fin 3) → ℝ)
    {x : EuclideanSpace ℝ (Fin 3)} (hx : x ∈ ball 0 (1 / 64 : ℝ))
    (hxu : 0 < x (Fin.last 2)) : boundaryHolderZeroFunction f x = f x := by
  simp only [boundaryHolderZeroFunction, indicator_apply, mem_ofPred_eq, hxu, ↓reduceIte,
    boundaryHolderBump_eq_one hx, one_mul]

lemma boundaryHolderZeroGradient_eq (f : EuclideanSpace ℝ (Fin 3) → ℝ)
    (G : EuclideanSpace ℝ (Fin 3) → EuclideanSpace ℝ (Fin 3))
    {x : EuclideanSpace ℝ (Fin 3)} (hx : x ∈ ball 0 (1 / 64 : ℝ))
    (hxu : 0 < x (Fin.last 2)) : boundaryHolderZeroGradient f G x = G x := by
  simp only [boundaryHolderZeroGradient, indicator_apply, mem_ofPred_eq, hxu, ↓reduceIte,
    boundaryHolderBump_eq_one hx, gradient_boundaryHolderBump_eq_zero hx,
    one_smul, smul_zero, add_zero]

lemma boundaryHolderZeroGradient_eq_zero (f : EuclideanSpace ℝ (Fin 3) → ℝ)
    (G : EuclideanSpace ℝ (Fin 3) → EuclideanSpace ℝ (Fin 3))
    {x : EuclideanSpace ℝ (Fin 3)} (hx : x (Fin.last 2) ≤ 0) :
    boundaryHolderZeroGradient f G x = 0 := by
  simp only [boundaryHolderZeroGradient, indicator_apply, mem_ofPred_eq,
    not_lt_of_ge hx, ↓reduceIte]

/-- Zero actual flat trace of a genuine half-ball H¹ function gives this concrete
global H¹ zero extension; no extension or gradient hypothesis is added. -/
theorem HasH1GradientOn.boundary_zero_extension_ball
    {f : EuclideanSpace ℝ (Fin 3) → ℝ}
    {G : EuclideanSpace ℝ (Fin 3) → EuclideanSpace ℝ (Fin 3)}
    (hf : HasH1GradientOn f G (ball 0 1 ∩ {x | 0 < x (Fin.last 2)}))
    (hT : HasZeroFlatTraceOn f G (ball 0 1)) :
    HasH1GradientOn (boundaryHolderZeroFunction f) (boundaryHolderZeroGradient f G) univ :=
  (hf.mono boundary_holder_halfCube_subset).boundary_zero_extension_halfCube (by norm_num)
    (hT.mono boundary_holder_cube_subset) boundaryHolderBump.contDiff
    boundaryHolderBump.hasCompactSupport boundaryHolderBump_support

lemma IsWeakDivergenceEquationOn.boundary_localized
    {A : EuclideanSpace ℝ (Fin 3) → EuclideanSpace ℝ (Fin 3) →L[ℝ] EuclideanSpace ℝ (Fin 3)}
    {f : EuclideanSpace ℝ (Fin 3) → ℝ}
    {G H : EuclideanSpace ℝ (Fin 3) → EuclideanSpace ℝ (Fin 3)}
    (hw : IsWeakDivergenceEquationOn A G H (ball 0 1 ∩ {x | 0 < x (Fin.last 2)})) :
    IsWeakDivergenceEquationOn A (boundaryHolderZeroGradient f G) H
      (ball 0 (1 / 64 : ℝ) ∩ {x | 0 < x (Fin.last 2)}) := by
  apply (hw.mono (inter_subset_inter_left _ (ball_subset_ball (by norm_num)))).congr_gradient_ae
    (isOpen_ball.inter boundary_holder_open_upper).measurableSet
  filter_upwards [ae_restrict_mem
    (isOpen_ball.inter (boundary_holder_open_upper (k := 2))).measurableSet] with x hx
  exact (boundaryHolderZeroGradient_eq f G hx.1 hx.2).symm

end LiquidDrop

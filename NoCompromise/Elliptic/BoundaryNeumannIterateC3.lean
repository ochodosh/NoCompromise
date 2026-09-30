module

public import NoCompromise.Elliptic.BoundaryNeumannIterateStep

@[expose] public section

/-!
# The first smooth boundary Neumann iteration as C³ regularity

Under the hypotheses of `boundary_neumann_tangential_c2_holder`, the solution `w` is
C³ on the half ball of radius `1/2 · 3/8`, and all its third derivatives are bounded
and α-Hölder there. The tangential derivatives `∂ᵢw` (`i ≠ 3`) are C² by the
tangential theorem. The normal derivative `∂₃w` is C² because its first partials are
C¹: `∂ₗ∂₃w = ∂₃∂ₗw` for tangential `l` (symmetry of the Hessian), and `∂₃∂₃w` equals
the C¹ expression obtained by solving the classical equation for it (using
`A₃₃ ≥ lam > 0`). A function whose coordinate partials are all C² is C³.
-/

noncomputable section
open MeasureTheory Filter Metric Set InnerProductSpace
open scoped ENNReal Topology Gradient RealInnerProductSpace
namespace LiquidDrop
set_option maxSynthPendingDepth 8

/-- A real linear functional on `ℝ³` is the sum of its coordinate entries times the
coordinate projections. -/
lemma boundaryNeumannIterateC3_functional_eq_sum (ℓ : EuclideanSpace ℝ (Fin 3) →L[ℝ] ℝ) :
    ℓ = ∑ k, ℓ (EuclideanSpace.single k 1) •
      (EuclideanSpace.proj k : EuclideanSpace ℝ (Fin 3) →L[ℝ] ℝ) := by
  apply ContinuousLinearMap.coe_injective
  refine (EuclideanSpace.basisFun (Fin 3) ℝ).toBasis.ext fun i => ?_
  simp only [OrthonormalBasis.coe_toBasis, EuclideanSpace.basisFun_apply,
    ContinuousLinearMap.coe_coe]
  simp

/-- On an open set, a differentiable real function on `ℝ³` whose coordinate partials
`x ↦ ∂ᵢg(x)` are all Cⁿ is Cⁿ⁺¹. -/
lemma boundaryNeumannIterateC3_contDiffOn_succ {S : Set (EuclideanSpace ℝ (Fin 3))}
    (hS : IsOpen S) {g : EuclideanSpace ℝ (Fin 3) → ℝ} {n : ℕ}
    (hg : DifferentiableOn ℝ g S)
    (hp : ∀ i : Fin 3,
      ContDiffOn ℝ n (fun x => fderiv ℝ g x (EuclideanSpace.single i 1)) S) :
    ContDiffOn ℝ (n + 1) g S := by
  rw [contDiffOn_succ_iff_fderiv_of_isOpen hS]
  refine ⟨hg, fun h => absurd h (by simp), ?_⟩
  have hsum : ContDiffOn ℝ n (fun x => ∑ k, fderiv ℝ g x (EuclideanSpace.single k 1) •
      (EuclideanSpace.proj k : EuclideanSpace ℝ (Fin 3) →L[ℝ] ℝ)) S :=
    ContDiffOn.sum fun k _ => (hp k).smul contDiffOn_const
  exact hsum.congr fun x _ => boundaryNeumannIterateC3_functional_eq_sum _

/-- First step of the smooth iteration for the homogeneous conormal problem
(blueprint `thm:boundary-neumann`), as C³ regularity. Under the hypotheses of
`boundary_neumann_tangential_c2_holder`, `w` is C³ on the half ball of radius
`1/2 · 3/8`, and all its third derivatives `∂ₖ∂ₗ∂ₘw`
(`boundaryNeumannC2Entry (∂ₘw) x k l`) are bounded and α-Hölder there. -/
theorem boundary_neumann_c3_holder {α : ℝ} (hα : 0 < α) (hα1 : α < 1)
    {lam cap : ℝ} (hlam : 0 < lam) (hcap : 0 ≤ cap)
    {U : Set (EuclideanSpace ℝ (Fin 3))} (hU : IsOpen U)
    (hUc : closure (boundaryHalfBall 1) ⊆ U)
    {A : EuclideanSpace ℝ (Fin 3) → EuclideanSpace ℝ (Fin 3) →L[ℝ]
      EuclideanSpace ℝ (Fin 3)}
    {H : EuclideanSpace ℝ (Fin 3) → EuclideanSpace ℝ (Fin 3)}
    {w : EuclideanSpace ℝ (Fin 3) → ℝ}
    (hA : ContDiffOn ℝ 3 A U) (hH : ContDiffOn ℝ 3 H U) (hw : ContDiffOn ℝ 2 w U)
    (hhol : ∃ C, ∀ i j : Fin 3, ∀ x ∈ closure (boundaryHalfBall 1),
      ∀ y ∈ closure (boundaryHalfBall 1),
        |boundaryNeumannC2Entry w x i j - boundaryNeumannC2Entry w y i j| ≤ C * dist x y ^ α)
    (hcap' : ∀ x ∈ closure (boundaryHalfBall 1), ‖A x‖ ≤ cap)
    (hell : ∀ x ∈ closure (boundaryHalfBall 1), ∀ v, lam * ‖v‖ ^ 2 ≤ inner ℝ (A x v) v)
    (hcross : ∀ x ∈ closure (boundaryHalfBall 1), x (Fin.last 2) = 0 →
      ∀ j : Fin 3, j ≠ Fin.last 2 →
        A x (EuclideanSpace.single j 1) (Fin.last 2) = 0 ∧
        A x (EuclideanSpace.single (Fin.last 2) 1) j = 0)
    (hH0 : ∀ x ∈ closure (boundaryHalfBall 1), x (Fin.last 2) = 0 → H x (Fin.last 2) = 0)
    (hw0 : ∀ x ∈ closure (boundaryHalfBall 1), x (Fin.last 2) = 0 →
      gradient w x (Fin.last 2) = 0)
    (he : IsBoundaryNeumannEquationOn A (gradient w) H 1) :
    ContDiffOn ℝ 3 w (boundaryHalfBall (1 / 2 * (3 / 8))) ∧
    ∃ C, ∀ m k l : Fin 3,
      (∀ x ∈ boundaryHalfBall (1 / 2 * (3 / 8)),
        |boundaryNeumannC2Entry (fun x => fderiv ℝ w x (EuclideanSpace.single m 1)) x k l| ≤
          C) ∧
      ∀ x ∈ boundaryHalfBall (1 / 2 * (3 / 8)), ∀ y ∈ boundaryHalfBall (1 / 2 * (3 / 8)),
        |boundaryNeumannC2Entry (fun x => fderiv ℝ w x (EuclideanSpace.single m 1)) x k l -
          boundaryNeumannC2Entry (fun x => fderiv ℝ w x (EuclideanSpace.single m 1)) y k l| ≤
          C * dist x y ^ α := by
  refine ⟨?_, boundary_neumann_third_derivatives_holder hα hα1 hlam hcap hU hUc hA hH hw
    hhol hcap' hell hcross hH0 hw0 he⟩
  have hS : IsOpen (boundaryHalfBall (1 / 2 * (3 / 8) : ℝ)) := isOpen_boundaryHalfBall _
  have hS1 : boundaryHalfBall (1 / 2 * (3 / 8) : ℝ) ⊆ boundaryHalfBall 1 :=
    boundaryHalfBall_mono (by norm_num)
  have hSU : boundaryHalfBall (1 / 2 * (3 / 8) : ℝ) ⊆ U :=
    hS1.trans (subset_closure.trans hUc)
  have hSK1 : boundaryHalfBall (1 / 2 * (3 / 8) : ℝ) ⊆ closure (boundaryHalfBall 1) :=
    hS1.trans subset_closure
  have h0 : (0 : Fin 3) ≠ 2 := by decide
  have h1 : (1 : Fin 3) ≠ 2 := by decide
  have hfin : ∀ t : Fin 3, t = 0 ∨ t = 1 ∨ t = 2 := by decide
  -- the tangential derivatives are C²
  have hT : ∀ t : Fin 3, t ≠ 2 →
      ContDiffOn ℝ 2 (fun x => fderiv ℝ w x (EuclideanSpace.single t 1))
        (boundaryHalfBall (1 / 2 * (3 / 8))) := fun t ht =>
    (boundary_neumann_tangential_c2_holder hα hα1 hlam hcap hU hUc hA hH hw hhol hcap' hell
      hcross hH0 hw0 he (i := t) ht).1
  -- Hessian entries with a tangential second index are C¹
  have hE : ∀ i j : Fin 3, j ≠ 2 → ContDiffOn ℝ 1 (fun x => boundaryNeumannC2Entry w x i j)
      (boundaryHalfBall (1 / 2 * (3 / 8))) := fun i j hj =>
    ((hT j hj).fderiv_of_isOpen hS (by norm_num)).clm_apply contDiffOn_const
  have hsymm : ∀ x ∈ boundaryHalfBall 1, ∀ i j : Fin 3,
      boundaryNeumannC2Entry w x i j = boundaryNeumannC2Entry w x j i :=
    fun x hx i j => boundary_neumann_c2_entry_comm (hw.mono (subset_closure.trans hUc)) hx i j
  -- the pieces of the classical equation are C¹
  have ha : ∀ i j : Fin 3, ContDiffOn ℝ 1 (fun x => A x (EuclideanSpace.single j 1) i)
      (boundaryHalfBall (1 / 2 * (3 / 8))) := fun i j =>
    ((EuclideanSpace.proj i).contDiff.comp_contDiffOn
      ((hA.of_le (by norm_num)).clm_apply contDiffOn_const)).mono hSU
  have hdA : ∀ i j : Fin 3, ContDiffOn ℝ 1
      (fun x => fderiv ℝ A x (EuclideanSpace.single i 1) (EuclideanSpace.single j 1) i)
      (boundaryHalfBall (1 / 2 * (3 / 8))) := fun i j =>
    ((EuclideanSpace.proj i).contDiff.comp_contDiffOn
      (((hA.fderiv_of_isOpen hU (by norm_num)).clm_apply contDiffOn_const).clm_apply
        contDiffOn_const)).mono hSU
  have hdw : ∀ j : Fin 3, ContDiffOn ℝ 1 (fun x => fderiv ℝ w x (EuclideanSpace.single j 1))
      (boundaryHalfBall (1 / 2 * (3 / 8))) := fun j =>
    ((hw.fderiv_of_isOpen hU (by norm_num)).clm_apply contDiffOn_const).mono hSU
  have hdivH : ContDiffOn ℝ 1 (divergenceN H) (boundaryHalfBall (1 / 2 * (3 / 8))) := by
    unfold divergenceN
    exact (ContDiffOn.sum fun i _ => (EuclideanSpace.proj i).contDiff.comp_contDiffOn
      ((hH.fderiv_of_isOpen hU (by norm_num)).clm_apply contDiffOn_const)).mono hSU
  have hlow : ∀ x ∈ boundaryHalfBall (1 / 2 * (3 / 8) : ℝ),
      lam ≤ A x (EuclideanSpace.single 2 1) 2 := by
    intro x hx
    have h := hell x (hSK1 hx) (EuclideanSpace.single 2 1)
    simpa [EuclideanSpace.inner_single_right, PiLp.norm_single] using h
  -- the normal second derivative solved from the classical equation
  let T : EuclideanSpace ℝ (Fin 3) → ℝ := fun x => ∑ i, ∑ j,
    fderiv ℝ A x (EuclideanSpace.single i 1) (EuclideanSpace.single j 1) i *
      fderiv ℝ w x (EuclideanSpace.single j 1)
  let R : EuclideanSpace ℝ (Fin 3) → ℝ := fun x =>
    A x (EuclideanSpace.single 0 1) 0 * boundaryNeumannC2Entry w x 0 0 +
    A x (EuclideanSpace.single 1 1) 0 * boundaryNeumannC2Entry w x 0 1 +
    A x (EuclideanSpace.single 2 1) 0 * boundaryNeumannC2Entry w x 2 0 +
    A x (EuclideanSpace.single 0 1) 1 * boundaryNeumannC2Entry w x 1 0 +
    A x (EuclideanSpace.single 1 1) 1 * boundaryNeumannC2Entry w x 1 1 +
    A x (EuclideanSpace.single 2 1) 1 * boundaryNeumannC2Entry w x 2 1 +
    A x (EuclideanSpace.single 0 1) 2 * boundaryNeumannC2Entry w x 2 0 +
    A x (EuclideanSpace.single 1 1) 2 * boundaryNeumannC2Entry w x 2 1
  let Q : EuclideanSpace ℝ (Fin 3) → ℝ := fun x =>
    (divergenceN H x - T x - R x) / A x (EuclideanSpace.single 2 1) 2
  have hTc : ContDiffOn ℝ 1 T (boundaryHalfBall (1 / 2 * (3 / 8))) :=
    ContDiffOn.sum fun i _ => ContDiffOn.sum fun j _ => (hdA i j).mul (hdw j)
  have hRc : ContDiffOn ℝ 1 R (boundaryHalfBall (1 / 2 * (3 / 8))) :=
    ((((((((ha 0 0).mul (hE 0 0 h0)).add ((ha 0 1).mul (hE 0 1 h1))).add
      ((ha 0 2).mul (hE 2 0 h0))).add ((ha 1 0).mul (hE 1 0 h0))).add
      ((ha 1 1).mul (hE 1 1 h1))).add ((ha 1 2).mul (hE 2 1 h1))).add
      ((ha 2 0).mul (hE 2 0 h0))).add ((ha 2 1).mul (hE 2 1 h1))
  have hQc : ContDiffOn ℝ 1 Q (boundaryHalfBall (1 / 2 * (3 / 8))) :=
    ((hdivH.sub hTc).sub hRc).div (ha 2 2) fun x hx => (hlam.trans_le (hlow x hx)).ne'
  have hQeq : ∀ x ∈ boundaryHalfBall (1 / 2 * (3 / 8) : ℝ),
      boundaryNeumannC2Entry w x 2 2 = Q x := by
    intro x hx
    have hx1 := hS1 hx
    have heqn := boundaryNeumannIterate_pointwise_equation hUc (hA.of_le (by norm_num))
      (hH.of_le (by norm_num)) hw he x hx1
    have hpos : 0 < A x (EuclideanSpace.single 2 1) 2 := hlam.trans_le (hlow x hx)
    simp only [Fin.sum_univ_three] at heqn
    rw [hsymm x hx1 0 2, hsymm x hx1 1 2] at heqn
    simp only [Q, T, R]
    rw [eq_div_iff hpos.ne']
    simp only [Fin.sum_univ_three]
    linear_combination heqn
  -- the normal derivative is C²
  have hN : ContDiffOn ℝ 2 (fun x => fderiv ℝ w x (EuclideanSpace.single 2 1))
      (boundaryHalfBall (1 / 2 * (3 / 8))) := by
    have h := boundaryNeumannIterateC3_contDiffOn_succ (n := 1) hS
      (g := fun x => fderiv ℝ w x (EuclideanSpace.single 2 1))
      ((hdw 2).differentiableOn one_ne_zero) fun l => by
        obtain rfl | rfl | rfl := hfin l
        · exact (hE 2 0 h0).congr fun y hy => hsymm y (hS1 hy) 0 2
        · exact (hE 2 1 h1).congr fun y hy => hsymm y (hS1 hy) 1 2
        · exact hQc.congr fun y hy => hQeq y hy
    exact h
  -- all coordinate partials of `w` are C², so `w` is C³
  have h := boundaryNeumannIterateC3_contDiffOn_succ (n := 2) hS (g := w)
    ((hw.mono hSU).differentiableOn two_ne_zero) fun i => by
      obtain rfl | rfl | rfl := hfin i
      · exact hT 0 h0
      · exact hT 1 h1
      · exact hN
  exact h

end LiquidDrop

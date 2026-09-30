module

public import NoCompromise.Elliptic.BoundaryNeumannC2Tangential
public import Mathlib.Topology.ExtendFrom

@[expose] public section

/-!
# Continuous extensions of the tangential second derivatives

The extension is constructed from interior limits. No claim is made about ambient
derivatives of an arbitrary chosen extension of `w` outside the closed half ball.
-/

noncomputable section
open MeasureTheory Filter Metric Set InnerProductSpace
open scoped ENNReal NNReal Topology Gradient RealInnerProductSpace
namespace LiquidDrop

/-- A bounded Hölder field with positive exponent has a continuous extension to
the closure, with the same uniform bound and Hölder constant. -/
theorem boundary_neumann_c2_holder_extension {E F : Type*}
    [NormedAddCommGroup E] [NormedAddCommGroup F] [CompleteSpace F]
    {U : Set E} {f : E → F} {α C : ℝ} (hα : 0 < α)
    (hb : ∀ x ∈ U, ‖f x‖ ≤ C)
    (hh : ∀ x ∈ U, ∀ y ∈ U, ‖f x - f y‖ ≤ C * dist x y ^ α) :
    ∃ g : E → F, EqOn g f U ∧ ContinuousOn g (closure U) ∧
      (∀ x ∈ closure U, ‖g x‖ ≤ C) ∧
      ∀ x ∈ closure U, ∀ y ∈ closure U, ‖g x - g y‖ ≤ C * dist x y ^ α := by
  have ht : Tendsto (fun t : ℝ => C * t ^ α) (𝓝 0) (𝓝 0) := by
    have hc : Continuous (fun t : ℝ => C * t ^ α) :=
      continuous_const.mul (Real.continuous_rpow_const hα.le)
    simpa only [Real.zero_rpow hα.ne', mul_zero] using hc.tendsto 0
  have huc : UniformContinuousOn f U := by
    apply Metric.uniformContinuousOn_iff.mpr
    intro ε hε
    obtain ⟨δ, hδ, hmod⟩ := Metric.tendsto_nhds_nhds.mp ht ε hε
    refine ⟨δ, hδ, ?_⟩
    intro x hx y hy hxy
    apply (show dist (f x) (f y) ≤ C * dist x y ^ α by
      simpa only [dist_eq_norm] using hh x hx y hy).trans_lt
    have h : dist (C * dist x y ^ α) 0 < ε := hmod
      (by simpa only [Real.dist_eq, sub_zero, abs_of_nonneg dist_nonneg] using hxy)
    exact (le_abs_self _).trans_lt (by simpa only [Real.dist_eq, sub_zero] using h)
  have hlim : ∀ x ∈ closure U, ∃ y, Tendsto f (𝓝[U] x) (𝓝 y) := by
    intro x hx
    have : NeBot (𝓝[U] x) := mem_closure_iff_nhdsWithin_neBot.mp hx
    exact cauchy_map_iff_exists_tendsto.mp
      ((cauchy_nhds.mono nhdsWithin_le_nhds).map_of_le huc inf_le_right)
  let g := extendFrom U f
  have he : EqOn g f U := extendFrom_extends huc.continuousOn
  have hc : ContinuousOn g (closure U) := continuousOn_extendFrom Subset.rfl hlim
  refine ⟨g, he, hc, ?_, ?_⟩
  · exact le_on_closure (fun x hx => by rw [he hx]; exact hb x hx)
      hc.norm continuousOn_const
  · apply boundary_nondiv_holder_on_closure hα.le hc
    intro x hx y hy
    rw [he hx, he hy]
    exact hh x hx y hy

/-- The tangential rows of the second derivative extend to the flat face (indeed,
the whole closed radius `3/8` half ball) with a uniform bound and Hölder modulus. -/
theorem boundary_neumann_tangential_second_derivatives_closed {α lam cap M N : ℝ}
    (hα : 0 < α) (hα1 : α < 1) (hlam : 0 < lam) (hcap : 0 ≤ cap)
    (hM : 0 ≤ M) (hN : 0 ≤ N) :
    ∃ C > 0, ∀ (A : EuclideanSpace ℝ (Fin 3) → EuclideanSpace ℝ (Fin 3) →L[ℝ]
        EuclideanSpace ℝ (Fin 3))
      (H : EuclideanSpace ℝ (Fin 3) → EuclideanSpace ℝ (Fin 3))
      (w : EuclideanSpace ℝ (Fin 3) → ℝ),
      BoundaryNeumannClosedData α lam cap M N A H w →
      ∀ i : Fin 3, i ≠ Fin.last 2 →
        DifferentiableOn ℝ (fun x => fderiv ℝ w x (EuclideanSpace.single i 1))
          (boundaryHalfBall (3 / 8)) ∧
        ∃ D : EuclideanSpace ℝ (Fin 3) → EuclideanSpace ℝ (Fin 3),
          EqOn D (gradient (fun x => fderiv ℝ w x (EuclideanSpace.single i 1)))
            (boundaryHalfBall (3 / 8)) ∧
          ContinuousOn D (closure (boundaryHalfBall (3 / 8))) ∧
          (∀ x ∈ closure (boundaryHalfBall (3 / 8)), ‖D x‖ ≤ C) ∧
          ∀ x ∈ closure (boundaryHalfBall (3 / 8)),
            ∀ y ∈ closure (boundaryHalfBall (3 / 8)),
              ‖D x - D y‖ ≤ C * dist x y ^ α := by
  obtain ⟨C, hC, ht⟩ := boundary_neumann_tangential_derivative_c1_holder_original
    hα hα1 hlam hcap hM hN
  refine ⟨C, hC, ?_⟩
  intro A H w d i hi
  obtain ⟨hd, hb, hh⟩ := ht A H w d i hi
  exact ⟨hd, boundary_neumann_c2_holder_extension hα hb hh⟩

end LiquidDrop

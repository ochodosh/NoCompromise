module

public import NoCompromise.Sobolev.AnnulusDomain

@[expose] public section

/-!
# Poincaré and the genuine L² trace on admissible domains

A single positive constant bounds both inequalities on every bounded connected
open Lipschitz domain. The geometric C¹ domains, balls, annuli and cubes used in
the blueprint have the required charts in the imported geometric modules.
-/

noncomputable section
open MeasureTheory Set Filter Metric Topology
open scoped ENNReal NNReal Gradient
namespace LiquidDrop

/-- Both clauses of blueprint `prop:poincare-trace` on bounded connected open
Lipschitz domains. The trace is a genuine bounded operator, agrees with continuous
representatives, and is the L² limit of the boundary values of smooth H¹
approximations. The same positive constant controls both inequalities. -/
theorem exists_h1_poincare_trace {D : Set AmbientSpace}
    (hD : IsOpen D) (hcD : IsPreconnected D) (hbD : Bornology.IsBounded D)
    (hL : HasLipschitzBoundary D) :
    ∃ T : H1Space D →L[ℝ] Lp ℝ 2 ((hausdorffMeasure2 3).restrict (frontier D)),
    ∃ C : ℝ, 0 < C ∧ ‖T‖ ≤ C ∧
      (∀ f G, HasH1GradientOn f G D →
        lpNorm (fun x => f x - ⨍ y in D, f y) 2 (volume.restrict D) ≤
          C * lpNorm G 2 (volume.restrict D)) ∧
      (∀ u : H1Space D, ‖T u‖ ≤ C *
        (lpNorm u 2 (volume.restrict D) + lpNorm u.gradientLp 2 (volume.restrict D))) ∧
      (∀ f G (hf : HasH1GradientOn f G D), Continuous f →
        ∀ᵐ x ∂(hausdorffMeasure2 3).restrict (frontier D),
          T (H1Space.ofFunction f G hf) x = f x) ∧
      ∀ u : H1Space D, ∃ v : ℕ → AmbientSpace → ℝ,
        ∃ hv : ∀ j, HasH1GradientOn (v j) (gradient (v j)) D,
        ∃ hb : ∀ j, MemLp (v j) 2 ((hausdorffMeasure2 3).restrict (frontier D)),
          (∀ j, ContDiff ℝ (⊤ : ℕ∞) (v j)) ∧
          Tendsto (fun j => H1Space.ofFunction (v j) (gradient (v j)) (hv j)) atTop (𝓝 u) ∧
          Tendsto (fun j => (hb j).toLp (v j)) atTop (𝓝 (T u)) := by
  obtain ⟨P, hP, hPI⟩ := h1_poincare_spatial hD hcD hbD hL
  obtain ⟨T, C, hC, hTC, hTI, hT, happrox⟩ :=
    exists_h1_trace hD hbD hL
  refine ⟨T, max P C, lt_of_lt_of_le hP (le_max_left _ _),
    hTC.trans (le_max_right _ _), ?_, ?_, hT, happrox⟩
  · intro f G hf
    exact (hPI f G hf).trans (mul_le_mul_of_nonneg_right
      (le_max_left _ _) lpNorm_nonneg)
  · intro u
    exact (hTI u).trans (mul_le_mul_of_nonneg_right (le_max_right _ _)
      (add_nonneg lpNorm_nonneg lpNorm_nonneg))

end LiquidDrop

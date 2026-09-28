import NoCompromise.Elliptic.WeakMaximumCore
import NoCompromise.Sobolev.H1TraceKernel

/-!
# Weak maximum principle with the actual boundary trace

On bounded Lipschitz domains in every positive dimension, the actual trace
commutes with positive parts and its kernel is the genuine H¹₀ closure.
The proved nonnegative test approximation and Poincaré inequality complete
the positive-part energy argument from the original distributional hypothesis.
-/

noncomputable section
open MeasureTheory Filter Set InnerProductSpace
open scoped ENNReal NNReal Topology Gradient RealInnerProductSpace
namespace LiquidDrop
set_option maxSynthPendingDepth 8

/-- The weak maximum principle on bounded Lipschitz domains, using the actual
Hausdorff boundary trace and the original nonnegative smooth interior tests.
Neither connectedness nor a separate positive-part admissibility hypothesis
is required. -/
theorem weak_maximum {k : ℕ}
    {D : Set (EuclideanSpace ℝ (Fin (k + 1)))} (hD : IsOpen D)
    (hbD : Bornology.IsBounded D) (hL : HasLipschitzBoundary D)
    (T : H1Space D →L[ℝ]
      Lp ℝ 2 ((Measure.euclideanHausdorffMeasure k).restrict (frontier D)))
    (hT : ∀ f G (hf : HasH1GradientOn f G D), Continuous f →
      ⇑(T (H1Space.ofFunction f G hf))
        =ᵐ[(Measure.euclideanHausdorffMeasure k).restrict (frontier D)] f)
    (u : H1Space D)
    (hu : ∀ φ : EuclideanSpace ℝ (Fin (k + 1)) → ℝ,
      ContDiff ℝ (⊤ : ℕ∞) φ → HasCompactSupport φ → tsupport φ ⊆ D →
      (∀ x, 0 ≤ φ x) → (∫ x in D, inner ℝ (u.gradientLp x) (gradient φ x)) ≤ 0)
    (hb : ∀ᵐ x ∂(Measure.euclideanHausdorffMeasure k).restrict (frontier D), T u x ≤ 0) :
    ∀ᵐ x ∂volume.restrict D, u x ≤ 0 := by
  exact weak_maximum_of_trace_kernel (Nat.succ_pos k) hD hbD hL T hT
    (fun v hz => H1Space.mem_h1Zero_of_trace_zero hD hbD hL T hT v hz) u hu hb

/-- Blueprint `lem:weak-max`, with `Δu ≥ 0` stated directly as the nonnegative
scalar distributional pairing against every nonnegative smooth interior test. -/
theorem weak_maximum_distributional {k : ℕ}
    {D : Set (EuclideanSpace ℝ (Fin (k + 1)))} (hD : IsOpen D)
    (hbD : Bornology.IsBounded D) (hL : HasLipschitzBoundary D)
    (T : H1Space D →L[ℝ]
      Lp ℝ 2 ((Measure.euclideanHausdorffMeasure k).restrict (frontier D)))
    (hT : ∀ f G (hf : HasH1GradientOn f G D), Continuous f →
      ⇑(T (H1Space.ofFunction f G hf))
        =ᵐ[(Measure.euclideanHausdorffMeasure k).restrict (frontier D)] f)
    (u : H1Space D)
    (hu : ∀ φ : EuclideanSpace ℝ (Fin (k + 1)) → ℝ,
      ContDiff ℝ (⊤ : ℕ∞) φ → HasCompactSupport φ → tsupport φ ⊆ D →
      (∀ x, 0 ≤ φ x) → 0 ≤ ∫ x in D, u x * laplacianN φ x)
    (hb : ∀ᵐ x ∂(Measure.euclideanHausdorffMeasure k).restrict (frontier D), T u x ≤ 0) :
    ∀ᵐ x ∂volume.restrict D, u x ≤ 0 := by
  exact weak_maximum_distributional_of_trace_kernel (Nat.succ_pos k) hD hbD hL T hT
    (fun v hz => H1Space.mem_h1Zero_of_trace_zero hD hbD hL T hT v hz) u hu hb

/-- The constructed actual trace satisfies the weak maximum principle for all
H¹ functions, without taking any trace-kernel property as an input. -/
theorem exists_h1_trace_with_weak_maximum {k : ℕ}
    {D : Set (EuclideanSpace ℝ (Fin (k + 1)))} (hD : IsOpen D)
    (hbD : Bornology.IsBounded D) (hL : HasLipschitzBoundary D) :
    ∃ T : H1Space D →L[ℝ]
      Lp ℝ 2 ((Measure.euclideanHausdorffMeasure k).restrict (frontier D)),
      (∀ f G (hf : HasH1GradientOn f G D), Continuous f →
        ⇑(T (H1Space.ofFunction f G hf))
          =ᵐ[(Measure.euclideanHausdorffMeasure k).restrict (frontier D)] f) ∧
      ∀ u : H1Space D,
        (∀ φ : EuclideanSpace ℝ (Fin (k + 1)) → ℝ,
          ContDiff ℝ (⊤ : ℕ∞) φ → HasCompactSupport φ → tsupport φ ⊆ D →
          (∀ x, 0 ≤ φ x) → 0 ≤ ∫ x in D, u x * laplacianN φ x) →
        (∀ᵐ x ∂(Measure.euclideanHausdorffMeasure k).restrict (frontier D), T u x ≤ 0) →
        ∀ᵐ x ∂volume.restrict D, u x ≤ 0 := by
  obtain ⟨T, _, _, _, hT⟩ := exists_h1_trace_operator hD hbD hL
  exact ⟨T, hT, fun u hu hb => weak_maximum_distributional hD hbD hL T hT u hu hb⟩

end LiquidDrop

import NoCompromise.Elliptic.BoundaryHolderTraceAlgebra
import NoCompromise.Elliptic.BoundaryHolderVariance

/-!
# Normal affine subtraction for boundary decay

The normal excess is invariant under normal constant shifts. Subtracting a
normal affine function preserves the genuine H¹ relation, the frozen weak
equation, and the actual zero flat trace.
-/

noncomputable section
open MeasureTheory Filter Metric Set InnerProductSpace
open scoped ENNReal NNReal Topology Gradient RealInnerProductSpace
namespace LiquidDrop

lemma boundary_normal_excess_sub_normal {α E : Type*} [MeasurableSpace α]
    [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]
    {μ : Measure α} [IsFiniteMeasure μ] {f : α → E}
    (hf : MemLp f 2 μ) (n : E) (hn : ‖n‖ = 1) (c : ℝ) :
    boundaryNormalExcess n (fun x => f x - c • n) μ = boundaryNormalExcess n f μ := by
  have hg : MemLp (fun x => f x - c • n) 2 μ := hf.sub (memLp_const _)
  apply le_antisymm
  · have h := boundary_normal_excess_minimizes hg n hn (boundaryNormalMean n f μ - c)
    have he (x) : f x - c • n - (boundaryNormalMean n f μ - c) • n =
        f x - boundaryNormalMean n f μ • n := by
      module
    simpa only [he, boundaryNormalExcess] using h
  · have h := boundary_normal_excess_minimizes hf n hn
      (boundaryNormalMean n (fun x => f x - c • n) μ + c)
    have he (x) : f x - (boundaryNormalMean n (fun x => f x - c • n) μ + c) • n =
        f x - c • n - boundaryNormalMean n (fun x => f x - c • n) μ • n := by
      module
    simpa only [he, boundaryNormalExcess] using h

lemma boundary_frozen_equation_sub_constant {n : ℕ}
    {D : Set (EuclideanSpace ℝ (Fin n))}
    (A : EuclideanSpace ℝ (Fin n) →L[ℝ] EuclideanSpace ℝ (Fin n))
    {G : EuclideanSpace ℝ (Fin n) → EuclideanSpace ℝ (Fin n)}
    (hG : MemLp G 2 (volume.restrict D))
    (hw : IsWeakDivergenceEquationOn (fun _ => A) G (fun _ => 0) D)
    (c : EuclideanSpace ℝ (Fin n)) :
    IsWeakDivergenceEquationOn (fun _ => A) (fun x => G x - c) (fun _ => 0) D := by
  intro φ hφ hcφ hsφ
  have hcgrad := hcφ.of_isClosed_subset (isClosed_tsupport _) (tsupport_gradient_subset φ)
  have hgrad := continuous_gradient_of_contDiff hφ
  have hmg : MemLp (gradient φ) 2 (volume.restrict D) :=
    hgrad.memLp_of_hasCompactSupport hcgrad
  have hi := integrable_inner_of_memLp_two (A.comp_memLp' hG) hmg
  have hic : Integrable (fun x => inner ℝ (A c) (gradient φ x)) volume :=
    (hgrad.integrable_of_hasCompactSupport hcgrad).const_inner (A c)
  have hset (F : EuclideanSpace ℝ (Fin n) → EuclideanSpace ℝ (Fin n)) :
      (∫ x in D, inner ℝ (F x) (gradient φ x)) = ∫ x, inner ℝ (F x) (gradient φ x) :=
    setIntegral_eq_integral_of_forall_compl_eq_zero (fun x hx => by
      rw [gradient_eq_zero_of_notMem_tsupport (fun ht => hx (hsφ ht)), inner_zero_right])
  have hh : (∫ x in D, inner ℝ (A (G x)) (gradient φ x)) = 0 := by
    rw [hset]
    simpa only [sub_zero] using hw φ hφ hcφ hsφ
  have hz : (∫ x in D, inner ℝ (A c) (gradient φ x)) = 0 := by
    rw [hset]
    exact campanato_integral_inner_const_gradient hφ hcφ (A c)
  simp only [sub_zero]
  rw [← hset]
  simp_rw [map_sub, inner_sub_left]
  have hi' : Integrable (fun x => inner ℝ (A (G x)) (gradient φ x)) (volume.restrict D) := hi
  rw [integral_sub hi' hic.integrableOn, hh, hz, sub_self]

/-- Normal affine subtraction preserves all hypotheses needed by the frozen
half-ball comparison and its boundary derivative estimate. -/
theorem boundary_frozen_sub_normal_affine {k : ℕ}
    {f : EuclideanSpace ℝ (Fin (k + 1)) → ℝ}
    {G : EuclideanSpace ℝ (Fin (k + 1)) → EuclideanSpace ℝ (Fin (k + 1))}
    (hf : HasH1GradientOn f G (ball 0 1 ∩ {x | 0 < x (Fin.last k)}))
    (hT : HasZeroFlatTraceOn f G (ball 0 1))
    (A : EuclideanSpace ℝ (Fin (k + 1)) →L[ℝ] EuclideanSpace ℝ (Fin (k + 1)))
    (hw : IsWeakDivergenceEquationOn (fun _ => A) G (fun _ => 0)
      (ball 0 1 ∩ {x | 0 < x (Fin.last k)})) (c : ℝ) :
    HasH1GradientOn
      (fun x => f x - inner ℝ (c • EuclideanSpace.single (Fin.last k) 1) x)
      (fun x => G x - c • EuclideanSpace.single (Fin.last k) 1)
      (ball 0 1 ∩ {x | 0 < x (Fin.last k)}) ∧
    HasZeroFlatTraceOn
      (fun x => f x - inner ℝ (c • EuclideanSpace.single (Fin.last k) 1) x)
      (fun x => G x - c • EuclideanSpace.single (Fin.last k) 1) (ball 0 1) ∧
    IsWeakDivergenceEquationOn (fun _ => A)
      (fun x => G x - c • EuclideanSpace.single (Fin.last k) 1) (fun _ => 0)
      (ball 0 1 ∩ {x | 0 < x (Fin.last k)}) :=
  ⟨hf.sub ((frozen_hasH1GradientOn_inner_ball _).mono inter_subset_left),
    hT.sub_normal_affine hf c, boundary_frozen_equation_sub_constant A hf.memLp_gradient hw _⟩

end LiquidDrop

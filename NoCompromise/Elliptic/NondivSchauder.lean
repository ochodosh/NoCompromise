module

public import NoCompromise.Elliptic.NondivSchauderNested
public import NoCompromise.Elliptic.NondivSchauderAbsorption
public import NoCompromise.Elliptic.SchauderInterpolationQuantitative

@[expose] public section

/-!
# Interior nondivergence Schauder regularity and the sharp estimate

The original solution is assumed C¹,α and satisfies the equation distributionally.
The conclusion constructs its actual C²,α regularity. The constant is fixed before
all coefficients, solutions, and sources, and the final estimate uses only the
L∞ norm of the solution and the C⁰,α norm of the source.

The Hölder norms are the previously fixed sums of uniform and seminorm terms;
C²,α sums these for the function, first derivative, and second derivative, with
operator norms on derivatives. The coefficient bound M controls the C¹,α norm
of A and the C⁰,α norm of b. The real linear coefficient maps need not be symmetric.
-/

noncomputable section
open MeasureTheory Filter Metric Set InnerProductSpace
open scoped ENNReal Topology Gradient RealInnerProductSpace
namespace LiquidDrop
set_option maxSynthPendingDepth 8

lemma nondiv_lpNorm_top_mono {n : ℕ} {f : EuclideanSpace ℝ (Fin n) → ℝ}
    {U V : Set (EuclideanSpace ℝ (Fin n))}
    (hf : MemLp f ∞ (volume.restrict V)) (hUV : U ⊆ V) :
    lpNorm f ∞ (volume.restrict U) ≤ lpNorm f ∞ (volume.restrict V) := by
  have hm := Measure.restrict_mono hUV (le_refl volume)
  have hfu := hf.mono_measure hm
  rw [← toReal_eLpNorm, ← toReal_eLpNorm]
  exact ENNReal.toReal_mono hf.eLpNorm_ne_top (eLpNorm_mono_measure f hm)

/-- The sharp interior Schauder estimate for a distributional nondivergence
solution, with no second-derivative premise and no solution-dependent constant. -/
theorem nondiv_schauder {n : ℕ} (hn0 : 0 < n) (hn : n < 4)
    {α lam cap M : ℝ} (hα : 0 < α) (hα1 : α < 1)
    (hlam : 0 < lam) (hlamcap : lam ≤ cap) (hM : 0 ≤ M) :
    ∃ C > 0, ∀ (A : EuclideanSpace ℝ (Fin n) →
        EuclideanSpace ℝ (Fin n) →L[ℝ] EuclideanSpace ℝ (Fin n))
      (b : EuclideanSpace ℝ (Fin n) → EuclideanSpace ℝ (Fin n))
      (z f : EuclideanSpace ℝ (Fin n) → ℝ),
      HasC1HolderOn α A (ball 0 1) → HasFiniteHolderNormOn α b (ball 0 1) →
      HasC1HolderOn α z (ball 0 1) → HasFiniteHolderNormOn α f (ball 0 1) →
      nondivC1HolderNorm α A (ball 0 1) ≤ M → holderNorm α b (ball 0 1) ≤ M →
      (∀ x ∈ ball 0 1, ‖A x‖ ≤ cap) →
      (∀ x ∈ ball 0 1, ∀ v, lam * ‖v‖ ^ 2 ≤ inner ℝ v (A x v)) →
      IsWeakNondivergenceEquationOn A b z f (ball 0 1) →
      HasC2HolderOn α z (ball 0 (1 / 2)) ∧
        schauderC2HolderNorm α z (ball 0 (1 / 2)) ≤ C *
          (lpNorm z ∞ (volume.restrict (ball 0 1)) + holderNorm α f (ball 0 1)) := by
  obtain ⟨K, hK, hnest⟩ := nondiv_schauder_nested hn0 hn hα hα1 hlam hlamcap hM
  obtain ⟨p, hp, P, hP, hinter⟩ := schauder_interpolation_polynomial (n := n) hα hα1
  obtain ⟨C, hC, habsorb⟩ := nondiv_schauder_absorb (p := p) hK hP
  refine ⟨C, hC, ?_⟩
  intro A b z f hA hb hz hf hbA hbb hcap hell he
  have hnested := hnest A b z f hA hb hz hf hbA hbb hcap hell he
  have houter := (hnested (3 / 4) 1 (by norm_num) (by norm_num) le_rfl).1
  have hhalf := (houter.nondiv_mono (ball_subset_ball (by norm_num : (1 / 2 : ℝ) ≤ 3 / 4))).1
  refine ⟨hhalf, ?_⟩
  let X : ℝ → ℝ := fun r => schauderC2HolderNorm α z (ball 0 r)
  let Y : ℝ → ℝ := fun r => nondivC1HolderNorm α z (ball 0 r)
  have hbX : BddAbove (X '' Icc (1 / 2 : ℝ) (3 / 4)) := by
    refine ⟨X (3 / 4), ?_⟩
    rintro _ ⟨r, hr, rfl⟩
    exact (houter.nondiv_mono (ball_subset_ball hr.2)).2
  have hzm := hz.memLp_top isOpen_ball
  apply habsorb X Y _ _ lpNorm_nonneg hf.norm_nonneg hbX
  · intro r hr s hs hrs
    exact (hnested r s (by linarith [hr.1]) hrs (by linarith [hs.2])).2
  · intro s hs ε hε hε1
    have hsreg := (houter.nondiv_mono (ball_subset_ball hs.2)).1
    have ht := hinter 0 s ε hs.1 hε hε1 z hsreg
    refine ht.trans (add_le_add le_rfl ?_)
    exact mul_le_mul_of_nonneg_left
      (nondiv_lpNorm_top_mono hzm (ball_subset_ball (by linarith [hs.2]))) (by positivity)

end LiquidDrop

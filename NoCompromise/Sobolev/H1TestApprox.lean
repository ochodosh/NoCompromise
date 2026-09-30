module

public import NoCompromise.Sobolev.H1Approximation

@[expose] public section

/-!
# Compactly supported smooth H¹ test approximation

A global H¹ function with compact support inside an open domain has smooth
approximants supported in one fixed relatively compact open subset of that domain.
Both the functions and their classical gradients converge strongly in L².
-/

noncomputable section

open MeasureTheory Filter Metric Set InnerProductSpace
open scoped NNReal ENNReal Topology Gradient Convolution

namespace LiquidDrop

set_option maxSynthPendingDepth 8

/-- Smooth compact approximation of an H¹ test function, with one fixed bounded
open support neighborhood whose closure stays inside the test domain. In particular,
all approximants are supported in the fixed compact set `closure V`. -/
theorem HasH1GradientOn.exists_smooth_compact_test_approximation {n : ℕ}
    {U : Set (EuclideanSpace ℝ (Fin n))} (hU : IsOpen U)
    {f : EuclideanSpace ℝ (Fin n) → ℝ}
    {G : EuclideanSpace ℝ (Fin n) → EuclideanSpace ℝ (Fin n)}
    (hf : HasH1GradientOn f G univ) (hcf : HasCompactSupport f) (hsf : tsupport f ⊆ U) :
    ∃ V : Set (EuclideanSpace ℝ (Fin n)),
      IsOpen V ∧ Bornology.IsBounded V ∧ IsCompact (closure V) ∧ closure V ⊆ U ∧
      tsupport f ⊆ V ∧ ∃ v : ℕ → EuclideanSpace ℝ (Fin n) → ℝ,
        (∀ j, ContDiff ℝ (⊤ : ℕ∞) (v j) ∧ HasCompactSupport (v j) ∧
          tsupport (v j) ⊆ V ∧
          HasH1GradientOn (v j) (gradient (v j)) univ) ∧
        Tendsto (fun j => eLpNorm (fun x => v j x - f x) 2 volume) atTop (𝓝 0) ∧
        Tendsto (fun j => eLpNorm (fun x => gradient (v j) x - G x) 2 volume)
          atTop (𝓝 0) := by
  obtain ⟨V, hV, hfV, hVU, hcV⟩ := exists_open_between_and_isCompact_closure hcf hU hsf
  obtain ⟨δ, hδ, hδV⟩ := hcf.exists_cthickening_subset_open hV hfV
  let φ (j : ℕ) : ContDiffBump (0 : EuclideanSpace ℝ (Fin n)) :=
    ⟨(δ / ((j : ℝ) + 1)) / 2, δ / ((j : ℝ) + 1), by positivity,
      half_lt_self (by positivity)⟩
  have hφδ (j) : (φ j).rOut ≤ δ :=
    div_le_self hδ.le (by linarith [Nat.cast_nonneg (α := ℝ) j])
  have hφlim : Tendsto (fun j => (φ j).rOut) atTop (𝓝 0) := by
    simpa only [mul_one_div, mul_zero] using
      (tendsto_one_div_add_atTop_nhds_zero_nat (𝕜 := ℝ)).const_mul δ
  let v (j : ℕ) := (φ j).normed volume ⋆[ContinuousLinearMap.lsmul ℝ ℝ] f
  have hconv := hf.tendsto_bump_convolution hφlim
  refine ⟨V, hV, hcV.isBounded.subset subset_closure, hcV, hVU, hfV, v, ?_,
    hconv.1, hconv.2⟩
  intro j
  have hb := hf.bump_convolution (φ j)
  refine ⟨hb.1, (φ j).hasCompactSupport_normed.convolution _ hcf,
    (tsupport_bump_convolution_subset (φ j) (hφδ j)).trans hδV, ?_⟩
  have heq := funext hb.2.1
  rw [heq]
  exact hb.2.2.1

end LiquidDrop

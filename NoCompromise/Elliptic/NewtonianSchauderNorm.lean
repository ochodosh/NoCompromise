module

public import NoCompromise.Elliptic.HolderInterpolation

@[expose] public section

/-!
# The C² Hölder norm used in the Schauder estimate

The norm is the sum of the three C⁰,α norms of the function, its first Fréchet
derivative and its second Fréchet derivative. Both derivative norms are operator
norms. Explicit finiteness is required, as in `HasC2HolderOn`.

The same-ball interpolation theorem controls the first derivative from the
Hessian and the essential uniform norm. A mean-value estimate then controls the
function's Hölder seminorm. This avoids assuming either lower-order Hölder norm.
-/

noncomputable section
open MeasureTheory Filter Metric Set
open scoped NNReal ENNReal Topology
namespace LiquidDrop
set_option maxSynthPendingDepth 8

/-- The explicit C²,α norm convention: the sum of the C⁰,α norms of orders 0, 1, 2. -/
def schauderC2HolderNorm {n : ℕ} (α : ℝ) (u : EuclideanSpace ℝ (Fin n) → ℝ)
    (U : Set (EuclideanSpace ℝ (Fin n))) : ℝ :=
  holderNorm α u U + holderNorm α (fderiv ℝ u) U +
    holderNorm α (fderiv ℝ (fderiv ℝ u)) U

lemma schauderC2HolderNorm_nonneg {n : ℕ} {α : ℝ}
    {u : EuclideanSpace ℝ (Fin n) → ℝ} {U : Set (EuclideanSpace ℝ (Fin n))}
    (hu : HasC2HolderOn α u U) : 0 ≤ schauderC2HolderNorm α u U :=
  add_nonneg (add_nonneg hu.function_holder.norm_nonneg hu.derivative_holder.norm_nonneg)
    hu.hessian_holder.norm_nonneg

/-- On the same positive-radius ball, a finite Hessian Hölder norm and an L∞
value bound give all of C²,α, with a constant chosen before the function. -/
theorem exists_schauderC2HolderNorm_le {n : ℕ} {α R : ℝ}
    (hα : 0 < α) (hα1 : α < 1) (hR : 0 < R) (c : EuclideanSpace ℝ (Fin n)) :
    ∃ C > 0, ∀ (u : EuclideanSpace ℝ (Fin n) → ℝ),
      ContDiffOn ℝ 2 u (ball c R) → MemLp u ∞ (volume.restrict (ball c R)) →
      HasFiniteHolderNormOn α (fderiv ℝ (fderiv ℝ u)) (ball c R) →
      HasC2HolderOn α u (ball c R) ∧
        schauderC2HolderNorm α u (ball c R) ≤
          C * (lpNorm u ∞ (volume.restrict (ball c R)) +
            holderNorm α (fderiv ℝ (fderiv ℝ u)) (ball c R)) := by
  obtain ⟨C, hC, hb⟩ := holder_interpolation_of_memLp hα hα1 (by norm_num : (0 : ℝ) < 1) hR c
  refine ⟨3 + 2 * C, by positivity, fun u hu hmu hH => ?_⟩
  obtain ⟨hD, hbD⟩ := hb u hu hmu hH
  simp only [one_mul] at hbD
  let L := lpNorm u ∞ (volume.restrict (ball c R))
  let M := holderNorm α (fderiv ℝ u) (ball c R)
  have hL : 0 ≤ L := lpNorm_nonneg
  have hM : 0 ≤ M := hD.norm_nonneg
  have hval : ∀ x ∈ ball c R, ‖u x‖ ≤ L :=
    holderInterpolation_norm_le_lpNorm_top isOpen_ball hu.continuousOn hmu
  have hderiv : ∀ x ∈ ball c R, ‖fderiv ℝ u x‖ ≤ M :=
    fun _ hx => (norm_le_holderUniformNorm hD.uniform_bounded hx).trans hD.uniformNorm_le
  have hlip : ∀ x ∈ ball c R, ∀ y ∈ ball c R, ‖u x - u y‖ ≤ M * ‖x - y‖ := by
    intro x hx y hy
    exact (convex_ball c R).norm_image_sub_le_of_norm_fderiv_le
      (fun z hz => ((hu z hz).contDiffAt (isOpen_ball.mem_nhds hz)).differentiableAt (by norm_num))
      hderiv hy hx
  have hquot : ∀ x ∈ ball c R, ∀ y ∈ ball c R,
      ‖u x - u y‖ / ‖x - y‖ ^ α ≤ M + 2 * L := by
    intro x hx y hy
    simpa only [Real.one_rpow, mul_one, div_one] using
      holderInterpolation_quotient_le hα hα1 (by norm_num : (0 : ℝ) < 1) hL hM hval hlip hx hy
  have hzero : 0 ≤ M + 2 * L := by positivity
  have huf : HasFiniteHolderNormOn α u (ball c R) :=
    HasFiniteHolderNormOn.of_bounds hL hzero hval hquot
  have hub : holderNorm α u (ball c R) ≤ 3 * L + M :=
    (holderNorm_le hL hzero hval hquot).trans_eq (by ring)
  refine ⟨⟨hu, huf, hD, hH⟩, ?_⟩
  calc
    schauderC2HolderNorm α u (ball c R) ≤
        3 * L + 2 * M + holderNorm α (fderiv ℝ (fderiv ℝ u)) (ball c R) := by
      dsimp [schauderC2HolderNorm, M] at hub ⊢
      linarith
    _ ≤ 3 * L + 2 * (holderNorm α (fderiv ℝ (fderiv ℝ u)) (ball c R) + C * L) +
        holderNorm α (fderiv ℝ (fderiv ℝ u)) (ball c R) := by
      gcongr
    _ ≤ _ := by
      have hH0 := hH.norm_nonneg
      dsimp [L]
      nlinarith [mul_nonneg hC.le hH0]

end LiquidDrop

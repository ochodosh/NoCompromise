module

public import NoCompromise.Elliptic.NondivSchauderScalingBall
public import NoCompromise.Elliptic.NondivSchauderLocalization

@[expose] public section

/-!
# Nested-radius nondivergence Schauder estimate

The loss is the explicit fourth inverse power of the radius gap. This estimate
will be combined with polynomial interpolation and a genuine absorption argument.
-/

noncomputable section
open MeasureTheory Filter Metric Set InnerProductSpace
open scoped ENNReal Topology Gradient RealInnerProductSpace
namespace LiquidDrop
set_option maxSynthPendingDepth 8

/-- The C¹,α-data estimate on concentric nested balls, uniformly before the
radii and all functions. In particular this constructs C²,α on B₃/₄. -/
theorem nondiv_schauder_nested {n : ℕ} (hn0 : 0 < n) (hn : n < 4)
    {α lam cap M : ℝ} (hα : 0 < α) (hα1 : α < 1)
    (hlam : 0 < lam) (hlamcap : lam ≤ cap) (hM : 0 ≤ M) :
    ∃ K ≥ 1, ∀ (A : EuclideanSpace ℝ (Fin n) →
        EuclideanSpace ℝ (Fin n) →L[ℝ] EuclideanSpace ℝ (Fin n))
      (b : EuclideanSpace ℝ (Fin n) → EuclideanSpace ℝ (Fin n))
      (z f : EuclideanSpace ℝ (Fin n) → ℝ),
      HasC1HolderOn α A (ball 0 1) → HasFiniteHolderNormOn α b (ball 0 1) →
      HasC1HolderOn α z (ball 0 1) → HasFiniteHolderNormOn α f (ball 0 1) →
      nondivC1HolderNorm α A (ball 0 1) ≤ M → holderNorm α b (ball 0 1) ≤ M →
      (∀ x ∈ ball 0 1, ‖A x‖ ≤ cap) →
      (∀ x ∈ ball 0 1, ∀ v, lam * ‖v‖ ^ 2 ≤ inner ℝ v (A x v)) →
      IsWeakNondivergenceEquationOn A b z f (ball 0 1) →
      ∀ r s : ℝ, 0 ≤ r → r < s → s ≤ 1 →
      HasC2HolderOn α z (ball 0 r) ∧
        schauderC2HolderNorm α z (ball 0 r) ≤ K * ((s - r)⁻¹) ^ 4 *
          (nondivC1HolderNorm α z (ball 0 s) + holderNorm α f (ball 0 1)) := by
  obtain ⟨C, hC, hbstr⟩ := nondiv_schauder_c1_ball hn0 hn hα hα1 hlam hlamcap hM
  refine ⟨18 * C + 1, by linarith, ?_⟩
  intro A b z f hA hb hz hf hbA hbb hcap hell he r s hr hrs hs
  let ρ := s - r
  have hρ : 0 < ρ := sub_pos.mpr hrs
  have hρ1 : ρ ≤ 1 := by dsimp [ρ]; linarith
  have hs1 : ball (0 : EuclideanSpace ℝ (Fin n)) s ⊆ ball 0 1 := ball_subset_ball hs
  have hzs := (hz.mono hs1).1
  let T := nondivC1HolderNorm α z (ball 0 s) + holderNorm α f (ball 0 1)
  have hT : 0 ≤ T := add_nonneg hzs.norm_nonneg hf.norm_nonneg
  have hlocal (x : EuclideanSpace ℝ (Fin n)) (hx : x ∈ ball 0 r) :
      HasC2HolderOn α z (ball x (ρ / 2)) ∧
        schauderC2HolderNorm α z (ball x (ρ / 2)) ≤ C * (ρ⁻¹) ^ 3 * T := by
    have hxs : ball x ρ ⊆ ball 0 s := by
      intro y hy
      rw [mem_ball] at hx hy ⊢
      have ht := dist_triangle y x 0
      dsimp [ρ] at hy
      linarith
    have hx1 := hxs.trans hs1
    obtain ⟨hAx, hbAx⟩ := hA.mono hx1
    obtain ⟨hbx, hbbx⟩ := schauder_holder_mono hb hx1
    obtain ⟨hzx, hbzx⟩ := hz.mono hx1
    obtain ⟨hfx, hbfx⟩ := schauder_holder_mono hf hx1
    obtain ⟨hlocal, hbound⟩ := hbstr x ρ hρ hρ1 A b z f hAx hbx hzx hfx
      (hbAx.trans hbA) (hbbx.trans hbb) (fun y hy => hcap y (hx1 hy))
      (fun y hy v => hell y (hx1 hy) v) (he.mono hx1)
    refine ⟨hlocal, hbound.trans ?_⟩
    exact mul_le_mul_of_nonneg_left
      (add_le_add (hzs.mono hxs).2 hbfx) (by positivity)
  obtain ⟨hreg, hbound⟩ := nondiv_c2Holder_local_ball_bound hα hα1.le
    (by positivity : 0 < ρ / 2) (by linarith : ρ / 2 ≤ 1)
    (by positivity : 0 ≤ C * (ρ⁻¹) ^ 3 * T) hlocal
  refine ⟨hreg, hbound.trans ?_⟩
  have heq : 9 * (ρ / 2)⁻¹ * (C * (ρ⁻¹) ^ 3 * T) = 18 * C * (ρ⁻¹) ^ 4 * T := by
    rw [inv_div]
    ring
  rw [heq]
  exact mul_le_mul_of_nonneg_right
    (mul_le_mul_of_nonneg_right (by linarith : 18 * C ≤ 18 * C + 1)
      (by positivity)) hT

end LiquidDrop

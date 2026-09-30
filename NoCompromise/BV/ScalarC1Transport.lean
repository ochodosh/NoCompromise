module

public import NoCompromise.Sobolev.Extension
public import Mathlib.Analysis.Calculus.ContDiff.RCLike

@[expose] public section

/-!
# Scalar locally BV functions under C¹ diffeomorphisms

On each bounded source region, a global C¹ map and inverse have finite Lipschitz
constants on containing compact balls. The quantitative BV composition theorem
then applies to the original function on a bounded target ball. No global
Lipschitz or finite-total-variation assumption is imposed.
-/

noncomputable section
open MeasureTheory Set Filter Metric
open scoped Topology ENNReal
namespace LiquidDrop

/-- Locally BV functions pull back to BV on every bounded open region. -/
theorem IsLocallyBVOn.isBVOn_comp_C1_diffeomorphism_on_bounded {n : ℕ}
    {f : EuclideanSpace ℝ (Fin n) → ℝ} (hf : IsLocallyBVOn f univ)
    (Φ : EuclideanSpace ℝ (Fin n) ≃ₜ EuclideanSpace ℝ (Fin n))
    (hΦ : ContDiff ℝ 1 Φ) (hiΦ : ContDiff ℝ 1 Φ.symm)
    {U : Set (EuclideanSpace ℝ (Fin n))} (hU : IsOpen U) (hbU : Bornology.IsBounded U) :
    IsBVOn (f ∘ Φ) U := by
  obtain ⟨R, hR, hUR⟩ := hbU.subset_ball_lt 0 (0 : EuclideanSpace ℝ (Fin n))
  obtain ⟨C, hC⟩ := hΦ.contDiffOn.exists_lipschitzOnWith one_ne_zero
    (convex_closedBall (0 : EuclideanSpace ℝ (Fin n)) R) (isCompact_closedBall _ _)
  have hcim := (isCompact_closedBall (0 : EuclideanSpace ℝ (Fin n)) R).image Φ.continuous
  obtain ⟨S, hS, hIS⟩ := hcim.isBounded.subset_ball_lt 0 (0 : EuclideanSpace ℝ (Fin n))
  obtain ⟨K, hK⟩ := hiΦ.contDiffOn.exists_lipschitzOnWith one_ne_zero
    (convex_closedBall (0 : EuclideanSpace ℝ (Fin n)) S) (isCompact_closedBall _ _)
  have hg : IsBVOn f (ball (0 : EuclideanSpace ℝ (Fin n)) S) := by
    refine ⟨?_, hf.2 _ isOpen_ball isBounded_ball.isCompact_closure (subset_univ _)⟩
    exact (hf.1.integrableOn_compact_subset (subset_univ _)
      (isCompact_closedBall (0 : EuclideanSpace ℝ (Fin n)) S)).mono_set ball_subset_closedBall
  exact (bv_comp_of_lipschitz_leftInverse hU isOpen_ball
    (hC.mono (hUR.trans ball_subset_closedBall)) (hK.mono ball_subset_closedBall)
    (fun x hx => hIS ⟨x, ball_subset_closedBall (hUR hx), rfl⟩)
    (fun x _ => Φ.symm_apply_apply x) hg).1

/-- Global C¹ diffeomorphisms preserve scalar local BV regularity. -/
theorem IsLocallyBVOn.comp_C1_diffeomorphism {n : ℕ}
    {f : EuclideanSpace ℝ (Fin n) → ℝ} (hf : IsLocallyBVOn f univ)
    (Φ : EuclideanSpace ℝ (Fin n) ≃ₜ EuclideanSpace ℝ (Fin n))
    (hΦ : ContDiff ℝ 1 Φ) (hiΦ : ContDiff ℝ 1 Φ.symm) :
    IsLocallyBVOn (f ∘ Φ) univ := by
  refine ⟨?_, fun U hU hcU _ => ?_⟩
  · apply (locallyIntegrableOn_iff isOpen_univ.isLocallyClosed).mpr
    intro K _ hK
    obtain ⟨R, _, hKR⟩ := hK.isBounded.subset_ball_lt 0 (0 : EuclideanSpace ℝ (Fin n))
    exact (hf.isBVOn_comp_C1_diffeomorphism_on_bounded Φ hΦ hiΦ
      isOpen_ball isBounded_ball).1.mono_set hKR
  · exact (hf.isBVOn_comp_C1_diffeomorphism_on_bounded Φ hΦ hiΦ hU
      (hcU.isBounded.subset subset_closure)).2

end LiquidDrop

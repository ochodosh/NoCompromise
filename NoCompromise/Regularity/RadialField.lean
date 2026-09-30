module

public import NoCompromise.Regularity.RadialDivergence

@[expose] public section

/-! # Compact smooth radial test fields -/

noncomputable section
open MeasureTheory Set Filter Metric
open scoped Topology
namespace LiquidDrop

/-- A radial coefficient constant near zero has no singularity at the origin. -/
theorem contDiff_radial_field {η : ℝ → ℝ} (hη : ContDiff ℝ 1 η)
    (h0 : ∀ᶠ r in 𝓝 (0 : ℝ), η r = η 0) :
    ContDiff ℝ 1 (fun y : AmbientSpace => η ‖y‖ • y) := by
  apply contDiff_iff_contDiffAt.mpr
  intro y
  by_cases hy : y = 0
  · subst y
    have he : (fun y : AmbientSpace => η ‖y‖ • y) =ᶠ[𝓝 0] (fun y => η 0 • y) := by
      have hh : ∀ᶠ y : AmbientSpace in 𝓝 0, η ‖y‖ = η 0 :=
        (continuous_norm.tendsto (0 : AmbientSpace)).eventually (by simpa only [norm_zero] using h0)
      exact hh.mono (fun y hy => congrArg (fun a : ℝ => a • y) hy)
    exact ((contDiffAt_const (c := η 0)).smul contDiffAt_id).congr_of_eventuallyEq he
  · exact (hη.contDiffAt.comp y (contDiffAt_norm ℝ hy)).smul contDiffAt_id

lemma tsupport_radial_field_subset {η : ℝ → ℝ} {b : ℝ}
    (hη : ∀ r, b ≤ r → η r = 0) :
    tsupport (fun y : AmbientSpace => η ‖y‖ • y) ⊆ closedBall 0 b := by
  apply closure_minimal _ isClosed_closedBall
  intro y hy
  by_contra hn
  have hb : b < ‖y‖ := by simpa only [mem_closedBall, dist_zero_right, not_le] using hn
  exact hy (by simp only [hη ‖y‖ hb.le, zero_smul])

lemma hasCompactSupport_radial_field {η : ℝ → ℝ} {b : ℝ}
    (hη : ∀ r, b ≤ r → η r = 0) :
    HasCompactSupport (fun y : AmbientSpace => η ‖y‖ • y) :=
  (isCompact_closedBall (0 : AmbientSpace) b).of_isClosed_subset
    (isClosed_tsupport _) (tsupport_radial_field_subset hη)

/-- The translated field is C¹ and compactly supported in the unit ball when
its radial profile vanishes at and beyond a radius strictly below one. -/
theorem radial_test_field {η : ℝ → ℝ} (hη : ContDiff ℝ 1 η)
    (h0 : ∀ᶠ r in 𝓝 (0 : ℝ), η r = η 0)
    {b : ℝ} (hb : b < 1) (hv : ∀ r, b ≤ r → η r = 0) (x : AmbientSpace) :
    ContDiff ℝ 1 (fun y : AmbientSpace => η ‖y - x‖ • (y - x)) ∧
      HasCompactSupport (fun y : AmbientSpace => η ‖y - x‖ • (y - x)) ∧
      tsupport (fun y : AmbientSpace => η ‖y - x‖ • (y - x)) ⊆ ball x 1 := by
  have hC : ContDiff ℝ 1 (fun y : AmbientSpace => η ‖y - x‖ • (y - x)) :=
    (contDiff_radial_field hη h0).comp (contDiff_id.sub (contDiff_const (c := x)))
  have hs : tsupport (fun y : AmbientSpace => η ‖y - x‖ • (y - x)) ⊆ closedBall x b := by
    apply closure_minimal _ isClosed_closedBall
    intro y hy
    by_contra hn
    have hh : b < ‖y - x‖ := by
      simpa only [mem_closedBall, dist_eq_norm, not_le] using hn
    exact hy (by simp only [hv _ hh.le, zero_smul])
  exact ⟨hC, (isCompact_closedBall x b).of_isClosed_subset (isClosed_tsupport _) hs,
    hs.trans (closedBall_subset_ball hb)⟩

end LiquidDrop

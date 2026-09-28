import NoCompromise.Regularity.Deformation

/-! # Compact tensor tests for the signed vertical flux -/

noncomputable section
open Set MeasureTheory Filter Metric
open scoped ENNReal Topology
namespace LiquidDrop
set_option maxSynthPendingDepth 8

lemma hasCompactSupport_vertical_tensor
    {β : EuclideanSpace ℝ (Fin 2) → ℝ} {ψ : ℝ → ℝ}
    (hβ : HasCompactSupport β) (hψ : HasCompactSupport ψ) :
    HasCompactSupport (fun x : AmbientSpace => β (graphProjectionN 2 x) * ψ (x 2)) := by
  apply HasCompactSupport.intro ((hβ.prod hψ).image (realLineCoordinates 2).continuous)
  intro x hx
  by_cases hb : β (graphProjectionN 2 x) = 0
  · simp only [hb, zero_mul]
  by_cases hh : ψ (x 2) = 0
  · simp only [hh, mul_zero]
  apply False.elim
  apply hx
  refine ⟨(graphProjectionN 2 x, x 2), ⟨subset_tsupport β hb,
    subset_tsupport ψ hh⟩, ?_⟩
  exact graphAppendN_projection x

lemma fderiv_vertical_tensor_last
    {β : EuclideanSpace ℝ (Fin 2) → ℝ} {ψ : ℝ → ℝ}
    (hβ : ContDiff ℝ 1 β) (hψ : ContDiff ℝ 1 ψ) (x : AmbientSpace) :
    fderiv ℝ (fun z : AmbientSpace => β (graphProjectionN 2 z) * ψ (z 2)) x
      (EuclideanSpace.single 2 1) = β (graphProjectionN 2 x) * deriv ψ (x 2) := by
  have hb := ((hβ.differentiable one_ne_zero).differentiableAt.hasFDerivAt).comp x
    (graphProjectionN 2).hasFDerivAt
  have hh := ((hψ.differentiable one_ne_zero).differentiableAt.hasDerivAt).comp_hasFDerivAt x
    (EuclideanSpace.proj (2 : Fin 3) : AmbientSpace →L[ℝ] ℝ).hasFDerivAt
  change (fderiv ℝ ((β ∘ graphProjectionN 2) *
    (ψ ∘ (EuclideanSpace.proj (2 : Fin 3) : AmbientSpace →L[ℝ] ℝ))) x) _ = _
  rw [(hb.mul hh).fderiv]
  have hp : graphProjectionN 2 (EuclideanSpace.single (2 : Fin 3) (1 : ℝ)) = 0 := by
    ext i
    simp [graphProjectionN]
  simp [ContinuousLinearMap.comp_apply, hp, EuclideanSpace.proj]

/-- The cleared slab admits a smooth cutoff that is identically one near it,
with compact support strictly between the two caps. -/
lemma exists_slab_flux_cutoff {r c η : ℝ} (hr : 0 < r) (hη : 0 < η)
    (hgap : |c| + η * r < r) :
    ∃ ψ : ℝ → ℝ, ContDiff ℝ 1 ψ ∧ HasCompactSupport ψ ∧
      tsupport ψ ⊆ Ioo (-r) r ∧
      ∀ t : ℝ, |t - c| ≤ η * r → ψ t = 1 ∧ deriv ψ t = 0 := by
  let δ := (r - |c| - η * r) / 3
  have hδ : 0 < δ := by dsimp [δ]; linarith
  let ψ : ContDiffBump c :=
    ⟨η * r + δ, η * r + 2 * δ, by positivity, by linarith⟩
  refine ⟨ψ, ψ.contDiff, ψ.hasCompactSupport, ?_, ?_⟩
  · intro t ht
    rw [ψ.tsupport_eq] at ht
    have hh : |t - c| ≤ η * r + 2 * δ := by
      simpa only [mem_closedBall, Real.dist_eq, ψ] using ht
    have hb := (abs_add_le (t - c) c)
    have hd : η * r + 2 * δ + |c| < r := by dsimp [δ]; linarith
    have htabs : |t| < r := by
      have he : t - c + c = t := by ring
      rw [he] at hb
      linarith
    exact abs_lt.mp htabs
  · intro t ht
    have hmem : t ∈ ball c ψ.rIn := by
      simp only [mem_ball, Real.dist_eq]
      change |t - c| < η * r + δ
      linarith
    refine ⟨ψ.one_of_mem_closedBall (ball_subset_closedBall hmem), ?_⟩
    have he := (ψ.eventuallyEq_one_of_mem_ball hmem).deriv_eq
    simpa only [Pi.one_def, deriv_const] using he

end LiquidDrop

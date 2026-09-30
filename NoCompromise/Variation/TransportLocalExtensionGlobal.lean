module

public import NoCompromise.Variation.TransportLocalExtension
public import Mathlib.Analysis.Calculus.BumpFunction.InnerProduct
public import Mathlib.Analysis.Calculus.ContDiff.RCLike

@[expose] public section

/-!
# Global C¹ diffeomorphisms agreeing locally with a C¹ diffeomorphism between open sets

Blueprint `thm:transport-perimeter`, localization step. At a source point `x₀` of a C¹
diffeomorphism `Φ : U → V`, with `A = DΦ(x₀)` invertible, the map
`y ↦ Φ x₀ + A (y - x₀) + ζ(y) • (Φ y - Φ x₀ - A (y - x₀))`, with `ζ` a C¹ bump equal to `1`
on `ball x₀ r` and vanishing off `ball x₀ (2 r)`, approximates `A` on the whole space with
constant below `‖A⁻¹‖⁻¹` for small `r`; hence it is a global homeomorphism with C¹ inverse.
-/

noncomputable section
open MeasureTheory Set Filter Metric
open scoped Topology NNReal
namespace LiquidDrop

/-- C¹ bumps at every scale `r` around `x₀`, with values in `[0, 1]`, equal to `1` on
`ball x₀ r`, vanishing off `ball x₀ (2 r)`, and Lipschitz with constant `M / r` for a single
`M` independent of `r`. -/
theorem exists_scaled_bump_lipschitz (x₀ : AmbientSpace) :
    ∃ M : ℝ, 0 ≤ M ∧ ∀ r : ℝ, 0 < r → ∃ ζ : AmbientSpace → ℝ, ContDiff ℝ 1 ζ ∧
      (∀ y z, |ζ y - ζ z| ≤ M * r⁻¹ * ‖y - z‖) ∧ (∀ y, 0 ≤ ζ y ∧ ζ y ≤ 1) ∧
      (∀ y ∈ ball x₀ r, ζ y = 1) ∧ (∀ y, y ∉ ball x₀ (2 * r) → ζ y = 0) := by
  let ζ₁ : ContDiffBump x₀ := ⟨1, 2, one_pos, one_lt_two⟩
  obtain ⟨M, hM⟩ := ContDiff.lipschitzWith_of_hasCompactSupport ζ₁.hasCompactSupport
    (ζ₁.contDiff (n := 1)) one_ne_zero
  refine ⟨M, M.2, fun r hr => ⟨fun y => ζ₁ (x₀ + r⁻¹ • (y - x₀)), ?_, ?_, ?_, ?_, ?_⟩⟩
  · exact ζ₁.contDiff.comp (contDiff_const.add ((contDiff_id.sub contDiff_const).const_smul _))
  · have hA : LipschitzWith ⟨r⁻¹, (inv_pos.mpr hr).le⟩
        (fun y : AmbientSpace => x₀ + r⁻¹ • (y - x₀)) := by
      apply LipschitzWith.of_dist_le_mul
      intro y z
      rw [dist_eq_norm, dist_eq_norm, add_sub_add_left_eq_sub, ← smul_sub, sub_sub_sub_cancel_right,
        norm_smul, Real.norm_of_nonneg (inv_pos.mpr hr).le]
      rfl
    intro y z
    have h := (hM.comp hA).dist_le_mul y z
    rw [Real.dist_eq, dist_eq_norm] at h
    have hc : ((M * ⟨r⁻¹, (inv_pos.mpr hr).le⟩ : ℝ≥0) : ℝ) = (M : ℝ) * r⁻¹ := rfl
    rw [hc] at h
    exact h
  · intro y
    exact ⟨ζ₁.nonneg, ζ₁.le_one⟩
  · intro y hy
    apply ζ₁.one_of_mem_closedBall
    rw [mem_closedBall, dist_eq_norm, add_sub_cancel_left, norm_smul,
      Real.norm_of_nonneg (inv_pos.mpr hr).le]
    rw [mem_ball, dist_eq_norm] at hy
    have : r⁻¹ * ‖y - x₀‖ ≤ r⁻¹ * r := by gcongr
    rw [inv_mul_cancel₀ hr.ne'] at this
    change r⁻¹ * ‖y - x₀‖ ≤ 1
    exact this
  · intro y hy
    apply ζ₁.zero_of_le_dist
    rw [dist_eq_norm, add_sub_cancel_left, norm_smul, Real.norm_of_nonneg (inv_pos.mpr hr).le]
    rw [mem_ball, dist_eq_norm, not_lt] at hy
    change 2 ≤ r⁻¹ * ‖y - x₀‖
    rw [le_inv_mul_iff₀ hr]
    linarith

/-- Blueprint localization step for `thm:transport-perimeter`: a C¹ diffeomorphism between
open sets agrees near each source point with a global homeomorphism which is C¹ with C¹
inverse. -/
theorem exists_local_C1_extension_of_C1_diffeomorphism_on
    (Φ : OpenPartialHomeomorph AmbientSpace AmbientSpace)
    (hΦ : ContDiffOn ℝ 1 Φ Φ.source) (hΦi : ContDiffOn ℝ 1 Φ.symm Φ.target)
    {x₀ : AmbientSpace} (hx₀ : x₀ ∈ Φ.source) :
    ∃ r > 0, closedBall x₀ (2 * r) ⊆ Φ.source ∧ ∃ Ψ : AmbientSpace ≃ₜ AmbientSpace,
      ContDiff ℝ 1 Ψ ∧ ContDiff ℝ 1 Ψ.symm ∧ EqOn Ψ Φ (ball x₀ r) := by
  obtain ⟨A, hA, -⟩ := exists_fderiv_equiv_of_C1_diffeomorphism_on Φ hΦ hΦi hx₀
  obtain ⟨M, hM0, hbump⟩ := exists_scaled_bump_lipschitz x₀
  set K : ℝ≥0 := ‖(A.symm : AmbientSpace →L[ℝ] AmbientSpace)‖₊⁻¹ with hKdef
  have hK : 0 < (K : ℝ) := by
    have : 0 < K := inv_pos.mpr A.nnnorm_symm_pos
    exact_mod_cast this
  set ε : ℝ := (K : ℝ) / (2 * (1 + 2 * M)) with hεdef
  have hε : 0 < ε := by positivity
  have hεK : ε * (1 + 2 * M) < K := by
    have h12 : 0 < 1 + 2 * M := by positivity
    rw [hεdef, div_mul_eq_mul_div, div_lt_iff₀ (by positivity)]
    nlinarith [mul_pos hK h12]
  have hcont : ContinuousAt (fderiv ℝ Φ) x₀ :=
    (hΦ.continuousOn_fderiv_of_isOpen Φ.open_source le_rfl).continuousAt
      (Φ.open_source.mem_nhds hx₀)
  obtain ⟨δ, hδ, hδc⟩ := Metric.continuousAt_iff.mp hcont ε hε
  obtain ⟨δ', hδ', hδ'U⟩ := Metric.isOpen_iff.mp Φ.open_source x₀ hx₀
  set δ₀ := min δ δ' with hδ₀
  have hδ₀pos : 0 < δ₀ := lt_min hδ hδ'
  have hBU : ball x₀ δ₀ ⊆ Φ.source := (ball_subset_ball (min_le_right _ _)).trans hδ'U
  have hderiv : ∀ y ∈ ball x₀ δ₀,
      ‖fderiv ℝ Φ y - (A : AmbientSpace →L[ℝ] AmbientSpace)‖ ≤ ε := by
    intro y hy
    rw [hA, ← dist_eq_norm]
    exact (hδc (lt_of_lt_of_le (mem_ball.mp hy) (min_le_left _ _))).le
  let g : AmbientSpace → AmbientSpace := fun y => Φ y - A y - (Φ x₀ - A x₀)
  have hgd : ∀ y ∈ ball x₀ δ₀, HasFDerivAt g
      (fderiv ℝ Φ y - (A : AmbientSpace →L[ℝ] AmbientSpace)) y := by
    intro y hy
    have hd : HasFDerivAt Φ (fderiv ℝ Φ y) y :=
      ((hΦ.contDiffAt (Φ.open_source.mem_nhds (hBU hy))).differentiableAt
        one_ne_zero).hasFDerivAt
    exact (hd.sub (A : AmbientSpace →L[ℝ] AmbientSpace).hasFDerivAt).sub_const _
  have hgLip : LipschitzOnWith ⟨ε, hε.le⟩ g (ball x₀ δ₀) := by
    apply (convex_ball x₀ δ₀).lipschitzOnWith_of_nnnorm_hasFDerivWithin_le
      (fun y hy => (hgd y hy).hasFDerivWithinAt)
    intro y hy
    exact NNReal.coe_le_coe.mp (by rw [coe_nnnorm]; exact hderiv y hy)
  have hg0 : g x₀ = 0 := sub_self _
  set r := δ₀ / 4 with hr
  have hrpos : 0 < r := by positivity
  have h2r : 2 * r < δ₀ := by rw [hr]; linarith
  have hB2 : ball x₀ (2 * r) ⊆ ball x₀ δ₀ := ball_subset_ball h2r.le
  have hcB2 : closedBall x₀ (2 * r) ⊆ ball x₀ δ₀ := closedBall_subset_ball h2r
  have hgsmall : ∀ y ∈ ball x₀ (2 * r), ‖g y‖ ≤ ε * (2 * r) := by
    intro y hy
    have h := hgLip.norm_sub_le (hB2 hy) (mem_ball_self hδ₀pos)
    rw [hg0, sub_zero] at h
    calc ‖g y‖ ≤ ε * ‖y - x₀‖ := h
      _ ≤ ε * (2 * r) := by
        gcongr
        exact (mem_ball_iff_norm.mp hy).le
  obtain ⟨ζ, hζC, hζL, hζ01, hζ1, hζ0⟩ := hbump r hrpos
  let h : AmbientSpace → AmbientSpace := fun y => ζ y • g y
  have haux : ∀ y ∈ ball x₀ (2 * r), ∀ z, ‖h y - h z‖ ≤ ε * (1 + 2 * M) * ‖y - z‖ := by
    intro y hy z
    have hsplit : h y - h z = (ζ y - ζ z) • g y + ζ z • (g y - g z) := by
      simp only [h, sub_smul, smul_sub]
      abel
    have h1 : ‖(ζ y - ζ z) • g y‖ ≤ 2 * M * ε * ‖y - z‖ := by
      rw [norm_smul, Real.norm_eq_abs]
      calc |ζ y - ζ z| * ‖g y‖ ≤ (M * r⁻¹ * ‖y - z‖) * (ε * (2 * r)) :=
            mul_le_mul (hζL y z) (hgsmall y hy) (norm_nonneg _) (by positivity)
        _ = 2 * M * ε * ‖y - z‖ := by field_simp
    have h2 : ‖ζ z • (g y - g z)‖ ≤ ε * ‖y - z‖ := by
      by_cases hz : z ∈ ball x₀ δ₀
      · rw [norm_smul, Real.norm_of_nonneg (hζ01 z).1]
        calc ζ z * ‖g y - g z‖ ≤ 1 * (ε * ‖y - z‖) :=
              mul_le_mul (hζ01 z).2 (hgLip.norm_sub_le (hB2 hy) hz) (norm_nonneg _) zero_le_one
          _ = ε * ‖y - z‖ := one_mul _
      · rw [hζ0 z (fun h' => hz (hB2 h')), zero_smul, norm_zero]
        positivity
    rw [hsplit]
    calc ‖(ζ y - ζ z) • g y + ζ z • (g y - g z)‖
        ≤ ‖(ζ y - ζ z) • g y‖ + ‖ζ z • (g y - g z)‖ := norm_add_le _ _
      _ ≤ 2 * M * ε * ‖y - z‖ + ε * ‖y - z‖ := add_le_add h1 h2
      _ = ε * (1 + 2 * M) * ‖y - z‖ := by ring
  have hLip : ∀ y z, ‖h y - h z‖ ≤ ε * (1 + 2 * M) * ‖y - z‖ := by
    intro y z
    by_cases hy : y ∈ ball x₀ (2 * r)
    · exact haux y hy z
    by_cases hz : z ∈ ball x₀ (2 * r)
    · rw [norm_sub_rev, norm_sub_rev y]
      exact haux z hz y
    · have hyz : h y - h z = 0 := by simp only [h, hζ0 y hy, hζ0 z hz, zero_smul, sub_self]
      rw [hyz, norm_zero]
      positivity
  let Ψ₀ : AmbientSpace → AmbientSpace := fun y => A y + (Φ x₀ - A x₀) + h y
  have hc0 : 0 ≤ ε * (1 + 2 * M) := by positivity
  have happrox : ApproximatesLinearOn Ψ₀ (A : AmbientSpace →L[ℝ] AmbientSpace) univ
      ⟨ε * (1 + 2 * M), hc0⟩ := by
    intro y _ z _
    have : Ψ₀ y - Ψ₀ z - (A : AmbientSpace →L[ℝ] AmbientSpace) (y - z) = h y - h z := by
      simp only [Ψ₀, ContinuousLinearEquiv.coe_coe, map_sub]
      abel
    rw [this]
    exact hLip y z
  have hhC : ContDiff ℝ 1 h := by
    rw [contDiff_iff_contDiffAt]
    intro y
    by_cases hy : y ∈ ball x₀ δ₀
    · have hgC : ContDiffAt ℝ 1 g y :=
        (((hΦ.contDiffAt (Φ.open_source.mem_nhds (hBU hy))).sub
          (A : AmbientSpace →L[ℝ] AmbientSpace).contDiff.contDiffAt).sub contDiffAt_const)
      exact hζC.contDiffAt.smul hgC
    · have hyc : y ∈ (closedBall x₀ (2 * r))ᶜ := fun h' => hy (hcB2 h')
      apply (contDiffAt_const (c := (0 : AmbientSpace))).congr_of_eventuallyEq
      filter_upwards [isClosed_closedBall.isOpen_compl.mem_nhds hyc] with w hw
      simp [h, hζ0 w (fun h' => hw (ball_subset_closedBall h'))]
  have hΨC : ContDiff ℝ 1 Ψ₀ :=
    ((A : AmbientSpace →L[ℝ] AmbientSpace).contDiff.add contDiff_const).add hhC
  have hcK : (⟨ε * (1 + 2 * M), hc0⟩ : ℝ≥0) <
      ‖(A.symm : AmbientSpace →L[ℝ] AmbientSpace)‖₊⁻¹ := by
    exact NNReal.coe_lt_coe.mp hεK
  obtain ⟨e, he, heC, heiC⟩ := exists_C1_homeomorph_of_approximatesLinearOn_univ A hΨC happrox hcK
  refine ⟨r, hrpos, hcB2.trans hBU, e, heC, heiC, ?_⟩
  intro y hy
  rw [he]
  simp only [Ψ₀, h, g, hζ1 y hy, one_smul]
  abel

end LiquidDrop

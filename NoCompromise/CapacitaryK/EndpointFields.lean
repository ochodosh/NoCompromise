import NoCompromise.CapacitaryK.CollarC2
import NoCompromise.Elliptic.HarmonicMeanValueLocal

/-!
# Pointwise identities for the endpoint `p(1)` of `thm:capacitary-inequalities`

For the capacitary potential `u` with a `C²` extension `g` across `∂K`:

* on a regular level in `Kᶜ`, `H|∇u| = ⟪-∇|∇g|, ν⟫` with `ν = -∇u/|∇u|`
  (`meanCurv_mul_gradNorm_eq_of_exterior`);
* on `∂K`, where `∇g = -|∇g| ν_K` and `Δg = 0` by continuity,
  `H_g|∇g| = ⟪-∇|∇g|, ν_K⟫` (`meanCurv_mul_gradNorm_eq_of_boundary`), with `H_g` the
  mean curvature of the level set of `g` through the point, i.e. of `∂K` with respect to `ν_K`;
* `-∇|∇g|` extends from a neighbourhood of any compact set on which `∇g ≠ 0` to a
  continuous field on `ℝ³` (`exists_continuous_neg_gradient_gradNorm`).
-/

noncomputable section
open Set Filter Metric MeasureTheory InnerProductSpace
open scoped Topology Gradient RealInnerProductSpace

namespace LiquidDrop.CapacitaryK

lemma norm_unitNormal_le (u : E3 → ℝ) (x : E3) : ‖unitNormal u x‖ ≤ 1 := by
  rw [unitNormal, norm_neg, norm_smul, norm_inv, Real.norm_eq_abs,
    abs_of_nonneg (gradNorm_nonneg u x)]
  change (gradNorm u x)⁻¹ * gradNorm u x ≤ 1
  rcases (gradNorm_nonneg u x).eq_or_lt with h | h
  · rw [← h]; simp
  · rw [inv_mul_cancel₀ h.ne']

/-- For `g ∈ C²`, the gradient of `|∇g|` is continuous where `∇g ≠ 0`. -/
lemma continuousAt_gradient_gradNorm {g : E3 → ℝ} (hg : ContDiff ℝ 2 g) {x : E3}
    (hx : gradient g x ≠ 0) : ContinuousAt (gradient (gradNorm g)) x := by
  have hG : ContDiff ℝ 1 (gradient g) := contDiff_gradient_of_contDiff_succ (r := 1) hg
  have hN : ContDiffAt ℝ 1 (gradNorm g) x := (contDiffAt_norm ℝ hx).comp x hG.contDiffAt
  have hF : ContinuousAt (fderiv ℝ (gradNorm g)) x :=
    (hN.fderiv_right (m := 0) (by norm_num)).continuousAt
  exact (toDual ℝ E3).symm.continuous.continuousAt.comp hF

/-- `-∇|∇g|` near a compact set on which `∇g ≠ 0`, extended to a continuous field. -/
lemma exists_continuous_neg_gradient_gradNorm {g : E3 → ℝ} (hg : ContDiff ℝ 2 g)
    {C : Set E3} (hC : IsCompact C) (hCg : ∀ x ∈ C, gradient g x ≠ 0) :
    ∃ Y : E3 → E3, Continuous Y ∧ ∀ᶠ x in 𝓝ˢ C, Y x = -gradient (gradNorm g) x := by
  let W : Set E3 := {x | gradient g x ≠ 0}
  have hW : IsOpen W :=
    isOpen_ne_fun (contDiff_gradient_of_contDiff_succ (r := 1) hg).continuous continuous_const
  obtain ⟨ζ, hζ, -, hsζ, hζ1, -⟩ := exists_smooth_cutoff_one_near_compact hC hW hCg
  refine ⟨fun x => ζ x • -gradient (gradNorm g) x, ?_, ?_⟩
  · refine continuous_iff_continuousAt.mpr fun x => ?_
    by_cases hx : x ∈ W
    · exact hζ.continuous.continuousAt.smul (continuousAt_gradient_gradNorm hg hx).neg
    · have hz : ζ =ᶠ[𝓝 x] (fun _ => 0) :=
        notMem_tsupport_iff_eventuallyEq.mp (fun h => hx (hsζ h))
      apply (continuousAt_const (y := (0 : E3))).congr
      filter_upwards [hz] with y hy
      simp [hy]
  · filter_upwards [hζ1] with x hx
    simp [hx]

/-- On `∂K`: `H_g |∇g| = ⟪-∇|∇g|, ν_K⟫` when `∇g = -|∇g| ν_K ≠ 0` and `Δg = 0`. -/
lemma meanCurv_mul_gradNorm_eq_of_boundary {g : E3 → ℝ} (hg : ContDiff ℝ 2 g) {p n : E3}
    (hgp : gradient g p = -‖gradient g p‖ • n) (hpos : 0 < ‖gradient g p‖)
    (hΔ : laplacianN g p = 0) :
    meanCurv g p * gradNorm g p = ⟪-gradient (gradNorm g) p, n⟫ := by
  have hw : 0 < gradNorm g p := hpos
  have hν : unitNormal g p = n := by
    rw [unitNormal, hgp]
    change -((‖gradient g p‖)⁻¹ • (-‖gradient g p‖ • n)) = n
    rw [smul_smul, mul_neg, inv_mul_cancel₀ hpos.ne', neg_smul, one_smul, neg_neg]
  have h := fderiv_gradNorm_unitNormal hg.contDiffAt hw hΔ
  rw [hν] at h
  rw [inner_neg_left, inner_gradient_eq_fderiv, h, neg_neg]

/-- On `Kᶜ`, where `u = g` near the point: `H |∇u| = ⟪-∇|∇g|, ν⟫`. -/
lemma meanCurv_mul_gradNorm_eq_of_exterior {K : Set E3} (hK : IsClosed K) {u g : E3 → ℝ}
    (hg : ContDiff ℝ 2 g) (hug : EqOn u g (closure Kᶜ)) {x : E3} (hx : x ∈ Kᶜ)
    (hw : 0 < gradNorm u x) (hΔ : laplacianN u x = 0) :
    meanCurv u x * gradNorm u x = ⟪-gradient (gradNorm g) x, unitNormal u x⟫ := by
  obtain ⟨hev, hgev⟩ := gradient_eventuallyEq_of_eqOn_closure hK hug hx
  have hu2 : ContDiffAt ℝ 2 u x := hg.contDiffAt.congr_of_eventuallyEq hev
  have hN : gradNorm u =ᶠ[𝓝 x] gradNorm g := hgev.mono fun y hy => by simp only [gradNorm, hy]
  have hNg : gradient (gradNorm u) x = gradient (gradNorm g) x := by
    unfold gradient
    rw [hN.fderiv_eq]
  rw [inner_neg_left, ← hNg, inner_gradient_eq_fderiv, fderiv_gradNorm_unitNormal hu2 hw hΔ,
    neg_neg]

/-- The extension is harmonic up to `∂K`: `Δg = 0` on `closure Kᶜ`. -/
lemma laplacianN_extension_eq_zero {K : Set E3} (hK : IsClosed K) {u g : E3 → ℝ}
    (hu : Continuous u) (hh : HasDistributionalLaplacianOn u (fun _ => 0) Kᶜ)
    (hg : ContDiff ℝ 2 g) (hug : EqOn u g (closure Kᶜ)) :
    ∀ x ∈ closure Kᶜ, laplacianN g x = 0 := by
  have h0 : Kᶜ ⊆ {x | laplacianN g x = 0} := fun x hx => by
    change laplacianN g x = 0
    rw [← laplacianN_congr_nhds (gradient_eventuallyEq_of_eqOn_closure hK hug hx).1]
    exact kelvin_laplacianN_eq_zero_of_distributional hK.isOpen_compl hu.continuousOn hh x hx
  exact fun x hx =>
    closure_minimal h0 (isClosed_eq (continuous_laplacianN hg) continuous_const) hx

end LiquidDrop.CapacitaryK

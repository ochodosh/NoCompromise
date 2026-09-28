import NoCompromise.CapacitaryK.Calculus
import NoCompromise.CapacitaryK.HarmonicSmooth
import NoCompromise.Surface.Geometry
import Mathlib.Geometry.Euclidean.Volume.Measure

/-!
# The total-curvature input (chapter 31, `lem:K-gauss-bonnet-input`)

For a regular level `Σ_t = {u = t}` of a function `u` smooth on an open set `Ω ⊇ Σ_t`, with `Σ_t`
compact and connected, `∫_{Σ_t} κ dH² ≤ 4π`, where `κ = gaussCurvature Σ_t ν` is the Gauss
curvature (`Surface/Geometry.lean`) for the level-set normal `ν = -∇u/|∇u|` (`unitNormal`).

External inputs are named hypotheses:
* `h_of_level_connected` is `lem:level-connected` (chapter 30): every regular level `{u = s}`,
  `0 < s < 1`, is connected;
* `h_of_total_curvature_bound` is `thm:total-curvature-bound` (chapter 14): every compact connected
  smooth embedded closed surface has `∫ κ dH² ≤ 4π`.

What is proved here is that a compact regular level of a smooth function is a smooth embedded
surface (`isSmoothEmbeddedSurface_level`) with smooth unit normal field `unitNormal u`
(`isUnitNormalField_level`), so that the two inputs combine.
-/

noncomputable section

open Set Filter Metric MeasureTheory InnerProductSpace
open scoped Topology Gradient RealInnerProductSpace

namespace LiquidDrop.CapacitaryK

lemma gradient_sub_const' (f : E3 → ℝ) (c : ℝ) (x : E3) :
    gradient (fun y => f y - c) x = gradient f x := by
  simp only [gradient, fderiv_sub_const]

/-- Near a point of `Ω`, a smooth function on `Ω` agrees with a globally smooth function. -/
lemma exists_global_smooth_local {Ω : Set E3} (hΩ : IsOpen Ω) {u : E3 → ℝ}
    (hu : ContDiffOn ℝ (⊤ : ℕ∞) u Ω) {p : E3} (hp : p ∈ Ω) :
    ∃ (U : Set E3) (φ : E3 → ℝ), IsOpen U ∧ p ∈ U ∧ U ⊆ Ω ∧ ContDiff ℝ (⊤ : ℕ∞) φ ∧
      ∀ x ∈ U, φ =ᶠ[𝓝 x] u := by
  obtain ⟨r, hr, hball⟩ := Metric.isOpen_iff.mp hΩ p hp
  let f : ContDiffBump p := ⟨r / 4, r / 2, by positivity, by linarith⟩
  refine ⟨ball p (r / 4), fun x => f x * u x, isOpen_ball, mem_ball_self (by positivity),
    (ball_subset_ball (by linarith)).trans hball, ?_, ?_⟩
  · rw [contDiff_iff_contDiffAt]
    intro x
    by_cases hx : x ∈ ball p r
    · exact f.contDiff.contDiffAt.mul (hu.contDiffAt (hΩ.mem_nhds (hball hx)))
    · have hfar : ∀ᶠ y in 𝓝 x, f y * u y = 0 := by
        have hxc : x ∉ closedBall p (r / 2) := by
          intro hx'
          exact hx (closedBall_subset_ball (by linarith) hx')
        filter_upwards [isClosed_closedBall.isOpen_compl.mem_nhds hxc] with y hy
        have : f y = 0 := by
          apply f.zero_of_le_dist
          have h' : r / 2 < dist y p := not_le.mp hy
          exact h'.le
        simp [this]
      exact (contDiffAt_const (c := (0:ℝ))).congr_of_eventuallyEq hfar
  · intro x hx
    filter_upwards [isOpen_ball.mem_nhds hx] with y hy
    have : f y = 1 := f.one_of_mem_closedBall (ball_subset_closedBall hy)
    simp [this]

/-- A regular level of a function smooth on an open neighbourhood is a smooth embedded surface. -/
theorem isSmoothEmbeddedSurface_level {Ω : Set E3} (hΩ : IsOpen Ω) {u : E3 → ℝ}
    (hu : ContDiffOn ℝ (⊤ : ℕ∞) u Ω) {t : ℝ} (hsub : u ⁻¹' {t} ⊆ Ω)
    (hreg : ∀ x ∈ u ⁻¹' {t}, gradient u x ≠ 0) :
    IsSmoothEmbeddedSurface (u ⁻¹' {t}) := by
  intro p hp
  obtain ⟨U, φ, hU, hpU, hUΩ, hφ, heq⟩ := exists_global_smooth_local hΩ hu (hsub hp)
  refine ⟨U, fun x => φ x - t, hU, hpU, hφ.sub contDiff_const, ?_, ?_⟩
  · ext x
    simp only [mem_inter_iff, mem_preimage, mem_singleton_iff, mem_ofPred_eq]
    constructor
    · rintro ⟨hx, hxU⟩
      exact ⟨hxU, by rw [(heq x hxU).eq_of_nhds, hx, sub_self]⟩
    · rintro ⟨hxU, hx⟩
      exact ⟨by rw [← (heq x hxU).eq_of_nhds]; linarith, hxU⟩
  · rintro x ⟨hx, hxU⟩
    have : (fun y => φ y - t) =ᶠ[𝓝 x] fun y => u y - t := by
      filter_upwards [heq x hxU] with y hy
      rw [hy]
    rw [this.gradient_eq, gradient_sub_const']
    exact hreg x hx

/-- The level-set normal `-∇u/|∇u|` is a smooth unit normal field of a regular level. -/
theorem isUnitNormalField_level {Ω : Set E3} (hΩ : IsOpen Ω) {u : E3 → ℝ}
    (hu : ContDiffOn ℝ (⊤ : ℕ∞) u Ω) {t : ℝ} (hsub : u ⁻¹' {t} ⊆ Ω)
    (hreg : ∀ x ∈ u ⁻¹' {t}, gradient u x ≠ 0) :
    IsUnitNormalField (u ⁻¹' {t}) (unitNormal u) := by
  have hgrad : ContDiffOn ℝ (⊤ : ℕ∞) (gradient u) Ω := by
    have hf : ContDiffOn ℝ (⊤ : ℕ∞) (fderiv ℝ u) Ω := hu.fderiv_of_isOpen hΩ (by simp)
    have : gradient u = fun x => (toDual ℝ E3).symm (fderiv ℝ u x) := rfl
    rw [this]
    exact (toDual ℝ E3).symm.toContinuousLinearEquiv.contDiff.comp_contDiffOn hf
  let V : Set E3 := Ω ∩ gradient u ⁻¹' {0}ᶜ
  have hV : IsOpen V := hgrad.continuousOn.isOpen_inter_preimage hΩ isOpen_compl_singleton
  have hne : ∀ x ∈ V, gradient u x ≠ 0 := fun x hx => hx.2
  refine ⟨⟨V, hV, fun x hx => ⟨hsub hx, hreg x hx⟩, ?_⟩, ?_⟩
  · have hg : ContDiffOn ℝ (⊤ : ℕ∞) (gradient u) V := hgrad.mono inter_subset_left
    have hn : ContDiffOn ℝ (⊤ : ℕ∞) (fun x => ‖gradient u x‖) V := hg.norm ℝ hne
    have hinv : ContDiffOn ℝ (⊤ : ℕ∞) (fun x => (gradNorm u x)⁻¹) V :=
      hn.inv fun x hx => norm_ne_zero_iff.mpr (hne x hx)
    exact (hinv.smul hg).neg
  · intro p hp
    have hgp := hreg p hp
    refine ⟨?_, ?_⟩
    · rw [unitNormal, norm_neg, norm_smul, norm_inv, Real.norm_eq_abs,
        abs_of_nonneg (gradNorm_nonneg u p), gradNorm]
      exact inv_mul_cancel₀ (norm_ne_zero_iff.mpr hgp)
    · intro X hX
      obtain ⟨U, φ, hU, hpU, hUΩ, hφ, heq⟩ := exists_global_smooth_local hΩ hu (hsub hp)
      have hzero : u ⁻¹' {t} ∩ U = {x ∈ U | (fun y => φ y - t) x = 0} := by
        ext x
        simp only [mem_inter_iff, mem_preimage, mem_singleton_iff, mem_ofPred_eq]
        constructor
        · rintro ⟨hx, hxU⟩
          exact ⟨hxU, by rw [(heq x hxU).eq_of_nhds, hx, sub_self]⟩
        · rintro ⟨hxU, hx⟩
          exact ⟨by rw [← (heq x hxU).eq_of_nhds]; linarith, hxU⟩
      have hgeq : gradient (fun y => φ y - t) p = gradient u p := by
        have : (fun y => φ y - t) =ᶠ[𝓝 p] fun y => u y - t := by
          filter_upwards [heq p hpU] with y hy
          rw [hy]
        rw [this.gradient_eq, gradient_sub_const']
      have hT := tangentPlane_eq hU hpU ((hφ.sub contDiff_const).of_le (by simp)).contDiffAt
        hzero hp (by rw [hgeq]; exact hgp)
      rw [hT, hgeq, Submodule.mem_orthogonal_singleton_iff_inner_right] at hX
      rw [unitNormal, inner_neg_left, real_inner_smul_left, hX, mul_zero, neg_zero]

/-- `lem:K-gauss-bonnet-input`: for every regular value `t ∈ (0,1)` whose level is compact and
contained in the open set where `u` is smooth, `∫_{u=t} κ dH² ≤ 4π`. The hypotheses
`h_of_level_connected` (`lem:level-connected`) and `h_of_total_curvature_bound`
(`thm:total-curvature-bound`) are the external inputs. -/
theorem K_gauss_bonnet_input {Ω : Set E3} (hΩ : IsOpen Ω) {u : E3 → ℝ}
    (hu : ContDiffOn ℝ (⊤ : ℕ∞) u Ω) {t : ℝ} (ht0 : 0 < t) (ht1 : t < 1)
    (hsub : u ⁻¹' {t} ⊆ Ω) (hreg : ∀ x ∈ u ⁻¹' {t}, gradient u x ≠ 0)
    (hcompact : IsCompact (u ⁻¹' {t}))
    (h_of_level_connected : ∀ s : ℝ, 0 < s → s < 1 → (∀ x ∈ u ⁻¹' {s}, gradient u x ≠ 0) →
      IsConnected (u ⁻¹' {s}))
    (h_of_total_curvature_bound : ∀ (S : Set E3) (n : E3 → E3), IsCompact S → IsConnected S →
      IsSmoothEmbeddedSurface S → IsUnitNormalField S n →
      ∫ x in S, gaussCurvature S n x ∂(Measure.euclideanHausdorffMeasure 2) ≤ 4 * Real.pi) :
    ∫ x in u ⁻¹' {t}, gaussCurvature (u ⁻¹' {t}) (unitNormal u) x
        ∂(Measure.euclideanHausdorffMeasure 2) ≤ 4 * Real.pi :=
  h_of_total_curvature_bound _ _ hcompact (h_of_level_connected t ht0 ht1 hreg)
    (isSmoothEmbeddedSurface_level hΩ hu hsub hreg) (isUnitNormalField_level hΩ hu hsub hreg)

/-- `lem:K-gauss-bonnet-input` for a `C²` function harmonic on `Ω` (the capacitary potential off
`K`): smoothness near the level is `contDiffOn_top_of_harmonic`. -/
theorem K_gauss_bonnet_input_of_harmonic {Ω : Set E3} (hΩ : IsOpen Ω) {u : E3 → ℝ}
    (hu : ContDiffOn ℝ 2 u Ω) (hΔ : ∀ x ∈ Ω, laplacianN u x = 0) {t : ℝ} (ht0 : 0 < t)
    (ht1 : t < 1) (hsub : u ⁻¹' {t} ⊆ Ω) (hreg : ∀ x ∈ u ⁻¹' {t}, gradient u x ≠ 0)
    (hcompact : IsCompact (u ⁻¹' {t}))
    (h_of_level_connected : ∀ s : ℝ, 0 < s → s < 1 → (∀ x ∈ u ⁻¹' {s}, gradient u x ≠ 0) →
      IsConnected (u ⁻¹' {s}))
    (h_of_total_curvature_bound : ∀ (S : Set E3) (n : E3 → E3), IsCompact S → IsConnected S →
      IsSmoothEmbeddedSurface S → IsUnitNormalField S n →
      ∫ x in S, gaussCurvature S n x ∂(Measure.euclideanHausdorffMeasure 2) ≤ 4 * Real.pi) :
    ∫ x in u ⁻¹' {t}, gaussCurvature (u ⁻¹' {t}) (unitNormal u) x
        ∂(Measure.euclideanHausdorffMeasure 2) ≤ 4 * Real.pi :=
  K_gauss_bonnet_input hΩ (contDiffOn_top_of_harmonic (by norm_num) hΩ hu hΔ) ht0 ht1 hsub hreg
    hcompact h_of_level_connected h_of_total_curvature_bound

end LiquidDrop.CapacitaryK

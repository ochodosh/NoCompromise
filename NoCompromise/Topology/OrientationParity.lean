module

public import NoCompromise.Topology.ParityPath
public import NoCompromise.Topology.ParitySides

@[expose] public section

/-!
# Orientation by parity: the two complementary components

`prop:orientation-parity` (iii): the complement of a compact connected smooth embedded surface
in `ℝ³` has exactly two connected components. The intersection parity `SurfaceOddParity` of
`ParityPath.lean` is path independent, locally constant off the surface and flips across it;
`ParitySides.lean` turns such a parity into the component count.
-/

noncomputable section
open Set Filter
open scoped Topology

namespace LiquidDrop

/-- A compact subset of `ℝ³` misses some point. -/
theorem exists_not_mem_of_isCompact {S : Set E₃} (hc : IsCompact S) : ∃ z : E₃, z ∉ S := by
  by_contra h
  push Not at h
  exact hc.ne_univ (eq_univ_of_forall h)

/-- The intersection parity is constant on every preconnected subset of the complement. -/
theorem surfaceOddParity_iff_of_isPreconnected {S : Set E₃}
    (hS : IsSmoothEmbeddedSurface S) (hc : IsCompact S) {z : E₃} (hz : z ∉ S)
    {K : Set E₃} (hK : IsPreconnected K) (hKS : K ⊆ Sᶜ) {x y : E₃} (hx : x ∈ K)
    (hy : y ∈ K) : SurfaceOddParity S z x ↔ SurfaceOddParity S z y := by
  classical
  let f : E₃ → Bool := fun w => decide (SurfaceOddParity S z w)
  have hf : ContinuousOn f K := by
    intro w hw
    apply ContinuousAt.continuousWithinAt
    have hev : ∀ᶠ v in 𝓝 w, f v = f w := by
      filter_upwards [surfaceOddParity_locally_constant hS hc hz w (hKS hw)] with v hv
      simp only [f, hv]
    exact tendsto_const_nhds.congr' (hev.mono fun v hv => hv.symm)
  have h := hK.constant hf hx hy
  simpa only [f, decide_eq_decide] using h

/-- prop:orientation-parity (iii): the complement of a compact connected smooth embedded
surface in `ℝ³` has exactly two connected components. -/
theorem card_connectedComponents_compl_surface_eq_two {S : Set E₃}
    (hS : IsSmoothEmbeddedSurface S) (hc : IsCompact S) (hconn : IsConnected S) :
    Nat.card (ConnectedComponents (Sᶜ : Set E₃)) = 2 := by
  obtain ⟨z, hz⟩ := exists_not_mem_of_isCompact hc
  exact card_connectedComponents_compl_eq_two hS hc hconn (SurfaceOddParity S z)
    (surfaceOddParity_locally_constant hS hc hz) (surfaceOddParity_crossing hS hc hz)

/-- The slope of a differentiable function along a line through `p₀` at which it vanishes. -/
theorem tendsto_slope_along_line {φ : E₃ → ℝ} {p₀ : E₃} (ν : E₃) (hφ : DifferentiableAt ℝ φ p₀)
    (hφ0 : φ p₀ = 0) :
    Tendsto (fun s : ℝ => s⁻¹ * φ (p₀ + s • ν)) (𝓝[>] (0 : ℝ)) (𝓝 (fderiv ℝ φ p₀ ν)) := by
  have h1 : HasDerivAt (fun t : ℝ => p₀ + t • ν) ν 0 := by
    simpa using ((hasDerivAt_id (0 : ℝ)).smul_const ν).const_add p₀
  have h2 : HasFDerivAt φ (fderiv ℝ φ p₀) (p₀ + (0 : ℝ) • ν) := by
    simpa using hφ.hasFDerivAt
  have hline : HasDerivAt (fun t : ℝ => φ (p₀ + t • ν)) (fderiv ℝ φ p₀ ν) 0 :=
    h2.comp_hasDerivAt 0 h1
  simpa [hφ0] using hline.tendsto_slope_zero_right

/-- Along a direction of positive derivative, a function vanishing at `p₀` is positive just
after and negative just before `p₀`. -/
theorem eventually_sign_along_line {φ : E₃ → ℝ} {p₀ ν : E₃} (hφ : DifferentiableAt ℝ φ p₀)
    (hφ0 : φ p₀ = 0) (hpos : 0 < fderiv ℝ φ p₀ ν) :
    ∀ᶠ s in 𝓝[>] (0 : ℝ), 0 < φ (p₀ + s • ν) ∧ φ (p₀ - s • ν) < 0 := by
  have hr := (tendsto_slope_along_line ν hφ hφ0).eventually (lt_mem_nhds hpos)
  have hneg : fderiv ℝ φ p₀ (-ν) < 0 := by rw [map_neg]; exact neg_lt_zero.mpr hpos
  have hl := (tendsto_slope_along_line (-ν) hφ hφ0).eventually (gt_mem_nhds hneg)
  filter_upwards [hr, hl, self_mem_nhdsWithin] with s hs hs' hs0
  have hs0' : (0 : ℝ) < s := hs0
  refine ⟨pos_of_mul_pos_right hs (inv_nonneg.mpr hs0'.le), ?_⟩
  rw [smul_neg, ← sub_eq_add_neg] at hs'
  by_contra hge
  push Not at hge
  exact absurd hs' (not_lt.mpr (mul_nonneg (inv_nonneg.mpr hs0'.le) hge))

/-- prop:orientation-parity (ii), local clause: in a regular defining chart the two local sides
of the surface carry opposite intersection parities, and each side carries a single parity. -/
theorem surfaceOddParity_local_sides {S : Set E₃}
    (hS : IsSmoothEmbeddedSurface S) (hc : IsCompact S) {z : E₃} (hz : z ∉ S)
    {U : Set E₃} {φ : E₃ → ℝ} (hU : IsOpen U) (hφ : ContDiff ℝ (⊤ : ℕ∞) φ)
    (hzero : S ∩ U = {x ∈ U | φ x = 0}) (hreg : ∀ x ∈ S ∩ U, gradient φ x ≠ 0)
    {p₀ : E₃} (hp₀ : p₀ ∈ S) (hp₀U : p₀ ∈ U) :
    ∃ r > 0, Metric.ball p₀ r ⊆ U ∧ ∀ x ∈ Metric.ball p₀ r, ∀ y ∈ Metric.ball p₀ r,
      (0 < φ x → 0 < φ y → (SurfaceOddParity S z x ↔ SurfaceOddParity S z y)) ∧
      (φ x < 0 → φ y < 0 → (SurfaceOddParity S z x ↔ SurfaceOddParity S z y)) ∧
      (0 < φ x → φ y < 0 → ¬ (SurfaceOddParity S z x ↔ SurfaceOddParity S z y)) := by
  have hφp₀ : φ p₀ = 0 := (hzero ▸ (show p₀ ∈ S ∩ U from ⟨hp₀, hp₀U⟩)).2
  have hg : gradient φ p₀ ≠ 0 := hreg p₀ ⟨hp₀, hp₀U⟩
  obtain ⟨r, hr, hrU, Kp, Kn, hKp, hKn, hKpS, hKnS, hpos, hneg⟩ :=
    exists_local_sides hU hφ hzero hp₀U hφp₀ hg
  have hsame : ∀ K : Set E₃, IsPreconnected K → K ⊆ Sᶜ → ∀ x ∈ K, ∀ y ∈ K,
      (SurfaceOddParity S z x ↔ SurfaceOddParity S z y) := fun K hK hKS x hx y hy =>
    surfaceOddParity_iff_of_isPreconnected hS hc hz hK hKS hx hy
  -- the crossing at `p₀` in the gradient direction
  have hν : gradient φ p₀ ∉ tangentPlane S p₀ := by
    rw [tangentPlane_eq hU hp₀U (hφ.contDiffAt.of_le (by exact_mod_cast le_top)) hzero hp₀ hg,
      Submodule.mem_orthogonal_singleton_iff_inner_right, real_inner_self_eq_norm_sq]
    exact pow_ne_zero 2 (norm_ne_zero_iff.mpr hg)
  obtain ⟨t₀, ht₀, hcross⟩ := surfaceOddParity_crossing hS hc hz p₀ hp₀ _ hν
  have hder : 0 < fderiv ℝ φ p₀ (gradient φ p₀) := by
    rw [← inner_gradient_left, real_inner_self_eq_norm_sq]
    exact pow_pos (norm_pos_iff.mpr hg) 2
  have hsign := eventually_sign_along_line
    (hφ.differentiable (by simp) p₀) hφp₀ hder
  have hsmall : ∀ᶠ s in 𝓝[>] (0 : ℝ), s < t₀ ∧ s * ‖gradient φ p₀‖ < r := by
    have h1 : ∀ᶠ s in 𝓝 (0 : ℝ), s < t₀ := gt_mem_nhds ht₀
    have h2 : ∀ᶠ s in 𝓝 (0 : ℝ), s * ‖gradient φ p₀‖ < r := by
      have hc0 : Continuous fun s : ℝ => s * ‖gradient φ p₀‖ := by fun_prop
      exact hc0.continuousAt.eventually (gt_mem_nhds (by simpa using hr))
    exact nhdsWithin_le_nhds (h1.and h2)
  obtain ⟨s, ⟨hsp, hsn⟩, ⟨hst, hsr⟩, hs0⟩ :=
    (hsign.and (hsmall.and self_mem_nhdsWithin)).exists
  have hs0' : (0 : ℝ) < s := hs0
  have hball : ∀ w : E₃, ‖w‖ = ‖gradient φ p₀‖ → p₀ + s • w ∈ Metric.ball p₀ r := by
    intro w hw
    rw [Metric.mem_ball, dist_eq_norm, add_sub_cancel_left, norm_smul, Real.norm_of_nonneg hs0'.le,
      hw]
    exact hsr
  have hplus : p₀ + s • gradient φ p₀ ∈ Kp := hpos ⟨hball _ rfl, hsp⟩
  have hminus : p₀ - s • gradient φ p₀ ∈ Kn := by
    refine hneg ⟨?_, hsn⟩
    rw [sub_eq_add_neg, ← smul_neg]
    exact hball _ (norm_neg _)
  have hflip := hcross s ⟨hs0', hst⟩
  refine ⟨r, hr, hrU, fun x hx y hy => ⟨fun hx' hy' => hsame Kp hKp hKpS x (hpos ⟨hx, hx'⟩) y
    (hpos ⟨hy, hy'⟩), fun hx' hy' => hsame Kn hKn hKnS x (hneg ⟨hx, hx'⟩) y (hneg ⟨hy, hy'⟩),
    fun hx' hy' h => hflip ?_⟩⟩
  have e1 := hsame Kp hKp hKpS _ hplus x (hpos ⟨hx, hx'⟩)
  have e2 := hsame Kn hKn hKnS _ hminus y (hneg ⟨hy, hy'⟩)
  exact e2.trans (h.symm.trans e1.symm)

end LiquidDrop

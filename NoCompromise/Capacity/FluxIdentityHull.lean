import NoCompromise.Capacity.FluxBoundaryW
import NoCompromise.Capacity.FluxLevel
import NoCompromise.Capacity.HullPotentialBoundaryC2

/-!
# `lem:flux-identity`, `not:w` and `lem:kelvin` for the filled hull, unconditionally

For `K = filledHull Ω`, `Ω` a bounded open set with `C³` boundary containing `0`, and `u` any
capacitary potential of `K` (continuous, harmonic off `K`, `u = 1` on `K`, `u → 0` at infinity),
`hullPotentialBoundaryC2` (`thm:boundary-C2a` for the hull potential) supplies a `C²` function
`g` on `ℝ³` with `u = g` on `closure Kᶜ`. Feeding it to the Chapter-30 theorems that take such a
`g` as an argument gives:

* `lem:flux-identity`, `eq:flux-boundary` (signed and `w = |∇u|` forms) and `eq:flux-level`;
* `not:w`, `eq:w-boundary`: `∇u = -w ν` on `∂K` with `w > 0`;
* `lem:kelvin`: `C∞ = Cap(K)` in the Kelvin expansion, and `Cap(K) > 0`.

The hypotheses on `K` used there (compact, regular closed, `C¹`/`C²` boundary of `int K`,
`0 ∈ int K`, `Kᶜ` connected, `K ⊆ closedBall 0 R₀`) are those of `lem:hull-properties`. On `∂K`
the boundary values `∇g` do not depend on the extension (the original theorems hold for every
`C²` extension); the statements below exhibit one.
-/

noncomputable section
open MeasureTheory Set Filter Metric Topology InnerProductSpace
open scoped Gradient

namespace LiquidDrop

/-- `C^k` boundary with `2 ≤ k` is `C²` boundary. -/
theorem HasCkBoundary.hasC2Boundary {k : ℕ∞} {D : Set AmbientSpace} (hD : HasCkBoundary k D)
    (hk : 2 ≤ k) : HasC2Boundary D := by
  intro p hp
  obtain ⟨c, hc, hpc, hck⟩ := hD p hp
  exact ⟨c, hc, hpc, hck.of_le (WithTop.coe_le_coe.mpr hk)⟩

/-- The filled hull of a bounded open set lies in a closed ball of positive radius about `0`. -/
lemma filledHull_exists_closedBall {Ω : Set AmbientSpace} (hbd : Bornology.IsBounded Ω) :
    ∃ R₀ : ℝ, 0 < R₀ ∧ filledHull Ω ⊆ closedBall 0 R₀ := by
  obtain ⟨R, hR⟩ := (filledHull_isCompact hbd).isBounded.subset_closedBall (0 : AmbientSpace)
  exact ⟨max R 1, lt_max_of_lt_right one_pos,
    hR.trans (closedBall_subset_closedBall (le_max_left _ _))⟩

/-- Blueprint `lem:flux-identity`, `eq:flux-boundary` (signed form), for the capacitary potential
of the filled hull of a bounded open `Ω ∋ 0` with `C³` boundary: some `C²` function `g` with
`u = g` on `closure Kᶜ` satisfies `4π Cap(K) = -∫_{∂K} ∂_ν g dH²`, `ν` the outward normal of
`int K`. The conclusion after the extension is that of `flux_identity_of_boundary_C2`. -/
theorem filledHull_flux_identity {Ω : Set AmbientSpace} (ho : IsOpen Ω)
    (hbd : Bornology.IsBounded Ω) (h3 : HasCkBoundary 3 Ω) (h0 : (0 : AmbientSpace) ∈ Ω)
    {u : AmbientSpace → ℝ} (hu : Continuous u)
    (hh : HasDistributionalLaplacianOn u (fun _ => 0) (filledHull Ω)ᶜ)
    (hb : ∀ x ∈ filledHull Ω, u x = 1) (hinf : Tendsto u (cocompact AmbientSpace) (𝓝 0)) :
    ∃ g : AmbientSpace → ℝ, ContDiff ℝ 2 g ∧ EqOn u g (closure (filledHull Ω)ᶜ) ∧
      4 * Real.pi * capacityOf (filledHull Ω) u =
        -∫ x in frontier (filledHull Ω), inner ℝ (gradient g x)
          ((filledHull_hasC1Boundary_interior ho h3.hasC1Boundary).outwardNormal x)
          ∂hausdorffMeasure2 3 := by
  obtain ⟨g, hg, hug⟩ := hullPotentialBoundaryC2 Ω ho hbd h3 h0 u hu hh hb hinf
  obtain ⟨R₀, hR₀, hKR⟩ := filledHull_exists_closedBall hbd
  exact ⟨g, hg, hug, flux_identity_of_boundary_C2 (filledHull_isCompact hbd)
    (filledHull_eq_closure_interior ho) _ hR₀ hKR (filledHull_subset_interior ho h0)
    hu hh hb hinf hg hug⟩

/-- Blueprint `not:w` (`eq:w-boundary`) for the capacitary potential of the filled hull of a
bounded open `Ω ∋ 0` with `C³` boundary: some `C²` function `g` with `u = g` on `closure Kᶜ`
has, at every `p ∈ ∂K`, `∇g(p) = -|∇g(p)| ν(p)` and `|∇g(p)| > 0`. The conclusion after the
extension is that of `gradient_eq_neg_norm_smul_normal`. -/
theorem filledHull_gradient_eq_neg_norm_smul_normal {Ω : Set AmbientSpace} (ho : IsOpen Ω)
    (hbd : Bornology.IsBounded Ω) (h3 : HasCkBoundary 3 Ω) (h0 : (0 : AmbientSpace) ∈ Ω)
    {u : AmbientSpace → ℝ} (hu : Continuous u)
    (hh : HasDistributionalLaplacianOn u (fun _ => 0) (filledHull Ω)ᶜ)
    (hb : ∀ x ∈ filledHull Ω, u x = 1) (hinf : Tendsto u (cocompact AmbientSpace) (𝓝 0)) :
    ∃ g : AmbientSpace → ℝ, ContDiff ℝ 2 g ∧ EqOn u g (closure (filledHull Ω)ᶜ) ∧
      ∀ p ∈ frontier (filledHull Ω),
        gradient g p = -‖gradient g p‖ •
          (filledHull_hasC1Boundary_interior ho h3.hasC1Boundary).outwardNormal p ∧
        0 < ‖gradient g p‖ := by
  obtain ⟨g, hg, hug⟩ := hullPotentialBoundaryC2 Ω ho hbd h3 h0 u hu hh hb hinf
  obtain ⟨R₀, hR₀, hKR⟩ := filledHull_exists_closedBall hbd
  exact ⟨g, hg, hug, gradient_eq_neg_norm_smul_normal (filledHull_isCompact hbd)
    (filledHull_eq_closure_interior ho) _ hR₀ hKR (filledHull_subset_interior ho h0)
    hu hh hb hinf hg hug (filledHull_hasC2Boundary_interior ho (h3.hasC2Boundary (by norm_num)))
    (filledHull_isConnected_compl hbd).isPreconnected⟩

/-- Blueprint `lem:flux-identity`, `eq:flux-boundary` in the form `4π Cap(K) = ∫_{∂K} w dH²`,
`w = |∇u|` on `∂K`, for the capacitary potential of the filled hull of a bounded open `Ω ∋ 0`
with `C³` boundary: some `C²` function `g` with `u = g` on `closure Kᶜ` satisfies it with
`w = |∇g|`. The conclusion after the extension is that of `flux_identity_w`. -/
theorem filledHull_flux_identity_w {Ω : Set AmbientSpace} (ho : IsOpen Ω)
    (hbd : Bornology.IsBounded Ω) (h3 : HasCkBoundary 3 Ω) (h0 : (0 : AmbientSpace) ∈ Ω)
    {u : AmbientSpace → ℝ} (hu : Continuous u)
    (hh : HasDistributionalLaplacianOn u (fun _ => 0) (filledHull Ω)ᶜ)
    (hb : ∀ x ∈ filledHull Ω, u x = 1) (hinf : Tendsto u (cocompact AmbientSpace) (𝓝 0)) :
    ∃ g : AmbientSpace → ℝ, ContDiff ℝ 2 g ∧ EqOn u g (closure (filledHull Ω)ᶜ) ∧
      4 * Real.pi * capacityOf (filledHull Ω) u =
        ∫ x in frontier (filledHull Ω), ‖gradient g x‖ ∂hausdorffMeasure2 3 := by
  obtain ⟨g, hg, hug⟩ := hullPotentialBoundaryC2 Ω ho hbd h3 h0 u hu hh hb hinf
  obtain ⟨R₀, hR₀, hKR⟩ := filledHull_exists_closedBall hbd
  exact ⟨g, hg, hug, flux_identity_w (filledHull_isCompact hbd)
    (filledHull_eq_closure_interior ho) (filledHull_hasC1Boundary_interior ho h3.hasC1Boundary)
    hR₀ hKR (filledHull_subset_interior ho h0) hu hh hb hinf hg hug
    (filledHull_hasC2Boundary_interior ho (h3.hasC2Boundary (by norm_num)))
    (filledHull_isConnected_compl hbd).isPreconnected⟩

/-- Blueprint `lem:flux-identity`, `eq:flux-level`, for the capacitary potential of the filled
hull of a bounded open `Ω ∋ 0` with `C³` boundary: on every regular level `{u = s}`,
`0 < s < 1`, `∫_{u=s} |∇u| dH² = 4π Cap(K)`. Exactly the conclusion of `capacitary_flux_level`,
with no extension hypothesis. -/
theorem filledHull_capacitary_flux_level {Ω : Set AmbientSpace} (ho : IsOpen Ω)
    (hbd : Bornology.IsBounded Ω) (h3 : HasCkBoundary 3 Ω) (h0 : (0 : AmbientSpace) ∈ Ω)
    {u : AmbientSpace → ℝ} (hu : Continuous u)
    (hh : HasDistributionalLaplacianOn u (fun _ => 0) (filledHull Ω)ᶜ)
    (hb : ∀ x ∈ filledHull Ω, u x = 1) (hinf : Tendsto u (cocompact AmbientSpace) (𝓝 0)) :
    ∀ s : ℝ, 0 < s → s < 1 → (∀ x, u x = s → gradient u x ≠ 0) →
      (∫ x in u ⁻¹' {s}, ‖gradient u x‖ ∂hausdorffMeasure2 3) =
        4 * Real.pi * capacityOf (filledHull Ω) u := by
  obtain ⟨g, hg, hug⟩ := hullPotentialBoundaryC2 Ω ho hbd h3 h0 u hu hh hb hinf
  obtain ⟨R₀, hR₀, hKR⟩ := filledHull_exists_closedBall hbd
  exact capacitary_flux_level (filledHull_isCompact hbd) (filledHull_eq_closure_interior ho)
    (filledHull_hasC1Boundary_interior ho h3.hasC1Boundary) hR₀ hKR
    (filledHull_subset_interior ho h0) hu hh hb hinf hg hug

/-- Blueprint `lem:kelvin`, `C∞ = C`, for the capacitary potential of the filled hull of a
bounded open `Ω ∋ 0` with `C³` boundary: `u = Cap(K)/|x| + O(|x|⁻²)` and
`∇u = -Cap(K) x/|x|³ + O(|x|⁻³)`. Exactly the conclusion of `kelvin_constant_eq_capacity`,
with no extension hypothesis. -/
theorem filledHull_kelvin_constant_eq_capacity {Ω : Set AmbientSpace} (ho : IsOpen Ω)
    (hbd : Bornology.IsBounded Ω) (h3 : HasCkBoundary 3 Ω) (h0 : (0 : AmbientSpace) ∈ Ω)
    {u : AmbientSpace → ℝ} (hu : Continuous u)
    (hh : HasDistributionalLaplacianOn u (fun _ => 0) (filledHull Ω)ᶜ)
    (hb : ∀ x ∈ filledHull Ω, u x = 1) (hinf : Tendsto u (cocompact AmbientSpace) (𝓝 0)) :
    ∃ R C' : ℝ, 0 < R ∧ ∀ x : AmbientSpace, R ≤ ‖x‖ →
      |u x - capacityOf (filledHull Ω) u / ‖x‖| ≤ C' / ‖x‖ ^ 2 ∧
      ‖gradient u x + (capacityOf (filledHull Ω) u / ‖x‖ ^ 3) • x‖ ≤ C' / ‖x‖ ^ 3 := by
  obtain ⟨g, hg, hug⟩ := hullPotentialBoundaryC2 Ω ho hbd h3 h0 u hu hh hb hinf
  obtain ⟨R₀, hR₀, hKR⟩ := filledHull_exists_closedBall hbd
  exact kelvin_constant_eq_capacity (filledHull_isCompact hbd)
    (filledHull_eq_closure_interior ho) (filledHull_hasC1Boundary_interior ho h3.hasC1Boundary)
    hR₀ hKR (filledHull_subset_interior ho h0) hu hh hb hinf hg hug

/-- Blueprint `lem:kelvin`, `C > 0`, for the capacitary potential of the filled hull of a
bounded open `Ω ∋ 0` with `C³` boundary. Exactly the conclusion of `capacityOf_pos`, with no
extension hypothesis. -/
theorem filledHull_capacityOf_pos {Ω : Set AmbientSpace} (ho : IsOpen Ω)
    (hbd : Bornology.IsBounded Ω) (h3 : HasCkBoundary 3 Ω) (h0 : (0 : AmbientSpace) ∈ Ω)
    {u : AmbientSpace → ℝ} (hu : Continuous u)
    (hh : HasDistributionalLaplacianOn u (fun _ => 0) (filledHull Ω)ᶜ)
    (hb : ∀ x ∈ filledHull Ω, u x = 1) (hinf : Tendsto u (cocompact AmbientSpace) (𝓝 0)) :
    0 < capacityOf (filledHull Ω) u := by
  obtain ⟨g, hg, hug⟩ := hullPotentialBoundaryC2 Ω ho hbd h3 h0 u hu hh hb hinf
  obtain ⟨R₀, hR₀, hKR⟩ := filledHull_exists_closedBall hbd
  exact capacityOf_pos (filledHull_isCompact hbd) (filledHull_eq_closure_interior ho)
    (filledHull_hasC1Boundary_interior ho h3.hasC1Boundary) hR₀ hKR
    (filledHull_subset_interior ho h0) hu hh hb hinf hg hug

end LiquidDrop

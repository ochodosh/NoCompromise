module

public import NoCompromise.Cones.ThreeDim
public import NoCompromise.Regularity.EpsRegularityMain
public import NoCompromise.Regularity.ExcessDecayCoordinates

@[expose] public section

/-!
# `thm:eps-regularity` at nonzero boundary points of a minimising cone (toward `lem:cone-smooth`)

Second step of blueprint `lem:cone-smooth` (chapter 25): once the cylindrical excess of a
nontrivial locally perimeter-minimising cone `C ⊂ ℝ³` becomes small along a sequence of scales
at a boundary point `p`, `thm:eps-regularity` (with `ω = 0`) represents `∂C` near `p`, in the
genuine rotated and rescaled coordinates `y ↦ p + s • Q y` (`Q = verticalAxisIsometry ν`), as the
graph of a `C^{1,1/2}` function over the disk of radius `1/4`, with an arbitrarily small
Hölder constant and at an arbitrarily small scale.

* `mem_frontier_densityOne_excessDecayCoordinates` : exact transport of the boundary;
* `cone_C1half_graph_of_tendsto_excess` : the graph representation;
* `MinimalGraphSmoothStatement` : the Schauder step, stated explicitly (not proved here);
* `cone_smooth_graph_of_tendsto_excess` : smooth graph representation from that statement.

The smallness of the excess itself is the first step of `lem:cone-smooth` and is a hypothesis
here. Higher regularity (Schauder) is only used through the explicit hypothesis
`MinimalGraphSmoothStatement`.
-/

noncomputable section
open MeasureTheory Set Filter Metric
open scoped Topology ContDiff
namespace LiquidDrop

/-- The boundary of the excess-decay coordinates is the exact rigid-and-dilation pullback of the
boundary of the density-one representative. -/
lemma mem_frontier_densityOne_excessDecayCoordinates (E : Set AmbientSpace) (x ν y : AmbientSpace)
    {r : ℝ} (hr : 0 < r) :
    y ∈ frontier (densityOne (excessDecayCoordinates E x r ν)) ↔
      x + r • verticalAxisIsometry ν y ∈ frontier (densityOne E) := by
  rw [excessDecayCoordinates, frontier_densityOne_preimage_affineIsometry, mem_preimage]
  change verticalAxisIsometry ν y ∈ frontier (densityOne (blowupSet E x r)) ↔ _
  rw [mem_frontier_densityOne_blowupSet E x _ hr]

/-- **`thm:eps-regularity` at a boundary point of a minimising cone with small excess.**  If the
cylindrical excess of `C` at `p` with unit axis `ν` tends to zero along scales `r j → 0`, then for
every `δ > 0` and `s₀ > 0` there are a scale `0 < s ≤ min s₀ 1` and a function `f` on the disk of
radius `1/4` such that, inside the rescaled rotated cylinder `p + s • Q (standardCylinder (1/4))`,
the boundary of `densityOne C` is exactly the graph of `f` (which lies in the cylinder), `|f| < 1/8`, `f` is differentiable
with derivative given by the unit normal field `νΩ`, and `Df` is `1/2`-Hölder with constant `δ`. -/
theorem cone_C1half_graph_of_tendsto_excess {C : Set AmbientSpace}
    (hC : IsNontrivialMinimizingCone C) {p ν : AmbientSpace} (hν : ‖ν‖ = 1)
    (hp : p ∈ frontier (densityOne C)) {r : ℕ → ℝ} (hr : ∀ j, 0 < r j)
    (hr0 : Tendsto r atTop (𝓝 0))
    (hexc : Tendsto (fun j => cylindricalExcess C hC.minimizing.isOmegaMinimal.locallyFinite
      hC.minimizing.isOmegaMinimal.nullMeasurable p (r j) ν) atTop (𝓝 0))
    {δ s₀ : ℝ} (hδ : 0 < δ) (hs₀ : 0 < s₀) :
    ∃ s : ℝ, 0 < s ∧ s ≤ s₀ ∧ s ≤ 1 ∧
      ∃ (f : EuclideanSpace ℝ (Fin 2) → ℝ) (νΩ : AmbientSpace → AmbientSpace),
        (∀ y ∈ standardCylinder (1 / 4),
          (p + s • verticalAxisIsometry ν y ∈ frontier (densityOne C) ↔
            ∃ x' ∈ ball (0 : EuclideanSpace ℝ (Fin 2)) (1 / 4), graphAppendN x' (f x') = y)) ∧
        (∀ x' ∈ ball (0 : EuclideanSpace ℝ (Fin 2)) (1 / 4),
          graphAppendN x' (f x') ∈ standardCylinder (1 / 4)) ∧
        (∀ x' ∈ ball (0 : EuclideanSpace ℝ (Fin 2)) (1 / 4), |f x'| < 1 / 8) ∧
        (∀ x' ∈ ball (0 : EuclideanSpace ℝ (Fin 2)) (1 / 4),
          HasFDerivAt f (-(νΩ (graphAppendN x' (f x')) 2)⁻¹ •
            innerSL ℝ (graphProjectionN 2 (νΩ (graphAppendN x' (f x'))))) x') ∧
        (∀ x' ∈ ball (0 : EuclideanSpace ℝ (Fin 2)) (1 / 4),
          ‖νΩ (graphAppendN x' (f x'))‖ = 1) ∧
        (∀ x' ∈ ball (0 : EuclideanSpace ℝ (Fin 2)) (1 / 4),
          ∀ y' ∈ ball (0 : EuclideanSpace ℝ (Fin 2)) (1 / 4),
          ‖fderiv ℝ f x' - fderiv ℝ f y'‖ ≤ δ * Real.sqrt ‖x' - y'‖) := by
  obtain ⟨ε₀, hε₀, K, hK, hreg⟩ := eps_regularity
  set hE := hC.minimizing.isOmegaMinimal with hEdef
  set η : ℝ := min ε₀ ((δ / K) ^ 2) with hη
  have hηpos : 0 < η := lt_min hε₀ (by positivity)
  have hev : ∀ᶠ j in atTop, cylindricalExcess C hE.locallyFinite hE.nullMeasurable p (r j) ν < η ∧
      r j < min s₀ 1 :=
    (hexc.eventually (gt_mem_nhds hηpos)).and (hr0.eventually (gt_mem_nhds (lt_min hs₀ one_pos)))
  obtain ⟨j, hj, hjr⟩ := hev.exists
  set s := r j with hsdef
  have hs : 0 < s := hr j
  have hs1 : s ≤ 1 := hjr.le.trans (min_le_right _ _)
  have hE' := hE.excessDecayCoordinates p hs hs1 ν
  have h0 : (0 : AmbientSpace) ∈ frontier (densityOne (excessDecayCoordinates C p s ν)) :=
    (excessDecayCoordinates_origin_frontier C p ν hs).2 hp
  have hexc' : cylindricalExcess (excessDecayCoordinates C p s ν) hE'.locallyFinite
      hE'.nullMeasurable 0 1 (EuclideanSpace.single 2 1) =
      cylindricalExcess C hE.locallyFinite hE.nullMeasurable p s ν :=
    cylindricalExcess_excessDecayCoordinates_unit hE p ν hs hs1 hν
  have hsmall : cylindricalExcess (excessDecayCoordinates C p s ν) hE'.locallyFinite
      hE'.nullMeasurable 0 1 (EuclideanSpace.single 2 1) + 0 * s * 1 ≤ ε₀ := by
    rw [hexc']
    linarith [min_le_left ε₀ ((δ / K) ^ 2)]
  obtain ⟨f, νΩ, hgraph, hf8, hfd, hhol, hnorm, _hred, _hνhol⟩ :=
    hreg _ _ hE' 1 h0 one_pos le_rfl hsmall
  refine ⟨s, hs, hjr.le.trans (min_le_left _ _), hs1, f, νΩ, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro y hy
    rw [← mem_frontier_densityOne_excessDecayCoordinates C p ν y hs]
    constructor
    · intro hyf
      have hmem : y ∈ frontier (densityOne (excessDecayCoordinates C p s ν)) ∩
          standardCylinder (1 / 4) := ⟨hyf, hy⟩
      rw [hgraph] at hmem
      obtain ⟨x', hx', rfl⟩ := hmem
      exact ⟨x', hx', rfl⟩
    · rintro ⟨x', hx', rfl⟩
      have hmem : graphAppendN x' (f x') ∈
          frontier (densityOne (excessDecayCoordinates C p s ν)) ∩ standardCylinder (1 / 4) := by
        rw [hgraph]
        exact ⟨x', hx', rfl⟩
      exact hmem.1
  · intro x' hx'
    have hmem : graphAppendN x' (f x') ∈
        frontier (densityOne (excessDecayCoordinates C p s ν)) ∩ standardCylinder (1 / 4) := by
      rw [hgraph]
      exact ⟨x', hx', rfl⟩
    exact hmem.2
  · intro x' hx'
    simpa using hf8 x' hx'
  · intro x' hx'
    exact hfd x' hx'
  · intro x' hx'
    have hmem : graphAppendN x' (f x') ∈
        frontier (densityOne (excessDecayCoordinates C p s ν)) ∩ standardCylinder (1 / 4) := by
      rw [hgraph]
      exact ⟨x', hx', rfl⟩
    exact (hnorm _ hmem).1
  · intro x' hx' y' hy'
    have h := hhol x' hx' y' hy'
    rw [hexc', div_one] at h
    have hle : cylindricalExcess C hE.locallyFinite hE.nullMeasurable p s ν + 0 * s * 1 ≤
        (δ / K) ^ 2 := by
      linarith [min_le_right ε₀ ((δ / K) ^ 2)]
    have hsq : Real.sqrt (cylindricalExcess C hE.locallyFinite hE.nullMeasurable p s ν +
        0 * s * 1) ≤ δ / K := by
      calc _ ≤ Real.sqrt ((δ / K) ^ 2) := Real.sqrt_le_sqrt hle
        _ = δ / K := Real.sqrt_sq (by positivity)
    calc ‖fderiv ℝ f x' - fderiv ℝ f y'‖
        ≤ K * Real.sqrt ‖x' - y'‖ * Real.sqrt
          (cylindricalExcess C hE.locallyFinite hE.nullMeasurable p s ν + 0 * s * 1) := h
      _ ≤ K * Real.sqrt ‖x' - y'‖ * (δ / K) := by
          gcongr
      _ = δ * Real.sqrt ‖x' - y'‖ := by
          field_simp

/-- **The Schauder step of `lem:cone-smooth`, as an explicit statement (not proved here).**
A function on the disk of radius `ρ ≤ 1` whose graph is exactly the boundary of the density-one
representative of a perimeter minimiser (`ω = 0`) inside `standardCylinder ρ`, which stays in the
middle half of the cylinder, and whose derivative is `1/2`-Hölder, is smooth on the open disk.
(The blueprint obtains this from `eq:bounded-H` with `ω = 0` and the Campanato/Schauder package
applied with zero right side; `mc_graph_C2_holder_unit` supplies the first, `C^{2,α}`, step.) -/
def MinimalGraphSmoothStatement : Prop :=
  ∀ (E : Set AmbientSpace), IsOmegaMinimal E 0 →
    ∀ (ρ K : ℝ) (f : EuclideanSpace ℝ (Fin 2) → ℝ), 0 < ρ → ρ ≤ 1 →
    frontier (densityOne E) ∩ standardCylinder ρ =
      (fun x' => graphAppendN x' (f x')) '' ball (0 : EuclideanSpace ℝ (Fin 2)) ρ →
    (∀ x' ∈ ball (0 : EuclideanSpace ℝ (Fin 2)) ρ, |f x'| < ρ / 2) →
    (∀ x' ∈ ball (0 : EuclideanSpace ℝ (Fin 2)) ρ, DifferentiableAt ℝ f x') →
    (∀ x' ∈ ball (0 : EuclideanSpace ℝ (Fin 2)) ρ, ∀ y' ∈ ball (0 : EuclideanSpace ℝ (Fin 2)) ρ,
      ‖fderiv ℝ f x' - fderiv ℝ f y'‖ ≤ K * Real.sqrt ‖x' - y'‖) →
    ContDiffOn ℝ ∞ f (ball (0 : EuclideanSpace ℝ (Fin 2)) ρ)

/-- **`lem:cone-smooth` at a boundary point with vanishing excess, from the Schauder step.**
Under `MinimalGraphSmoothStatement`, the boundary of `densityOne C` near `p` is, in the rotated and
rescaled cylinder `p + s • Q (standardCylinder (1/4))`, the graph of a smooth function. -/
theorem cone_smooth_graph_of_tendsto_excess (hS : MinimalGraphSmoothStatement)
    {C : Set AmbientSpace}
    (hC : IsNontrivialMinimizingCone C) {p ν : AmbientSpace} (hν : ‖ν‖ = 1)
    (hp : p ∈ frontier (densityOne C)) {r : ℕ → ℝ} (hr : ∀ j, 0 < r j)
    (hr0 : Tendsto r atTop (𝓝 0))
    (hexc : Tendsto (fun j => cylindricalExcess C hC.minimizing.isOmegaMinimal.locallyFinite
      hC.minimizing.isOmegaMinimal.nullMeasurable p (r j) ν) atTop (𝓝 0))
    {s₀ : ℝ} (hs₀ : 0 < s₀) :
    ∃ s : ℝ, 0 < s ∧ s ≤ s₀ ∧
      ∃ f : EuclideanSpace ℝ (Fin 2) → ℝ,
        (∀ y ∈ standardCylinder (1 / 4),
          (p + s • verticalAxisIsometry ν y ∈ frontier (densityOne C) ↔
            ∃ x' ∈ ball (0 : EuclideanSpace ℝ (Fin 2)) (1 / 4), graphAppendN x' (f x') = y)) ∧
        (∀ x' ∈ ball (0 : EuclideanSpace ℝ (Fin 2)) (1 / 4), |f x'| < 1 / 8) ∧
        ContDiffOn ℝ ∞ f (ball (0 : EuclideanSpace ℝ (Fin 2)) (1 / 4)) := by
  obtain ⟨s, hs, hss₀, hs1, f, νΩ, hiff, hcyl, hf8, hfd, _hn, hhol⟩ :=
    cone_C1half_graph_of_tendsto_excess hC hν hp hr hr0 hexc one_pos hs₀
  refine ⟨s, hs, hss₀, f, hiff, hf8, ?_⟩
  have hE' : IsOmegaMinimal (excessDecayCoordinates C p s ν) 0 := by
    simpa only [zero_mul] using hC.minimizing.isOmegaMinimal.excessDecayCoordinates p hs hs1 ν
  have hgraph : frontier (densityOne (excessDecayCoordinates C p s ν)) ∩ standardCylinder (1 / 4) =
      (fun x' => graphAppendN x' (f x')) '' ball (0 : EuclideanSpace ℝ (Fin 2)) (1 / 4) := by
    ext y
    constructor
    · rintro ⟨hyf, hy⟩
      rw [mem_frontier_densityOne_excessDecayCoordinates C p ν y hs, hiff y hy] at hyf
      obtain ⟨x', hx', rfl⟩ := hyf
      exact ⟨x', hx', rfl⟩
    · rintro ⟨x', hx', rfl⟩
      refine ⟨?_, hcyl x' hx'⟩
      rw [mem_frontier_densityOne_excessDecayCoordinates C p ν _ hs, hiff _ (hcyl x' hx')]
      exact ⟨x', hx', rfl⟩
  refine hS _ hE' (1 / 4) 1 f (by norm_num) (by norm_num) hgraph ?_
    (fun x' hx' => (hfd x' hx').differentiableAt) (by simpa only [one_mul] using hhol)
  intro x' hx'
  have := hf8 x' hx'
  linarith

end LiquidDrop

module

public import NoCompromise.Green.IdentityCapacity
public import NoCompromise.Capacity.HullExistence

@[expose] public section

/-!
# `lem:wronskian` for the capacitary potential, unconditionally

`wronskian_bound_of_kelvin` and `wronskian_tendsto_zero_of_kelvin` (Green/Identity.lean) take the
Kelvin expansion `u = C/|x| + O(|x|⁻²)`, `∇u = −Cx/|x|³ + O(|x|⁻³)` as the named hypothesis
`hu_of_kelvin`. For the capacitary potential of a compact `K` with `0 ∈ int K` this expansion is
`kelvin_expansion` (Capacity/Kelvin.lean, `lem:kelvin`, value and gradient parts, unconditional).

The cancellation of the monopole terms in `eq:wronskian` holds for whatever constant `C`
appears in the expansion, so the identification `C = cap(K)` (which uses `thm:boundary-C2a`) is
not needed for `lem:wronskian`.

* `capacitary_wronskian`: `eq:wronskian` for the capacitary potential of any compact `K` with
  `0 ∈ int K` and any bounded measurable `Ω`;
* `exists_filledHull_capacitary_potential_wronskian`: for the filled hull `K` of a bounded open
  `Ω ∋ 0` with `C²` boundary (the setting of `thm:capacitary-potential`), the capacitary
  potential exists and satisfies `eq:wronskian`.

The filled-hull instances `filledHull_wronskian_bound` and `filledHull_wronskian_tendsto_zero`
(Green/IdentityCapacity.lean) are the same statement for the hull, for every `u` with the
defining properties.
-/

noncomputable section
open Set Filter Metric MeasureTheory
open scoped Topology

namespace LiquidDrop

/-- **`lem:wronskian`** (`eq:wronskian`) for the capacitary potential `u` of a compact `K` with
`0 ∈ int K` (`u` continuous, harmonic off `K`, `u = 1` on `K`, `u → 0` at infinity) and the
Coulomb potential `v = v_Ω` of a bounded measurable `Ω`, with no named hypothesis: the outer
Wronskian `∫_{∂B_R} (v ∂_r u − u ∂_r v) dH²` is `O(R⁻²)` and tends to `0` as `R → ∞`. -/
theorem capacitary_wronskian {K : Set AmbientSpace} (hK : IsCompact K)
    (hzero : (0 : AmbientSpace) ∈ interior K)
    {u : AmbientSpace → ℝ} (hu : Continuous u)
    (hh : HasDistributionalLaplacianOn u (fun _ => 0) Kᶜ)
    (hb : ∀ x ∈ K, u x = 1) (hinf : Tendsto u (cocompact AmbientSpace) (𝓝 0))
    {Ω : Set AmbientSpace} (hΩm : MeasurableSet Ω) (hΩb : Bornology.IsBounded Ω) :
    (∃ M R₂, ∀ R, R₂ < R → |outerWronskian u (coulombPotentialReal Ω) R| ≤ M / R ^ 2) ∧
      Tendsto (outerWronskian u (coulombPotentialReal Ω)) atTop (𝓝 0) := by
  obtain ⟨RK, hRK⟩ := hK.isBounded.subset_closedBall (0 : AmbientSpace)
  obtain ⟨RΩ, hRΩ⟩ := hΩb.subset_closedBall (0 : AmbientSpace)
  set R₀ := max (max RK RΩ) 1 with hR₀def
  have hR₀ : (0 : ℝ) < R₀ := lt_of_lt_of_le one_pos (le_max_right _ _)
  have hKR : K ⊆ closedBall 0 R₀ :=
    hRK.trans (closedBall_subset_closedBall ((le_max_left _ _).trans (le_max_left _ _)))
  have hΩR : Ω ⊆ closedBall 0 R₀ :=
    hRΩ.trans (closedBall_subset_closedBall ((le_max_right _ _).trans (le_max_left _ _)))
  obtain ⟨Cinf, R, C', -, hexp⟩ := kelvin_expansion hK hR₀ hKR hzero hu hh hb hinf
  have hkel : ∃ M R₁, ∀ x : AmbientSpace, R₁ < ‖x‖ →
      |u x - Cinf / ‖x‖| ≤ M / ‖x‖ ^ 2 ∧
        ‖gradient u x + (Cinf / ‖x‖ ^ 3) • x‖ ≤ M / ‖x‖ ^ 3 :=
    ⟨C', R, fun x hx => hexp x hx.le⟩
  exact ⟨wronskian_bound_of_kelvin Ω R₀ hΩm hΩR hR₀ u Cinf hkel,
    wronskian_tendsto_zero_of_kelvin Ω R₀ hΩm hΩR hR₀ u Cinf hkel⟩

/-- **`lem:wronskian`** with `u` from `thm:capacitary-potential`: for the filled hull `K` of a
bounded open `Ω ∋ 0` with `C²` boundary, the capacitary potential `u` of `K` exists
(continuous, harmonic and smooth off `K`, `u = 1` on `K`, `u → 0` at infinity, `0 < u < 1` off
`K`), and its outer Wronskian with `v_Ω` is `O(R⁻²)` and tends to `0` (`eq:wronskian`). -/
theorem exists_filledHull_capacitary_potential_wronskian {Ω : Set AmbientSpace}
    (ho : IsOpen Ω) (hbd : Bornology.IsBounded Ω) (h2 : HasC2Boundary Ω)
    (h0 : (0 : AmbientSpace) ∈ Ω) :
    ∃ u : AmbientSpace → ℝ, Continuous u ∧
      HasDistributionalLaplacianOn u (fun _ => 0) (filledHull Ω)ᶜ ∧
      ContDiffOn ℝ (⊤ : ℕ∞) u (filledHull Ω)ᶜ ∧
      (∀ x ∈ filledHull Ω, u x = 1) ∧ Tendsto u (cocompact AmbientSpace) (𝓝 0) ∧
      (∀ x ∈ (filledHull Ω)ᶜ, 0 < u x ∧ u x < 1) ∧
      (∃ M R₂, ∀ R, R₂ < R → |outerWronskian u (coulombPotentialReal Ω) R| ≤ M / R ^ 2) ∧
      Tendsto (outerWronskian u (coulombPotentialReal Ω)) atTop (𝓝 0) := by
  obtain ⟨u, hu, hh, hs, hb, hinf, hsign⟩ := exists_filledHull_capacitary_potential ho hbd h2 h0
  exact ⟨u, hu, hh, hs, hb, hinf, hsign,
    capacitary_wronskian (filledHull_isCompact hbd) (filledHull_subset_interior ho h0) hu hh hb
      hinf ho.measurableSet hbd⟩

end LiquidDrop

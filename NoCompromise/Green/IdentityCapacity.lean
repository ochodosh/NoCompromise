module

public import NoCompromise.Green.Identity
public import NoCompromise.Capacity.HullPotential
public import NoCompromise.Elliptic.ClassicalBoundaryMeasure

@[expose] public section

/-!
# `lem:wronskian` and `thm:green-identity` for the capacitary potential of the filled hull

For the filled hull `K` of a bounded open `Ω ∋ 0` with `C¹` boundary and any continuous `u`,
harmonic off `K`, `u = 1` on `K`, `u → 0` at infinity, the Kelvin-expansion input of
`wronskian_bound_of_kelvin` and `green_identity` is discharged by `filledHull_capacitary_properties`
(`lem:kelvin`, value and gradient parts, unconditional). The hull data of `green_identity` are the
conclusions of `lem:hull-properties`. For any `C²` function `g` (in the application, the
`C²` function agreeing with `u` on the closed exterior, the stand-in for `thm:boundary-C2a`,
so that `w = |∇g|` is the one-sided `|∇u|` on `∂K`), the integrability of `v_Ω w` on `∂K`
is proved. The only remaining named input is the second Green identity on
`B_R ∖ K` (`eq:green-second`).
-/

noncomputable section
open Set Filter Metric MeasureTheory
open scoped Topology
namespace LiquidDrop

variable {Ω : Set AmbientSpace}

/-- The real Coulomb potential of a bounded measurable set is continuous. -/
lemma continuous_coulombPotentialReal_of_isBounded (hΩm : MeasurableSet Ω)
    (hb : Bornology.IsBounded Ω) : Continuous (coulombPotentialReal Ω) := by
  have heq : coulombPotentialReal Ω = fun a => (coulombPotential Ω a).toReal := by
    funext a
    rw [coulombPotentialReal_eq_setIntegral Ω hΩm a,
      coulombPotential_toReal Ω hb.measure_lt_top a]
    simp only [one_div]
  rw [heq]
  exact (contDiff_one_coulombPotential_of_isBounded hb).continuous

/-- Blueprint `lem:wronskian` for the capacitary potential of the filled hull: the outer
Wronskian of `u` and `v_Ω` on the sphere of radius `R` is `O(R⁻²)`, with the Kelvin expansion
discharged. -/
theorem filledHull_wronskian_bound (ho : IsOpen Ω) (hbd : Bornology.IsBounded Ω)
    (h0 : (0 : AmbientSpace) ∈ Ω)
    {u : AmbientSpace → ℝ} (hu : Continuous u)
    (hh : HasDistributionalLaplacianOn u (fun _ => 0) (filledHull Ω)ᶜ)
    (hb : ∀ x ∈ filledHull Ω, u x = 1) (hinf : Tendsto u (cocompact AmbientSpace) (𝓝 0)) :
    ∃ M R₂, ∀ R, R₂ < R → |outerWronskian u (coulombPotentialReal Ω) R| ≤ M / R ^ 2 := by
  obtain ⟨-, ⟨R₀, -, hR₀, hKR, -, -⟩, ⟨Cinf, -, R, C', -, hexp⟩, -, -⟩ :=
    filledHull_capacitary_properties ho hbd h0 hu hh hb hinf
  exact wronskian_bound_of_kelvin Ω R₀ ho.measurableSet
    ((filledHull_closure_subset Ω).trans' subset_closure |>.trans hKR) hR₀ u Cinf
    ⟨C', R, fun x hx => hexp x hx.le⟩

/-- Blueprint `lem:wronskian` for the capacitary potential of the filled hull: the outer
Wronskian tends to zero. -/
theorem filledHull_wronskian_tendsto_zero (ho : IsOpen Ω) (hbd : Bornology.IsBounded Ω)
    (h0 : (0 : AmbientSpace) ∈ Ω)
    {u : AmbientSpace → ℝ} (hu : Continuous u)
    (hh : HasDistributionalLaplacianOn u (fun _ => 0) (filledHull Ω)ᶜ)
    (hb : ∀ x ∈ filledHull Ω, u x = 1) (hinf : Tendsto u (cocompact AmbientSpace) (𝓝 0)) :
    Tendsto (outerWronskian u (coulombPotentialReal Ω)) atTop (𝓝 0) := by
  obtain ⟨-, ⟨R₀, -, hR₀, hKR, -, -⟩, ⟨Cinf, -, R, C', -, hexp⟩, -, -⟩ :=
    filledHull_capacitary_properties ho hbd h0 hu hh hb hinf
  exact wronskian_tendsto_zero_of_kelvin Ω R₀ ho.measurableSet
    ((filledHull_closure_subset Ω).trans' subset_closure |>.trans hKR) hR₀ u Cinf
    ⟨C', R, fun x hx => hexp x hx.le⟩

/-- Blueprint `thm:green-identity` (`eq:green-identity`) for the capacitary potential `u` of the
filled hull `K` of a bounded open `Ω ∋ 0` with `C¹` boundary:
`(4π)⁻¹ ∫_{∂K} v_Ω w = |Ω|`, with `w = |∇g|` for any `C²` function `g`; in the application `g`
agrees with `u` on the closed exterior (the stand-in for `thm:boundary-C2a`), so `w` is the
one-sided `|∇u|` on `∂K`. No agreement hypothesis is needed for this implication.
Proved inputs: `lem:hull-properties` (hull data), `lem:kelvin` (expansion), `lem:wronskian`,
`lem:interior-flux`, integrability of `∂_ν v_Ω` and of `v_Ω w` on `∂K`.
Remaining named input: `hgreen_second_of_W11_gauss_green`, the second Green identity on
`B_R ∖ K` for large `R` (`eq:green-second`). -/
theorem filledHull_green_identity (ho : IsOpen Ω) (hbd : Bornology.IsBounded Ω)
    (h1 : HasC1Boundary Ω) (h0 : (0 : AmbientSpace) ∈ Ω)
    {u : AmbientSpace → ℝ} (hu : Continuous u)
    (hh : HasDistributionalLaplacianOn u (fun _ => 0) (filledHull Ω)ᶜ)
    (hb : ∀ x ∈ filledHull Ω, u x = 1) (hinf : Tendsto u (cocompact AmbientSpace) (𝓝 0))
    {g : AmbientSpace → ℝ} (hg : ContDiff ℝ 2 g)
    (hgreen_second_of_W11_gauss_green : ∀ᶠ R in atTop,
      (∫ x in frontier (filledHull Ω), (coulombPotentialReal Ω x * ‖gradient g x‖ +
          inner ℝ (gradient (coulombPotentialReal Ω) x)
            ((filledHull_hasC1Boundary_interior ho h1).outwardNormal x))
          ∂hausdorffMeasure2 3) +
        outerWronskian u (coulombPotentialReal Ω) R = 0) :
    (4 * Real.pi)⁻¹ * (∫ x in frontier (filledHull Ω),
      coulombPotentialReal Ω x * ‖gradient g x‖ ∂hausdorffMeasure2 3) = (volume Ω).toReal := by
  obtain ⟨-, ⟨R₀, -, hR₀, hKR, -, -⟩, ⟨Cinf, -, R, C', -, hexp⟩, -, -⟩ :=
    filledHull_capacitary_properties ho hbd h0 hu hh hb hinf
  have hΩK : Ω ⊆ closedBall 0 R₀ :=
    ((filledHull_closure_subset Ω).trans' subset_closure).trans hKR
  have hC1 := filledHull_hasC1Boundary_interior ho h1
  have hD : IsOpen (interior (filledHull Ω)) := isOpen_interior
  have hbD : Bornology.IsBounded (interior (filledHull Ω)) :=
    (filledHull_isCompact hbd).isBounded.subset interior_subset
  have hΩD : volume (Ω \ interior (filledHull Ω)) = 0 := by
    rw [sdiff_eq_empty.mpr (interior_maximal
      ((filledHull_closure_subset Ω).trans' subset_closure) ho), measure_empty]
  have hfr : frontier (interior (filledHull Ω)) = frontier (filledHull Ω) :=
    filledHull_frontier_interior ho
  have hvw : Integrable (fun x => coulombPotentialReal Ω x * ‖gradient g x‖)
      ((hausdorffMeasure2 3).restrict (frontier (interior (filledHull Ω)))) := by
    have : IsFiniteMeasure
        ((hausdorffMeasure2 3).restrict (frontier (interior (filledHull Ω)))) :=
      finite_boundary_area hD hbD hC1
    have hcont : Continuous (fun x => coulombPotentialReal Ω x * ‖gradient g x‖) :=
      (continuous_coulombPotentialReal_of_isBounded ho.measurableSet hbd).mul
        ((InnerProductSpace.toDual ℝ AmbientSpace).symm.continuous.comp
          (hg.continuous_fderiv (by norm_num))).norm
    have hK : IsCompact (frontier (interior (filledHull Ω))) :=
      hbD.isCompact_closure.of_isClosed_subset isClosed_frontier frontier_subset_closure
    obtain ⟨M, hM⟩ := hK.exists_bound_of_continuousOn hcont.continuousOn
    refine Integrable.mono' (integrable_const M) hcont.aestronglyMeasurable ?_
    filter_upwards [ae_restrict_mem isClosed_frontier.measurableSet] with x hx
    exact hM x hx
  have h := green_identity Ω (interior (filledHull Ω)) R₀ ho.measurableSet hΩK hR₀ hD hbD hC1
    hΩD u Cinf ⟨C', R, fun x hx => hexp x hx.le⟩ (fun x => ‖gradient g x‖)
    (by simpa only [hfr] using hgreen_second_of_W11_gauss_green) hvw
  simpa only [hfr] using h

end LiquidDrop

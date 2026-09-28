import NoCompromise.Hull.Properties
import NoCompromise.Capacity.KelvinLevels
import NoCompromise.Capacity.Flux
import NoCompromise.Capacity.Slabs
import NoCompromise.Elliptic.ClassicalNormal

/-!
# The capacitary potential of the filled hull (`thm:capacitary-potential`, properties)

For the filled hull `K` of a bounded open set `Ω ∋ 0` (the blueprint's
normalisation "translate so that `0 ∈ int K`"), every continuous `u` harmonic on `Kᶜ` with `u = 1`
on `K` and `u → 0` at infinity satisfies `eq:capacitary-signs` (`0 < u < 1` off `K`), the decay
of `lem:potential-decay`, the Kelvin expansion with `C∞ > 0`, and the slab/level compactness used
by chapter 31. With `C²` boundary and a derivative up to `∂K`, the Hopf sign holds in every
boundary chart of `Ω` at a point of `∂K`. Existence of `u` and its regularity up to `∂K` remain.
-/

noncomputable section
open Set Filter Metric Topology

namespace LiquidDrop

variable {Ω : Set AmbientSpace}

/-- `thm:capacitary-potential` for the filled hull `K` of a bounded open `Ω ∋ 0`, all properties
except existence and boundary regularity: for any continuous `u`, harmonic off `K`, `u = 1` on
`K`, `u → 0` at infinity: `0 < u < 1` off `K` (`eq:capacitary-signs`, using that `Kᶜ` is
connected), `lem:potential-decay`, the Kelvin expansion of `lem:kelvin` with `C∞ > 0`, and the
compact slabs and nonempty compact levels in `Kᶜ` required by chapter 31. -/
theorem filledHull_capacitary_properties (ho : IsOpen Ω) (hbd : Bornology.IsBounded Ω)
    (h0 : (0 : AmbientSpace) ∈ Ω)
    {u : AmbientSpace → ℝ} (hu : Continuous u)
    (hh : HasDistributionalLaplacianOn u (fun _ => 0) (filledHull Ω)ᶜ)
    (hb : ∀ x ∈ filledHull Ω, u x = 1) (hinf : Tendsto u (cocompact AmbientSpace) (𝓝 0)) :
    (∀ x ∈ (filledHull Ω)ᶜ, 0 < u x ∧ u x < 1) ∧
    (∃ R₀ C : ℝ, 0 < R₀ ∧ filledHull Ω ⊆ closedBall 0 R₀ ∧
      (∀ x ∈ (filledHull Ω)ᶜ, |u x| ≤ R₀ / ‖x‖) ∧
      ∀ x : AmbientSpace, 2 * R₀ ≤ ‖x‖ → ‖gradient u x‖ ≤ C / ‖x‖ ^ 2) ∧
    (∃ Cinf : ℝ, 0 < Cinf ∧ ∃ R C' : ℝ, 0 < R ∧ ∀ x : AmbientSpace, R ≤ ‖x‖ →
      |u x - Cinf / ‖x‖| ≤ C' / ‖x‖ ^ 2 ∧
      ‖gradient u x + (Cinf / ‖x‖ ^ 3) • x‖ ≤ C' / ‖x‖ ^ 3) ∧
    (∀ a b : ℝ, 0 < a → a < b → b < 1 →
      IsCompact (closure ((filledHull Ω)ᶜ ∩ u ⁻¹' Ioo a b)) ∧
        closure ((filledHull Ω)ᶜ ∩ u ⁻¹' Ioo a b) ⊆ (filledHull Ω)ᶜ) ∧
    (∀ t : ℝ, 0 < t → t < 1 →
      u ⁻¹' {t} ⊆ (filledHull Ω)ᶜ ∧ IsCompact (u ⁻¹' {t}) ∧ (u ⁻¹' {t}).Nonempty) := by
  have hK := filledHull_isCompact hbd
  have hzero : (0 : AmbientSpace) ∈ interior (filledHull Ω) := filledHull_subset_interior ho h0
  have hconn : IsPreconnected (filledHull Ω)ᶜ := (filledHull_isConnected_compl hbd).isPreconnected
  have hKne : (filledHull Ω).Nonempty := ⟨0, interior_subset hzero⟩
  obtain ⟨R₀, hR₀⟩ := hK.isBounded.subset_closedBall (0 : AmbientSpace)
  have hR₀' : filledHull Ω ⊆ closedBall 0 (max R₀ 1) :=
    hR₀.trans (closedBall_subset_closedBall (le_max_left _ _))
  have hpos : (0 : ℝ) < max R₀ 1 := lt_of_lt_of_le one_pos (le_max_right _ _)
  obtain ⟨hsign, hstrict⟩ := capacitary_signs hK hzero hu hh hb hinf
  obtain ⟨C, habs, hgrad⟩ := potential_decay hK hpos hR₀' hzero hu hh hb hinf
  refine ⟨fun x hx => ⟨(hsign x hx).1, hstrict hconn x hx⟩,
    ⟨max R₀ 1, C, hpos, hR₀', habs, hgrad⟩,
    kelvin_expansion_pos hK hpos hR₀' hzero hu hh hb hinf,
    capacitary_slab_Ioo hu hb hinf,
    capacitary_levels hK hKne hconn hu hb hinf⟩

/-- `thm:capacitary-potential`, Step 5 (`eq:capacitary-signs`, Hopf half) for the filled hull:
at a point of `∂K ⊆ ∂Ω`, in every `C²` boundary chart of `Ω`, the derivative of `u` up to the
boundary is strictly negative on the outward normal (which is also the outward normal of `K`). -/
theorem filledHull_capacitary_hopf_sign (ho : IsOpen Ω) (hbd : Bornology.IsBounded Ω)
    (h1 : HasC1Boundary Ω) (h0 : (0 : AmbientSpace) ∈ Ω)
    {u : AmbientSpace → ℝ} (hu : Continuous u)
    (hh : HasDistributionalLaplacianOn u (fun _ => 0) (filledHull Ω)ᶜ)
    (hb : ∀ x ∈ filledHull Ω, u x = 1) (hinf : Tendsto u (cocompact AmbientSpace) (𝓝 0))
    {p : AmbientSpace} (hp : p ∈ frontier (filledHull Ω))
    {L : AmbientSpace →L[ℝ] ℝ} (hd : HasFDerivWithinAt u L (closure (filledHull Ω)ᶜ) p)
    {c : C1BoundaryChart} (hcΩ : c.IsChartFor Ω) (hpc : p ∈ c.region)
    (hC2 : ContDiff ℝ 2 c.height) :
    L (c.outwardNormal p) < 0 := by
  have hK := filledHull_isCompact hbd
  have hzero : (0 : AmbientSpace) ∈ interior (filledHull Ω) := filledHull_subset_interior ho h0
  have hconn : IsPreconnected (filledHull Ω)ᶜ :=
    (filledHull_isConnected_compl hbd).isPreconnected
  have hcl : closure (interior (filledHull Ω)) = filledHull Ω :=
    (filledHull_eq_closure_interior ho).symm
  obtain ⟨c', hhe, hpl, -, hpc', hc'⟩ := hull_chart_of_chart ho h1 hcΩ hp hpc
  have hn : c'.outwardNormal = c.outwardNormal := by
    funext z
    simp only [C1BoundaryChart.outwardNormal, hhe, hpl]
  have hp' : p ∈ frontier (interior (filledHull Ω)) := by
    rw [filledHull_frontier_interior ho]
    exact hp
  have hpK : p ∈ filledHull Ω := (filledHull_isClosed Ω).frontier_subset hp
  have hstrict := (capacitary_signs hK hzero hu hh hb hinf).2 hconn
  rw [← hn]
  refine hopf_exterior_chart hc' (by rw [hhe]; exact hC2) hp' hpc' ?_ ?_ ?_ (hb p hpK) ?_
  · exact hu.continuousOn
  · rw [hcl]
    exact hh
  · rw [hcl]
    exact hstrict
  · rw [hcl]
    exact hd

/-- `lem:hull-properties`: the outward normals of `K` and `Ω` agree on `∂K`. -/
theorem filledHull_outwardNormal_eq (ho : IsOpen Ω) (h1 : HasC1Boundary Ω)
    {p : AmbientSpace} (hp : p ∈ frontier (filledHull Ω)) :
    (filledHull_hasC1Boundary_interior ho h1).outwardNormal p = h1.outwardNormal p := by
  have hpΩ := filledHull_frontier_subset ho hp
  obtain ⟨c, hc, hpc⟩ := h1 p hpΩ
  obtain ⟨c', hhe, hpl, -, hpc', hc'⟩ := hull_chart_of_chart ho h1 hc hp hpc
  have hp' : p ∈ frontier (interior (filledHull Ω)) := by
    rw [filledHull_frontier_interior ho]
    exact hp
  rw [HasC1Boundary.outwardNormal_eq_chart _ hc' hp' hpc',
    HasC1Boundary.outwardNormal_eq_chart _ hc hpΩ hpc]
  simp only [C1BoundaryChart.outwardNormal, hhe, hpl]

end LiquidDrop

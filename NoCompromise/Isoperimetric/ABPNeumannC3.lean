module

public import NoCompromise.Isoperimetric.ABPNeumann
public import NoCompromise.Stationary.Defs

@[expose] public section

/-!
# The ABP Neumann problem on domains with `C³` boundary

The contact-set argument of `prop:iso-smooth` consumes only a solution `z` of the ABP Neumann
problem that is `C²` in `G`, `C¹` up to the boundary, with `Δz = Per(G)/|G|` pointwise in `G`
and the classical conormal condition `∂_ν z = 1` on `∂G` (`IsABPNeumannC1Solution`). Such a
solution exists already for bounded connected domains with `C³` boundary (Schauder theory for
the Neumann problem needs a `C^{2,α}` boundary for `C^{2,α}` up to the boundary). This file
records blueprint `lem:abp-neumann` in that strengthened form as the named predicate
`ABPNeumannSolvableC3`, and proves

* `ABPNeumannSolvableC3.c1Solvable`: it implies `ABPNeumannC1Solvable` (smooth boundary is `C³`);
* the weak-to-classical reduction, mirroring `ABPNeumann.lean`: the compatibility condition and
  the mean-zero weak solution for `C¹` domains, the interior regularity, and
  `abpNeumannSolvableC3_of_localBoundary` reducing `ABPNeumannSolvableC3` to the single local
  boundary hypothesis `ABPNeumannLocalBoundaryC1RegularityC3`;
* `iso_C3`: blueprint `prop:iso-smooth` for bounded connected open sets with `C³` boundary.
-/

noncomputable section

open MeasureTheory Set Filter Metric
open scoped Topology ENNReal InnerProductSpace

namespace LiquidDrop

/-- Blueprint `lem:abp-neumann`, strengthened to domains with `C³` boundary and stated with the
regularity consumed by the contact-set argument: every bounded connected open set `G` with `C³`
boundary carries `z` that is `C²` in `G`, `C¹` on `closure G`, with `Δz = Per(G)/|G|` in `G` and
`∂_ν z = 1` on `∂G` (derivative within `closure G`, classical outward normal). -/
def ABPNeumannSolvableC3 : Prop :=
  ∀ G : Set AmbientSpace, IsOpen G → Bornology.IsBounded G → IsConnected G →
    ∀ hG : HasCkBoundary 3 G, ∃ z : AmbientSpace → ℝ,
      IsABPNeumannC1Solution G hG.hasC1Boundary z

/-- Smooth boundary is `C³` boundary, so `ABPNeumannSolvableC3` gives the C¹-up-to-the-boundary
ABP Neumann solutions on smooth domains. -/
theorem ABPNeumannSolvableC3.c1Solvable (h : ABPNeumannSolvableC3) : ABPNeumannC1Solvable :=
  fun G hGo hGb hGc hGs => h G hGo hGb hGc (hGs.hasCkBoundary 3)

/-! ### The weak problem on a `C¹` domain -/

/-- The unit boundary datum on the normalized Hausdorff boundary measure of a bounded open set
with `C¹` boundary. For smooth `G` it is `abpNeumannFlux` (`abpNeumannFlux_eq_fluxC1`). -/
def abpNeumannFluxC1 (G : Set AmbientSpace) (hGo : IsOpen G)
    (hGb : Bornology.IsBounded G) (hG : HasC1Boundary G) :
    Lp ℝ 2 ((hausdorffMeasure2 3).restrict (frontier G)) := by
  haveI := finite_boundary_area hGo hGb hG
  exact Lp.const 2 ((hausdorffMeasure2 3).restrict (frontier G)) 1

lemma abpNeumannFlux_eq_fluxC1 (G : Set AmbientSpace) (hGo : IsOpen G)
    (hGb : Bornology.IsBounded G) (hGs : HasSmoothBoundary G) :
    abpNeumannFlux G hGo hGb hGs = abpNeumannFluxC1 G hGo hGb hGs.hasC1Boundary :=
  rfl

lemma abpNeumannFluxC1_ae (G : Set AmbientSpace) (hGo : IsOpen G)
    (hGb : Bornology.IsBounded G) (hG : HasC1Boundary G) :
    ⇑(abpNeumannFluxC1 G hGo hGb hG) =ᵐ[
      (hausdorffMeasure2 3).restrict (frontier G)] fun _ => (1 : ℝ) := by
  unfold abpNeumannFluxC1
  let := finite_boundary_area hGo hGb hG
  filter_upwards [Lp.coeFn_const (2 : ℝ≥0∞)
      ((hausdorffMeasure2 3).restrict (frontier G)) (1 : ℝ)] with x hx
  simpa using hx

/-- The constant ABP data satisfy Neumann compatibility on a bounded connected `C¹` domain. -/
theorem abpNeumann_compatibility_C1 (G : Set AmbientSpace) (hGo : IsOpen G)
    (hGb : Bornology.IsBounded G) (hGc : IsConnected G) (hG : HasC1Boundary G) :
    (∫ x in G, abpNeumannForcing G hGb x) =
      ∫ x, abpNeumannFluxC1 G hGo hGb hG x
        ∂(hausdorffMeasure2 3).restrict (frontier G) := by
  rw [integral_congr_ae (abpNeumannForcing_ae G hGb),
    integral_congr_ae (abpNeumannFluxC1_ae G hGo hGb hG)]
  simp only [integral_const, smul_eq_mul, mul_one, Measure.real,
    Measure.restrict_apply_univ]
  rw [hG.perimeter_eq_boundaryArea hGo]
  have hV : volume.real G ≠ 0 :=
    (ENNReal.toReal_pos_iff.mpr ⟨hGo.measure_pos volume hGc.nonempty,
      hGb.measure_lt_top⟩).ne'
  change (volume G).toReal ≠ 0 at hV
  field_simp [hV]

/-- The ABP constant data have a mean-zero weak H¹ solution on a bounded connected `C¹`
domain. -/
theorem exists_abpNeumann_weak_solution_C1 (G : Set AmbientSpace) (hGo : IsOpen G)
    (hGb : Bornology.IsBounded G) (hGc : IsConnected G) (hG : HasC1Boundary G) :
    ∃ z : H1Space G, (∫ x in G, z x) = 0 ∧
      IsWeakNeumannSolution hGo hGb hG.hasLipschitzBoundary
        (abpNeumannForcing G hGb) (abpNeumannFluxC1 G hGo hGb hG) z := by
  obtain ⟨_, _, hsolve⟩ := exists_weak_neumann hGo hGc.isPreconnected hGb
    hG.hasLipschitzBoundary
  obtain ⟨z, hz, hw, _⟩ := hsolve (abpNeumannForcing G hGb)
    (abpNeumannFluxC1 G hGo hGb hG) (abpNeumann_compatibility_C1 G hGo hGb hGc hG)
  exact ⟨z, hz, hw⟩

/-- Interior regularity on a `C¹` domain: every weak solution of the constant ABP data has a
`C²` interior representative with `Δ = Per(G)/|G|` pointwise. -/
theorem abpNeumann_interior_regularity_C1 (G : Set AmbientSpace) (hGo : IsOpen G)
    (hGb : Bornology.IsBounded G) (hG : HasC1Boundary G) (z : H1Space G)
    (hz : IsWeakNeumannSolution hGo hGb hG.hasLipschitzBoundary
      (abpNeumannForcing G hGb) (abpNeumannFluxC1 G hGo hGb hG) z) :
    ∃ v₀ : AmbientSpace → ℝ, ContDiffOn ℝ 2 v₀ G ∧
      (⇑z =ᵐ[volume.restrict G] v₀) ∧
      ∀ x ∈ G, laplacianTrace v₀ x = (perimeter G).toReal / volume.real G := by
  obtain ⟨v, hv, hzv, hlap, _⟩ :=
    hz.exists_smooth_interior_representative (abpNeumannForcing_ae G hGb)
  exact ⟨v, (by simpa using contDiffOn_infty.mp hv 2 : ContDiffOn ℝ 2 v G), hzv, hlap⟩

/-! ### Weak-to-classical boundary regularity on `C³` domains -/

/-- First-order boundary regularity for every weak solution of the constant ABP data on a
bounded connected open set with `C³` boundary: the `C³` analogue of
`ABPNeumannBoundaryC1Regularity`. -/
def ABPNeumannBoundaryC1RegularityC3 : Prop :=
  ∀ (G : Set AmbientSpace) (hGo : IsOpen G) (hGb : Bornology.IsBounded G)
    (_hGc : IsConnected G) (hG : HasCkBoundary 3 G) (z : H1Space G),
    IsWeakNeumannSolution hGo hGb hG.hasC1Boundary.hasLipschitzBoundary
      (abpNeumannForcing G hGb) (abpNeumannFluxC1 G hGo hGb hG.hasC1Boundary) z →
    ∃ v : AmbientSpace → ℝ, (⇑z =ᵐ[volume.restrict G] v) ∧
      IsABPNeumannC1Solution G hG.hasC1Boundary v

/-- First-order boundary regularity on `C³` domains restricts to the one on smooth domains. -/
theorem ABPNeumannBoundaryC1RegularityC3.toSmooth
    (h : ABPNeumannBoundaryC1RegularityC3) : ABPNeumannBoundaryC1Regularity :=
  fun G hGo hGb hGc hGs z hz => h G hGo hGb hGc (hGs.hasCkBoundary 3) z hz

/-- The weak theorem and first-order boundary regularity give `ABPNeumannSolvableC3`. -/
theorem abpNeumannSolvableC3_of_boundaryC1Regularity
    (hR : ABPNeumannBoundaryC1RegularityC3) : ABPNeumannSolvableC3 := by
  intro G hGo hGb hGc hG
  obtain ⟨z, _, hz⟩ := exists_abpNeumann_weak_solution_C1 G hGo hGb hGc hG.hasC1Boundary
  obtain ⟨v, _, hv⟩ := hR G hGo hGb hGc hG z hz
  exact ⟨v, hv⟩

/-- The local boundary ingredient on `C³` domains, as a named hypothesis: the `C³` analogue of
`ABPNeumannLocalBoundaryC1Regularity`. Near every boundary point a weak solution of the
constant ABP data agrees a.e. with a `C¹` function on an open neighbourhood whose derivative
along the classical outward normal is `1` on the boundary. -/
def ABPNeumannLocalBoundaryC1RegularityC3 : Prop :=
  ∀ (G : Set AmbientSpace) (hGo : IsOpen G) (hGb : Bornology.IsBounded G)
    (_hGc : IsConnected G) (hG : HasCkBoundary 3 G) (z : H1Space G),
    IsWeakNeumannSolution hGo hGb hG.hasC1Boundary.hasLipschitzBoundary
      (abpNeumannForcing G hGb) (abpNeumannFluxC1 G hGo hGb hG.hasC1Boundary) z →
    ∀ p ∈ frontier G, ∃ V : Set AmbientSpace, ∃ w : AmbientSpace → ℝ,
      IsOpen V ∧ p ∈ V ∧ ContDiffOn ℝ 1 w V ∧ (⇑z =ᵐ[volume.restrict (G ∩ V)] w) ∧
      ∀ x ∈ frontier G ∩ V, fderiv ℝ w x (hG.hasC1Boundary.outwardNormal x) = 1

/-- The local boundary hypothesis on `C³` domains restricts to the one on smooth domains. -/
theorem ABPNeumannLocalBoundaryC1RegularityC3.toSmooth
    (h : ABPNeumannLocalBoundaryC1RegularityC3) : ABPNeumannLocalBoundaryC1Regularity :=
  fun G hGo hGb hGc hGs z hz => h G hGo hGb hGc (hGs.hasCkBoundary 3) z hz

/-- `ABPNeumannBoundaryC1RegularityC3` from the single local boundary hypothesis: the interior
regularity is proved and the gluing is `neumann_glue_c1_closure`. -/
theorem abpNeumannBoundaryC1RegularityC3_of_localBoundary
    (hb : ABPNeumannLocalBoundaryC1RegularityC3) : ABPNeumannBoundaryC1RegularityC3 := by
  intro G hGo hGb hGc hG z hz
  obtain ⟨v₀, hv₀, hz₀, hlap⟩ :=
    abpNeumann_interior_regularity_C1 G hGo hGb hG.hasC1Boundary z hz
  obtain ⟨v, hvG, hzv, hv2, hv1, hν⟩ := neumann_glue_c1_closure hGo hv₀ hz₀
    (hb G hGo hGb hGc hG z hz)
    (fun x hx => hG.hasC1Boundary.uniqueDiffWithinAt_closure hx)
  refine ⟨v, hzv, hv2, hv1, ?_, hν⟩
  intro x hx
  have he : v =ᶠ[𝓝 x] v₀ := Filter.eventually_of_mem (hGo.mem_nhds hx) (fun y hy => hvG hy)
  have hd : fderiv ℝ (fderiv ℝ v) x = fderiv ℝ (fderiv ℝ v₀) x := he.fderiv.fderiv_eq
  rw [← hlap x hx]
  simp only [laplacianTrace, hessianForm, hd]

/-- `ABPNeumannSolvableC3` from the single local boundary hypothesis
`ABPNeumannLocalBoundaryC1RegularityC3`. -/
theorem abpNeumannSolvableC3_of_localBoundary
    (hb : ABPNeumannLocalBoundaryC1RegularityC3) : ABPNeumannSolvableC3 :=
  abpNeumannSolvableC3_of_boundaryC1Regularity
    (abpNeumannBoundaryC1RegularityC3_of_localBoundary hb)

/-! ### `prop:iso-smooth` for `C³` domains -/

/-- Blueprint `prop:iso-smooth`, strengthened to `C³` boundary: a bounded connected open set
with `C³` boundary satisfies `Per(G)^3 ≥ 36π |G|^2`, given `ABPNeumannSolvableC3`. -/
theorem iso_C3 (hN : ABPNeumannSolvableC3) {G : Set AmbientSpace} (hGo : IsOpen G)
    (hGb : Bornology.IsBounded G) (hGc : IsConnected G) (hG : HasCkBoundary 3 G) :
    36 * Real.pi * volume.real G ^ 2 ≤ (perimeter G).toReal ^ 3 := by
  obtain ⟨z, hz2, hz1, hlap, hν⟩ := hN G hGo hGb hGc hG
  exact iso_smooth_of_neumann_solution hGb hGo hGc.nonempty hz2 hz1.continuousOn
    (hG.hasC1Boundary.neumannOne hz1 hν) hlap

/-- Blueprint `prop:iso-smooth` (smooth domains) from `ABPNeumannSolvableC3`. -/
theorem iso_smooth_of_abpNeumannSolvableC3 (hN : ABPNeumannSolvableC3) {G : Set AmbientSpace}
    (hGo : IsOpen G) (hGb : Bornology.IsBounded G) (hGc : IsConnected G)
    (hGs : HasSmoothBoundary G) :
    36 * Real.pi * volume.real G ^ 2 ≤ (perimeter G).toReal ^ 3 :=
  iso_C3 hN hGo hGb hGc (hGs.hasCkBoundary 3)

end LiquidDrop

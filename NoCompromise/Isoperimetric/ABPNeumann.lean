module

public import NoCompromise.Isoperimetric.ABPContact
public import NoCompromise.Elliptic.ClassicalNormal
public import NoCompromise.Elliptic.WeakSolutions
public import NoCompromise.Elliptic.ClassicalBoundaryMeasure
public import NoCompromise.BV.SmoothApproxBoundary
public import NoCompromise.Elliptic.NeumannGlue
public import NoCompromise.Elliptic.NeumannUniqueDiff
public import NoCompromise.Elliptic.NeumannInteriorSmooth

@[expose] public section

/-!
# The ABP auxiliary Neumann problem

Blueprint `lem:abp-neumann` asserts that a bounded connected smooth domain `G` carries a
function `z`, smooth up to the boundary, with `Δz = Per(G)/|G|` in `G` and `∂_ν z = 1` on
`∂G`. Compatibility and a mean-zero weak H¹ solution follow from `exists_weak_neumann`.
The weak-to-classical boundary regularity step is stated explicitly as
`ABPNeumannBoundaryRegularity`; the classical existence assertion is still carried as
the named predicate `ABPNeumannSolvable`.

What is proved here is the passage from such a classical solution to the hypotheses of
the contact-set argument: the classical conormal condition `∂_ν z = 1`, with `ν` the chart
outward normal `HasC1Boundary.outwardNormal`, gives the inward-ray form `NeumannOne`.
-/

noncomputable section

open MeasureTheory Set Filter Metric
open scoped Topology ENNReal InnerProductSpace

namespace LiquidDrop

/-- The conclusion of blueprint `lem:abp-neumann` for one domain: `z` is smooth up to the
boundary, `Δz = Per(G)/|G|` in `G`, and `∂_ν z = 1` on `∂G` for the classical outward unit
normal `ν`. The normal derivative is the derivative within `closure G`. -/
def IsABPNeumannSolution (G : Set AmbientSpace) (hG : HasC1Boundary G)
    (z : AmbientSpace → ℝ) : Prop :=
  ContDiffOn ℝ (⊤ : ℕ∞) z (closure G) ∧
    (∀ x ∈ G, laplacianTrace z x = (perimeter G).toReal / volume.real G) ∧
    ∀ x ∈ frontier G, fderivWithin ℝ z (closure G) x (hG.outwardNormal x) = 1

/-- Blueprint `lem:abp-neumann` as a named hypothesis: every bounded connected open set with
smooth boundary carries a solution of the ABP Neumann problem. Its proof needs
`thm:boundary-neumann` (Chapter 10), not yet stated in Lean. -/
def ABPNeumannSolvable : Prop :=
  ∀ G : Set AmbientSpace, IsOpen G → Bornology.IsBounded G → IsConnected G →
    ∀ hG : HasSmoothBoundary G, ∃ z : AmbientSpace → ℝ,
      IsABPNeumannSolution G hG.hasC1Boundary z

/-- The constant interior datum in the ABP Neumann problem, as an actual L² class. -/
def abpNeumannForcing (G : Set AmbientSpace) (hGb : Bornology.IsBounded G) :
    Lp ℝ 2 (volume.restrict G) := by
  haveI : IsFiniteMeasure (volume.restrict G) := ⟨by simpa using hGb.measure_lt_top⟩
  exact Lp.const 2 (volume.restrict G) ((perimeter G).toReal / volume.real G)

/-- The unit boundary datum on the actual normalized Hausdorff boundary measure. -/
def abpNeumannFlux (G : Set AmbientSpace) (hGo : IsOpen G)
    (hGb : Bornology.IsBounded G) (hGs : HasSmoothBoundary G) :
    Lp ℝ 2 ((hausdorffMeasure2 3).restrict (frontier G)) := by
  haveI := finite_boundary_area hGo hGb hGs.hasC1Boundary
  exact Lp.const 2 ((hausdorffMeasure2 3).restrict (frontier G)) 1

lemma abpNeumannForcing_ae (G : Set AmbientSpace) (hGb : Bornology.IsBounded G) :
    ⇑(abpNeumannForcing G hGb) =ᵐ[volume.restrict G]
      fun _ => (perimeter G).toReal / volume.real G := by
  unfold abpNeumannForcing
  let : IsFiniteMeasure (volume.restrict G) := ⟨by simpa using hGb.measure_lt_top⟩
  filter_upwards [Lp.coeFn_const (2 : ℝ≥0∞) (volume.restrict G)
      ((perimeter G).toReal / volume.real G)] with x hx
  simpa using hx

lemma abpNeumannFlux_ae (G : Set AmbientSpace) (hGo : IsOpen G)
    (hGb : Bornology.IsBounded G) (hGs : HasSmoothBoundary G) :
    ⇑(abpNeumannFlux G hGo hGb hGs) =ᵐ[
      (hausdorffMeasure2 3).restrict (frontier G)] fun _ => (1 : ℝ) := by
  unfold abpNeumannFlux
  let := finite_boundary_area hGo hGb hGs.hasC1Boundary
  filter_upwards [Lp.coeFn_const (2 : ℝ≥0∞)
      ((hausdorffMeasure2 3).restrict (frontier G)) (1 : ℝ)] with x hx
  simpa using hx

/-- The constant ABP data satisfy Neumann compatibility, using the actual boundary area. -/
theorem abpNeumann_compatibility (G : Set AmbientSpace) (hGo : IsOpen G)
    (hGb : Bornology.IsBounded G) (hGc : IsConnected G) (hGs : HasSmoothBoundary G) :
    (∫ x in G, abpNeumannForcing G hGb x) =
      ∫ x, abpNeumannFlux G hGo hGb hGs x
        ∂(hausdorffMeasure2 3).restrict (frontier G) := by
  rw [integral_congr_ae (abpNeumannForcing_ae G hGb),
    integral_congr_ae (abpNeumannFlux_ae G hGo hGb hGs)]
  simp only [integral_const, smul_eq_mul, mul_one, Measure.real,
    Measure.restrict_apply_univ]
  rw [hGs.hasC1Boundary.perimeter_eq_boundaryArea hGo]
  have hV : volume.real G ≠ 0 :=
    (ENNReal.toReal_pos_iff.mpr ⟨hGo.measure_pos volume hGc.nonempty,
      hGb.measure_lt_top⟩).ne'
  change (volume G).toReal ≠ 0 at hV
  field_simp [hV]

/-- The ABP constant data have a mean-zero weak H¹ solution. -/
theorem exists_abpNeumann_weak_solution (G : Set AmbientSpace) (hGo : IsOpen G)
    (hGb : Bornology.IsBounded G) (hGc : IsConnected G) (hGs : HasSmoothBoundary G) :
    ∃ z : H1Space G, (∫ x in G, z x) = 0 ∧
      IsWeakNeumannSolution hGo hGb hGs.hasC1Boundary.hasLipschitzBoundary
        (abpNeumannForcing G hGb) (abpNeumannFlux G hGo hGb hGs) z := by
  obtain ⟨_, _, hsolve⟩ := exists_weak_neumann hGo hGc.isPreconnected hGb
    hGs.hasC1Boundary.hasLipschitzBoundary
  obtain ⟨z, hz, hw, _⟩ := hsolve (abpNeumannForcing G hGb)
    (abpNeumannFlux G hGo hGb hGs) (abpNeumann_compatibility G hGo hGb hGc hGs)
  exact ⟨z, hz, hw⟩

/-- Boundary regularity for every weak solution of the constant ABP data. The
representative agrees with its H¹ class almost
everywhere on `G`; its classical equations use the same constants and outward normal. -/
def ABPNeumannBoundaryRegularity : Prop :=
  ∀ (G : Set AmbientSpace) (hGo : IsOpen G) (hGb : Bornology.IsBounded G)
    (_hGc : IsConnected G) (hGs : HasSmoothBoundary G) (z : H1Space G),
    IsWeakNeumannSolution hGo hGb hGs.hasC1Boundary.hasLipschitzBoundary
      (abpNeumannForcing G hGb) (abpNeumannFlux G hGo hGb hGs) z →
    ∃ v : AmbientSpace → ℝ, (⇑z =ᵐ[volume.restrict G] v) ∧
      IsABPNeumannSolution G hGs.hasC1Boundary v

/-- The weak theorem and an explicitly assumed weak-to-classical boundary regularity
result give the classical ABP Neumann solution. -/
theorem abpNeumannSolvable_of_boundaryRegularity
    (hR : ABPNeumannBoundaryRegularity) : ABPNeumannSolvable := by
  intro G hGo hGb hGc hGs
  obtain ⟨z, _, hz⟩ := exists_abpNeumann_weak_solution G hGo hGb hGc hGs
  obtain ⟨v, _, hv⟩ := hR G hGo hGb hGc hGs z hz
  exact ⟨v, hv⟩

/-- The inward ray along the classical outward normal enters a C¹ domain. -/
theorem HasC1Boundary.eventually_sub_smul_outwardNormal_mem {G : Set AmbientSpace}
    (hG : HasC1Boundary G) {x : AmbientSpace} (hx : x ∈ frontier G) :
    ∀ᶠ t in 𝓝[>] (0 : ℝ), x - t • hG.outwardNormal x ∈ G := by
  obtain ⟨c, hc, hxc⟩ := hG x hx
  have hν : hG.outwardNormal x = c.outwardNormal x := hG.outwardNormal_eq_chart hc hx hxc
  have hd := c.hasDerivAt_definingFunction_line x (-c.outwardNormal x)
  have hneg : Real.sqrt
      (1 + ‖gradient c.height (graphProjectionN 2 (c.placement.symm x))‖ ^ 2) *
      ⟪-c.outwardNormal x, c.outwardNormal x⟫_ℝ < 0 := by
    rw [inner_neg_left, real_inner_self_eq_norm_sq, c.norm_outwardNormal]
    have : 0 < Real.sqrt
        (1 + ‖gradient c.height (graphProjectionN 2 (c.placement.symm x))‖ ^ 2) :=
      Real.sqrt_pos.mpr (by positivity)
    nlinarith
  have hev := classicalNormal_eventually_neg_of_hasDerivAt hd
    (by simpa using hc.definingFunction_eq_zero hx hxc) hneg
  have ht : Tendsto (fun t : ℝ => x + t • (-c.outwardNormal x)) (𝓝[>] 0) (𝓝 x) := by
    have hh : Continuous (fun t : ℝ => x + t • (-c.outwardNormal x)) := by fun_prop
    simpa using (hh.continuousAt (x := (0 : ℝ))).tendsto.mono_left nhdsWithin_le_nhds
  have hr := ht (c.isOpen_region.mem_nhds hxc)
  filter_upwards [hev, hr] with t htneg htr
  have hmem := (hc.mem_iff_definingFunction_neg htr).mpr htneg
  rwa [hν, sub_eq_add_neg, ← smul_neg]

/-- Blueprint `lem:abp-neumann`, the boundary condition in the form used by
`lem:abp-contact`: the classical condition `∂_ν z = 1` gives `NeumannOne`. -/
theorem HasC1Boundary.neumannOne {G : Set AmbientSpace} (hG : HasC1Boundary G)
    {z : AmbientSpace → ℝ} (hz : ContDiffOn ℝ 1 z (closure G))
    (hν : ∀ x ∈ frontier G, fderivWithin ℝ z (closure G) x (hG.outwardNormal x) = 1) :
    NeumannOne G z := by
  intro x hx
  refine ⟨hG.outwardNormal x, hG.norm_outwardNormal hx,
    hG.eventually_sub_smul_outwardNormal_mem hx, ?_⟩
  set ν := hG.outwardNormal x
  let r : ℝ → AmbientSpace := fun t => x - t • ν
  have hxcl : x ∈ closure G := frontier_subset_closure hx
  have hzd : HasFDerivWithinAt z (fderivWithin ℝ z (closure G) x) (closure G) x :=
    ((hz.differentiableOn one_ne_zero) x hxcl).hasFDerivWithinAt
  have hline : HasDerivAt r (-ν) 0 := by
    simpa [r] using ((hasDerivAt_id (0 : ℝ)).smul_const ν).const_sub x
  have hcomp : HasDerivWithinAt (fun t => z (r t))
      (fderivWithin ℝ z (closure G) x (-ν)) (r ⁻¹' closure G) 0 := by
    have hzd' : HasFDerivWithinAt z (fderivWithin ℝ z (closure G) x) (closure G) (r 0) := by
      simpa [r] using hzd
    exact hzd'.comp_hasDerivWithinAt 0 hline.hasDerivWithinAt (mapsTo_preimage r _)
  have hval : fderivWithin ℝ z (closure G) x (-ν) = -1 := by
    rw [map_neg, hν x hx]
  rw [hval] at hcomp
  apply hcomp.mono_of_mem_nhdsWithin
  obtain ⟨u, hu, hsub⟩ :=
    mem_nhdsGT_iff_exists_Ioo_subset.mp (hG.eventually_sub_smul_outwardNormal_mem hx)
  filter_upwards [Ico_mem_nhdsGE hu] with t ht
  rcases eq_or_lt_of_le ht.1 with h0 | hpos
  · subst h0
    simpa [r] using hxcl
  · exact subset_closure (hsub ⟨hpos, ht.2⟩)

namespace IsABPNeumannSolution

variable {G : Set AmbientSpace} {hG : HasC1Boundary G} {z : AmbientSpace → ℝ}

lemma contDiffOn_two (h : IsABPNeumannSolution G hG z) : ContDiffOn ℝ 2 z G :=
  (by simpa using contDiffOn_infty.mp h.1 2 : ContDiffOn ℝ 2 z (closure G)).mono
    subset_closure

lemma continuousOn (h : IsABPNeumannSolution G hG z) : ContinuousOn z (closure G) :=
  h.1.continuousOn

/-- A solution of the ABP Neumann problem satisfies `NeumannOne`. -/
lemma neumannOne (h : IsABPNeumannSolution G hG z) : NeumannOne G z :=
  hG.neumannOne (h.1.of_le (by exact_mod_cast (le_top : (1 : ℕ∞) ≤ ⊤))) h.2.2

end IsABPNeumannSolution

/-- Blueprint `prop:iso-smooth`: a bounded connected open set with smooth boundary satisfies
`Per(G)^3 ≥ 36π |G|^2`. The existence of the Neumann solution (`lem:abp-neumann`) enters as
the named hypothesis `ABPNeumannSolvable`. -/
theorem iso_smooth (hN : ABPNeumannSolvable) {G : Set AmbientSpace} (hGo : IsOpen G)
    (hGb : Bornology.IsBounded G) (hGc : IsConnected G) (hGs : HasSmoothBoundary G) :
    36 * Real.pi * volume.real G ^ 2 ≤ (perimeter G).toReal ^ 3 := by
  obtain ⟨z, hz⟩ := hN G hGo hGb hGc hGs
  exact iso_smooth_of_neumann_solution hGb hGo hGc.nonempty hz.contDiffOn_two
    hz.continuousOn hz.neumannOne hz.2.1

/-! ### The regularity actually consumed by the contact-set argument

`iso_smooth_of_neumann_solution` uses only interior C² regularity, C¹ regularity up to the
boundary (for `NeumannOne` and continuity on the closure), the interior equation, and the
classical conormal condition. The following weaker predicates record exactly this, so that
`prop:iso-smooth` needs only first-order boundary regularity of the weak solution. -/

/-- A C¹-up-to-the-boundary classical solution of the ABP Neumann problem: `z` is C² in `G`,
C¹ on `closure G`, `Δz = Per(G)/|G|` in `G`, and `∂_ν z = 1` on `∂G` (derivative within
`closure G`, classical outward normal). -/
def IsABPNeumannC1Solution (G : Set AmbientSpace) (hG : HasC1Boundary G)
    (z : AmbientSpace → ℝ) : Prop :=
  ContDiffOn ℝ 2 z G ∧ ContDiffOn ℝ 1 z (closure G) ∧
    (∀ x ∈ G, laplacianTrace z x = (perimeter G).toReal / volume.real G) ∧
    ∀ x ∈ frontier G, fderivWithin ℝ z (closure G) x (hG.outwardNormal x) = 1

lemma IsABPNeumannSolution.isABPNeumannC1Solution {G : Set AmbientSpace}
    {hG : HasC1Boundary G} {z : AmbientSpace → ℝ} (h : IsABPNeumannSolution G hG z) :
    IsABPNeumannC1Solution G hG z :=
  ⟨h.contDiffOn_two, h.1.of_le (by exact_mod_cast (le_top : (1 : ℕ∞) ≤ ⊤)), h.2.1, h.2.2⟩

/-- Existence of C¹-up-to-the-boundary ABP Neumann solutions; implied by
`ABPNeumannSolvable`. -/
def ABPNeumannC1Solvable : Prop :=
  ∀ G : Set AmbientSpace, IsOpen G → Bornology.IsBounded G → IsConnected G →
    ∀ hG : HasSmoothBoundary G, ∃ z : AmbientSpace → ℝ,
      IsABPNeumannC1Solution G hG.hasC1Boundary z

theorem ABPNeumannSolvable.c1Solvable (h : ABPNeumannSolvable) : ABPNeumannC1Solvable := by
  intro G hGo hGb hGc hGs
  obtain ⟨z, hz⟩ := h G hGo hGb hGc hGs
  exact ⟨z, hz.isABPNeumannC1Solution⟩

/-- First-order boundary regularity for every weak solution of the constant ABP data;
implied by `ABPNeumannBoundaryRegularity`. -/
def ABPNeumannBoundaryC1Regularity : Prop :=
  ∀ (G : Set AmbientSpace) (hGo : IsOpen G) (hGb : Bornology.IsBounded G)
    (_hGc : IsConnected G) (hGs : HasSmoothBoundary G) (z : H1Space G),
    IsWeakNeumannSolution hGo hGb hGs.hasC1Boundary.hasLipschitzBoundary
      (abpNeumannForcing G hGb) (abpNeumannFlux G hGo hGb hGs) z →
    ∃ v : AmbientSpace → ℝ, (⇑z =ᵐ[volume.restrict G] v) ∧
      IsABPNeumannC1Solution G hGs.hasC1Boundary v

theorem ABPNeumannBoundaryRegularity.c1 (h : ABPNeumannBoundaryRegularity) :
    ABPNeumannBoundaryC1Regularity := by
  intro G hGo hGb hGc hGs z hz
  obtain ⟨v, hv, hsol⟩ := h G hGo hGb hGc hGs z hz
  exact ⟨v, hv, hsol.isABPNeumannC1Solution⟩

theorem abpNeumannC1Solvable_of_boundaryC1Regularity
    (hR : ABPNeumannBoundaryC1Regularity) : ABPNeumannC1Solvable := by
  intro G hGo hGb hGc hGs
  obtain ⟨z, _, hz⟩ := exists_abpNeumann_weak_solution G hGo hGb hGc hGs
  obtain ⟨v, _, hv⟩ := hR G hGo hGb hGc hGs z hz
  exact ⟨v, hv⟩

/-- Blueprint `prop:iso-smooth` from C¹-up-to-the-boundary ABP Neumann solutions: the same
conclusion as `iso_smooth` under the weaker named hypothesis `ABPNeumannC1Solvable`. -/
theorem iso_smooth_of_c1Solvable (hN : ABPNeumannC1Solvable) {G : Set AmbientSpace}
    (hGo : IsOpen G) (hGb : Bornology.IsBounded G) (hGc : IsConnected G)
    (hGs : HasSmoothBoundary G) :
    36 * Real.pi * volume.real G ^ 2 ≤ (perimeter G).toReal ^ 3 := by
  obtain ⟨z, hz2, hz1, hlap, hν⟩ := hN G hGo hGb hGc hGs
  exact iso_smooth_of_neumann_solution hGb hGo hGc.nonempty hz2 hz1.continuousOn
    (hGs.hasC1Boundary.neumannOne hz1 hν) hlap

/-- `ABPNeumannBoundaryC1Regularity` from its two local ingredients, carried as named
hypotheses: interior C² regularity with the pointwise equation (`hint`), and C¹ regularity
with the classical conormal condition on a neighbourhood of each boundary point (`hbdry`).
The gluing (`neumann_glue_c1_closure`) and the unique differentiability of `closure G`
(`HasC1Boundary.uniqueDiffWithinAt_closure`) are proved. -/
theorem abpNeumannBoundaryC1Regularity_of_local
    (hint : ∀ (G : Set AmbientSpace) (hGo : IsOpen G) (hGb : Bornology.IsBounded G)
      (_hGc : IsConnected G) (hGs : HasSmoothBoundary G) (z : H1Space G),
      IsWeakNeumannSolution hGo hGb hGs.hasC1Boundary.hasLipschitzBoundary
        (abpNeumannForcing G hGb) (abpNeumannFlux G hGo hGb hGs) z →
      ∃ v₀ : AmbientSpace → ℝ, ContDiffOn ℝ 2 v₀ G ∧ (⇑z =ᵐ[volume.restrict G] v₀) ∧
        ∀ x ∈ G, laplacianTrace v₀ x = (perimeter G).toReal / volume.real G)
    (hbdry : ∀ (G : Set AmbientSpace) (hGo : IsOpen G) (hGb : Bornology.IsBounded G)
      (_hGc : IsConnected G) (hGs : HasSmoothBoundary G) (z : H1Space G),
      IsWeakNeumannSolution hGo hGb hGs.hasC1Boundary.hasLipschitzBoundary
        (abpNeumannForcing G hGb) (abpNeumannFlux G hGo hGb hGs) z →
      ∀ p ∈ frontier G, ∃ V : Set AmbientSpace, ∃ w : AmbientSpace → ℝ,
        IsOpen V ∧ p ∈ V ∧ ContDiffOn ℝ 1 w V ∧ (⇑z =ᵐ[volume.restrict (G ∩ V)] w) ∧
        ∀ x ∈ frontier G ∩ V, fderiv ℝ w x (hGs.hasC1Boundary.outwardNormal x) = 1) :
    ABPNeumannBoundaryC1Regularity := by
  intro G hGo hGb hGc hGs z hz
  obtain ⟨v₀, hv₀, hz₀, hlap⟩ := hint G hGo hGb hGc hGs z hz
  obtain ⟨v, hvG, hzv, hv2, hv1, hν⟩ := neumann_glue_c1_closure hGo hv₀ hz₀
    (hbdry G hGo hGb hGc hGs z hz)
    (fun x hx => hGs.hasC1Boundary.uniqueDiffWithinAt_closure hx)
  refine ⟨v, hzv, hv2, hv1, ?_, hν⟩
  intro x hx
  have he : v =ᶠ[𝓝 x] v₀ := Filter.eventually_of_mem (hGo.mem_nhds hx) (fun y hy => hvG hy)
  have hd : fderiv ℝ (fderiv ℝ v) x = fderiv ℝ (fderiv ℝ v₀) x := he.fderiv.fderiv_eq
  rw [← hlap x hx]
  simp only [laplacianTrace, hessianForm, hd]

/-- The interior ingredient `hint` of `abpNeumannBoundaryC1Regularity_of_local`, proved: every
weak solution of the constant ABP data has a smooth interior representative with
`Δ = Per(G)/|G|` pointwise. -/
theorem abpNeumann_interior_regularity (G : Set AmbientSpace) (hGo : IsOpen G)
    (hGb : Bornology.IsBounded G) (_hGc : IsConnected G) (hGs : HasSmoothBoundary G)
    (z : H1Space G)
    (hz : IsWeakNeumannSolution hGo hGb hGs.hasC1Boundary.hasLipschitzBoundary
      (abpNeumannForcing G hGb) (abpNeumannFlux G hGo hGb hGs) z) :
    ∃ v₀ : AmbientSpace → ℝ, ContDiffOn ℝ 2 v₀ G ∧ (⇑z =ᵐ[volume.restrict G] v₀) ∧
      ∀ x ∈ G, laplacianTrace v₀ x = (perimeter G).toReal / volume.real G := by
  obtain ⟨v, hv, hzv, hlap, _⟩ :=
    hz.exists_smooth_interior_representative (abpNeumannForcing_ae G hGb)
  exact ⟨v, (by simpa using contDiffOn_infty.mp hv 2 : ContDiffOn ℝ 2 v G), hzv, hlap⟩

/-- The remaining local boundary ingredient, as a named hypothesis: near every boundary point a
weak solution of the constant ABP data agrees a.e. with a C¹ function on an open neighbourhood
whose derivative along the classical outward normal is `1` on the boundary. -/
def ABPNeumannLocalBoundaryC1Regularity : Prop :=
  ∀ (G : Set AmbientSpace) (hGo : IsOpen G) (hGb : Bornology.IsBounded G)
    (_hGc : IsConnected G) (hGs : HasSmoothBoundary G) (z : H1Space G),
    IsWeakNeumannSolution hGo hGb hGs.hasC1Boundary.hasLipschitzBoundary
      (abpNeumannForcing G hGb) (abpNeumannFlux G hGo hGb hGs) z →
    ∀ p ∈ frontier G, ∃ V : Set AmbientSpace, ∃ w : AmbientSpace → ℝ,
      IsOpen V ∧ p ∈ V ∧ ContDiffOn ℝ 1 w V ∧ (⇑z =ᵐ[volume.restrict (G ∩ V)] w) ∧
      ∀ x ∈ frontier G ∩ V, fderiv ℝ w x (hGs.hasC1Boundary.outwardNormal x) = 1

/-- `ABPNeumannBoundaryC1Regularity` from the single local boundary hypothesis. -/
theorem abpNeumannBoundaryC1Regularity_of_localBoundary
    (hb : ABPNeumannLocalBoundaryC1Regularity) : ABPNeumannBoundaryC1Regularity :=
  abpNeumannBoundaryC1Regularity_of_local abpNeumann_interior_regularity hb

/-- Blueprint `prop:iso-smooth` with the only remaining analytic input the local boundary
C¹ regularity `ABPNeumannLocalBoundaryC1Regularity`. -/
theorem iso_smooth_of_localBoundary (hb : ABPNeumannLocalBoundaryC1Regularity)
    {G : Set AmbientSpace} (hGo : IsOpen G) (hGb : Bornology.IsBounded G)
    (hGc : IsConnected G) (hGs : HasSmoothBoundary G) :
    36 * Real.pi * volume.real G ^ 2 ≤ (perimeter G).toReal ^ 3 :=
  iso_smooth_of_c1Solvable
    (abpNeumannC1Solvable_of_boundaryC1Regularity
      (abpNeumannBoundaryC1Regularity_of_localBoundary hb)) hGo hGb hGc hGs

end LiquidDrop

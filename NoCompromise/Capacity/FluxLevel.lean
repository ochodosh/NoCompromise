module

public import NoCompromise.Capacity.FluxIdentity
public import NoCompromise.CapacitaryK.SlabGaussGreen

@[expose] public section

/-!
# Flux through regular levels of the capacitary potential

The truncated sublevel has the regular level and a large sphere as its two
boundary components. Its outward normal on the level is the normalized gradient.
-/

noncomputable section
open Set Filter Metric MeasureTheory InnerProductSpace
open scoped Topology Gradient RealInnerProductSpace
namespace LiquidDrop

/-- A positive closed superlevel of a continuous function vanishing at infinity
is compact. -/
lemma fluxLevel_isCompact_superlevel {u : AmbientSpace → ℝ} (hu : Continuous u)
    (hinf : Tendsto u (cocompact AmbientSpace) (𝓝 0)) {s : ℝ} (hs : 0 < s) :
    IsCompact (u ⁻¹' Ici s) := by
  obtain ⟨T, hT, hsub⟩ := Filter.mem_cocompact.mp (hinf.eventually (gt_mem_nhds hs))
  apply hT.of_isClosed_subset (isClosed_Ici.preimage hu)
  intro x hx
  by_contra hn
  exact (show u x < s from hsub hn).not_ge (show s ≤ u x from hx)

/-- At a regular value the entire level is the frontier of the strict sublevel. -/
lemma fluxLevel_frontier_sublevel {u : AmbientSpace → ℝ} (hu : Continuous u)
    {s : ℝ} (hreg : ∀ x, u x = s → gradient u x ≠ 0) :
    frontier (u ⁻¹' Iio s) = u ⁻¹' {s} := by
  have hopen : IsOpen (u ⁻¹' Iio s) := isOpen_Iio.preimage hu
  have hcl : closure (u ⁻¹' Iio s) ⊆ u ⁻¹' Iic s :=
    closure_minimal (by intro x hx; exact (show u x < s from hx).le)
      (isClosed_Iic.preimage hu)
  ext x
  rw [hopen.frontier_eq]
  constructor
  · rintro ⟨hxc, hxs⟩
    exact le_antisymm (hcl hxc) (le_of_not_gt hxs)
  · intro hx
    change u x = s at hx
    refine ⟨?_, by simp only [mem_preimage, mem_Iio, hx, lt_self_iff_false, not_false_eq_true]⟩
    by_contra hxc
    have hnear := isClosed_closure.isOpen_compl.mem_nhds hxc
    have hm : IsLocalMin u x := by
      filter_upwards [hnear] with y hy
      rw [hx]
      exact le_of_not_gt (fun h => hy (subset_closure h))
    apply hreg x hx
    simp only [gradient, hm.fderiv_eq_zero, map_zero]

/-- Only smoothness near the regular level is needed for its sublevel boundary. -/
lemma fluxLevel_sublevel_hasC1Boundary {U : Set AmbientSpace} (hU : IsOpen U)
    {u : AmbientSpace → ℝ} (hu : Continuous u) (hdu : ContDiffOn ℝ 1 u U)
    {s : ℝ} (hlevel : u ⁻¹' {s} ⊆ U)
    (hreg : ∀ x, u x = s → gradient u x ≠ 0) :
    HasC1Boundary (u ⁻¹' Iio s) := by
  apply hasC1Boundary_of_local_graphs
  intro x hx
  rw [fluxLevel_frontier_sublevel hu hreg] at hx
  have hxval : u x = s := hx
  have hr : gradient (fun z => -u z) x ≠ 0 := by
    rw [gradient, show (fun z => -u z) = -u from rfl, fderiv_neg, map_neg]
    exact neg_ne_zero.mpr (hreg x hxval)
  obtain ⟨e, f, B, W, hB, hf, hxB, hW, hxW, hgraph⟩ :=
    CapacitaryK.exists_c1_superlevel_graph hU hdu.neg (hlevel hx) hr
  refine ⟨e, f, B, W, hB, hf, hxB, hW, hxW, ?_⟩
  intro z hz
  simpa only [neg_lt_neg_iff, hxval, mem_preimage, mem_Iio] using hgraph z hz

/-- The frontier of a truncated sublevel is a disjoint sphere and level. -/
lemma fluxLevel_frontier_truncation {u : AmbientSpace → ℝ} (hu : Continuous u)
    (hinf : Tendsto u (cocompact AmbientSpace) (𝓝 0)) {s r : ℝ}
    (hs : 0 < s) (hr : 0 < r) (hAr : u ⁻¹' Ici s ⊆ ball 0 r)
    (hreg : ∀ x, u x = s → gradient u x ≠ 0) :
    frontier (ball (0 : AmbientSpace) r ∩ u ⁻¹' Iio s) =
      sphere 0 r ∪ u ⁻¹' {s} := by
  have heq : (u ⁻¹' Ici s)ᶜ = u ⁻¹' Iio s := by ext x; simp
  have hfront : frontier (u ⁻¹' Ici s) = u ⁻¹' {s} := by
    rw [← frontier_compl, heq, fluxLevel_frontier_sublevel hu hreg]
  simpa only [heq, hfront] using
    annulus_frontier (fluxLevel_isCompact_superlevel hu hinf hs) hr hAr

/-- Gluing ball charts and regular sublevel charts gives the truncation boundary. -/
lemma fluxLevel_truncation_hasC1Boundary {U : Set AmbientSpace} (hU : IsOpen U)
    {u : AmbientSpace → ℝ} (hu : Continuous u) (hdu : ContDiffOn ℝ 1 u U)
    (hinf : Tendsto u (cocompact AmbientSpace) (𝓝 0)) {s r : ℝ}
    (hs : 0 < s) (hr : 0 < r) (hAr : u ⁻¹' Ici s ⊆ ball 0 r)
    (hlevel : u ⁻¹' {s} ⊆ U)
    (hreg : ∀ x, u x = s → gradient u x ≠ 0) :
    HasC1Boundary (ball (0 : AmbientSpace) r ∩ u ⁻¹' Iio s) := by
  intro x hx
  rw [fluxLevel_frontier_truncation hu hinf hs hr hAr hreg] at hx
  rcases hx with hx | hx
  · have hxsub : x ∈ u ⁻¹' Iio s := by
      change u x < s
      apply lt_of_not_ge
      intro h
      exact (mem_ball.mp (hAr h)).ne (mem_sphere.mp hx)
    refine exists_c1BoundaryChart_of_local_eq (W := u ⁻¹' Iio s)
      (hasC1Boundary_ball 0 hr) (by rwa [frontier_ball (0 : AmbientSpace) hr.ne'])
      (isOpen_Iio.preimage hu) hxsub ?_
    intro y hy
    exact and_iff_left hy
  · refine exists_c1BoundaryChart_of_local_eq (W := ball 0 r)
      (fluxLevel_sublevel_hasC1Boundary hU hu hdu hlevel hreg)
      (by rwa [fluxLevel_frontier_sublevel hu hreg])
      isOpen_ball (hAr (le_of_eq (show s = u x from hx.symm))) ?_
    intro y hy
    exact and_iff_right hy

/-- On the outer sphere the truncation has the radial outward normal. -/
lemma fluxLevel_outwardNormal_sphere {u : AmbientSpace → ℝ} (hu : Continuous u)
    {s r : ℝ} (hr : 0 < r) (hAr : u ⁻¹' Ici s ⊆ ball 0 r)
    (hD : HasC1Boundary (ball (0 : AmbientSpace) r ∩ u ⁻¹' Iio s))
    {x : AmbientSpace} (hx : x ∈ sphere (0 : AmbientSpace) r)
    (hxD : x ∈ frontier (ball (0 : AmbientSpace) r ∩ u ⁻¹' Iio s)) :
    hD.outwardNormal x = r⁻¹ • x := by
  have hxB : x ∈ frontier (ball (0 : AmbientSpace) r) := by
    rwa [frontier_ball (0 : AmbientSpace) hr.ne']
  have hxsub : x ∈ u ⁻¹' Iio s := by
    change u x < s
    apply lt_of_not_ge
    intro h
    exact (mem_ball.mp (hAr h)).ne (mem_sphere.mp hx)
  obtain ⟨c, hc, hxc⟩ := hasC1Boundary_ball (0 : AmbientSpace) hr x hxB
  calc
    _ = (hasC1Boundary_ball (0 : AmbientSpace) hr).outwardNormal x :=
      capacity_outwardNormal_of_local_eq hD _ hxD hxB
        (isOpen_Iio.preimage hu) hxsub (fun _ hy => and_iff_left hy)
    _ = c.outwardNormal x := (hasC1Boundary_ball (0 : AmbientSpace) hr).outwardNormal_eq_chart
      hc hxB hxc
    _ = r⁻¹ • x := capacity_ball_chart_outwardNormal hr hc hx hxc

/-- On the level the outward normal of the sublevel points along the gradient. -/
lemma fluxLevel_outwardNormal_level {u : AmbientSpace → ℝ} {s r : ℝ}
    (hAr : u ⁻¹' Ici s ⊆ ball 0 r)
    (hD : HasC1Boundary (ball (0 : AmbientSpace) r ∩ u ⁻¹' Iio s))
    {x : AmbientSpace} (hx : u x = s) (hdu : DifferentiableAt ℝ u x)
    (hreg : gradient u x ≠ 0)
    (hxD : x ∈ frontier (ball (0 : AmbientSpace) r ∩ u ⁻¹' Iio s)) :
    hD.outwardNormal x = ‖gradient u x‖⁻¹ • gradient u x := by
  obtain ⟨c, hc, hxc⟩ := hD x hxD
  rw [hD.outwardNormal_eq_chart hc hxD hxc]
  apply CapacitaryK.chart_outwardNormal_eq_normalized_gradient c hc hxD hxc hdu hreg
  filter_upwards [isOpen_ball.mem_nhds (hAr (le_of_eq hx.symm))] with z hz
  simp only [mem_inter_iff, mem_preimage, mem_Iio, hz, true_and, hx]

/-- Gauss--Green on a truncated regular sublevel, with both boundary terms explicit. -/
lemma fluxLevel_truncation_gauss_green {U : Set AmbientSpace} (hU : IsOpen U)
    {u : AmbientSpace → ℝ} (hu : Continuous u) (hdu : ContDiffOn ℝ 1 u U)
    (hinf : Tendsto u (cocompact AmbientSpace) (𝓝 0)) {s r : ℝ}
    (hs : 0 < s) (hr : 0 < r) (hAr : u ⁻¹' Ici s ⊆ ball 0 r)
    (hlevel : u ⁻¹' {s} ⊆ U)
    (hreg : ∀ x, u x = s → gradient u x ≠ 0)
    {Z : AmbientSpace → AmbientSpace} (hZ : ContDiff ℝ 1 Z) :
    (∫ x in ball (0 : AmbientSpace) r ∩ u ⁻¹' Iio s, divergenceN Z x) =
      (∫ x in sphere (0 : AmbientSpace) r, inner ℝ (Z x) (r⁻¹ • x)
        ∂hausdorffMeasure2 3) +
      ∫ x in u ⁻¹' {s}, inner ℝ (Z x) (‖gradient u x‖⁻¹ • gradient u x)
        ∂hausdorffMeasure2 3 := by
  let hD := fluxLevel_truncation_hasC1Boundary hU hu hdu hinf hs hr hAr hlevel hreg
  have hopen : IsOpen (ball (0 : AmbientSpace) r ∩ u ⁻¹' Iio s) :=
    isOpen_ball.inter (isOpen_Iio.preimage hu)
  have hbdd : Bornology.IsBounded (ball (0 : AmbientSpace) r ∩ u ⁻¹' Iio s) :=
    isBounded_ball.subset inter_subset_left
  have hfront := fluxLevel_frontier_truncation hu hinf hs hr hAr hreg
  have hi := capacity_integrable_boundary_flux hopen hbdd hD hZ.continuous
  rw [hfront] at hi
  have hdis : Disjoint (sphere (0 : AmbientSpace) r) (u ⁻¹' {s}) := by
    apply disjoint_left.mpr
    intro x hx hxs
    exact (mem_ball.mp (hAr (le_of_eq (show s = u x from hxs.symm)))).ne
      (mem_sphere.mp hx)
  have hg := classical_gauss_green hopen hbdd hD hZ
  change (∫ x in ball (0 : AmbientSpace) r ∩ u ⁻¹' Iio s, divergenceN Z x) = _ at hg
  rw [hg, hfront, setIntegral_union hdis (isClosed_singleton.preimage hu).measurableSet
    (hi.mono_set subset_union_left) (hi.mono_set subset_union_right)]
  congr 1
  · apply setIntegral_congr_fun isClosed_sphere.measurableSet
    intro x hx
    dsimp only
    rw [fluxLevel_outwardNormal_sphere hu hr hAr hD hx (hfront.symm ▸ Or.inl hx)]
  · apply setIntegral_congr_fun (isClosed_singleton.preimage hu).measurableSet
    intro x hx
    dsimp only
    rw [fluxLevel_outwardNormal_level hAr hD hx
      ((hdu.differentiableOn one_ne_zero x (hlevel hx)).differentiableAt
        (hU.mem_nhds (hlevel hx)))
      (hreg x hx) (hfront.symm ▸ Or.inr hx)]

/-- A harmonic exterior potential has opposite fluxes on a regular level and
any sphere containing its closed superlevel. No boundary extension at the
original conductor is used. -/
theorem capacitary_sphere_flux_eq_neg_level {K : Set AmbientSpace} (hK : IsCompact K)
    {u : AmbientSpace → ℝ} (hu : Continuous u)
    (hh : HasDistributionalLaplacianOn u (fun _ => 0) Kᶜ)
    (hb : ∀ x ∈ K, u x = 1) (hinf : Tendsto u (cocompact AmbientSpace) (𝓝 0))
    {s r : ℝ} (hs : 0 < s) (hs1 : s < 1) (hr : 0 < r)
    (hAr : u ⁻¹' Ici s ⊆ ball 0 r)
    (hreg : ∀ x, u x = s → gradient u x ≠ 0) :
    (∫ x in sphere (0 : AmbientSpace) r,
      inner ℝ (gradient u x) (r⁻¹ • x) ∂hausdorffMeasure2 3) =
      -(∫ x in u ⁻¹' {s}, ‖gradient u x‖ ∂hausdorffMeasure2 3) := by
  let D := ball (0 : AmbientSpace) r ∩ u ⁻¹' Iio s
  have hopen : IsOpen D := isOpen_ball.inter (isOpen_Iio.preimage hu)
  have hbdd : Bornology.IsBounded D := isBounded_ball.subset inter_subset_left
  have hclsub : closure D ⊆ u ⁻¹' Iic s :=
    closure_minimal (by intro x hx; exact (show u x < s from hx.2).le)
      (isClosed_Iic.preimage hu)
  have hclK : closure D ⊆ Kᶜ := by
    intro x hx hxK
    have hle : u x ≤ s := hclsub hx
    rw [hb x hxK] at hle
    exact hs1.not_ge hle
  have hlevel : u ⁻¹' {s} ⊆ Kᶜ := by
    intro x hx hxK
    have hxval : u x = s := hx
    rw [hb x hxK] at hxval
    exact hs1.ne hxval.symm
  have hsmooth := capacitary_potential_contDiffOn hK hu hh
  have hdu : ContDiffOn ℝ 1 u Kᶜ := hsmooth.of_le (by simp)
  obtain ⟨g, hg, hgu⟩ := exists_global_contDiff_eq_near_compact hK.isClosed.isOpen_compl
    hbdd.isCompact_closure hclK hsmooth
  have hg2 : ContDiff ℝ 2 g := hg.of_le (by simp)
  have hΔ : ∀ x ∈ D, laplacianN g x = 0 := by
    have hgg := (hh.mono (subset_closure.trans hclK)).congr_ae
      (ae_restrict_of_forall_mem hopen.measurableSet
        (fun x hx => (hgu x (subset_closure hx)).self_of_nhds.symm))
      (Filter.EventuallyEq.refl _ _)
    exact hgg.laplacianN_eq_zero hopen hg2
  have hfront : frontier D = sphere 0 r ∪ u ⁻¹' {s} :=
    fluxLevel_frontier_truncation hu hinf hs hr hAr hreg
  have hgrad (x : AmbientSpace) (hx : x ∈ sphere (0 : AmbientSpace) r ∪ u ⁻¹' {s}) :
      gradient g x = gradient u x :=
    (hgu x (frontier_subset_closure (hfront.symm ▸ hx))).gradient_eq
  have hgg := fluxLevel_truncation_gauss_green hK.isClosed.isOpen_compl hu hdu hinf
    hs hr hAr hlevel hreg (contDiff_gradient_of_contDiff_succ hg2)
  have hz : (∫ x in D, divergenceN (gradient g) x) = 0 := by
    apply setIntegral_eq_zero_of_forall_eq_zero
    intro x hx
    rw [← laplacianN_eq_divergenceN_gradient hg2, hΔ x hx]
  have hout : (∫ x in sphere (0 : AmbientSpace) r,
      inner ℝ (gradient g x) (r⁻¹ • x) ∂hausdorffMeasure2 3) =
      ∫ x in sphere (0 : AmbientSpace) r,
        inner ℝ (gradient u x) (r⁻¹ • x) ∂hausdorffMeasure2 3 := by
    apply setIntegral_congr_fun isClosed_sphere.measurableSet
    intro x hx
    dsimp only
    rw [hgrad x (Or.inl hx)]
  have hin : (∫ x in u ⁻¹' {s},
      inner ℝ (gradient g x) (‖gradient u x‖⁻¹ • gradient u x) ∂hausdorffMeasure2 3) =
      ∫ x in u ⁻¹' {s}, ‖gradient u x‖ ∂hausdorffMeasure2 3 := by
    apply setIntegral_congr_fun (isClosed_singleton.preimage hu).measurableSet
    intro x hx
    dsimp only
    rw [hgrad x (Or.inr hx), real_inner_smul_right, real_inner_self_eq_norm_sq]
    have hn : ‖gradient u x‖ ≠ 0 := norm_ne_zero_iff.mpr (hreg x hx)
    field_simp
  change (∫ x in D, divergenceN (gradient g) x) = _ at hgg
  rw [hz, hout, hin] at hgg
  linarith

/-- The gradient expansion identifies the flux of each regular level by letting
the truncation radius tend to infinity. -/
theorem capacitary_flux_level_of_gradient_expansion {K : Set AmbientSpace}
    (hK : IsCompact K) {u : AmbientSpace → ℝ} (hu : Continuous u)
    (hh : HasDistributionalLaplacianOn u (fun _ => 0) Kᶜ)
    (hb : ∀ x ∈ K, u x = 1) (hinf : Tendsto u (cocompact AmbientSpace) (𝓝 0))
    {Cinf R C' : ℝ} (hR : 0 < R)
    (hexp : ∀ x : AmbientSpace, R ≤ ‖x‖ →
      ‖gradient u x + (Cinf / ‖x‖ ^ 3) • x‖ ≤ C' / ‖x‖ ^ 3)
    {s : ℝ} (hs : 0 < s) (hs1 : s < 1)
    (hreg : ∀ x, u x = s → gradient u x ≠ 0) :
    (∫ x in u ⁻¹' {s}, ‖gradient u x‖ ∂hausdorffMeasure2 3) =
      4 * Real.pi * Cinf := by
  obtain ⟨S, _, hAS⟩ := (fluxLevel_isCompact_superlevel hu hinf hs).isBounded.subset_ball_lt
    0 (0 : AmbientSpace)
  have hbound : ∀ᶠ r : ℝ in atTop,
      |-(∫ x in u ⁻¹' {s}, ‖gradient u x‖ ∂hausdorffMeasure2 3) + 4 * Real.pi * Cinf| ≤
        4 * Real.pi * C' / r := by
    filter_upwards [eventually_ge_atTop (max R S)] with r hr
    have hrR := (le_max_left R S).trans hr
    have hAr := hAS.trans (ball_subset_ball ((le_max_right R S).trans hr))
    have hf := sphere_flux_of_gradient_expansion hR hexp hrR
    rwa [capacitary_sphere_flux_eq_neg_level hK hu hh hb hinf hs hs1
      (hR.trans_le hrR) hAr hreg] at hf
  have hz :
      |-(∫ x in u ⁻¹' {s}, ‖gradient u x‖ ∂hausdorffMeasure2 3) + 4 * Real.pi * Cinf| ≤ 0 :=
    ge_of_tendsto (tendsto_const_nhds.div_atTop tendsto_id) hbound
  have he := abs_eq_zero.mp (le_antisymm hz (abs_nonneg _))
  linarith

/-- Blueprint `lem:flux-identity`, Kelvin-coefficient form of `eq:flux-level`.
This statement requires no regularity of the conductor boundary. -/
theorem capacitary_flux_level_kelvin {K : Set AmbientSpace} (hK : IsCompact K)
    {R₀ : ℝ} (hR₀ : 0 < R₀) (hKR : K ⊆ closedBall 0 R₀)
    (hzero : (0 : AmbientSpace) ∈ interior K)
    {u : AmbientSpace → ℝ} (hu : Continuous u)
    (hh : HasDistributionalLaplacianOn u (fun _ => 0) Kᶜ)
    (hb : ∀ x ∈ K, u x = 1) (hinf : Tendsto u (cocompact AmbientSpace) (𝓝 0)) :
    ∃ Cinf R C' : ℝ, 0 < R ∧
      (∀ x : AmbientSpace, R ≤ ‖x‖ →
        |u x - Cinf / ‖x‖| ≤ C' / ‖x‖ ^ 2 ∧
        ‖gradient u x + (Cinf / ‖x‖ ^ 3) • x‖ ≤ C' / ‖x‖ ^ 3) ∧
      ∀ s : ℝ, 0 < s → s < 1 → (∀ x, u x = s → gradient u x ≠ 0) →
        (∫ x in u ⁻¹' {s}, ‖gradient u x‖ ∂hausdorffMeasure2 3) = 4 * Real.pi * Cinf := by
  obtain ⟨Cinf, R, C', hR, hexp⟩ := kelvin_expansion hK hR₀ hKR hzero hu hh hb hinf
  refine ⟨Cinf, R, C', hR, hexp, ?_⟩
  intro s hs hs1 hreg
  exact capacitary_flux_level_of_gradient_expansion hK hu hh hb hinf hR
    (fun x hx => (hexp x hx).2) hs hs1 hreg

/-- Blueprint `lem:flux-identity` (`eq:flux-level`), under the named C² boundary
extension hypothesis used to identify the Kelvin coefficient with capacity. -/
theorem capacitary_flux_level {K : Set AmbientSpace} (hK : IsCompact K)
    (hreg : K = closure (interior K)) (hC1 : HasC1Boundary (interior K))
    {R₀ : ℝ} (hR₀ : 0 < R₀) (hKR : K ⊆ closedBall 0 R₀)
    (hzero : (0 : AmbientSpace) ∈ interior K)
    {u : AmbientSpace → ℝ} (hu : Continuous u)
    (hh : HasDistributionalLaplacianOn u (fun _ => 0) Kᶜ)
    (hb : ∀ x ∈ K, u x = 1) (hinf : Tendsto u (cocompact AmbientSpace) (𝓝 0))
    {g : AmbientSpace → ℝ} (hg : ContDiff ℝ 2 g) (hug : EqOn u g (closure Kᶜ)) :
    ∀ s : ℝ, 0 < s → s < 1 → (∀ x, u x = s → gradient u x ≠ 0) →
      (∫ x in u ⁻¹' {s}, ‖gradient u x‖ ∂hausdorffMeasure2 3) = 4 * Real.pi * capacityOf K u := by
  obtain ⟨R, C', hR, hexp⟩ :=
    kelvin_constant_eq_capacity hK hreg hC1 hR₀ hKR hzero hu hh hb hinf hg hug
  intro s hs hs1 hregular
  exact capacitary_flux_level_of_gradient_expansion hK hu hh hb hinf hR
    (fun x hx => (hexp x hx).2) hs hs1 hregular

end LiquidDrop

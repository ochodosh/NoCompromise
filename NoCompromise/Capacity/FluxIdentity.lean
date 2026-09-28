import NoCompromise.Capacity.SphereFlux
import NoCompromise.Capacity.KelvinLevels
import NoCompromise.Elliptic.ClassicalCalculus
import NoCompromise.Elliptic.ClassicalNormal
import NoCompromise.Sobolev.AnnulusDomain
import NoCompromise.BV.ExteriorGeometry

/-!
# Capacity, boundary flux, and the Kelvin coefficient

Blueprint `def:capacity`, the boundary identity of `lem:flux-identity`, and
`C∞ = capacity` in `lem:kelvin`. Boundary regularity is represented explicitly
by `hg : ContDiff ℝ 2 g` and `hug : EqOn u g (closure Kᶜ)`.

The annulus geometry fixes both normal orientations. Gauss–Green gives the
energy identity on bounded truncations, and the decay bounds make the outer
energy flux vanish. An exhaustion proves exterior integrability and the exact
boundary identity. The constant sphere flux then identifies the Kelvin coefficient.
-/

noncomputable section
open MeasureTheory Set Filter Metric Topology InnerProductSpace
open scoped ENNReal NNReal Gradient
namespace LiquidDrop

/-- Blueprint `def:capacity` (`eq:capacity`):
`Cap(K) = (4π)⁻¹ ∫_{ℝ³∖K} |∇u|²`, for the potential `u`. -/
def capacityOf (K : Set AmbientSpace) (u : AmbientSpace → ℝ) : ℝ :=
  (4 * Real.pi)⁻¹ * ∫ x in Kᶜ, ‖gradient u x‖ ^ 2

/-- A regular closed compact set and its interior have the same frontier. -/
lemma capacity_frontier_interior {K : Set AmbientSpace} (hK : IsCompact K)
    (hreg : K = closure (interior K)) : frontier (interior K) = frontier K := by
  rw [frontier, interior_interior, ← hreg, hK.isClosed.frontier_eq]

/-- The two boundary components of an exterior truncation are disjoint. -/
lemma annulus_boundary_disjoint {K : Set AmbientSpace} (hK : IsCompact K)
    {r : ℝ} (hKr : K ⊆ ball 0 r) : Disjoint (sphere (0 : AmbientSpace) r) (frontier K) := by
  apply Set.disjoint_left.mpr
  intro x hx hxK
  have hlt := hKr (hK.isClosed.frontier_subset hxK)
  exact (mem_ball.mp hlt).ne (mem_sphere.mp hx)

/-- The boundary of the truncated exterior consists precisely of its two pieces. -/
lemma annulus_frontier {K : Set AmbientSpace} (hK : IsCompact K)
    {r : ℝ} (hr : 0 < r) (hKr : K ⊆ ball 0 r) :
    frontier (ball (0 : AmbientSpace) r ∩ Kᶜ) = sphere 0 r ∪ frontier K := by
  apply Subset.antisymm
  · intro x hx
    rcases frontier_inter_subset _ _ hx with h | h
    · exact Or.inl (by simpa only [frontier_ball (0 : AmbientSpace) hr.ne'] using h.1)
    · exact Or.inr (by simpa only [frontier_compl] using h.2)
  · intro x hx
    rw [(isOpen_ball.inter hK.isClosed.isOpen_compl).frontier_eq]
    rcases hx with hx | hx
    · have hxs : x ∈ frontier (ball (0 : AmbientSpace) r) := by
        simpa only [frontier_ball (0 : AmbientSpace) hr.ne'] using hx
      have hxK : x ∈ Kᶜ := by
        intro hxK
        exact (mem_ball.mp (hKr hxK)).ne (mem_sphere.mp hx)
      exact ⟨hK.isClosed.isOpen_compl.closure_inter ⟨frontier_subset_closure hxs, hxK⟩,
        fun h => (mem_ball.mp h.1).ne (mem_sphere.mp hx)⟩
    · have hxb := hKr (hK.isClosed.frontier_subset hx)
      have hxc : x ∈ closure Kᶜ := frontier_subset_closure (by simpa using hx)
      exact ⟨isOpen_ball.inter_closure ⟨hxb, hxc⟩,
        fun h => h.2 (hK.isClosed.frontier_subset hx)⟩

/-- A ball with a compact regular C¹ obstacle removed has C¹ boundary. -/
theorem annulus_hasC1Boundary {K : Set AmbientSpace} (hK : IsCompact K)
    (hreg : K = closure (interior K)) (hC1 : HasC1Boundary (interior K))
    {r : ℝ} (hr : 0 < r) (hKr : K ⊆ ball 0 r) :
    HasC1Boundary (ball (0 : AmbientSpace) r ∩ Kᶜ) := by
  have hext : HasC1Boundary Kᶜ := by rw [hreg]; exact hC1.exterior
  intro x hx
  rw [annulus_frontier hK hr hKr] at hx
  rcases hx with hx | hx
  · have hxK : x ∈ Kᶜ := by
      intro hxK
      exact (mem_ball.mp (hKr hxK)).ne (mem_sphere.mp hx)
    refine exists_c1BoundaryChart_of_local_eq (W := Kᶜ)
      (hasC1Boundary_ball 0 hr) (by simpa only [frontier_ball (0 : AmbientSpace) hr.ne'] using hx)
      hK.isClosed.isOpen_compl hxK ?_
    intro y hy
    exact and_iff_left hy
  · refine exists_c1BoundaryChart_of_local_eq (W := ball 0 r)
      hext (by simpa only [frontier_compl] using hx)
      isOpen_ball (hKr (hK.isClosed.frontier_subset hx)) ?_
    intro y hy
    exact and_iff_right hy

/-- Local equality of domains preserves the chosen classical normal. -/
lemma capacity_outwardNormal_of_local_eq {D E W : Set AmbientSpace}
    (hD : HasC1Boundary D) (hE : HasC1Boundary E) {x : AmbientSpace}
    (hxD : x ∈ frontier D) (hxE : x ∈ frontier E)
    (hW : IsOpen W) (hxW : x ∈ W)
    (heq : ∀ y ∈ W, y ∈ D ↔ y ∈ E) :
    hD.outwardNormal x = hE.outwardNormal x := by
  obtain ⟨c, hc, hxc⟩ := hE x hxE
  let d : C1BoundaryChart := ⟨c.height, c.height_contDiff, c.placement,
    c.region ∩ W, c.isOpen_region.inter hW, c.bounded_region.subset inter_subset_left⟩
  have hd : d.IsChartFor D := fun y hy => (heq y hy.2).trans (hc y hy.1)
  rw [hD.outwardNormal_eq_chart hd hxD ⟨hxc, hxW⟩,
    hE.outwardNormal_eq_chart hc hxE hxc]
  rfl

/-- At the obstacle, the exterior normal is the negative of its interior normal. -/
lemma annulus_outwardNormal_inner {K : Set AmbientSpace} (hK : IsCompact K)
    (hreg : K = closure (interior K)) (hC1 : HasC1Boundary (interior K))
    {r : ℝ} (hr : 0 < r) (hKr : K ⊆ ball 0 r) {x : AmbientSpace}
    (hx : x ∈ frontier K) :
    (annulus_hasC1Boundary hK hreg hC1 hr hKr).outwardNormal x = -hC1.outwardNormal x := by
  have hext : HasC1Boundary Kᶜ := by rw [hreg]; exact hC1.exterior
  have hxi : x ∈ frontier (interior K) := by rwa [capacity_frontier_interior hK hreg]
  obtain ⟨c, hc, hxc⟩ := hC1 x hxi
  have hcE : c.exteriorChart.IsChartFor Kᶜ := by rw [hreg]; exact hc.exterior
  calc
    _ = hext.outwardNormal x := capacity_outwardNormal_of_local_eq
      (annulus_hasC1Boundary hK hreg hC1 hr hKr) hext
      (by rw [annulus_frontier hK hr hKr]; exact Or.inr hx)
      (by simpa using hx) isOpen_ball (hKr (hK.isClosed.frontier_subset hx))
      (fun _ hy => and_iff_right hy)
    _ = c.exteriorChart.outwardNormal x := hext.outwardNormal_eq_chart hcE
      (by simpa using hx) hxc
    _ = -c.outwardNormal x := c.exteriorChart_outwardNormal x
    _ = -hC1.outwardNormal x := by rw [hC1.outwardNormal_eq_chart hc hxi hxc]

/-- The normal selected by any ball chart is the outward radial unit vector. -/
lemma capacity_ball_chart_outwardNormal {c : C1BoundaryChart} {r : ℝ}
    (hr : 0 < r) (hc : c.IsChartFor (ball (0 : AmbientSpace) r))
    {x : AmbientSpace} (hx : x ∈ sphere (0 : AmbientSpace) r) (hxc : x ∈ c.region) :
    c.outwardNormal x = r⁻¹ • x := by
  have hxn : ‖x‖ = r := by simpa using hx
  have hn : ‖r⁻¹ • x‖ = 1 := by
    rw [norm_smul, Real.norm_of_nonneg (inv_nonneg.mpr hr.le), hxn, inv_mul_cancel₀ hr.ne']
  by_contra hne
  let v := c.outwardNormal x - r⁻¹ • x
  have hi : inner ℝ (c.outwardNormal x) (r⁻¹ • x) < 1 := by
    have hp := sq_pos_of_pos (norm_pos_iff.mpr (sub_ne_zero.mpr hne))
    rw [norm_sub_sq_real, c.norm_outwardNormal, hn] at hp
    nlinarith
  have hcpos : 0 < inner ℝ v (c.outwardNormal x) := by
    simp only [v, inner_sub_left, real_inner_self_eq_norm_sq, c.norm_outwardNormal]
    rw [real_inner_comm]
    nlinarith
  have hrneg : inner ℝ v (r⁻¹ • x) < 0 := by
    simp only [v, inner_sub_left, real_inner_self_eq_norm_sq, hn]
    nlinarith
  have hxneg : inner ℝ x v < 0 := by
    rw [inner_smul_right, real_inner_comm] at hrneg
    exact neg_of_mul_neg_right hrneg (inv_nonneg.mpr hr.le)
  have hpc := classicalNormal_eventually_pos_of_hasDerivAt
    (c.hasDerivAt_definingFunction_line x v)
    (by simpa using (hc.definingFunction_eq_zero
      (show x ∈ frontier (ball (0 : AmbientSpace) r) by
        rwa [frontier_ball (0 : AmbientSpace) hr.ne']) hxc))
    (mul_pos (Real.sqrt_pos.mpr (by positivity)) hcpos)
  have hline : HasDerivAt (fun t : ℝ => x + t • v) v 0 := by
    simpa using ((hasDerivAt_id (0 : ℝ)).smul_const v).const_add x
  have hd : HasDerivAt (fun t : ℝ => ‖x + t • v‖ ^ 2 - r ^ 2)
      (2 * inner ℝ x v) 0 := by
    simpa only [real_inner_self_eq_norm_sq, zero_smul, add_zero, real_inner_comm, two_mul]
      using (HasDerivAt.inner ℝ hline hline).sub_const (r ^ 2)
  have hpd := classicalNormal_eventually_neg_of_hasDerivAt hd
    (by simp [hxn]) (mul_neg_of_pos_of_neg (by norm_num) hxneg)
  have ht : Tendsto (fun t : ℝ => x + t • v) (𝓝[>] 0) (𝓝 x) := by
    have hh : Continuous (fun t : ℝ => x + t • v) := by fun_prop
    simpa using (hh.continuousAt (x := (0 : ℝ))).tendsto.mono_left nhdsWithin_le_nhds
  obtain ⟨t, htc, htd, htr⟩ :=
    (hpc.and (hpd.and (ht (c.isOpen_region.mem_nhds hxc)))).exists
  have hm : x + t • v ∈ ball (0 : AmbientSpace) r := by
    rw [mem_ball, dist_zero_right]
    nlinarith [norm_nonneg (x + t • v)]
  exact (not_lt_of_gt htc) ((hc.mem_iff_definingFunction_neg htr).mp hm)

/-- At the outer sphere, the annulus normal points radially outward. -/
lemma annulus_outwardNormal_outer {K : Set AmbientSpace} (hK : IsCompact K)
    (hreg : K = closure (interior K)) (hC1 : HasC1Boundary (interior K))
    {r : ℝ} (hr : 0 < r) (hKr : K ⊆ ball 0 r) {x : AmbientSpace}
    (hx : x ∈ sphere (0 : AmbientSpace) r) :
    (annulus_hasC1Boundary hK hreg hC1 hr hKr).outwardNormal x = r⁻¹ • x := by
  have hxB : x ∈ frontier (ball (0 : AmbientSpace) r) := by
    rwa [frontier_ball (0 : AmbientSpace) hr.ne']
  have hxK : x ∈ Kᶜ := by
    intro hxK
    exact (mem_ball.mp (hKr hxK)).ne (mem_sphere.mp hx)
  obtain ⟨c, hc, hxc⟩ := hasC1Boundary_ball (0 : AmbientSpace) hr x hxB
  calc
    _ = (hasC1Boundary_ball (0 : AmbientSpace) hr).outwardNormal x :=
      capacity_outwardNormal_of_local_eq (annulus_hasC1Boundary hK hreg hC1 hr hKr) _
        (by rw [annulus_frontier hK hr hKr]; exact Or.inl hx) hxB
        hK.isClosed.isOpen_compl hxK (fun _ hy => and_iff_left hy)
    _ = c.outwardNormal x := (hasC1Boundary_ball (0 : AmbientSpace) hr).outwardNormal_eq_chart
      hc hxB hxc
    _ = r⁻¹ • x := capacity_ball_chart_outwardNormal hr hc hx hxc

/-- A bounded C¹ domain has finite classical boundary area. -/
lemma capacity_boundary_measure_lt_top {D : Set AmbientSpace} (hD : IsOpen D)
    (hbD : Bornology.IsBounded D) (hC1 : HasC1Boundary D) :
    hausdorffMeasure2 3 (frontier D) < ⊤ := by
  obtain ⟨ζ, hζ, hcζ, _, hone, _⟩ := exists_smooth_cutoff_one_near_compact
    hbD.isCompact_closure isOpen_univ (subset_univ _)
  obtain ⟨_, _, htrace⟩ := exists_global_w11_boundary_restriction_bound hD hbD
    hC1.hasLipschitzBoundary
  have hi : IntegrableOn ζ (frontier D) (hausdorffMeasure2 3) :=
    memLp_one_iff_integrable.mp (htrace ζ (gradient ζ)
      (hasW11GradientOn_of_contDiff_compact (hζ.of_le (by simp)) hcζ) hζ.continuous).1
  have h1 : IntegrableOn (fun _ : AmbientSpace => (1 : ℝ)) (frontier D)
      (hausdorffMeasure2 3) := hi.congr (by
    filter_upwards [ae_restrict_mem isClosed_frontier.measurableSet] with x hx
    exact (hone.filter_mono (nhds_le_nhdsSet (frontier_subset_closure hx))).self_of_nhds)
  have : IsFiniteMeasure ((hausdorffMeasure2 3).restrict (frontier D)) :=
    (integrable_const_iff_isFiniteMeasure (one_ne_zero : (1 : ℝ) ≠ 0)).mp h1
  simpa only [Measure.restrict_apply_univ] using
    (measure_lt_top ((hausdorffMeasure2 3).restrict (frontier D)) univ)

/-- Continuous classical vector fields have integrable boundary flux. -/
lemma capacity_integrable_boundary_flux {D : Set AmbientSpace} (hD : IsOpen D)
    (hbD : Bornology.IsBounded D) (hC1 : HasC1Boundary D)
    {Z : AmbientSpace → AmbientSpace} (hZ : Continuous Z) :
    IntegrableOn (fun x => inner ℝ (Z x) (hC1.outwardNormal x)) (frontier D)
      (hausdorffMeasure2 3) :=
  (hZ.continuousOn.inner hC1.continuousOn_outwardNormal).integrableOn_of_subset_isCompact
    (hbD.isCompact_closure.of_isClosed_subset isClosed_frontier frontier_subset_closure)
    isClosed_frontier.measurableSet Subset.rfl (capacity_boundary_measure_lt_top hD hbD hC1).ne

/-- Gauss–Green on the exterior truncation, with its two oriented components. -/
lemma capacity_annulus_gauss_green {K : Set AmbientSpace} (hK : IsCompact K)
    (hreg : K = closure (interior K)) (hC1 : HasC1Boundary (interior K))
    {r : ℝ} (hr : 0 < r) (hKr : K ⊆ ball 0 r)
    {Z : AmbientSpace → AmbientSpace} (hZ : ContDiff ℝ 1 Z) :
    (∫ x in ball (0 : AmbientSpace) r ∩ Kᶜ, divergenceN Z x) =
      (∫ x in sphere (0 : AmbientSpace) r, inner ℝ (Z x) (r⁻¹ • x) ∂hausdorffMeasure2 3) -
      ∫ x in frontier K, inner ℝ (Z x) (hC1.outwardNormal x) ∂hausdorffMeasure2 3 := by
  let hA := annulus_hasC1Boundary hK hreg hC1 hr hKr
  have ho : IsOpen (ball (0 : AmbientSpace) r ∩ Kᶜ) :=
    isOpen_ball.inter hK.isClosed.isOpen_compl
  have hbA : Bornology.IsBounded (ball (0 : AmbientSpace) r ∩ Kᶜ) :=
    isBounded_ball.subset inter_subset_left
  have hi := capacity_integrable_boundary_flux ho hbA hA hZ.continuous
  rw [annulus_frontier hK hr hKr] at hi
  have hg := classical_gauss_green ho hbA hA hZ
  change (∫ x in ball (0 : AmbientSpace) r ∩ Kᶜ, divergenceN Z x) = _ at hg
  rw [hg, annulus_frontier hK hr hKr,
    setIntegral_union (annulus_boundary_disjoint hK hKr) isClosed_frontier.measurableSet
      (hi.mono_set subset_union_left) (hi.mono_set subset_union_right)]
  have hout : (∫ x in sphere (0 : AmbientSpace) r,
      inner ℝ (Z x) (hA.outwardNormal x) ∂hausdorffMeasure2 3) =
      ∫ x in sphere (0 : AmbientSpace) r, inner ℝ (Z x) (r⁻¹ • x) ∂hausdorffMeasure2 3 :=
    setIntegral_congr_fun isClosed_sphere.measurableSet fun x hx => by
      rw [show hA.outwardNormal x = r⁻¹ • x from annulus_outwardNormal_outer hK hreg hC1 hr hKr hx]
  have hin : (∫ x in frontier K,
      inner ℝ (Z x) (hA.outwardNormal x) ∂hausdorffMeasure2 3) =
      -(∫ x in frontier K, inner ℝ (Z x) (hC1.outwardNormal x) ∂hausdorffMeasure2 3) := by
    rw [← integral_neg]
    apply setIntegral_congr_fun isClosed_frontier.measurableSet
    intro x hx
    dsimp only
    rw [show hA.outwardNormal x = -hC1.outwardNormal x from
      annulus_outwardNormal_inner hK hreg hC1 hr hKr hx, inner_neg_right]
  rw [hout, hin, sub_eq_add_neg]

/-- A harmonic C² function has the same outward flux on a surrounding sphere
and on the boundary of the obstacle. -/
theorem sphere_flux_eq_boundary_flux {K : Set AmbientSpace} (hK : IsCompact K)
    (hreg : K = closure (interior K)) (hC1 : HasC1Boundary (interior K))
    {g : AmbientSpace → ℝ} (hg : ContDiff ℝ 2 g)
    (hΔ : ∀ x ∈ Kᶜ, laplacianN g x = 0)
    {r : ℝ} (hr : 0 < r) (hKr : K ⊆ ball 0 r) :
    (∫ x in sphere (0 : AmbientSpace) r,
      inner ℝ (gradient g x) (r⁻¹ • x) ∂hausdorffMeasure2 3) =
      ∫ x in frontier K, inner ℝ (gradient g x) (hC1.outwardNormal x) ∂hausdorffMeasure2 3 := by
  have h := capacity_annulus_gauss_green hK hreg hC1 hr hKr
    (contDiff_gradient_of_contDiff_succ hg)
  have hz : (∫ x in ball (0 : AmbientSpace) r ∩ Kᶜ, divergenceN (gradient g) x) = 0 := by
    apply setIntegral_eq_zero_of_forall_eq_zero
    intro x hx
    rw [← laplacianN_eq_divergenceN_gradient hg, hΔ x hx.2]
  rw [hz] at h
  exact sub_eq_zero.mp h.symm

/-- Integration by parts before the truncation radius tends to infinity. -/
lemma capacity_annulus_energy {K : Set AmbientSpace} (hK : IsCompact K)
    (hreg : K = closure (interior K)) (hC1 : HasC1Boundary (interior K))
    {g : AmbientSpace → ℝ} (hg : ContDiff ℝ 2 g)
    (hΔ : ∀ x ∈ Kᶜ, laplacianN g x = 0) (hb : ∀ x ∈ frontier K, g x = 1)
    {r : ℝ} (hr : 0 < r) (hKr : K ⊆ ball 0 r) :
    (∫ x in ball (0 : AmbientSpace) r ∩ Kᶜ, ‖gradient g x‖ ^ 2) =
      (∫ x in sphere (0 : AmbientSpace) r,
        g x * inner ℝ (gradient g x) (r⁻¹ • x) ∂hausdorffMeasure2 3) -
      ∫ x in frontier K, inner ℝ (gradient g x) (hC1.outwardNormal x) ∂hausdorffMeasure2 3 := by
  have hg1 : ContDiff ℝ 1 g := hg.of_le (by norm_num)
  have hgrad : ContDiff ℝ 1 (gradient g) := contDiff_gradient_of_contDiff_succ hg
  have h := capacity_annulus_gauss_green hK hreg hC1 hr hKr
    (Z := fun y => g y • gradient g y) (hg1.smul hgrad)
  have hdiv : (∫ x in ball (0 : AmbientSpace) r ∩ Kᶜ,
      divergenceN (fun y => g y • gradient g y) x) =
      ∫ x in ball (0 : AmbientSpace) r ∩ Kᶜ, ‖gradient g x‖ ^ 2 := by
    apply setIntegral_congr_fun (isOpen_ball.inter hK.isClosed.isOpen_compl).measurableSet
    intro x hx
    rw [divergenceN_smul hg1 hgrad, ← laplacianN_eq_divergenceN_gradient hg,
      hΔ x hx.2, mul_zero, zero_add, real_inner_self_eq_norm_sq]
  rw [hdiv] at h
  simp only [real_inner_smul_left] at h
  rw [h]
  congr 1
  apply setIntegral_congr_fun isClosed_frontier.measurableSet
  intro x hx
  dsimp only
  rw [hb x hx, one_mul]

/-- The energy flux at infinity is bounded by `4π C²/r`. -/
lemma capacity_sphere_energy_bound {g : AmbientSpace → ℝ} {C R : ℝ}
    (hR : 0 < R)
    (hdecay : ∀ x : AmbientSpace, R ≤ ‖x‖ →
      |g x| ≤ C / ‖x‖ ∧ ‖gradient g x‖ ≤ C / ‖x‖ ^ 2)
    {r : ℝ} (hr : R ≤ r) :
    ‖∫ x in sphere (0 : AmbientSpace) r,
      g x * inner ℝ (gradient g x) (r⁻¹ • x) ∂hausdorffMeasure2 3‖ ≤
        4 * Real.pi * C ^ 2 / r := by
  have hr0 := hR.trans_le hr
  have harea := hausdorffMeasure2_sphere (0 : AmbientSpace) hr0
  have hbound : ∀ x ∈ sphere (0 : AmbientSpace) r,
      ‖g x * inner ℝ (gradient g x) (r⁻¹ • x)‖ ≤ C ^ 2 / r ^ 3 := by
    intro x hx
    have hxn : ‖x‖ = r := by simpa using hx
    obtain ⟨hv, hd⟩ := hdecay x (by rwa [hxn])
    rw [hxn] at hv hd
    have hn : ‖r⁻¹ • x‖ = 1 := by
      rw [norm_smul, Real.norm_of_nonneg (inv_nonneg.mpr hr0.le), hxn,
        inv_mul_cancel₀ hr0.ne']
    calc
      _ ≤ |g x| * (‖gradient g x‖ * ‖r⁻¹ • x‖) := by
        rw [norm_mul, Real.norm_eq_abs (g x)]
        exact mul_le_mul_of_nonneg_left (norm_inner_le_norm _ _) (abs_nonneg _)
      _ = |g x| * ‖gradient g x‖ := by rw [hn, mul_one]
      _ ≤ (C / r) * (C / r ^ 2) :=
        mul_le_mul hv hd (norm_nonneg _) ((abs_nonneg _).trans hv)
      _ = C ^ 2 / r ^ 3 := by ring
  have h := norm_setIntegral_le_of_norm_le_const
    (by rw [harea]; exact ENNReal.ofReal_lt_top) hbound
  rw [measureReal_def, harea, ENNReal.toReal_ofReal (by positivity)] at h
  calc
    _ ≤ C ^ 2 / r ^ 3 * (4 * Real.pi * r ^ 2) := h
    _ = 4 * Real.pi * C ^ 2 / r := by field_simp

/-- Finite exterior energy and its exact boundary-flux identity. The only
regularity assumption here is the stated global C² regularity of `g`. -/
theorem energy_eq_neg_boundary_flux {K : Set AmbientSpace} (hK : IsCompact K)
    (hreg : K = closure (interior K)) (hC1 : HasC1Boundary (interior K))
    {g : AmbientSpace → ℝ} (hg : ContDiff ℝ 2 g)
    (hΔ : ∀ x ∈ Kᶜ, laplacianN g x = 0) (hb : ∀ x ∈ frontier K, g x = 1)
    (hdecay : ∃ C R : ℝ, 0 < R ∧ ∀ x : AmbientSpace, R ≤ ‖x‖ →
      |g x| ≤ C / ‖x‖ ∧ ‖gradient g x‖ ≤ C / ‖x‖ ^ 2) :
    IntegrableOn (fun x => ‖gradient g x‖ ^ 2) Kᶜ ∧
      (∫ x in Kᶜ, ‖gradient g x‖ ^ 2) =
        -∫ x in frontier K, inner ℝ (gradient g x) (hC1.outwardNormal x) ∂hausdorffMeasure2 3 := by
  obtain ⟨C, R, hR, hd⟩ := hdecay
  have hzero : Tendsto (fun r : ℝ => ∫ x in sphere (0 : AmbientSpace) r,
      g x * inner ℝ (gradient g x) (r⁻¹ • x) ∂hausdorffMeasure2 3) atTop (𝓝 0) := by
    apply squeeze_zero_norm' (a := fun r : ℝ => 4 * Real.pi * C ^ 2 / r)
      _ (tendsto_const_nhds.div_atTop tendsto_id)
    filter_upwards [eventually_ge_atTop R] with r hr
    exact capacity_sphere_energy_bound hR hd hr
  obtain ⟨S, hS, hKS⟩ := hK.isBounded.subset_ball_lt 0 (0 : AmbientSpace)
  have hlim : Tendsto (fun r : ℝ => ∫ x in ball (0 : AmbientSpace) r,
      ‖gradient g x‖ ^ 2 ∂volume.restrict Kᶜ) atTop
      (𝓝 (-∫ x in frontier K, inner ℝ (gradient g x) (hC1.outwardNormal x)
        ∂hausdorffMeasure2 3)) := by
    have ht := hzero.sub (tendsto_const_nhds (x := ∫ x in frontier K,
      inner ℝ (gradient g x) (hC1.outwardNormal x) ∂hausdorffMeasure2 3))
    simp only [zero_sub] at ht
    apply ht.congr'
    filter_upwards [eventually_ge_atTop S] with r hr
    rw [Measure.restrict_restrict isOpen_ball.measurableSet]
    exact (capacity_annulus_energy hK hreg hC1 hg hΔ hb (hS.trans_le hr)
      (hKS.trans (ball_subset_ball hr))).symm
  have hcover := aecover_ball (μ := volume.restrict Kᶜ) (x := (0 : AmbientSpace))
    (tendsto_id : Tendsto (fun r : ℝ => r) atTop atTop)
  have hlocal (r : ℝ) : IntegrableOn (fun x => ‖gradient g x‖ ^ 2)
      (ball (0 : AmbientSpace) r) (volume.restrict Kᶜ) := by
    have hc : Continuous (fun x => ‖gradient g x‖ ^ 2) :=
      (show ContDiff ℝ 1 (gradient g) from
        contDiff_gradient_of_contDiff_succ hg).continuous.norm.pow 2
    exact (hc.continuousOn.integrableOn_compact
      (isCompact_closedBall (0 : AmbientSpace) r)).mono_set ball_subset_closedBall
  have hn : ∀ᵐ x ∂volume.restrict Kᶜ, 0 ≤ ‖gradient g x‖ ^ 2 :=
    Eventually.of_forall fun _ => sq_nonneg _
  have hi := hcover.integrable_of_integral_tendsto_of_nonneg_ae _ hlocal hn hlim
  exact ⟨hi, hcover.integral_eq_of_tendsto _ hi hlim⟩

/-- Equality with the C² extension implies equality of gradients throughout
the open exterior; no differentiability across the obstacle is assumed for `u`. -/
lemma capacity_gradient_eq_of_boundary_C2 {K : Set AmbientSpace} (hK : IsCompact K)
    {u g : AmbientSpace → ℝ} (hug : EqOn u g (closure Kᶜ)) :
    EqOn (gradient u) (gradient g) Kᶜ := by
  intro x hx
  have heq : u =ᶠ[𝓝 x] g :=
    Filter.mem_of_superset (hK.isClosed.isOpen_compl.mem_nhds hx)
      (fun y hy => hug (subset_closure hy))
  exact heq.gradient_eq

/-- Transfer the distributional harmonic equation to the C² extension. -/
lemma capacity_laplacian_eq_zero_of_boundary_C2 {K : Set AmbientSpace} (hK : IsCompact K)
    {u g : AmbientSpace → ℝ} (hg : ContDiff ℝ 2 g) (hug : EqOn u g (closure Kᶜ))
    (hh : HasDistributionalLaplacianOn u (fun _ => 0) Kᶜ) :
    ∀ x ∈ Kᶜ, laplacianN g x = 0 := by
  have hgg := hh.congr_ae (ae_restrict_of_forall_mem hK.isClosed.measurableSet.compl
    (fun _ hx => hug (subset_closure hx))) (Filter.EventuallyEq.refl _ _)
  exact hgg.laplacianN_eq_zero hK.isClosed.isOpen_compl hg

/-- Blueprint `lem:flux-identity` (`eq:flux-boundary`), conditional on the
named C² boundary extension hypothesis. -/
theorem flux_identity_of_boundary_C2 {K : Set AmbientSpace} (hK : IsCompact K)
    (hreg : K = closure (interior K)) (hC1 : HasC1Boundary (interior K))
    {R₀ : ℝ} (hR₀ : 0 < R₀) (hKR : K ⊆ closedBall 0 R₀)
    (hzero : (0 : AmbientSpace) ∈ interior K)
    {u : AmbientSpace → ℝ} (hu : Continuous u)
    (hh : HasDistributionalLaplacianOn u (fun _ => 0) Kᶜ)
    (hb : ∀ x ∈ K, u x = 1) (hinf : Tendsto u (cocompact AmbientSpace) (𝓝 0))
    {g : AmbientSpace → ℝ} (hg : ContDiff ℝ 2 g) (hug : EqOn u g (closure Kᶜ)) :
    4 * Real.pi * capacityOf K u =
      -∫ x in frontier K, inner ℝ (gradient g x) (hC1.outwardNormal x) ∂hausdorffMeasure2 3 := by
  have hgrad := capacity_gradient_eq_of_boundary_C2 hK hug
  have hΔ := capacity_laplacian_eq_zero_of_boundary_C2 hK hg hug hh
  have hbg : ∀ x ∈ frontier K, g x = 1 := by
    intro x hx
    rw [← hug (frontier_subset_closure (show x ∈ frontier Kᶜ by simpa using hx))]
    exact hb x (hK.isClosed.frontier_subset hx)
  obtain ⟨C, hv, hd⟩ := potential_decay hK hR₀ hKR hzero hu hh hb hinf
  have hdecay : ∃ C R : ℝ, 0 < R ∧ ∀ x : AmbientSpace, R ≤ ‖x‖ →
      |g x| ≤ C / ‖x‖ ∧ ‖gradient g x‖ ≤ C / ‖x‖ ^ 2 := by
    refine ⟨max R₀ C, 2 * R₀, by positivity, ?_⟩
    intro x hx
    have hxK : x ∈ Kᶜ := by
      intro hxK
      have ht : ‖x‖ ≤ R₀ := by simpa using hKR hxK
      linarith
    rw [← hug (subset_closure hxK), ← hgrad hxK]
    exact ⟨(hv x hxK).trans (div_le_div_of_nonneg_right (le_max_left _ _) (norm_nonneg _)),
      (hd x hx).trans (div_le_div_of_nonneg_right (le_max_right _ _) (sq_nonneg _))⟩
  have he := (energy_eq_neg_boundary_flux hK hreg hC1 hg hΔ hbg hdecay).2
  have heq : (∫ x in Kᶜ, ‖gradient u x‖ ^ 2) = ∫ x in Kᶜ, ‖gradient g x‖ ^ 2 :=
    setIntegral_congr_fun hK.isClosed.measurableSet.compl (fun _ hx => by rw [hgrad hx])
  rw [capacityOf, ← mul_assoc, mul_inv_cancel₀ (by positivity : (4 : ℝ) * Real.pi ≠ 0),
    one_mul, heq, he]

/-- Blueprint `lem:kelvin`: the coefficient at infinity is exactly capacity,
under the named C² boundary extension hypothesis. -/
theorem kelvin_constant_eq_capacity {K : Set AmbientSpace} (hK : IsCompact K)
    (hreg : K = closure (interior K)) (hC1 : HasC1Boundary (interior K))
    {R₀ : ℝ} (hR₀ : 0 < R₀) (hKR : K ⊆ closedBall 0 R₀)
    (hzero : (0 : AmbientSpace) ∈ interior K)
    {u : AmbientSpace → ℝ} (hu : Continuous u)
    (hh : HasDistributionalLaplacianOn u (fun _ => 0) Kᶜ)
    (hb : ∀ x ∈ K, u x = 1) (hinf : Tendsto u (cocompact AmbientSpace) (𝓝 0))
    {g : AmbientSpace → ℝ} (hg : ContDiff ℝ 2 g) (hug : EqOn u g (closure Kᶜ)) :
    ∃ R C' : ℝ, 0 < R ∧ ∀ x : AmbientSpace, R ≤ ‖x‖ →
      |u x - capacityOf K u / ‖x‖| ≤ C' / ‖x‖ ^ 2 ∧
      ‖gradient u x + (capacityOf K u / ‖x‖ ^ 3) • x‖ ≤ C' / ‖x‖ ^ 3 := by
  obtain ⟨Cinf, R, C', hR, hexp, hflux⟩ :=
    capacitary_sphere_flux hK hR₀ hKR hzero hu hh hb hinf
  have hgrad := capacity_gradient_eq_of_boundary_C2 hK hug
  have hΔ := capacity_laplacian_eq_zero_of_boundary_C2 hK hg hug hh
  have hboundary : (∫ x in frontier K,
      inner ℝ (gradient g x) (hC1.outwardNormal x) ∂hausdorffMeasure2 3) =
      -(4 * Real.pi * capacityOf K u) := by
    linarith [flux_identity_of_boundary_C2 hK hreg hC1 hR₀ hKR hzero hu hh hb hinf hg hug]
  have hbound : ∀ᶠ r : ℝ in atTop,
      |4 * Real.pi * (Cinf - capacityOf K u)| ≤ 4 * Real.pi * C' / r := by
    filter_upwards [eventually_ge_atTop (max R (R₀ + 1))] with r hr
    have hrR := (le_max_left R (R₀ + 1)).trans hr
    have hr0 := hR.trans_le hrR
    have hrR₀ : R₀ < r := (lt_add_one R₀).trans_le ((le_max_right R (R₀ + 1)).trans hr)
    have hKr : K ⊆ ball (0 : AmbientSpace) r := hKR.trans (closedBall_subset_ball hrR₀)
    have hs : (∫ x in sphere (0 : AmbientSpace) r,
        inner ℝ (gradient u x) (r⁻¹ • x) ∂hausdorffMeasure2 3) =
        -(4 * Real.pi * capacityOf K u) := by
      calc
        _ = ∫ x in sphere (0 : AmbientSpace) r,
            inner ℝ (gradient g x) (r⁻¹ • x) ∂hausdorffMeasure2 3 := by
          apply setIntegral_congr_fun isClosed_sphere.measurableSet
          intro x hx
          dsimp only
          have hxK : x ∈ Kᶜ := by
            intro hxK
            exact (mem_ball.mp (hKr hxK)).ne (mem_sphere.mp hx)
          rw [hgrad hxK]
        _ = _ := (sphere_flux_eq_boundary_flux hK hreg hC1 hg hΔ hr0 hKr).trans hboundary
    have hf := hflux r hrR
    rw [hs] at hf
    convert hf using 1
    congr 1
    ring
  have hz : |4 * Real.pi * (Cinf - capacityOf K u)| ≤ 0 :=
    ge_of_tendsto (tendsto_const_nhds.div_atTop tendsto_id) hbound
  have heq : Cinf = capacityOf K u := by
    have he := abs_eq_zero.mp (le_antisymm hz (abs_nonneg _))
    have hp : (4 : ℝ) * Real.pi ≠ 0 := by positivity
    exact sub_eq_zero.mp ((mul_eq_zero.mp he).resolve_left hp)
  exact ⟨R, C', hR, by simpa only [heq] using hexp⟩

/-- A capacitary potential with the stated boundary extension has strictly
positive capacity when the obstacle contains the origin in its interior. -/
theorem capacityOf_pos {K : Set AmbientSpace} (hK : IsCompact K)
    (hreg : K = closure (interior K)) (hC1 : HasC1Boundary (interior K))
    {R₀ : ℝ} (hR₀ : 0 < R₀) (hKR : K ⊆ closedBall 0 R₀)
    (hzero : (0 : AmbientSpace) ∈ interior K)
    {u : AmbientSpace → ℝ} (hu : Continuous u)
    (hh : HasDistributionalLaplacianOn u (fun _ => 0) Kᶜ)
    (hb : ∀ x ∈ K, u x = 1) (hinf : Tendsto u (cocompact AmbientSpace) (𝓝 0))
    {g : AmbientSpace → ℝ} (hg : ContDiff ℝ 2 g) (hug : EqOn u g (closure Kᶜ)) :
    0 < capacityOf K u := by
  obtain ⟨a, ha, haK⟩ := Metric.mem_nhds_iff.mp (mem_interior_iff_mem_nhds.mp hzero)
  obtain ⟨R, C', _, hexp⟩ :=
    kelvin_constant_eq_capacity hK hreg hC1 hR₀ hKR hzero hu hh hb hinf hg hug
  have hl := div_norm_le_of_exterior_harmonic hK ha haK hu hh
    (fun x hx => (hb x hx).ge) hinf
  have haC : a ≤ capacityOf K u := kelvin_coefficient_ge_of_lower_bound
    (R₀ := R₀) (R := R) (C' := C') (fun x hx => hl x (by
      intro hxK
      have hxR : ‖x‖ ≤ R₀ := by simpa using hKR hxK
      exact (not_lt_of_ge hxR) hx)) (fun x hx => (hexp x hx).1)
  exact ha.trans_le haC

end LiquidDrop

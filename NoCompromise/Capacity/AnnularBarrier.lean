import NoCompromise.Capacity.AnnularDirichlet

/-!
# Exterior-ball barriers for annular boundary continuity

The ball lies inside the obstacle, and is therefore exterior to the annular
domain. All comparisons use the actual Sobolev trace.

The explicit lower barrier proves `AnnularBoundaryContinuity` under the
tangent interior-ball condition. Reflected C² charts supply this condition,
giving capacitary-potential existence without an extra continuity hypothesis.
-/

noncomputable section
open MeasureTheory Set Filter Metric InnerProductSpace
open scoped ENNReal NNReal Topology Gradient
namespace LiquidDrop

/-- The explicit barrier associated with a ball inside the obstacle. -/
def annularBallBarrier (q : AmbientSpace) (ρ R : ℝ) (x : AmbientSpace) : ℝ :=
  1 - (ρ⁻¹ - (R - ‖q‖)⁻¹)⁻¹ * (ρ⁻¹ - ‖x - q‖⁻¹)

/-- The closed annular domain stays outside every open ball in the obstacle. -/
lemma annular_ball_distance {K : Set AmbientSpace} {q : AmbientSpace} {ρ R : ℝ}
    (hball : ball q ρ ⊆ K) {x : AmbientSpace}
    (hx : x ∈ closure (annularDomain K R)) : ρ ≤ ‖x - q‖ := by
  have hxK := closure_mono (show annularDomain K R ⊆ Kᶜ from inter_subset_right) hx
  rw [closure_compl] at hxK
  by_contra! hlt
  exact hxK ((interior_maximal hball isOpen_ball) (by
    simpa only [mem_ball, dist_eq_norm] using hlt))

/-- The center and radius of a tangent interior ball fit inside the enclosing ball. -/
lemma annular_ball_center_radius {K : Set AmbientSpace} (hK : IsCompact K)
    {R₀ ρ : ℝ} (hKR : K ⊆ ball 0 R₀) {p q : AmbientSpace}
    (hp : p ∈ frontier K) (hρ : 0 < ρ) (hball : ball q ρ ⊆ K)
    (hpq : ‖p - q‖ = ρ) : ‖q‖ + ρ < R₀ := by
  have hclosed : closedBall q ρ ⊆ K := by
    rw [← closure_ball q hρ.ne']
    exact hK.isClosed.closure_subset_iff.mpr hball
  by_cases hq : q = 0
  · subst q
    simp only [sub_zero] at hpq
    have hpR := mem_ball.mp (hKR (hK.isClosed.frontier_subset hp))
    simpa only [dist_zero_right, sub_zero, norm_zero, zero_add, hpq] using hpR
  · have hqn : 0 < ‖q‖ := norm_pos_iff.mpr hq
    have he : (1 + ρ / ‖q‖) • q - q = (ρ / ‖q‖) • q := by module
    have hn : ‖(1 + ρ / ‖q‖) • q‖ = ‖q‖ + ρ := by
      rw [norm_smul_of_nonneg (by positivity)]
      field_simp
    have hx : (1 + ρ / ‖q‖) • q ∈ closedBall q ρ := by
      rw [mem_closedBall, dist_eq_norm, he, norm_smul_of_nonneg (by positivity)]
      exact le_of_eq (div_mul_cancel₀ ρ hqn.ne')
    simpa only [dist_zero_right, hn] using mem_ball.mp (hKR (hclosed hx))

/-- The explicit barrier is smooth away from its pole. -/
lemma contDiffOn_annularBallBarrier (q : AmbientSpace) (ρ R : ℝ) :
    ContDiffOn ℝ (⊤ : ℕ∞) (annularBallBarrier q ρ R) {q}ᶜ := by
  intro x hx
  have hxq : x - q ≠ 0 := sub_ne_zero.mpr hx
  exact (contDiffAt_const.sub (contDiffAt_const.mul (contDiffAt_const.sub
    (((contDiffAt_id.sub contDiffAt_const).norm ℝ hxq).inv
      (norm_ne_zero_iff.mpr hxq))))).contDiffWithinAt

/-- A smooth global function agreeing with the barrier near the closed annulus. -/
lemma exists_annular_ball_smooth_barrier {K : Set AmbientSpace} {q : AmbientSpace}
    {ρ : ℝ} (hρ : 0 < ρ) (hball : ball q ρ ⊆ K) (R : ℝ) :
    ∃ β : AmbientSpace → ℝ, ContDiff ℝ (⊤ : ℕ∞) β ∧
      ∀ x ∈ closure (annularDomain K R), β x = annularBallBarrier q ρ R x := by
  have hs : closure (annularDomain K R) ⊆ ({q} : Set AmbientSpace)ᶜ := by
    intro x hx hxq
    have hd := annular_ball_distance hball hx
    rw [mem_singleton_iff.mp hxq, sub_self, norm_zero] at hd
    exact (not_le_of_gt hρ) hd
  obtain ⟨β, hβ, he⟩ := exists_global_contDiff_eq_near_compact isOpen_compl_singleton
    (annularDomain_isBounded K R).isCompact_closure hs
    (contDiffOn_annularBallBarrier q ρ R)
  exact ⟨β, hβ, fun x hx => (he x hx).self_of_nhds⟩

/-- The barrier is distributionally harmonic on domains avoiding its pole. -/
lemma hasDistributionalLaplacianOn_annularBallBarrier (q : AmbientSpace) (ρ R : ℝ)
    {D : Set AmbientSpace} (hq : q ∉ D) :
    HasDistributionalLaplacianOn (annularBallBarrier q ρ R) (fun _ => 0) D := by
  change HasDistributionalLaplacianOn
    (fun x => 1 - (ρ⁻¹ - (R - ‖q‖)⁻¹)⁻¹ * (ρ⁻¹ - ‖x - q‖⁻¹)) (fun _ => 0) D
  have hh := (hasDistributionalLaplacianOn_const D 1).sub
    (((hasDistributionalLaplacianOn_const D ρ⁻¹).sub
      (hasDistributionalLaplacianOn_newtonKernel_away q hq)).const_mul
      (ρ⁻¹ - (R - ‖q‖)⁻¹)⁻¹)
  simpa only [annularBallBarrier, sub_self, mul_zero] using hh

/-- The normalization coefficient is positive when the outer sphere encloses the ball. -/
lemma annular_ball_coefficient_pos {q : AmbientSpace} {ρ R : ℝ}
    (hρ : 0 < ρ) (hR : ‖q‖ + ρ < R) :
    0 < (ρ⁻¹ - (R - ‖q‖)⁻¹)⁻¹ := by
  have hg : ρ < R - ‖q‖ := by linarith
  exact inv_pos.mpr (sub_pos.mpr ((inv_lt_inv₀ (hρ.trans hg) hρ).mpr hg))

/-- Outside the tangent ball, the barrier is at most one. -/
lemma annularBallBarrier_le_one {q x : AmbientSpace} {ρ R : ℝ}
    (hρ : 0 < ρ) (hR : ‖q‖ + ρ < R) (hx : ρ ≤ ‖x - q‖) :
    annularBallBarrier q ρ R x ≤ 1 := by
  have hi : ‖x - q‖⁻¹ ≤ ρ⁻¹ := (inv_le_inv₀ (hρ.trans_le hx) hρ).mpr hx
  exact sub_le_self _ (mul_nonneg (annular_ball_coefficient_pos hρ hR).le
    (sub_nonneg.mpr hi))

/-- On the outer sphere the normalized barrier is nonpositive. -/
lemma annularBallBarrier_le_zero {q x : AmbientSpace} {ρ R : ℝ}
    (hρ : 0 < ρ) (hR : ‖q‖ + ρ < R) (hx : x ∈ sphere 0 R) :
    annularBallBarrier q ρ R x ≤ 0 := by
  have hg : 0 < R - ‖q‖ := by linarith
  have hd : R - ‖q‖ ≤ ‖x - q‖ := by
    have hn := norm_sub_norm_le x q
    have hxR : ‖x‖ = R := by simpa only [mem_sphere, dist_zero_right] using hx
    rwa [hxR] at hn
  have hi := (inv_le_inv₀ (hg.trans_le hd) hg).mpr hd
  have hc := annular_ball_coefficient_pos hρ hR
  have hm : 1 ≤ (ρ⁻¹ - (R - ‖q‖)⁻¹)⁻¹ * (ρ⁻¹ - ‖x - q‖⁻¹) := by
    calc
      1 = (ρ⁻¹ - (R - ‖q‖)⁻¹)⁻¹ * (ρ⁻¹ - (R - ‖q‖)⁻¹) :=
        (inv_mul_cancel₀ (inv_pos.mp hc).ne').symm
      _ ≤ _ := mul_le_mul_of_nonneg_left (sub_le_sub_left hi _) hc.le
  exact sub_nonpos.mpr hm

/-- At the tangency point the explicit barrier has value one. -/
lemma annularBallBarrier_eq_one {q p : AmbientSpace} {ρ R : ℝ}
    (hp : ‖p - q‖ = ρ) : annularBallBarrier q ρ R p = 1 := by
  simp only [annularBallBarrier, hp, sub_self, mul_zero, sub_zero]

/-- Milestone 1: the exterior-ball barrier lies below the weak annular solution. -/
theorem annular_weak_dirichlet_ball_barrier {K : Set AmbientSpace} (hK : IsCompact K)
    (hreg : K = closure (interior K)) (hC1 : HasC1Boundary (interior K))
    (hzero : (0 : AmbientSpace) ∈ interior K) {R₀ : ℝ} (hKR : K ⊆ ball 0 R₀)
    {ψ : AmbientSpace → ℝ} (hψ : IsAnnularDatum K R₀ ψ) {R : ℝ} (hR : R₀ < R)
    {z : H1Space (annularDomain K R)}
    (hz : IsWeakDirichletSolution (annularDomain_isOpen hK R) 0 (hψ.toH1 hK R) z)
    {p q : AmbientSpace} (hp : p ∈ frontier K) {ρ : ℝ} (hρ : 0 < ρ)
    (hball : ball q ρ ⊆ K) (hpq : ‖p - q‖ = ρ) :
    ∀ᵐ x ∂volume.restrict (annularDomain K R), annularBallBarrier q ρ R x ≤ z x := by
  have hR₀ : 0 < R₀ := by simpa using hKR (interior_subset hzero)
  have hqR : ‖q‖ + ρ < R := (annular_ball_center_radius hK hKR hp hρ hball hpq).trans hR
  have hD := annularDomain_isOpen hK R
  have hb := annularDomain_isBounded K R
  have hL : HasLipschitzBoundary (annularDomain K R) :=
    (annulus_hasC1Boundary hK hreg hC1 (hR₀.trans hR)
      (hKR.trans (ball_subset_ball hR.le))).hasLipschitzBoundary
  obtain ⟨β, hβ, heβ⟩ := exists_annular_ball_smooth_barrier hρ hball R
  have hβH := annular_hasH1GradientOn_of_smooth hD hb hβ
  let b := H1Space.ofFunction β (gradient β) hβH
  have he : ⇑b =ᵐ[volume.restrict (annularDomain K R)] annularBallBarrier q ρ R := by
    filter_upwards [H1Space.coeFn_ofFunction β (gradient β) hβH,
      ae_restrict_mem hD.measurableSet] with x hx hxd
    exact hx.trans (heβ x (subset_closure hxd))
  have hbh : HasDistributionalLaplacianOn (⇑b) (fun _ => 0) (annularDomain K R) :=
    (hasDistributionalLaplacianOn_annularBallBarrier q ρ R
      (fun hx => hx.2 (hball (mem_ball_self hρ)))).congr_ae he.symm EventuallyEq.rfl
  obtain ⟨T, -, -, -, hT⟩ := exists_h1_trace_operator hD hb hL
  have ht := hz.trace_eq_annular (hψ.hasH1GradientOn hD) hψ.smooth.continuous T hT
  have htb : ⇑(T b) =ᵐ[
      (Measure.euclideanHausdorffMeasure 2).restrict (frontier (annularDomain K R))] β :=
    hT _ _ hβH hβ.continuous
  have hcomp := annular_h1_harmonic_comparison hD hb hL T hT b z hbh hz.harmonic (by
    filter_upwards [htb, ht, ae_restrict_mem isClosed_frontier.measurableSet]
      with x hb hx hxF
    have hxcl := frontier_subset_closure hxF
    rw [hb, hx, heβ x hxcl]
    change x ∈ frontier (ball (0 : AmbientSpace) R ∩ Kᶜ) at hxF
    rw [annulus_frontier hK (hR₀.trans hR) (hKR.trans (ball_subset_ball hR.le))] at hxF
    rcases hxF with hxF | hxF
    · rw [hψ.zero_on_sphere hR x hxF]
      exact annularBallBarrier_le_zero hρ hqR hxF
    · rw [hψ.one_on_frontier hK x hxF]
      exact annularBallBarrier_le_one hρ hqR (annular_ball_distance hball hxcl))
  filter_upwards [hcomp, he] with x hx he
  exact he ▸ hx

/-- Milestone 2: tangent balls inside the obstacle give continuous annular representatives. -/
theorem annularBoundaryContinuity_of_interior_ball {K : Set AmbientSpace} (hK : IsCompact K)
    (hreg : K = closure (interior K)) (hC1 : HasC1Boundary (interior K))
    (hzero : (0 : AmbientSpace) ∈ interior K) {R₀ : ℝ} (hKR : K ⊆ ball 0 R₀)
    {ψ : AmbientSpace → ℝ} (hψ : IsAnnularDatum K R₀ ψ)
    (hball : ∀ p ∈ frontier K, ∃ q : AmbientSpace, ∃ ρ > 0,
      ball q ρ ⊆ K ∧ ‖p - q‖ = ρ) : AnnularBoundaryContinuity hK hψ := by
  classical
  intro R hR z hz
  have hD := annularDomain_isOpen hK R
  obtain ⟨w, hw, he, -, -⟩ := hz.harmonic.exists_smooth_mean_value (by norm_num) hD
    (fun x hx => by
      obtain ⟨r, hr, hs⟩ := Metric.mem_nhds_iff.mp (hD.mem_nhds hx)
      exact ⟨r, hr, hs, z.hasH1GradientOn.memLp_function.mono_measure
        (Measure.restrict_mono hs le_rfl)⟩)
  have hu : ∀ x ∈ annularDomain K R, w x ≤ 1 :=
    annular_le_on_of_ae hD hw.continuousOn continuousOn_const (by
      filter_upwards [he, annular_weak_dirichlet_bounds hK hreg hC1 hzero hKR hψ hR hz]
        with x he hb
      exact he.symm ▸ hb.2)
  let v : AmbientSpace → ℝ := fun x => if x ∈ K then 1 else w x
  have hv1 : ∀ x ∈ K, v x = 1 := fun x hx => ite_eq_left hx
  have hvu : ∀ x ∈ ball (0 : AmbientSpace) R, v x ≤ 1 := by
    intro x hx
    by_cases hxK : x ∈ K
    · exact (hv1 x hxK).le
    · simpa only [v, ite_eq_right hxK] using hu x ⟨hx, hxK⟩
  refine ⟨v, ?_, ?_, hv1⟩
  · intro p hpR
    by_cases hpK : p ∈ K
    · by_cases hpi : p ∈ interior K
      · apply ContinuousAt.continuousWithinAt
        apply (continuousAt_const :
          ContinuousAt (fun _ : AmbientSpace => (1 : ℝ)) p).congr_of_eventuallyEq
        filter_upwards [isOpen_interior.mem_nhds hpi] with x hx
        exact hv1 x (interior_subset hx)
      · have hp : p ∈ frontier K :=
          ⟨hK.isClosed.closure_eq.symm ▸ hpK, hpi⟩
        obtain ⟨q, ρ, hρ, hballq, hpq⟩ := hball p hp
        have hq : q ∈ K := hballq (mem_ball_self hρ)
        have hbc : ContinuousOn (annularBallBarrier q ρ R) (annularDomain K R) :=
          (contDiffOn_annularBallBarrier q ρ R).continuousOn.mono (by
            intro x hx hxq
            exact hx.2 (mem_singleton_iff.mp hxq ▸ hq))
        have hl : ∀ x ∈ annularDomain K R, annularBallBarrier q ρ R x ≤ w x :=
          annular_le_on_of_ae hD hbc hw.continuousOn (by
            filter_upwards [he, annular_weak_dirichlet_ball_barrier
              hK hreg hC1 hzero hKR hψ hR hz hp hρ hballq hpq] with x he hb
            exact he.symm ▸ hb)
        have hpne : p ∈ ({q} : Set AmbientSpace)ᶜ := by
          intro heq
          have hh := mem_singleton_iff.mp heq
          rw [hh, sub_self, norm_zero] at hpq
          exact hρ.ne' hpq.symm
        have hbp : ContinuousAt (annularBallBarrier q ρ R) p :=
          ((contDiffOn_annularBallBarrier q ρ R).continuousOn p hpne).continuousAt
            (isOpen_compl_singleton.mem_nhds hpne)
        -- Taking the minimum with one gives a lower bound on both sides of the boundary.
        have hmin : Tendsto (fun x => min (annularBallBarrier q ρ R x) 1)
            (𝓝[ball 0 R] p) (𝓝 1) := by
          have hmc : ContinuousAt (fun x => min (annularBallBarrier q ρ R x) 1) p :=
            hbp.min continuousAt_const
          have hh := hmc.continuousWithinAt (s := ball (0 : AmbientSpace) R)
          simpa only [ContinuousWithinAt, annularBallBarrier_eq_one hpq, min_self] using hh
        change Tendsto v (𝓝[ball 0 R] p) (𝓝 (v p))
        rw [hv1 p hpK]
        apply tendsto_of_tendsto_of_tendsto_of_le_of_le' hmin tendsto_const_nhds
        · filter_upwards [self_mem_nhdsWithin] with x hx
          by_cases hxK : x ∈ K
          · rw [hv1 x hxK]
            exact min_le_right _ _
          · exact (min_le_left _ _).trans (by
              simpa only [v, ite_eq_right hxK] using hl x ⟨hx, hxK⟩)
        · filter_upwards [self_mem_nhdsWithin] with x hx
          exact hvu x hx
    · have hpD : p ∈ annularDomain K R := ⟨hpR, hpK⟩
      apply ContinuousAt.continuousWithinAt
      apply ((hw.continuousOn p hpD).continuousAt (hD.mem_nhds hpD)).congr_of_eventuallyEq
      filter_upwards [hD.mem_nhds hpD] with x hx
      exact ite_eq_right hx.2
  · filter_upwards [he, ae_restrict_mem hD.measurableSet] with x he hx
    exact (ite_eq_right hx.2).trans he

/-- Milestone 3: capacitary potentials exist when every obstacle boundary point
has a tangent ball inside the obstacle. -/
theorem exists_capacitary_potential_of_interior_ball
    {K : Set AmbientSpace} (hK : IsCompact K)
    (hreg : K = closure (interior K)) (hC1 : HasC1Boundary (interior K))
    (hzero : (0 : AmbientSpace) ∈ interior K) {R₀ : ℝ} (hKR : K ⊆ ball 0 R₀)
    (hball : ∀ p ∈ frontier K, ∃ q : AmbientSpace, ∃ ρ > 0,
      ball q ρ ⊆ K ∧ ‖p - q‖ = ρ) :
    ∃ u : AmbientSpace → ℝ, Continuous u ∧
      HasDistributionalLaplacianOn u (fun _ => 0) Kᶜ ∧
      ContDiffOn ℝ (⊤ : ℕ∞) u Kᶜ ∧
      (∀ x ∈ K, u x = 1) ∧ Tendsto u (cocompact AmbientSpace) (𝓝 0) ∧
      (∀ x, 0 ≤ u x ∧ u x ≤ 1) ∧ (∀ x ∉ K, u x ≤ R₀ / ‖x‖) := by
  obtain ⟨ψ, hψ⟩ := exists_annularDatum hK hKR
  exact exists_capacitary_potential_of_annular_boundary_continuity
    hK hreg hC1 hzero hKR hψ
    (annularBoundaryContinuity_of_interior_ball hK hreg hC1 hzero hKR hψ hball)

/-- Milestone 4: reflection of a C² boundary chart supplies tangent balls inside
a regular closed obstacle. -/
theorem interior_ball_of_hasC2Boundary {K : Set AmbientSpace}
    (hreg : K = closure (interior K)) (hC2 : HasC2Boundary (interior K)) :
    ∀ p ∈ frontier K, ∃ q : AmbientSpace, ∃ ρ > 0,
      ball q ρ ⊆ K ∧ ‖p - q‖ = ρ := by
  intro p hp
  have hf : frontier (interior K) = frontier K := by
    rw [← hC2.hasC1Boundary.frontier_exterior, ← hreg, frontier_compl]
  obtain ⟨c, hc, hpc, hc2⟩ := hC2 p (by rwa [hf])
  have hext : c.exteriorChart.IsChartFor Kᶜ := by
    simpa only [← hreg] using hc.exterior
  obtain ⟨ρ, hρ, hb, hsp⟩ := hext.exists_exterior_tangent_ball
    (show ContDiff ℝ 2 c.exteriorChart.height from hc2.neg)
    (show p ∈ frontier Kᶜ from by rwa [frontier_compl]) hpc
  refine ⟨p + ρ • c.exteriorChart.outwardNormal p, ρ, hρ, ?_, ?_⟩
  · have hbi : ball (p + ρ • c.exteriorChart.outwardNormal p) ρ ⊆ interior K := by
      simpa only [closure_compl, compl_compl] using hb
    exact hbi.trans interior_subset
  · simpa only [mem_sphere, dist_eq_norm] using hsp

/-- C² boundary discharges the annular boundary-continuity input. -/
theorem annularBoundaryContinuity_of_hasC2Boundary {K : Set AmbientSpace} (hK : IsCompact K)
    (hreg : K = closure (interior K)) (hC2 : HasC2Boundary (interior K))
    (hzero : (0 : AmbientSpace) ∈ interior K) {R₀ : ℝ} (hKR : K ⊆ ball 0 R₀)
    {ψ : AmbientSpace → ℝ} (hψ : IsAnnularDatum K R₀ ψ) :
    AnnularBoundaryContinuity hK hψ :=
  annularBoundaryContinuity_of_interior_ball hK hreg hC2.hasC1Boundary hzero hKR hψ
    (interior_ball_of_hasC2Boundary hreg hC2)

/-- The capacitary potential exists for compact regular closed obstacles with
C² boundary and the specified enclosing radius. -/
theorem exists_capacitary_potential_of_hasC2Boundary
    {K : Set AmbientSpace} (hK : IsCompact K)
    (hreg : K = closure (interior K)) (hC2 : HasC2Boundary (interior K))
    (hzero : (0 : AmbientSpace) ∈ interior K) {R₀ : ℝ} (hKR : K ⊆ ball 0 R₀) :
    ∃ u : AmbientSpace → ℝ, Continuous u ∧
      HasDistributionalLaplacianOn u (fun _ => 0) Kᶜ ∧
      ContDiffOn ℝ (⊤ : ℕ∞) u Kᶜ ∧
      (∀ x ∈ K, u x = 1) ∧ Tendsto u (cocompact AmbientSpace) (𝓝 0) ∧
      (∀ x, 0 ≤ u x ∧ u x ≤ 1) ∧ (∀ x ∉ K, u x ≤ R₀ / ‖x‖) :=
  exists_capacitary_potential_of_interior_ball hK hreg hC2.hasC1Boundary hzero hKR
    (interior_ball_of_hasC2Boundary hreg hC2)

end LiquidDrop

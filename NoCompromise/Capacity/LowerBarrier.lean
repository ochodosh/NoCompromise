import NoCompromise.Capacity.Potential
import NoCompromise.Elliptic.HopfExterior

/-!
# The lower reciprocal-distance barrier

Blueprint `thm:capacitary-potential`, Step 3 (`eq:lower-barrier`): if `B_a ⊆ K`, an exterior
harmonic potential with boundary values at least one and limit zero at infinity satisfies
`a / |x| ≤ u(x)` outside `K`. Together with `le_div_norm_of_exterior_harmonic` this shows
`u → 0` and `u ≢ 0`.
-/

noncomputable section
open Set Filter Metric MeasureTheory
open scoped Topology
namespace LiquidDrop

/-- Blueprint `thm:capacitary-potential` (`eq:lower-barrier`): the reciprocal-distance lower
barrier for an exterior harmonic potential. -/
theorem div_norm_le_of_exterior_harmonic
    {K : Set (EuclideanSpace ℝ (Fin 3))} (hK : IsCompact K)
    {a : ℝ} (ha : 0 < a) (haK : ball (0 : EuclideanSpace ℝ (Fin 3)) a ⊆ K)
    {u : EuclideanSpace ℝ (Fin 3) → ℝ} (hu : Continuous u)
    (hh : HasDistributionalLaplacianOn u (fun _ => 0) Kᶜ)
    (hb : ∀ x ∈ K, 1 ≤ u x)
    (hinf : Tendsto u (cocompact (EuclideanSpace ℝ (Fin 3))) (𝓝 0)) :
    ∀ x ∈ Kᶜ, a / ‖x‖ ≤ u x := by
  have hzero : (0 : EuclideanSpace ℝ (Fin 3)) ∈ interior K :=
    interior_mono haK (by rw [isOpen_ball.interior_eq]; exact mem_ball_self ha)
  have hfar : ∀ x ∈ closure Kᶜ, a ≤ ‖x‖ := by
    intro x hx
    by_contra hlt
    rw [not_le] at hlt
    rw [closure_compl] at hx
    exact hx (interior_mono haK (by
      rw [isOpen_ball.interior_eq, mem_ball, dist_zero_right]; exact hlt))
  have hne : ∀ x ∈ closure Kᶜ, x ≠ 0 := by
    intro x hx heq
    have := hfar x hx
    rw [heq, norm_zero] at this
    linarith
  have hc : ContinuousOn (fun x : EuclideanSpace ℝ (Fin 3) => a / ‖x‖)
      (closure Kᶜ) :=
    continuousOn_const.div continuous_norm.continuousOn
      (fun x hx => norm_ne_zero_iff.mpr (hne x hx))
  have hkernel : HasDistributionalLaplacianOn
      (fun x : EuclideanSpace ℝ (Fin 3) => a / ‖x‖) (fun _ => 0) Kᶜ := by
    simpa only [sub_zero, mul_zero, div_eq_mul_inv] using
      (hasDistributionalLaplacianOn_newtonKernel_away 0
        (show (0 : EuclideanSpace ℝ (Fin 3)) ∉ Kᶜ from
          fun h => h (interior_subset hzero))).const_mul a
  have hkernel_inf : Tendsto (fun x : EuclideanSpace ℝ (Fin 3) => a / ‖x‖)
      (cocompact (EuclideanSpace ℝ (Fin 3))) (𝓝 0) :=
    tendsto_const_nhds.div_atTop tendsto_norm_cocompact_atTop
  have hcomparison := exterior_maximum_principle_of_continuousOn
    (v := fun x => a / ‖x‖ - u x) hK
    (by simpa only [Pi.sub_def] using hc.sub hu.continuousOn)
    (by simpa only [sub_self] using hkernel.sub hh)
    (fun x hx => by
      have hxK : x ∈ K := hK.isClosed.frontier_subset
        (by simpa only [frontier_compl] using hx)
      have hxcl : x ∈ closure Kᶜ := frontier_subset_closure hx
      have hnormpos : 0 < ‖x‖ := norm_pos_iff.mpr (hne x hxcl)
      have hbarrier : a / ‖x‖ ≤ 1 := (div_le_one hnormpos).mpr (hfar x hxcl)
      exact sub_nonpos.mpr (hbarrier.trans (hb x hxK)))
    (by simpa only [sub_self] using hkernel_inf.sub hinf)
  exact fun x hx => sub_nonpos.mp (hcomparison x hx)

/-- Blueprint `thm:capacitary-potential` (`eq:capacitary-signs`, lower half): an exterior
harmonic potential with boundary values at least one and limit zero at infinity is positive
outside `K`, as soon as `0 ∈ int K`. -/
theorem pos_of_exterior_harmonic
    {K : Set (EuclideanSpace ℝ (Fin 3))} (hK : IsCompact K)
    (hzero : (0 : EuclideanSpace ℝ (Fin 3)) ∈ interior K)
    {u : EuclideanSpace ℝ (Fin 3) → ℝ} (hu : Continuous u)
    (hh : HasDistributionalLaplacianOn u (fun _ => 0) Kᶜ)
    (hb : ∀ x ∈ K, 1 ≤ u x)
    (hinf : Tendsto u (cocompact (EuclideanSpace ℝ (Fin 3))) (𝓝 0)) :
    ∀ x ∈ Kᶜ, 0 < u x := by
  obtain ⟨a, ha, haK⟩ := Metric.mem_nhds_iff.mp (mem_interior_iff_mem_nhds.mp hzero)
  intro x hx
  have hx0 : x ≠ 0 := fun h => hx (h ▸ interior_subset hzero)
  exact (div_pos ha (norm_pos_iff.mpr hx0)).trans_le
    (div_norm_le_of_exterior_harmonic hK ha haK hu hh hb hinf x hx)

/-- Blueprint `thm:capacitary-potential`: the exterior maximum principle with a nonpositive
limit at infinity (the case of limit zero is `exterior_maximum_principle_of_continuousOn`). -/
theorem exterior_maximum_principle_of_tendsto_nonpos
    {K : Set (EuclideanSpace ℝ (Fin 3))} (hK : IsCompact K)
    {v : EuclideanSpace ℝ (Fin 3) → ℝ}
    (hv : ContinuousOn v (closure Kᶜ))
    (hh : HasDistributionalLaplacianOn v (fun _ => 0) Kᶜ)
    (hb : ∀ x ∈ frontier Kᶜ, v x ≤ 0) {L : ℝ} (hL : L ≤ 0)
    (hinf : Tendsto v (cocompact (EuclideanSpace ℝ (Fin 3))) (𝓝 L)) :
    ∀ x ∈ Kᶜ, v x ≤ 0 := by
  intro x hx
  by_contra hneg
  have hpos : 0 < v x := lt_of_not_ge hneg
  have hevent : ∀ᶠ y in cocompact (EuclideanSpace ℝ (Fin 3)), v y ≤ v x :=
    (hinf.eventually (gt_mem_nhds (hL.trans_lt hpos))).mono fun _ hy => hy.le
  obtain ⟨z, hz, hmax⟩ := hv.exists_isMaxOn' isClosed_closure
    (subset_closure hx) (hevent.filter_mono inf_le_left)
  have hzpos : 0 < v z := hpos.trans_le (hmax (subset_closure hx))
  let S := closure Kᶜ ∩ {y | v y = v z}
  have hSclosed : IsClosed S :=
    hv.preimage_isClosed_of_isClosed isClosed_closure isClosed_singleton
  have hSopen : IsOpen S := by
    apply isOpen_iff_mem_nhds.mpr
    intro y hy
    have hyout : y ∈ Kᶜ := by
      by_contra hyK
      have hyfront : y ∈ frontier Kᶜ := by
        exact ⟨hy.1, by simpa only [hK.isClosed.isOpen_compl.interior_eq] using hyK⟩
      have := hb y hyfront
      rw [hy.2] at this
      exact (not_le_of_gt hzpos) this
    obtain ⟨r, hr, hrsub⟩ := Metric.isOpen_iff.mp hK.isClosed.isOpen_compl y hyout
    have heq := strong_maximum (by decide : 3 < 4) isOpen_ball
      (convex_ball y r).isPreconnected (hv.mono (hrsub.trans subset_closure))
      (hh.mono hrsub) (mem_ball_self hr)
      (fun w hw => (hmax (subset_closure (hrsub hw))).trans_eq hy.2.symm)
    exact mem_of_superset (ball_mem_nhds y hr) fun w hw =>
      ⟨subset_closure (hrsub hw), (heq w hw).trans hy.2⟩
  have hSuniv : S = univ := (show IsClopen S from ⟨hSclosed, hSopen⟩).eq_univ
    ⟨z, hz, rfl⟩
  obtain ⟨y, hy⟩ := (hinf.eventually (gt_mem_nhds (hL.trans_lt hzpos))).exists
  have hyS : y ∈ S := by rw [hSuniv]; exact mem_univ y
  exact (ne_of_lt hy) hyS.2

/-- Blueprint `thm:capacitary-potential` (`eq:capacitary-signs`): the capacitary potential
satisfies `0 < u ≤ 1` outside `K`, and `u < 1` there when `Kᶜ` is connected. -/
theorem capacitary_signs
    {K : Set (EuclideanSpace ℝ (Fin 3))} (hK : IsCompact K)
    (hzero : (0 : EuclideanSpace ℝ (Fin 3)) ∈ interior K)
    {u : EuclideanSpace ℝ (Fin 3) → ℝ} (hu : Continuous u)
    (hh : HasDistributionalLaplacianOn u (fun _ => 0) Kᶜ)
    (hb : ∀ x ∈ K, u x = 1)
    (hinf : Tendsto u (cocompact (EuclideanSpace ℝ (Fin 3))) (𝓝 0)) :
    (∀ x ∈ Kᶜ, 0 < u x ∧ u x ≤ 1) ∧
      (IsPreconnected Kᶜ → ∀ x ∈ Kᶜ, u x < 1) := by
  have hpos := pos_of_exterior_harmonic hK hzero hu hh (fun x hx => (hb x hx).ge) hinf
  have hle : ∀ x ∈ Kᶜ, u x ≤ 1 := by
    have h := exterior_maximum_principle_of_tendsto_nonpos (v := fun x => u x - 1) hK
      (hu.continuousOn.sub continuousOn_const)
      (by simpa only [sub_self] using hh.sub (hasDistributionalLaplacianOn_const Kᶜ 1))
      (fun x hx => by
        have hxK : x ∈ K := hK.isClosed.frontier_subset
          (by simpa only [frontier_compl] using hx)
        simp [hb x hxK])
      (show (-1 : ℝ) ≤ 0 by norm_num)
      (by simpa only [zero_sub] using hinf.sub_const 1)
    exact fun x hx => sub_nonpos.mp (h x hx)
  refine ⟨fun x hx => ⟨hpos x hx, hle x hx⟩, ?_⟩
  intro hconn x hx
  refine lt_of_le_of_ne (hle x hx) fun hx1 => ?_
  have heq := strong_maximum (by decide : 3 < 4) hK.isClosed.isOpen_compl hconn
    hu.continuousOn hh hx (fun y hy => (hle y hy).trans hx1.ge)
  have hev : ∀ᶠ y in cocompact (EuclideanSpace ℝ (Fin 3)), y ∈ Kᶜ ∧ u y < 1 :=
    Filter.Eventually.and hK.compl_mem_cocompact (hinf.eventually (gt_mem_nhds (by norm_num)))
  obtain ⟨y, hyK, hy1⟩ := hev.exists
  rw [heq y hyK, hx1] at hy1
  exact lt_irrefl _ hy1

/-- Blueprint `thm:capacitary-potential` (`eq:capacitary-signs`, Step 5, Hopf sign): for a
regular closed compact `K` with `C²` boundary, connected complement and `0 ∈ int K`, the
capacitary potential, if differentiable up to `∂K` from outside, has `∂_{ν_K} u < 0` on `∂K`. -/
theorem capacitary_hopf_sign {K : Set AmbientSpace} (hK : IsCompact K)
    (hregular : K = closure (interior K)) (hK2 : HasC2Boundary (interior K))
    (hconn : IsPreconnected Kᶜ) (hzero : (0 : AmbientSpace) ∈ interior K)
    {u : AmbientSpace → ℝ} (hu : Continuous u)
    (hh : HasDistributionalLaplacianOn u (fun _ => 0) Kᶜ)
    (hb : ∀ x ∈ K, u x = 1)
    (hinf : Tendsto u (cocompact AmbientSpace) (𝓝 0))
    {L : AmbientSpace → AmbientSpace →L[ℝ] ℝ}
    (hd : ∀ p ∈ frontier K, HasFDerivWithinAt u (L p) (closure Kᶜ) p) :
    ∀ p ∈ frontier K, L p (hK2.outwardNormal p) < 0 :=
  hopf_exterior_regular_closed hregular hK2 hu.continuousOn hh
    ((capacitary_signs hK hzero hu hh hb hinf).2 hconn)
    (fun p hp => hb p (hK.isClosed.frontier_subset hp)) hd

end LiquidDrop

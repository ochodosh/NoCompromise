import NoCompromise.Elliptic.StrongMaximumHarmonic
import NoCompromise.Elliptic.HarmonicAlgebra

/-!
# Exterior comparison for capacitary potentials

The maximum principle uses only the boundary values and continuity on the
closure of the exterior. In particular it applies to the reciprocal-distance
barrier without assigning a continuous value to that barrier at its pole.
-/

noncomputable section
open Set Filter Metric MeasureTheory
open scoped Topology
namespace LiquidDrop

/-- Exterior maximum principle with continuity only on the closed exterior. -/
theorem exterior_maximum_principle_of_continuousOn
    {K : Set (EuclideanSpace ℝ (Fin 3))} (hK : IsCompact K)
    {v : EuclideanSpace ℝ (Fin 3) → ℝ}
    (hv : ContinuousOn v (closure Kᶜ))
    (hh : HasDistributionalLaplacianOn v (fun _ => 0) Kᶜ)
    (hb : ∀ x ∈ frontier Kᶜ, v x ≤ 0)
    (hinf : Tendsto v (cocompact (EuclideanSpace ℝ (Fin 3))) (𝓝 0)) :
    ∀ x ∈ Kᶜ, v x ≤ 0 := by
  intro x hx
  by_contra hneg
  have hpos : 0 < v x := lt_of_not_ge hneg
  have hevent : ∀ᶠ y in cocompact (EuclideanSpace ℝ (Fin 3)), v y ≤ v x :=
    (hinf.eventually (gt_mem_nhds hpos)).mono fun _ hy => hy.le
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
  obtain ⟨y, hy⟩ := (hinf.eventually (gt_mem_nhds hzpos)).exists
  have hyS : y ∈ S := by rw [hSuniv]; exact mem_univ y
  exact (ne_of_lt hy) hyS.2

/-- A continuous exterior harmonic function vanishing at infinity is bounded
above by zero if its boundary values are bounded above by zero. -/
theorem exterior_maximum_principle
    {K : Set (EuclideanSpace ℝ (Fin 3))} (hK : IsCompact K)
    {v : EuclideanSpace ℝ (Fin 3) → ℝ} (hv : Continuous v)
    (hh : HasDistributionalLaplacianOn v (fun _ => 0) Kᶜ)
    (hb : ∀ x ∈ frontier Kᶜ, v x ≤ 0)
    (hinf : Tendsto v (cocompact (EuclideanSpace ℝ (Fin 3))) (𝓝 0)) :
    ∀ x ∈ Kᶜ, v x ≤ 0 :=
  exterior_maximum_principle_of_continuousOn hK hv.continuousOn hh hb hinf

/-- Uniqueness of a continuous exterior harmonic function with prescribed
values on the compact set and limit zero at infinity. -/
theorem exterior_harmonic_unique
    {K : Set (EuclideanSpace ℝ (Fin 3))} (hK : IsCompact K)
    {u₁ u₂ : EuclideanSpace ℝ (Fin 3) → ℝ}
    (h₁ : Continuous u₁) (h₂ : Continuous u₂)
    (hh₁ : HasDistributionalLaplacianOn u₁ (fun _ => 0) Kᶜ)
    (hh₂ : HasDistributionalLaplacianOn u₂ (fun _ => 0) Kᶜ)
    (hboundary : ∀ x ∈ K, u₁ x = u₂ x)
    (hinf₁ : Tendsto u₁ (cocompact (EuclideanSpace ℝ (Fin 3))) (𝓝 0))
    (hinf₂ : Tendsto u₂ (cocompact (EuclideanSpace ℝ (Fin 3))) (𝓝 0)) :
    u₁ = u₂ := by
  have hb : ∀ x ∈ frontier Kᶜ, u₁ x = u₂ x := by
    intro x hx
    apply hboundary x
    have : x ∈ frontier K := by simpa only [frontier_compl] using hx
    exact hK.isClosed.frontier_subset this
  have hle := exterior_maximum_principle (v := fun x => u₁ x - u₂ x) hK
    (by simpa only [Pi.sub_def] using h₁.sub h₂)
    (by simpa only [sub_self] using hh₁.sub hh₂)
    (fun x hx => by simp [hb x hx])
    (by simpa only [sub_self] using hinf₁.sub hinf₂)
  have hge := exterior_maximum_principle (v := fun x => u₂ x - u₁ x) hK
    (by simpa only [Pi.sub_def] using h₂.sub h₁)
    (by simpa only [sub_self] using hh₂.sub hh₁)
    (fun x hx => by simp [hb x hx])
    (by simpa only [sub_self] using hinf₂.sub hinf₁)
  funext x
  by_cases hx : x ∈ K
  · exact hboundary x hx
  · exact le_antisymm (sub_nonpos.mp (hle x hx)) (sub_nonpos.mp (hge x hx))

/-- The reciprocal-distance upper barrier for an exterior harmonic potential. -/
theorem le_div_norm_of_exterior_harmonic
    {K : Set (EuclideanSpace ℝ (Fin 3))} (hK : IsCompact K)
    {R₀ : ℝ} (_hR₀ : 0 < R₀) (hKR : K ⊆ closedBall 0 R₀)
    (hzero : (0 : EuclideanSpace ℝ (Fin 3)) ∈ interior K)
    {u : EuclideanSpace ℝ (Fin 3) → ℝ} (hu : Continuous u)
    (hh : HasDistributionalLaplacianOn u (fun _ => 0) Kᶜ)
    (hb : ∀ x ∈ K, u x ≤ 1)
    (hinf : Tendsto u (cocompact (EuclideanSpace ℝ (Fin 3))) (𝓝 0)) :
    ∀ x ∈ Kᶜ, u x ≤ R₀ / ‖x‖ := by
  have hne : ∀ x ∈ closure Kᶜ, x ≠ 0 := by
    intro x hx heq
    subst x
    rw [closure_compl] at hx
    exact hx hzero
  have hc : ContinuousOn (fun x : EuclideanSpace ℝ (Fin 3) => R₀ / ‖x‖)
      (closure Kᶜ) :=
    continuousOn_const.div continuous_norm.continuousOn
      (fun x hx => norm_ne_zero_iff.mpr (hne x hx))
  have hkernel : HasDistributionalLaplacianOn
      (fun x : EuclideanSpace ℝ (Fin 3) => R₀ / ‖x‖) (fun _ => 0) Kᶜ := by
    simpa only [sub_zero, mul_zero, div_eq_mul_inv] using
      (hasDistributionalLaplacianOn_newtonKernel_away 0
        (show (0 : EuclideanSpace ℝ (Fin 3)) ∉ Kᶜ from
          fun h => h (interior_subset hzero))).const_mul R₀
  have hkernel_inf : Tendsto (fun x : EuclideanSpace ℝ (Fin 3) => R₀ / ‖x‖)
      (cocompact (EuclideanSpace ℝ (Fin 3))) (𝓝 0) :=
    tendsto_const_nhds.div_atTop tendsto_norm_cocompact_atTop
  have hcomparison := exterior_maximum_principle_of_continuousOn
    (v := fun x => u x - R₀ / ‖x‖) hK
    (by simpa only [Pi.sub_def] using hu.continuousOn.sub hc)
    (by simpa only [sub_self] using hh.sub hkernel)
    (fun x hx => by
      have hxK : x ∈ K := hK.isClosed.frontier_subset
        (by simpa only [frontier_compl] using hx)
      have hnormpos : 0 < ‖x‖ := norm_pos_iff.mpr (hne x (frontier_subset_closure hx))
      have hnormle : ‖x‖ ≤ R₀ := by simpa only [mem_closedBall, dist_zero_right] using hKR hxK
      have hbarrier : 1 ≤ R₀ / ‖x‖ := (le_div_iff₀ hnormpos).mpr (by simpa using hnormle)
      exact sub_nonpos.mpr ((hb x hxK).trans hbarrier))
    (by simpa only [sub_self] using hinf.sub hkernel_inf)
  exact fun x hx => sub_nonpos.mp (hcomparison x hx)

end LiquidDrop

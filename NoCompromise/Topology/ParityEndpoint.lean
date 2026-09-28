import NoCompromise.Topology.Parity

/-!
# Moving the endpoint of a transverse path (towards `prop:orientation-parity` (ii))

The local-constancy step of `prop:orientation-parity`(ii): if a transverse path ends at `x`
and a ball about `x` misses the surface, then for every `x'` in that ball the path can be
modified near its terminal end, by a convex combination with the constant path `x'`, into a
transverse path ending at `x'`, unchanged on the first half, constant near its end, and with
exactly the same intersection set. Consequently the intersection parity of transverse paths
from a fixed base point is locally constant off the surface (once path independence is known).
-/

noncomputable section
open Set

namespace LiquidDrop

/-- The norm on `EuclideanSpace ℝ (Fin 1)` is the absolute value of the coordinate. -/
theorem euclideanSpace_fin_one_norm_eq (p : EuclideanSpace ℝ (Fin 1)) : ‖p‖ = |p 0| := by
  rw [EuclideanSpace.norm_eq, Fin.sum_univ_one, Real.sqrt_sq (norm_nonneg _), Real.norm_eq_abs]

/-- Endpoint shift: a transverse path ending at `x`, with a surface-free ball about `x`, can be
redirected to any `x'` in that ball without changing its first half or its intersections. -/
theorem exists_transverse_path_endpoint_shift {S : Set E₃}
    {α : EuclideanSpace ℝ (Fin 1) → E₃} (hα : ContDiff ℝ (⊤ : ℕ∞) α)
    (htα : ∀ p ∈ Metric.closedBall (0 : EuclideanSpace ℝ (Fin 1)) 1, TransverseAt S α p)
    {x x' : E₃} {r : ℝ} (hxr : Disjoint (Metric.ball x r) S)
    (hx : α (EuclideanSpace.single 0 1) = x) (hx' : x' ∈ Metric.ball x r) :
    ∃ α' : EuclideanSpace ℝ (Fin 1) → E₃, ContDiff ℝ (⊤ : ℕ∞) α' ∧
      (∀ p : EuclideanSpace ℝ (Fin 1), p 0 ≤ 0 → α' p = α p) ∧
      α' (EuclideanSpace.single 0 1) = x' ∧
      (∃ η > 0, ∀ p : EuclideanSpace ℝ (Fin 1), 1 - η < p 0 → α' p = x') ∧
      (∀ p ∈ Metric.closedBall (0 : EuclideanSpace ℝ (Fin 1)) 1, TransverseAt S α' p) ∧
      Metric.closedBall (0 : EuclideanSpace ℝ (Fin 1)) 1 ∩ α' ⁻¹' S =
        Metric.closedBall (0 : EuclideanSpace ℝ (Fin 1)) 1 ∩ α ⁻¹' S := by
  set e : EuclideanSpace ℝ (Fin 1) := EuclideanSpace.single 0 1 with he
  have hr : 0 < r := Metric.pos_of_mem_ball hx'
  -- a neighbourhood of the terminal point mapped into the ball
  obtain ⟨δ, hδ, hδball⟩ : ∃ δ > 0, ∀ p, dist p e < δ → α p ∈ Metric.ball x r := by
    have hcont := hα.continuous.continuousAt (x := e)
    rw [Metric.continuousAt_iff] at hcont
    obtain ⟨δ, hδ, h⟩ := hcont r hr
    exact ⟨δ, hδ, fun p hp => by rw [Metric.mem_ball, ← hx]; exact h hp⟩
  set η : ℝ := min (δ / 4) (1 / 2) with hη
  have hη0 : 0 < η := lt_min (by positivity) (by norm_num)
  have hηh : η ≤ 1 / 2 := min_le_right _ _
  have hηδ : η ≤ δ / 4 := min_le_left _ _
  let ψ : ℝ → ℝ := fun s => Real.smoothTransition ((s - (1 - 2 * η)) / η)
  have hψ0 : ∀ s, s ≤ 1 - 2 * η → ψ s = 0 := fun s hs =>
    Real.smoothTransition.zero_of_nonpos (div_nonpos_of_nonpos_of_nonneg (by linarith) hη0.le)
  have hψ1 : ∀ s, 1 - η ≤ s → ψ s = 1 := fun s hs =>
    Real.smoothTransition.one_of_one_le (by rw [le_div_iff₀ hη0]; linarith)
  let α' : EuclideanSpace ℝ (Fin 1) → E₃ := fun p => (1 - ψ (p 0)) • α p + ψ (p 0) • x'
  have hcoord : ContDiff ℝ (⊤ : ℕ∞) fun p : EuclideanSpace ℝ (Fin 1) => p 0 :=
    (EuclideanSpace.proj (𝕜 := ℝ) (0 : Fin 1)).contDiff
  have hψc : ContDiff ℝ (⊤ : ℕ∞) fun p : EuclideanSpace ℝ (Fin 1) => ψ (p 0) :=
    Real.smoothTransition.contDiff.comp ((hcoord.sub contDiff_const).div_const _)
  have hα'c : ContDiff ℝ (⊤ : ℕ∞) α' :=
    ((contDiff_const.sub hψc).smul hα).add (hψc.smul contDiff_const)
  have he0 : e 0 = 1 := by simp [he]
  -- near the end, both paths lie in the surface-free ball
  have hfar : ∀ p ∈ Metric.closedBall (0 : EuclideanSpace ℝ (Fin 1)) 1, 1 - 2 * η ≤ p 0 →
      α p ∈ Metric.ball x r ∧ α' p ∈ Metric.ball x r := by
    intro p hp hp0
    have hpn : |p 0| ≤ 1 := by
      rw [← euclideanSpace_fin_one_norm_eq]; simpa using hp
    have hdist : dist p e < δ := by
      rw [dist_eq_norm, euclideanSpace_fin_one_norm_eq]
      have : (p - e) 0 = p 0 - 1 := by simp [he0]
      rw [this, abs_sub_comm, abs_of_nonneg (by linarith [(abs_le.mp hpn).2])]
      linarith
    have hαp := hδball p hdist
    refine ⟨hαp, ?_⟩
    exact convex_ball x r hαp hx' (sub_nonneg.mpr (Real.smoothTransition.le_one _))
      (Real.smoothTransition.nonneg _) (by ring)
  -- away from the end the modified path agrees with `α` near every point
  have hnear : ∀ p : EuclideanSpace ℝ (Fin 1), p 0 < 1 - 2 * η → α' =ᶠ[nhds p] α := by
    intro p hp
    have hopen : IsOpen {q : EuclideanSpace ℝ (Fin 1) | q 0 < 1 - 2 * η} :=
      isOpen_lt hcoord.continuous continuous_const
    filter_upwards [hopen.mem_nhds hp] with q hq
    simp only [α', hψ0 _ hq.le, sub_zero, one_smul, zero_smul, add_zero]
  refine ⟨α', hα'c, ?_, ?_, ⟨η, hη0, ?_⟩, ?_, ?_⟩
  · intro p hp
    simp only [α', hψ0 _ (by linarith), sub_zero, one_smul, zero_smul, add_zero]
  · have h1 : 1 - η ≤ e 0 := by rw [he0]; linarith
    simp only [α', hψ1 _ h1, sub_self, zero_smul, one_smul, zero_add]
  · intro p hp
    simp only [α', hψ1 _ hp.le, sub_self, zero_smul, one_smul, zero_add]
  · intro p hp
    by_cases hp0 : p 0 < 1 - 2 * η
    · have hev := hnear p hp0
      intro hmem
      rw [hev.eq_of_nhds] at hmem ⊢
      rw [hev.fderiv_eq]
      exact htα p hp hmem
    · intro hmem
      exact absurd hmem (Set.disjoint_left.mp hxr (hfar p hp (not_lt.mp hp0)).2)
  · ext p
    simp only [mem_inter_iff, mem_preimage]
    constructor
    · rintro ⟨hp, hmem⟩
      refine ⟨hp, ?_⟩
      by_cases hp0 : p 0 < 1 - 2 * η
      · rwa [(hnear p hp0).eq_of_nhds] at hmem
      · exact absurd hmem (Set.disjoint_left.mp hxr (hfar p hp (not_lt.mp hp0)).2)
    · rintro ⟨hp, hmem⟩
      refine ⟨hp, ?_⟩
      by_cases hp0 : p 0 < 1 - 2 * η
      · rwa [(hnear p hp0).eq_of_nhds]
      · exact absurd hmem (Set.disjoint_left.mp hxr (hfar p hp (not_lt.mp hp0)).1)

end LiquidDrop

module

public import NoCompromise.DeGiorgi.RectifiabilityGeometry
public import NoCompromise.DeGiorgi.ConeConcentration
public import Mathlib.Topology.Bases

@[expose] public section

/-!
# Countable graph covers from density and cone concentration

Countable choices of lower density, radius, nearby unit normal, and a small
spatial ball split the good points into uniform pieces. Each such piece is
contained in a global rotated Lipschitz graph by the geometric separation lemma.
-/

noncomputable section
open MeasureTheory Set Filter Metric
open scoped Topology ENNReal NNReal
namespace LiquidDrop

/-- A fixed countable scale for uniform density pieces. -/
def rectifiabilityScale (k : ℕ) : ℝ := 1 / ((k : ℝ) + 1)

lemma rectifiabilityScale_pos (k : ℕ) : 0 < rectifiabilityScale k := by
  unfold rectifiabilityScale
  positivity

/-- Countably many uniform density/cone bounds give a cover by actual rotated
one-Lipschitz graphs, without requiring measurability of a chosen normal field. -/
theorem countable_graph_cover_of_uniform_bounds
    (μ : Measure AmbientSpace) [IsFiniteMeasureOnCompacts μ]
    (ν : AmbientSpace → AmbientSpace)
    (hgood : ∀ᵐ x ∂μ, ‖ν x‖ = 1 ∧ ∃ k m : ℕ, ∀ r : ℝ,
      0 < r → r < rectifiabilityScale m →
      rectifiabilityScale k * r ^ 2 ≤ μ.real (ball x r) ∧
      μ.real (ball x r ∩ {z | (1 / 8 : ℝ) * ‖z - x‖ ≤ |inner ℝ (ν x) (z - x)|}) ≤
        rectifiabilityScale k / 8192 * r ^ 2) :
    ∃ (e : ℕ → AmbientSpace ≃ₗᵢ[ℝ] AmbientSpace)
      (f : ℕ → EuclideanSpace ℝ (Fin 2) → ℝ),
      (∀ j, LipschitzWith 1 (f j)) ∧
      μ (⋃ j, range (fun p => e j (graphMapN (f j) p)))ᶜ = 0 := by
  classical
  let : Nonempty (sphere (0 : AmbientSpace) 1) :=
    ⟨⟨EuclideanSpace.single 0 1, by simp⟩⟩
  let v := TopologicalSpace.denseSeq (sphere (0 : AmbientSpace) 1)
  let a := TopologicalSpace.denseSeq AmbientSpace
  have hv (j : ℕ) : ‖(v j : AmbientSpace)‖ = 1 := by
    simpa only [mem_sphere, dist_zero_right] using (v j).property
  let G (i : ℕ × ℕ × ℕ × ℕ) : Set AmbientSpace :=
    {x | ‖ν x‖ = 1 ∧
      (∀ r : ℝ, 0 < r → r < rectifiabilityScale i.2.1 →
        rectifiabilityScale i.1 * r ^ 2 ≤ μ.real (ball x r) ∧
        μ.real (ball x r ∩ {z | (1 / 8 : ℝ) * ‖z - x‖ ≤ |inner ℝ (ν x) (z - x)|}) ≤
          rectifiabilityScale i.1 / 8192 * r ^ 2) ∧
      ‖ν x - (v i.2.2.1 : AmbientSpace)‖ ≤ (1 / 16 : ℝ) ∧
      x ∈ ball (a i.2.2.2) (rectifiabilityScale i.2.1 / 8)}
  have hgraph (i : ℕ × ℕ × ℕ × ℕ) :
      ∃ (e : AmbientSpace ≃ₗᵢ[ℝ] AmbientSpace) (f : EuclideanSpace ℝ (Fin 2) → ℝ),
        LipschitzWith 1 f ∧ G i ⊆ range (fun p => e (graphMapN f p)) := by
    have hdiam : ∀ x ∈ G i, ∀ y ∈ G i, 2 * ‖y - x‖ < rectifiabilityScale i.2.1 := by
      intro x hx y hy
      have hx' := hx.2.2.2
      have hy' := hy.2.2.2
      have hd := dist_triangle y (a i.2.2.2) x
      rw [dist_comm (a i.2.2.2) x] at hd
      simp only [mem_ball, dist_eq_norm] at hx' hy' hd
      linarith [rectifiabilityScale_pos i.2.1]
    have hh := uniform_mass_piece_height_bound μ (G i) ν (rectifiabilityScale_pos i.1)
      (fun x hx => hx.1) hdiam
      (fun x hx r hr hR => (hx.2.1 r hr hR).1)
      (fun x hx r hr hR => (hx.2.1 r hr hR).2)
    obtain ⟨e, f, he, hf, hc⟩ := exists_rotated_graph_of_nearby_normal_bound (G i) ν
      (hv i.2.2.1) (fun x hx => hx.2.2.1) hh
    exact ⟨e, f, hf, hc⟩
  choose e f hf hc using hgraph
  obtain ⟨q, hq⟩ := exists_surjective_nat (ℕ × ℕ × ℕ × ℕ)
  refine ⟨fun j => e (q j), fun j => f (q j), fun j => hf (q j), ?_⟩
  apply ae_iff.mp
  filter_upwards [hgood] with x hx
  obtain ⟨hunit, k, m, hbounds⟩ := hx
  let u : sphere (0 : AmbientSpace) 1 := ⟨ν x, by simpa only [mem_sphere, dist_zero_right]⟩
  obtain ⟨j, hj⟩ := (TopologicalSpace.denseRange_denseSeq
    (sphere (0 : AmbientSpace) 1)).exists_dist_lt u (by norm_num : (0 : ℝ) < 1 / 16)
  obtain ⟨l, hl⟩ := (TopologicalSpace.denseRange_denseSeq AmbientSpace).exists_dist_lt x
    (div_pos (rectifiabilityScale_pos m) (by norm_num : (0 : ℝ) < 8))
  have hxG : x ∈ G (k, m, j, l) := by
    refine ⟨hunit, hbounds, ?_, hl⟩
    exact (show ‖ν x - (v j : AmbientSpace)‖ < (1 / 16 : ℝ) from hj).le
  obtain ⟨b, hb⟩ := hq (k, m, j, l)
  apply mem_iUnion.mpr
  refine ⟨b, ?_⟩
  rw [hb]
  exact hc _ hxG

/-- Positive quadratic density and concentration outside one fixed narrow cone
supply a pair of countable uniform density/cone parameters at a point. -/
theorem exists_uniform_bounds_of_density_cone (μ : Measure AmbientSpace)
    (x ν : AmbientSpace) {d : ℝ} (hd : 0 < d)
    (hden : Tendsto (fun r : ℝ => μ.real (ball x r) / r ^ 2) (𝓝[>] 0) (𝓝 d))
    (hcone : Tendsto (fun r : ℝ => μ.real (ball x r \ normalPlaneCone x ν (1 / 8)) /
      μ.real (ball x r)) (𝓝[>] 0) (𝓝 0)) :
    ∃ k m : ℕ, ∀ r : ℝ, 0 < r → r < rectifiabilityScale m →
      rectifiabilityScale k * r ^ 2 ≤ μ.real (ball x r) ∧
      μ.real (ball x r ∩ {z | (1 / 8 : ℝ) * ‖z - x‖ ≤ |inner ℝ ν (z - x)|}) ≤
        rectifiabilityScale k / 8192 * r ^ 2 := by
  obtain ⟨k, hk⟩ := exists_nat_one_div_lt hd
  change rectifiabilityScale k < d at hk
  have hlo : ∀ᶠ r : ℝ in 𝓝[>] 0,
      rectifiabilityScale k * r ^ 2 < μ.real (ball x r) := by
    filter_upwards [hden.eventually (Ioi_mem_nhds hk), self_mem_nhdsWithin] with r hr hp
    exact (lt_div_iff₀ (sq_pos_of_pos hp)).mp hr
  have hs (r : ℝ) :
      ball x r ∩ {z | (1 / 8 : ℝ) * ‖z - x‖ ≤ |inner ℝ ν (z - x)|} =
        ball x r \ normalPlaneCone x ν (1 / 8) := by
    ext z
    simp only [mem_inter_iff, mem_ofPred_eq, Set.mem_sdiff, normalPlaneCone, not_lt]
  have hscaled : Tendsto (fun r : ℝ =>
      μ.real (ball x r \ normalPlaneCone x ν (1 / 8)) / r ^ 2) (𝓝[>] 0) (𝓝 0) := by
    have ht := hcone.mul hden
    rw [zero_mul] at ht
    apply ht.congr'
    filter_upwards [hlo, self_mem_nhdsWithin] with r hr hp
    have hm : 0 < μ.real (ball x r) :=
      (mul_pos (rectifiabilityScale_pos k) (sq_pos_of_pos hp)).trans hr
    change 0 < r at hp
    field_simp [hm.ne', hp.ne']
  have hhi : ∀ᶠ r : ℝ in 𝓝[>] 0,
      μ.real (ball x r \ normalPlaneCone x ν (1 / 8)) ≤
        rectifiabilityScale k / 8192 * r ^ 2 := by
    filter_upwards [hscaled.eventually (Iio_mem_nhds
      (div_pos (rectifiabilityScale_pos k) (by norm_num : (0 : ℝ) < 8192))),
      self_mem_nhdsWithin] with r hr hp
    exact ((div_lt_iff₀ (sq_pos_of_pos hp)).mp hr).le
  obtain ⟨δ, hδ, hb⟩ := Metric.mem_nhdsWithin_iff.mp (hlo.and hhi)
  obtain ⟨m, hm⟩ := exists_nat_one_div_lt hδ
  change rectifiabilityScale m < δ at hm
  refine ⟨k, m, fun r hr hR => ?_⟩
  have hh := hb (show r ∈ ball (0 : ℝ) δ ∩ Ioi 0 from
    ⟨by simpa only [mem_ball, Real.dist_eq, sub_zero, abs_of_pos hr] using hR.trans hm, hr⟩)
  exact ⟨hh.1.le, by simpa only [hs] using hh.2⟩

/-- Positive finite quadratic density and cone concentration imply that the
measure is carried by countably many actual rotated Lipschitz graphs. -/
theorem rectifiability_of_density_and_cone (μ : Measure AmbientSpace)
    [IsFiniteMeasureOnCompacts μ] (ν : AmbientSpace → AmbientSpace)
    (hν : ∀ᵐ x ∂μ, ‖ν x‖ = 1)
    (hden : ∀ᵐ x ∂μ, ∃ d : ℝ, 0 < d ∧
      Tendsto (fun r : ℝ => μ.real (ball x r) / r ^ 2) (𝓝[>] 0) (𝓝 d))
    (hcone : ∀ᵐ x ∂μ, Tendsto (fun r : ℝ =>
      μ.real (ball x r \ normalPlaneCone x (ν x) (1 / 8)) / μ.real (ball x r))
      (𝓝[>] 0) (𝓝 0)) :
    ∃ (e : ℕ → AmbientSpace ≃ₗᵢ[ℝ] AmbientSpace)
      (f : ℕ → EuclideanSpace ℝ (Fin 2) → ℝ),
      (∀ j, LipschitzWith 1 (f j)) ∧
      μ (⋃ j, range (fun p => e j (graphMapN (f j) p)))ᶜ = 0 := by
  apply countable_graph_cover_of_uniform_bounds μ ν
  filter_upwards [hν, hden, hcone] with x hx hd hc
  obtain ⟨d, hd, hden⟩ := hd
  exact ⟨hx, exists_uniform_bounds_of_density_cone μ x (ν x) hd hden hc⟩

/-- Blueprint `lem:rectifiability-criterion`, with a plane represented by a unit
normal. The normal is chosen independently at each point and need not be measurable. -/
theorem rectifiability_criterion (μ : Measure AmbientSpace) [IsFiniteMeasureOnCompacts μ]
    (h : ∀ᵐ x ∂μ, ∃ ν : AmbientSpace, ‖ν‖ = 1 ∧ ∃ d : ℝ, 0 < d ∧
      Tendsto (fun r : ℝ => μ.real (ball x r) / (Real.pi * r ^ 2)) (𝓝[>] 0) (𝓝 d) ∧
      ∀ ε : ℝ, 0 < ε → Tendsto (fun r : ℝ =>
        μ.real (ball x r \ normalPlaneCone x ν ε) / μ.real (ball x r)) (𝓝[>] 0) (𝓝 0)) :
    ∃ (e : ℕ → AmbientSpace ≃ₗᵢ[ℝ] AmbientSpace)
      (f : ℕ → EuclideanSpace ℝ (Fin 2) → ℝ),
      (∀ j, LipschitzWith 1 (f j)) ∧
      μ (⋃ j, range (fun p => e j (graphMapN (f j) p)))ᶜ = 0 := by
  classical
  let P (x ν : AmbientSpace) : Prop := ‖ν‖ = 1 ∧ ∃ d : ℝ, 0 < d ∧
    Tendsto (fun r : ℝ => μ.real (ball x r) / (Real.pi * r ^ 2)) (𝓝[>] 0) (𝓝 d) ∧
    ∀ ε : ℝ, 0 < ε → Tendsto (fun r : ℝ =>
      μ.real (ball x r \ normalPlaneCone x ν ε) / μ.real (ball x r)) (𝓝[>] 0) (𝓝 0)
  let ν (x : AmbientSpace) : AmbientSpace := if hx : ∃ v, P x v then hx.choose else 0
  have hv : ∀ᵐ x ∂μ, P x (ν x) := by
    filter_upwards [h] with x hx
    change ∃ v, P x v at hx
    simp only [ν, dite_eq_left hx]
    exact hx.choose_spec
  apply rectifiability_of_density_and_cone μ ν
  · exact hv.mono fun x hx => hx.1
  · filter_upwards [hv] with x hx
    obtain ⟨d, hd, hden, hcone⟩ := hx.2
    refine ⟨d * Real.pi, mul_pos hd Real.pi_pos, ?_⟩
    have ht := hden.mul_const Real.pi
    apply ht.congr'
    filter_upwards [self_mem_nhdsWithin] with r hr
    change 0 < r at hr
    field_simp [Real.pi_ne_zero, hr.ne']
  · exact hv.mono fun x hx => hx.2.choose_spec.2.2 (1 / 8) (by norm_num)

/-- A canonical locally finite perimeter measure is carried by countably many
rotated one-Lipschitz graphs. This assertion precedes Hausdorff-measure identification. -/
theorem canonicalPerimeterMeasure_carried_by_graphs (E : Set AmbientSpace)
    (hE : HasLocallyFinitePerimeter E) (hmE : NullMeasurableSet E volume) :
    ∃ (e : ℕ → AmbientSpace ≃ₗᵢ[ℝ] AmbientSpace)
      (f : ℕ → EuclideanSpace ℝ (Fin 2) → ℝ),
      (∀ j, LipschitzWith 1 (f j)) ∧
      canonicalPerimeterMeasure E hE hmE
        (⋃ j, range (fun p => e j (graphMapN (f j) p)))ᶜ = 0 := by
  let := (canonicalPerimeterPolar E hE hmE).finiteOnCompacts
  apply rectifiability_criterion
  filter_upwards [ae_mem_reducedBoundary E hE hmE] with x hx
  exact ⟨reducedNormal E hE hmE x, norm_reducedNormal E hE hmE hx,
    1, zero_lt_one, exact_perimeter_density E hE hmE hx,
    fun ε hε => cone_concentration E hE hmE hx hε⟩

end LiquidDrop

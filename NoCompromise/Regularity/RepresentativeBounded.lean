import NoCompromise.Regularity.RepresentativeBoundary
import Mathlib.MeasureTheory.Measure.Regular

/-! # Boundedness of the finite-volume canonical representative -/

noncomputable section
open MeasureTheory Set Filter Metric
open scoped ENNReal Topology
namespace LiquidDrop

/-- Every point of the density-one phase has a uniform positive amount of
that phase in its unit ball, including points far from the boundary. -/
theorem IsOmegaMinimal.unit_ball_volume_lower {E : Set AmbientSpace} {ω : ℝ}
    (hE : IsOmegaMinimal E ω) {x : AmbientSpace} (hx : x ∈ densityOne E) :
    quasiminimalDensityConstant ω / 8 ≤ radialVolume E x 1 := by
  by_cases hb : ∃ z ∈ ball x (1 / 2 : ℝ), z ∈ essentialBoundary E
  · obtain ⟨z, hz, hzE⟩ := hb
    have hl := (hE.two_sided_density_explicit hzE (by norm_num : (0 : ℝ) ≤ 1 / 2)
      (by norm_num : (1 / 2 : ℝ) ≤ 1)).1
    have hsub : ball z (1 / 2 : ℝ) ⊆ ball x 1 := by
      intro y hy
      have ht := dist_triangle y z x
      have hy' : dist y z < 1 / 2 := hy
      have hz' : dist z x < 1 / 2 := hz
      change dist y x < 1
      linarith
    have hm : radialVolume E z (1 / 2) ≤ radialVolume E x 1 :=
      ENNReal.toReal_mono
        ((measure_mono inter_subset_right).trans_lt measure_ball_lt_top).ne
        (measure_mono (inter_subset_inter_right E hsub))
    norm_num at hl
    linarith
  · have hd : Disjoint (ball x (1 / 2 : ℝ)) (essentialBoundary E) := by
      exact disjoint_left.mpr (fun z hz he => hb ⟨z, hz, he⟩)
    have hp := perimeterIn_eq_zero_of_disjoint_essentialBoundary hE.locallyFinite
      hE.nullMeasurable isOpen_ball hd
    have hc := compl_volume_eq_zero_of_zero_perimeter_ball hE.locallyFinite
      hE.nullMeasurable hx (by norm_num : (0 : ℝ) < 1 / 2) hp
    have hball : volume (ball x (1 / 2 : ℝ)) = volume (E ∩ ball x (1 / 2 : ℝ)) := by
      have he : volume (ball x (1 / 2 : ℝ) \ E) = 0 := by
        simpa only [sdiff_eq_compl_inter] using hc
      exact (measure_sdiff_null he).symm.trans (by
        congr 1
        ext z
        simp only [Set.mem_sdiff, mem_inter_iff]
        tauto)
    have hm : (volume (ball x (1 / 2 : ℝ))).toReal ≤ radialVolume E x 1 := by
      rw [hball]
      exact ENNReal.toReal_mono
        ((measure_mono inter_subset_right).trans_lt measure_ball_lt_top).ne
        (measure_mono (inter_subset_inter_right E (ball_subset_ball (by norm_num))))
    rw [volumeReal_ball_three x (by norm_num)] at hm
    have hconst := @quasiminimalDensityConstant_lt ω
    norm_num at hm
    have := Real.pi_pos
    linarith

/-- A finite-volume quasiminimizer has a bounded density-one representative. -/
theorem IsOmegaMinimal.isBounded_densityOne {E : Set AmbientSpace} {ω : ℝ}
    (hE : IsOmegaMinimal E ω) (hV : volume E < ∞) : Bornology.IsBounded (densityOne E) := by
  let m := quasiminimalDensityConstant ω / 8
  have hm : 0 < m := div_pos (quasiminimalDensityConstant_pos hE.nonneg) (by norm_num)
  have heq := densityOne_ae_eq (by norm_num : 0 < 3) hE.nullMeasurable
  have hfin : volume (densityOne E) ≠ ∞ := by rw [measure_congr heq]; exact hV.ne
  obtain ⟨K, _, hK, htail⟩ := hE.isOpen_densityOne.measurableSet.exists_isCompact_sdiff_lt
    hfin (ENNReal.ofReal_ne_zero_iff.mpr hm)
  obtain ⟨R, hR⟩ := Metric.isBounded_iff_subset_ball (0 : AmbientSpace) |>.mp hK.isBounded
  apply (Metric.isBounded_iff_subset_closedBall (0 : AmbientSpace)).mpr
  refine ⟨R + 1, fun x hx => ?_⟩
  by_contra hn
  have hxR : R + 1 < dist x 0 := lt_of_not_ge hn
  have hbK : Disjoint (ball x 1) K := by
    apply disjoint_left.mpr
    intro z hz hzK
    have hz0 : dist z 0 < R := hR hzK
    have hzx : dist z x < 1 := hz
    have ht := dist_triangle x z 0
    rw [dist_comm x z] at ht
    linarith
  have hsub : densityOne E ∩ ball x 1 ⊆ densityOne E \ K := by
    exact fun z hz => ⟨hz.1, fun hzK => disjoint_left.mp hbK hz.2 hzK⟩
  have hsmall : volume (E ∩ ball x 1) < ENNReal.ofReal m := by
    have hm' := (measure_mono hsub).trans_lt htail
    have hcon : (densityOne E ∩ ball x 1 : Set AmbientSpace) =ᵐ[volume]
        (E ∩ ball x 1 : Set AmbientSpace) :=
      heq.inter (EventuallyEq.rfl : ball x 1 =ᵐ[volume] ball x 1)
    rwa [measure_congr hcon] at hm'
  have hbig : ENNReal.ofReal m ≤ volume (E ∩ ball x 1) := by
    apply (ENNReal.ofReal_le_iff_le_toReal
      ((measure_mono inter_subset_right).trans_lt measure_ball_lt_top).ne).mpr
    exact hE.unit_ball_volume_lower hx
  exact (not_lt_of_ge hbig) hsmall

/-- Blueprint `lem:bounded-representative`, including compactness of the
actual topological boundary. -/
theorem quasiminimal_bounded_representative {E : Set AmbientSpace} {ω : ℝ}
    (hE : IsOmegaMinimal E ω) (hV : volume E < ∞) :
    Bornology.IsBounded (densityOne E) ∧ IsCompact (frontier (densityOne E)) := by
  have hb := hE.isBounded_densityOne hV
  exact ⟨hb, hb.isCompact_closure.of_isClosed_subset isClosed_frontier frontier_subset_closure⟩

end LiquidDrop

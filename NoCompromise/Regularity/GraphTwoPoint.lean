module

public import NoCompromise.Regularity.GraphTwoPointGeometry
public import NoCompromise.Regularity.GraphHeightCenters

@[expose] public section

/-! # The actual two-point Lipschitz estimate over the good base

Only the first point needs a good horizontal projection. The estimate applies
to the whole canonical boundary, hence also to its reduced boundary.
-/

noncomputable section
open Set MeasureTheory Filter Metric
open scoped ENNReal Topology
namespace LiquidDrop

theorem graph_two_point_lipschitz_estimate {γ : ℝ} (hγ : 0 < γ) (hγ8 : γ < 1 / 8) :
    ∃ c > 0, ∃ ε > 0, ∀ (E : Set AmbientSpace) (ω : ℝ) (hE : IsOmegaMinimal E ω),
      (0 : AmbientSpace) ∈ frontier (densityOne E) →
      cylindricalExcess E hE.locallyFinite hE.nullMeasurable 0 1
        (EuclideanSpace.single 2 1) + ω ≤ ε →
      ∀ p ∈ frontier (densityOne E) ∩ standardCylinder (1 / 2),
      ∀ q ∈ frontier (densityOne E) ∩ standardCylinder (1 / 2),
      graphProjectionN 2 p ∈ goodExcessBase E hE.locallyFinite hE.nullMeasurable c γ →
      |q 2 - p 2| ≤ γ * dist (graphProjectionN 2 q) (graphProjectionN 2 p) := by
  let τ := γ / 1024
  have hτ : 0 < τ := by dsimp [τ]; positivity
  obtain ⟨εs, hεs, hs⟩ := height_bound hτ
  obtain ⟨εh, hεh, hh⟩ := graph_height_difference (by positivity : 0 < γ / 4)
  let c := εh / (2 * Real.pi * γ ^ 2)
  have hc : 0 < c := by dsimp [c]; positivity
  refine ⟨c, hc, min εs (min (εh / 2) 1),
    lt_min hεs (lt_min (by positivity) (by norm_num)), ?_⟩
  intro E ω hE h0 he p hp q hq hg
  have heS : cylindricalExcess E hE.locallyFinite hE.nullMeasurable 0 1
      (EuclideanSpace.single 2 1) + ω * 1 ≤ εs := by
    simpa only [mul_one] using he.trans (min_le_left _ _)
  have hω : ω ≤ εh / 2 := by
    have hn := normalExcessIntegral_nonneg E hE.locallyFinite hE.nullMeasurable
      (cylinder 0 1 (EuclideanSpace.single 2 1)) (EuclideanSpace.single 2 1)
    have hb := he.trans ((min_le_right _ _).trans (min_le_left _ _))
    simp only [cylindricalExcess, one_pow, div_one] at hb
    linarith
  have hsub : standardCylinder (1 / 2) ⊆ standardCylinder (3 * (1 : ℝ) / 4) := by
    rw [standardCylinder_eq_cylinder, standardCylinder_eq_cylinder]
    exact cylinder_mono (by norm_num)
  have hpτ : |p 2| < τ := by
    simpa only [mul_one] using hs E ω hE h0 1 (by norm_num) le_rfl heS p ⟨hp.1, hsub hp.2⟩
  have hqτ : |q 2| < τ := by
    simpa only [mul_one] using hs E ω hE h0 1 (by norm_num) le_rfl heS q ⟨hq.1, hsub hq.2⟩
  let d := dist (graphProjectionN 2 q) (graphProjectionN 2 p)
  let h := |q 2 - p 2|
  have hd : 0 ≤ d := dist_nonneg
  have hsmall : h < 2 * τ := by
    have ht : |q 2 - p 2| ≤ |q 2| + |p 2| := by
      simpa only [sub_zero, zero_sub, abs_neg] using abs_sub_le (q 2) 0 (p 2)
    dsimp [h]
    linarith
  by_contra hb
  have hbad : γ * d < h := lt_of_not_ge hb
  by_cases hdlarge : (1 / 32 : ℝ) ≤ d
  · have hmul := mul_le_mul_of_nonneg_left hdlarge hγ.le
    dsimp [τ] at hsmall
    nlinarith
  have hdsmall : d < 1 / 32 := lt_of_not_ge hdlarge
  have hhsmall : h < 1 / 32 := by dsimp [τ] at hsmall; linarith
  let r := 2 * max d h
  have hr : 0 < r := graph_two_point_radius_positive hγ hd hbad
  have hr8 : r < 1 / 8 := by have hm := max_lt hdsmall hhsmall; dsimp [r]; linarith
  have hr1 : r ≤ 1 := by linarith
  have hqp : q ∈ cylinder p (3 * r / 4) (EuclideanSpace.single 2 1) :=
    graph_two_point_mem_cylinder p q hγ hbad
  have heP := cylindricalExcess_le_of_good_base E hE.locallyFinite hE.nullMeasurable
    hc.le hp.2 hg hr hr8
  have hcval : Real.pi * c * γ ^ 2 = εh / 2 := by
    dsimp [c]
    field_simp [hγ.ne', Real.pi_ne_zero]
  rw [hcval] at heP
  have hωr : ω * r ≤ εh / 2 :=
    (mul_le_mul_of_nonneg_left hr1 hE.nonneg).trans (by simpa only [mul_one] using hω)
  have hhgt := hh E ω hE p q r hp.1 hq.1 hr hr1 hqp (by linarith)
  exact graph_two_point_height_contradiction hγ (by linarith) hd hbad hhgt

end LiquidDrop

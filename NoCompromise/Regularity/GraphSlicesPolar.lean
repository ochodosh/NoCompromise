module

public import NoCompromise.Regularity.GraphSlicesUniqueness
public import NoCompromise.BV.JumpDisintegration
public import NoCompromise.DeGiorgi.Structure

@[expose] public section

/-! # Directional slice measures and the actual reduced boundary -/

noncomputable section
open Set MeasureTheory Filter Metric
open scoped ENNReal Topology
namespace LiquidDrop
set_option maxSynthPendingDepth 8

/-- The genuine directional derivative and the vertical component of the
canonical outward polar give the same signed pairing on every Borel set. -/
theorem IsDirectionalBVPolar.setIntegral_vertical_eq
    {E : Set AmbientSpace} (hE : HasLocallyFinitePerimeter E)
    (hmE : NullMeasurableSet E volume)
    {τ : Measure AmbientSpace} {s : AmbientSpace → ℝ}
    (h : IsDirectionalBVPolar (E.indicator (fun _ => (1 : ℝ)))
      (EuclideanSpace.single 2 1) τ s)
    {A : Set AmbientSpace} (hA : MeasurableSet A) (q : AmbientSpace → ℝ) :
    (∫ x in A, q x * s x ∂τ) =
      ∫ x in A, q x * (-reducedNormal E hE hmE x 2)
        ∂canonicalPerimeterMeasure E hE hmE := by
  let := h.finiteOnCompacts
  have hp : IsAmbientOutwardPerimeterPolar E (canonicalPerimeterMeasure E hE hmE)
      (reducedNormal E hE hmE) := by
    rw [canonicalPerimeterMeasure_eq_reducedBoundary_area]
    exact reducedBoundary_outwardPerimeterPolar E hE hmE
  let := hp.finiteOnCompacts
  have hi : LocallyIntegrable (fun x => -reducedNormal E hE hmE x 2)
      (canonicalPerimeterMeasure E hE hmE) := by
    apply locallyIntegrable_iff.mpr
    intro K hK
    exact ((EuclideanSpace.proj (𝕜 := ℝ) (2 : Fin 3)).integrable_comp
      (hp.locallyIntegrable.integrableOn_isCompact hK)).neg
  apply setIntegral_mul_eq_of_scalar_pairings isOpen_univ h.locallyIntegrable_density hi
    (fun φ hφ _ => (h.test_eq φ hφ φ.hasCompactSupport).symm.trans
      (hp.coordinate_eq 2 φ hφ)) hA (subset_univ _) q

/-- No actual vertical derivative mass lies outside the genuine reduced
boundary. This follows from signed-pairing uniqueness, not a slice-structure premise. -/
theorem IsDirectionalBVPolar.measure_compl_reducedBoundary_eq_zero
    {E : Set AmbientSpace} (hE : HasLocallyFinitePerimeter E)
    (hmE : NullMeasurableSet E volume)
    {τ : Measure AmbientSpace} {s : AmbientSpace → ℝ}
    (h : IsDirectionalBVPolar (E.indicator (fun _ => (1 : ℝ)))
      (EuclideanSpace.single 2 1) τ s) :
    τ (reducedBoundary E hE hmE)ᶜ = 0 := by
  let := h.finiteOnCompacts
  have hm := measurableSet_reducedBoundary E hE hmE
  have hz : canonicalPerimeterMeasure E hE hmE (reducedBoundary E hE hmE)ᶜ = 0 :=
    (ae_iff.mp (ae_mem_reducedBoundary E hE hmE))
  have hball (j : ℕ) : τ ((reducedBoundary E hE hmE)ᶜ ∩ ball 0 (j : ℝ)) = 0 := by
    let A := (reducedBoundary E hE hmE)ᶜ ∩ ball 0 (j : ℝ)
    have hA : MeasurableSet A := hm.compl.inter measurableSet_ball
    have hτA : τ A ≠ ∞ := ne_top_of_le_ne_top
      (measure_ball_lt_top (μ := τ) (x := (0 : AmbientSpace)) (r := j)).ne
      (measure_mono inter_subset_right)
    have hμA : canonicalPerimeterMeasure E hE hmE A = 0 :=
      measure_mono_null inter_subset_left hz
    have he := h.setIntegral_vertical_eq hE hmE hA s
    have hl : (∫ x in A, s x * s x ∂τ) = (τ A).toReal := by
      calc
        _ = ∫ _ in A, (1 : ℝ) ∂τ := integral_congr_ae (by
          filter_upwards [ae_restrict_of_ae h.norm_ae] with x hx
          nlinarith [sq_abs (s x)])
        _ = _ := by simp [Measure.real]
    rw [hl, Measure.restrict_eq_zero.mpr hμA, integral_zero_measure] at he
    exact (ENNReal.toReal_eq_zero_iff _).mp he |>.resolve_right hτA
  have hu : (reducedBoundary E hE hmE)ᶜ =
      ⋃ j : ℕ, (reducedBoundary E hE hmE)ᶜ ∩ ball 0 (j : ℝ) := by
    rw [← inter_iUnion, iUnion_ball_nat, inter_univ]
  rw [hu]
  exact measure_iUnion_null hball

end LiquidDrop

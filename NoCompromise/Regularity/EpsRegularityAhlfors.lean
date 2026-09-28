import NoCompromise.Regularity.LimitingNormal
import NoCompromise.Regularity.DensityAhlfors
import NoCompromise.Regularity.ExcessDecayCoordinates
import NoCompromise.DeGiorgi.BlowupCompactness

/-!
# Uniform Ahlfors lower bound and two-centre normal comparison

Step 4 of `thm:eps-regularity`. A quasiminimal set has reduced-boundary area at
least `c s ^ 2` in every ball of radius `s ≤ 1` about a point of the
density-one frontier, provided `ω s ≤ 1`, with `c` independent of the set.
Consequently two unit axes that both have small cylindrical excess at nearby
centres and a common scale are close.
-/

noncomputable section
open Set MeasureTheory Filter Metric
open scoped Topology ENNReal
namespace LiquidDrop

/-- Quasiminimality is monotone in the error constant. -/
lemma IsOmegaMinimal.mono_omega {n : ℕ} {E : Set (EuclideanSpace ℝ (Fin n))} {ω ω' : ℝ}
    (hE : IsOmegaMinimal E ω) (h : ω ≤ ω') : IsOmegaMinimal E ω' := by
  refine ⟨hE.nonneg.trans h, hE.scale_pos, hE.nullMeasurable, hE.locallyFinite, ?_⟩
  intro x r hr hrr F hmF hpF hc hs
  exact (hE.comparison x r hr hrr F hmF hpF hc hs).trans
    (add_le_add le_rfl (mul_le_mul' (ENNReal.ofReal_le_ofReal h) le_rfl))

/-- Uniform lower area bound for the reduced boundary at all scales `s ≤ 1`
with `ω s ≤ 1`, about points of the density-one frontier. -/
theorem reducedBoundary_area_lower_uniform :
    ∃ c : ℝ, 0 < c ∧ ∀ (E : Set AmbientSpace) (ω : ℝ) (hE : IsOmegaMinimal E ω)
      (x : AmbientSpace) (s : ℝ), x ∈ frontier (densityOne E) → 0 < s → s ≤ 1 → ω * s ≤ 1 →
      c * s ^ 2 ≤ ((hausdorffMeasure2 3).restrict
        (reducedBoundary E hE.locallyFinite hE.nullMeasurable)).real (ball x s) := by
  obtain ⟨c, hc, hlow⟩ := quasiminimal_perimeter_lower_bound 1 zero_le_one
  refine ⟨c, hc, ?_⟩
  intro E ω hE x s hx hs hs1 hωs
  have hB : IsOmegaMinimal (blowupSet E x s) (ω * s) := by
    apply IsOmegaMinimalAtScales.blowupSet hE x hs (by norm_num)
    simpa only [mul_one, ENNReal.ofReal_one] using ENNReal.ofReal_le_ofReal hs1
  have hB1 : IsOmegaMinimal (blowupSet E x s) 1 := hB.mono_omega hωs
  have h0 : (0 : AmbientSpace) ∈ essentialBoundary (blowupSet E x s) := by
    rw [← hB1.frontier_densityOne, mem_frontier_densityOne_blowupSet E x 0 hs]
    simpa only [smul_zero, add_zero] using hx
  have h1 := hlow _ hB1 0 h0 1 one_pos le_rfl
  rw [perimeterIn_blowupSet_ball_real E hE.locallyFinite hE.nullMeasurable x hs 1, mul_one,
    canonicalPerimeterMeasure_eq_reducedBoundary_area] at h1
  have hs2 : 0 < s ^ 2 := by positivity
  calc
    c * s ^ 2 = s ^ 2 * (c * 1 ^ 2) := by ring
    _ ≤ s ^ 2 * ((s⁻¹) ^ 2 * ((hausdorffMeasure2 3).restrict
        (reducedBoundary E hE.locallyFinite hE.nullMeasurable)).real (ball x s)) :=
      mul_le_mul_of_nonneg_left h1 hs2.le
    _ = _ := by field_simp

/-- Pointwise comparison of two axes through the reduced normal, integrated over
a common measurable subregion of two bounded regions. -/
theorem sq_norm_sub_mul_area_le_excess (E : Set AmbientSpace)
    (hE : HasLocallyFinitePerimeter E) (hmE : NullMeasurableSet E volume)
    {U V B : Set AmbientSpace} (hU : Bornology.IsBounded U) (hV : Bornology.IsBounded V)
    (hBU : B ⊆ U) (hBV : B ⊆ V) (hB : MeasurableSet B) (a b : AmbientSpace) :
    ‖a - b‖ ^ 2 * ((hausdorffMeasure2 3).restrict (reducedBoundary E hE hmE)).real B ≤
      2 * normalExcessIntegral E hE hmE U a + 2 * normalExcessIntegral E hE hmE V b := by
  set μ := (hausdorffMeasure2 3).restrict (reducedBoundary E hE hmE) with hμ
  have hBb : Bornology.IsBounded B := hU.subset hBU
  have hia := integrableOn_normal_excess E hE hmE hBb a
  have hib := integrableOn_normal_excess E hE hmE hBb b
  have hpt : ∀ y, ‖a - b‖ ^ 2 ≤ 2 * ‖reducedNormal E hE hmE y - a‖ ^ 2 +
      2 * ‖reducedNormal E hE hmE y - b‖ ^ 2 := by
    intro y
    set ν := reducedNormal E hE hmE y
    have htri : ‖a - b‖ ≤ ‖ν - b‖ + ‖ν - a‖ := by
      have := norm_sub_le (ν - b) (ν - a)
      rwa [show ν - b - (ν - a) = a - b by abel] at this
    have h0 : 0 ≤ ‖a - b‖ := norm_nonneg _
    nlinarith [sq_nonneg (‖ν - a‖ - ‖ν - b‖), norm_nonneg (ν - a), norm_nonneg (ν - b)]
  have hint : ∫ y in B, ‖a - b‖ ^ 2 ∂μ ≤
      ∫ y in B, (2 * ‖reducedNormal E hE hmE y - a‖ ^ 2 +
        2 * ‖reducedNormal E hE hmE y - b‖ ^ 2) ∂μ :=
    integral_mono_of_nonneg (Eventually.of_forall (fun _ => sq_nonneg _))
      ((hia.const_mul 2).add (hib.const_mul 2)) (Eventually.of_forall hpt)
  rw [setIntegral_const, smul_eq_mul, mul_comm, integral_add (hia.const_mul 2)
    (hib.const_mul 2), integral_const_mul, integral_const_mul] at hint
  have hma := normalExcessIntegral_mono E hE hmE hU hBU a
  have hmb := normalExcessIntegral_mono E hE hmE hV hBV b
  exact hint.trans (add_le_add (mul_le_mul_of_nonneg_left hma zero_le_two)
    (mul_le_mul_of_nonneg_left hmb zero_le_two))

/-- Blueprint `thm:eps-regularity`, Step 4: two unit axes with small cylindrical
excess at nearby centres and a common admissible scale are close. -/
theorem normals_two_centre_comparison :
    ∃ K : ℝ, 0 < K ∧ ∀ (E : Set AmbientSpace) (ω : ℝ) (hE : IsOmegaMinimal E ω)
      (x y a b : AmbientSpace) (s : ℝ), x ∈ frontier (densityOne E) →
      0 < s → s ≤ 1 → ω * s ≤ 1 → ‖a‖ = 1 → ‖b‖ = 1 → ‖x - y‖ ≤ s / 4 →
      ‖a - b‖ ^ 2 ≤ K * (cylindricalExcess E hE.locallyFinite hE.nullMeasurable x s a +
        cylindricalExcess E hE.locallyFinite hE.nullMeasurable y s b) := by
  obtain ⟨c, hc, hlow⟩ := reducedBoundary_area_lower_uniform
  refine ⟨8 / c, by positivity, ?_⟩
  intro E ω hE x y a b s hx hs hs1 hωs ha hb hxy
  have hBU : ball x (s / 2) ⊆ cylinder x s a :=
    (ball_subset_ball (by linarith)).trans (ball_subset_cylinder x s ha)
  have hBV : ball x (s / 2) ⊆ cylinder y s b := by
    refine (ball_subset_ball' ?_).trans (ball_subset_cylinder y s hb)
    rw [dist_eq_norm]
    linarith
  have hω0 : 0 ≤ ω := hE.nonneg
  have hlowB := hlow E ω hE x (s / 2) hx (by positivity) (by linarith)
    (by nlinarith)
  have hcmp := sq_norm_sub_mul_area_le_excess E hE.locallyFinite hE.nullMeasurable
    (isBounded_cylinder x s ha) (isBounded_cylinder y s hb) hBU hBV measurableSet_ball a b
  unfold cylindricalExcess
  set m := ((hausdorffMeasure2 3).restrict
    (reducedBoundary E hE.locallyFinite hE.nullMeasurable)).real (ball x (s / 2))
  set Nx := normalExcessIntegral E hE.locallyFinite hE.nullMeasurable (cylinder x s a) a
  set Ny := normalExcessIntegral E hE.locallyFinite hE.nullMeasurable (cylinder y s b) b
  have hs2 : 0 < s ^ 2 := by positivity
  have hkey : ‖a - b‖ ^ 2 * (c * (s / 2) ^ 2) ≤ ‖a - b‖ ^ 2 * m :=
    mul_le_mul_of_nonneg_left hlowB (sq_nonneg _)
  rw [show 8 / c * (Nx / s ^ 2 + Ny / s ^ 2) = 8 * (Nx + Ny) / (c * s ^ 2) by
    field_simp, le_div_iff₀ (by positivity)]
  nlinarith

end LiquidDrop

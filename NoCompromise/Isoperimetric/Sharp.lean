import NoCompromise.BV.SmoothApprox

/-!
# The sharp isoperimetric inequality from the smooth case

Blueprint `thm:sharp-isoperimetric`: its proof applies
`cor:iso-smooth-components` to the smooth exact-volume approximants of
`thm:smooth-approx` and passes to the limit. The limit passage is proved here
in full; the smooth bounded case (`cor:iso-smooth-components`) enters as the
named predicate `SmoothIsoperimetric`.
-/

noncomputable section
open MeasureTheory Set Filter
open scoped ENNReal Topology
namespace LiquidDrop

/-- The conclusion of blueprint `cor:iso-smooth-components`, second inequality, for every
bounded open set with smooth boundary: `P(S) ≥ (36π)^{1/3} |S|^{2/3}`. -/
def SmoothIsoperimetric : Prop :=
  ∀ S : Set AmbientSpace, IsOpen S → Bornology.IsBounded S → HasSmoothBoundary S →
    ENNReal.ofReal ((36 * Real.pi) ^ (1 / (3 : ℝ)) * (volume S).toReal ^ (2 / (3 : ℝ)))
      ≤ perimeter S

/-- Blueprint `thm:sharp-isoperimetric`, from the smooth bounded case
(`cor:iso-smooth-components`) and `thm:smooth-approx`. -/
theorem sharp_isoperimetric_of_smooth (h : SmoothIsoperimetric) {E : Set AmbientSpace}
    (hE : NullMeasurableSet E volume) (hfin : volume E < ∞) :
    ENNReal.ofReal ((36 * Real.pi) ^ (1 / (3 : ℝ)) * (volume E).toReal ^ (2 / (3 : ℝ)))
      ≤ perimeter E := by
  rcases eq_or_ne (volume E) 0 with h0 | hpos
  · rw [h0, ENNReal.toReal_zero, Real.zero_rpow (by norm_num), mul_zero,
      ENNReal.ofReal_zero]
    exact bot_le
  rcases eq_or_ne (perimeter E) ∞ with htop | hper
  · rw [htop]
    exact le_top
  have hfp : HasFinitePerimeter E := by
    change perimeterN E < ∞
    rw [perimeterN_eq_perimeter E hE]
    exact lt_top_iff_ne_top.mpr hper
  obtain ⟨S, hS, -, hlim⟩ :=
    smooth_approximation_exact_volume hE hfin (pos_iff_ne_zero.mpr hpos) hfp
  refine ge_of_tendsto hlim (Eventually.of_forall fun j => ?_)
  have hj := h (S j) (hS j).1 (hS j).2.1 (hS j).2.2.1
  rwa [(hS j).2.2.2] at hj

end LiquidDrop

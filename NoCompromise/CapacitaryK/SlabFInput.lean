import NoCompromise.CapacitaryK.SlabCoarea

/-!
# Integrability of `∇w·∇u` on slabs (chapter 31, input to `lem:K-slab-F`)

`|⟪∇w, ∇u⟫| ≤ |D²u| w` on the regular set (`fderiv_gradNorm_apply`), and `⟪∇w, ∇u⟫ = 0` where
`∇u = 0`, so `∇w·∇u` is bounded on any set with compact closure inside the open set where `u`
is `C²`; hence it is integrable there. This supplies the hypothesis `hint` of `K_slab_F_coarea`.
-/

noncomputable section
open MeasureTheory Filter Set InnerProductSpace
open scoped Topology Gradient RealInnerProductSpace

namespace LiquidDrop.CapacitaryK

/-- `|⟪∇w, ∇u⟫| ≤ ‖D(∇u)‖ w` at every point where `u` is `C²`. -/
lemma abs_inner_gradient_gradNorm_le {u : E3 → ℝ} {x : E3} (hu : ContDiffAt ℝ 2 u x) :
    |⟪gradient (gradNorm u) x, gradient u x⟫| ≤
      ‖fderiv ℝ (gradient u) x‖ * gradNorm u x := by
  rcases (gradNorm_nonneg u x).lt_or_eq with hw | hw
  · rw [inner_gradient_eq_fderiv, fderiv_gradNorm_apply hu hw, dirHess_eq_inner hu,
      abs_mul, abs_inv, abs_of_pos hw]
    have h1 : |⟪fderiv ℝ (gradient u) x (gradient u x), gradient u x⟫| ≤
        ‖fderiv ℝ (gradient u) x‖ * gradNorm u x * gradNorm u x := by
      refine (abs_real_inner_le_norm _ _).trans ?_
      have := (fderiv ℝ (gradient u) x).le_opNorm (gradient u x)
      simp only [gradNorm] at *
      nlinarith [norm_nonneg (gradient u x)]
    rw [inv_mul_le_iff₀ hw]
    nlinarith [h1]
  · have hz : gradient u x = 0 := norm_eq_zero.mp (by simpa [gradNorm] using hw.symm)
    rw [hz, inner_zero_right, abs_zero]
    exact mul_nonneg (norm_nonneg _) (gradNorm_nonneg u x)

/-- `∇w·∇u` is integrable on a measurable set with compact closure in the open set where `u`
is `C³`. -/
theorem integrableOn_inner_gradient_gradNorm {U : Set E3} (hU : IsOpen U) {u : E3 → ℝ}
    (hu : ContDiffOn ℝ 3 u U) {S : Set E3} (hS : MeasurableSet S)
    (hK : IsCompact (closure S)) (hSU : closure S ⊆ U) :
    IntegrableOn (fun x => ⟪gradient (gradNorm u) x, gradient u x⟫) S := by
  have hgrad : ContDiffOn ℝ 2 (gradient u) U := by
    have hf : ContDiffOn ℝ 2 (fderiv ℝ u) U := hu.fderiv_of_isOpen hU (by norm_num)
    have : gradient u = fun x => (toDual ℝ E3).symm (fderiv ℝ u x) := rfl
    rw [this]
    exact (toDual ℝ E3).symm.toContinuousLinearEquiv.contDiff.comp_contDiffOn hf
  have hM : ContinuousOn (fun x => ‖fderiv ℝ (gradient u) x‖ * gradNorm u x) U :=
    ((hgrad.continuousOn_fderiv_of_isOpen hU (by norm_num)).norm).mul
      (hgrad.continuousOn.norm)
  obtain ⟨C, hC⟩ := hK.exists_bound_of_continuousOn (hM.mono hSU)
  have hmeasG : Measurable (gradient u) :=
    (toDual ℝ E3).symm.continuous.measurable.comp (measurable_fderiv ℝ u)
  have hmeasW : Measurable (gradient (gradNorm u)) :=
    (toDual ℝ E3).symm.continuous.measurable.comp (measurable_fderiv ℝ (gradNorm u))
  have hfin : volume S < ⊤ :=
    (measure_mono subset_closure).trans_lt hK.measure_lt_top
  refine Measure.integrableOn_of_bounded (M := C) hfin.ne
    (hmeasW.inner hmeasG).aestronglyMeasurable ?_
  filter_upwards [ae_restrict_mem hS] with x hx
  have hxU : x ∈ U := hSU (subset_closure hx)
  have hb := abs_inner_gradient_gradNorm_le
    ((hu.contDiffAt (hU.mem_nhds hxU)).of_le (by norm_num))
  have hc := hC x (subset_closure hx)
  rw [Real.norm_eq_abs] at hc ⊢
  exact hb.trans ((le_abs_self _).trans hc)

end LiquidDrop.CapacitaryK

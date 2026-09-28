import NoCompromise.Measure.BallAverages

/-!
# Elementary radial measure facts

Almost every sphere is null for a locally finite measure. Ball integrals of
locally integrable fields tend to zero at radius zero when the center is not
an atom. No density theorem, coarea formula, or doubling assumption is used.
-/

noncomputable section
open MeasureTheory Set Filter Metric
open scoped Topology ENNReal
namespace LiquidDrop

lemma ae_measure_sphere_eq_zero {n : ℕ}
    (μ : Measure (EuclideanSpace ℝ (Fin n))) [SFinite μ]
    (a : EuclideanSpace ℝ (Fin n)) : ∀ᵐ r : ℝ, μ (sphere a r) = 0 := by
  have hc := Measure.countable_meas_level_set_pos (μ := μ) (g := fun x => dist x a)
    (continuous_id.dist continuous_const).measurable
  have hn := hc.measure_zero (μ := (volume : Measure ℝ))
  have hae : ∀ᵐ r : ℝ, ¬0 < μ {x | dist x a = r} := by
    apply ae_iff.mpr
    simpa only [not_not] using hn
  filter_upwards [hae] with r hr
  exact nonpos_iff_eq_zero.mp (le_of_not_gt hr)

/-- Ball integrals tend to zero at a center with zero singleton mass. -/
lemma tendsto_integral_ball_zero {n m : ℕ}
    (μ : Measure (EuclideanSpace ℝ (Fin n)))
    {f : EuclideanSpace ℝ (Fin n) → EuclideanSpace ℝ (Fin m)}
    (hf : Measurable f) (hi : LocallyIntegrable f μ)
    (a : EuclideanSpace ℝ (Fin n)) (ha : μ {a} = 0) :
    Tendsto (fun r : ℝ => ∫ x in ball a r, f x ∂μ) (𝓝 0) (𝓝 0) := by
  have hib : Integrable ((closedBall a 1).indicator (fun x => ‖f x‖)) μ :=
    (integrable_indicator_iff isClosed_closedBall.measurableSet).mpr
      (hi.integrableOn_isCompact (isCompact_closedBall a 1)).norm
  have ht : Tendsto (fun r : ℝ => ∫ x, (ball a r).indicator f x ∂μ) (𝓝 0)
      (𝓝 (∫ _ : EuclideanSpace ℝ (Fin n), (0 : EuclideanSpace ℝ (Fin m)) ∂μ)) := by
    apply tendsto_integral_filter_of_dominated_convergence
      ((closedBall a 1).indicator (fun x => ‖f x‖))
    · exact Eventually.of_forall fun r => (hf.indicator measurableSet_ball).aestronglyMeasurable
    · filter_upwards [eventually_lt_nhds (by norm_num : (0 : ℝ) < 1)] with r hr
      apply Eventually.of_forall
      intro x
      by_cases hx : x ∈ ball a r
      · rw [indicator_of_mem hx,
          indicator_of_mem ((ball_subset_closedBall.trans (closedBall_subset_closedBall hr.le)) hx)]
      · rw [indicator_of_notMem hx, norm_zero]
        exact indicator_nonneg (fun _ _ => norm_nonneg _) _
    · exact hib
    · have hae : ∀ᵐ x ∂μ, x ≠ a := by
        simpa only [mem_singleton_iff] using (measure_eq_zero_iff_ae_notMem.mp ha)
      filter_upwards [hae] with x hx
      have hd : 0 < dist x a := dist_pos.mpr hx
      have heq : ∀ᶠ r : ℝ in 𝓝 0, (ball a r).indicator f x = 0 := by
        filter_upwards [eventually_lt_nhds hd] with r hr
        exact indicator_of_notMem (show x ∉ ball a r from
          fun h => (not_lt_of_ge hr.le) h) f
      exact (tendsto_const_nhds (x := (0 : EuclideanSpace ℝ (Fin m)))).congr'
        (heq.mono fun _ h => h.symm)
  simpa only [integral_indicator measurableSet_ball, integral_zero] using ht

end LiquidDrop

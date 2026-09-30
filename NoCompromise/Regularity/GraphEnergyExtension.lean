module

public import NoCompromise.Regularity.GraphLoss
public import NoCompromise.Sobolev.Extension

@[expose] public section

/-! # The Dirichlet cost of extending across the omitted base -/

noncomputable section
open Set MeasureTheory Filter Metric
open scoped ENNReal NNReal Topology Gradient
namespace LiquidDrop

lemma integrableOn_sq_gradient_of_lipschitz {f : EuclideanSpace ℝ (Fin 2) → ℝ}
    {K : ℝ≥0} (hf : LipschitzWith K f) {A : Set (EuclideanSpace ℝ (Fin 2))}
    (hA : volume A < ∞) : IntegrableOn (fun x => ‖gradient f x‖ ^ 2) A volume := by
  let : IsFiniteMeasure (volume.restrict A) := ⟨by simpa using hA⟩
  apply (integrable_const ((K : ℝ) ^ 2)).mono'
    ((measurable_gradient f).norm.pow_const 2).aestronglyMeasurable
  filter_upwards [] with x
  rw [Real.norm_eq_abs, abs_of_nonneg (sq_nonneg _)]
  exact sq_le_sq₀ (norm_nonneg _) K.coe_nonneg |>.mpr (norm_gradient_le_of_lipschitz hf x)

lemma integral_sq_gradient_le_lipschitz_mul_volume {f : EuclideanSpace ℝ (Fin 2) → ℝ}
    {K : ℝ≥0} (hf : LipschitzWith K f) {A : Set (EuclideanSpace ℝ (Fin 2))}
    (hA : volume A < ∞) :
    (∫ x in A, ‖gradient f x‖ ^ 2) ≤ (K : ℝ) ^ 2 * volume.real A := by
  let : IsFiniteMeasure (volume.restrict A) := ⟨by simpa using hA⟩
  calc
    _ ≤ ∫ _ in A, (K : ℝ) ^ 2 := integral_mono_ae
      (integrableOn_sq_gradient_of_lipschitz hf hA) (integrable_const _) (by
        filter_upwards [] with x
        exact sq_le_sq₀ (norm_nonneg _) K.coe_nonneg |>.mpr (norm_gradient_le_of_lipschitz hf x))
    _ = _ := by simp [mul_comm]

/-- The global gradient integral splits into its actual good-base integral
and an extension cost bounded by γ² times the omitted base area. -/
theorem HasGraphCapPhases.graph_extension_energy
    {E : Set AmbientSpace} (h : HasGraphCapPhases E)
    (hE : HasLocallyFinitePerimeter E) (hmE : NullMeasurableSet E volume)
    {c γ : ℝ} (hc : 0 < c) (hγ : 0 < γ)
    (hG : MeasurableSet (graphGoodBase E hE hmE c γ))
    {f : EuclideanSpace ℝ (Fin 2) → ℝ} (hf : LipschitzWith ⟨γ, hγ.le⟩ f) :
    (∫ x in ball (0 : EuclideanSpace ℝ (Fin 2)) (1 / 2), ‖gradient f x‖ ^ 2) ≤
      (∫ x in graphGoodBase E hE hmE c γ, ‖gradient f x‖ ^ 2) +
        (25 / c) * cylindricalExcess E hE hmE 0 1 (EuclideanSpace.single 2 1) := by
  let A := ball (0 : EuclideanSpace ℝ (Fin 2)) (1 / 2)
  let G := graphGoodBase E hE hmE c γ
  have hA : volume A < ∞ := isBounded_ball.measure_lt_top
  have hGA : G ⊆ A := graphGoodBase_subset_ball E hE hmE c γ
  have he := setIntegral_sdiff hG (integrableOn_sq_gradient_of_lipschitz hf hA) hGA
  have hb := integral_sq_gradient_le_lipschitz_mul_volume hf
    ((measure_mono (sdiff_subset : A \ G ⊆ A)).trans_lt hA)
  have hm := mul_le_mul_of_nonneg_left (h.goodBase_real_measure_bound hE hmE hc hγ)
    (sq_nonneg γ)
  have hcval : γ ^ 2 * ((25 / (c * γ ^ 2)) *
      cylindricalExcess E hE hmE 0 1 (EuclideanSpace.single 2 1)) =
      (25 / c) * cylindricalExcess E hE hmE 0 1 (EuclideanSpace.single 2 1) := by
    field_simp [hγ.ne', hc.ne']
  rw [hcval] at hm
  change (∫ x in A, ‖gradient f x‖ ^ 2) ≤ (∫ x in G, ‖gradient f x‖ ^ 2) + _
  change (∫ x in A \ G, ‖gradient f x‖ ^ 2) ≤ γ ^ 2 * volume.real (A \ G) at hb
  change γ ^ 2 * volume.real (A \ G) ≤ _ at hm
  linarith

end LiquidDrop

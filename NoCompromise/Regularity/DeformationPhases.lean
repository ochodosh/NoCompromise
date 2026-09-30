module

public import NoCompromise.Regularity.DeformationCompression
public import NoCompromise.Regularity.DeformationExtensionPhases

@[expose] public section

/-! # The genuine compressed set retains the prescribed phases -/

noncomputable section
open Set MeasureTheory Filter
namespace LiquidDrop

lemma quasiMeasurePreserving_symm_of_differentiable
    (Φ : AmbientSpace ≃ₜ AmbientSpace) (hΦ : Differentiable ℝ Φ) :
    Measure.QuasiMeasurePreserving Φ.symm volume volume := by
  refine ⟨Φ.symm.measurable, Measure.AbsolutelyContinuous.mk ?_⟩
  intro S hS hz
  rw [Measure.map_apply Φ.symm.measurable hS, Φ.preimage_symm]
  exact addHaar_image_eq_zero_of_differentiableOn_of_addHaar_eq_zero volume
    hΦ.differentiableOn hz

lemma indicator_image_homeomorph (Φ : AmbientSpace ≃ₜ AmbientSpace)
    (E : Set AmbientSpace) (y : AmbientSpace) :
    (Φ '' E).indicator (fun _ => (1 : ℝ)) y =
      E.indicator (fun _ => (1 : ℝ)) (Φ.symm y) := by
  have he : y ∈ Φ '' E ↔ Φ.symm y ∈ E := by
    constructor
    · rintro ⟨x, hx, rfl⟩
      simpa only [Φ.symm_apply_apply] using hx
    · intro hy
      exact ⟨Φ.symm y, hy, Φ.apply_symm_apply y⟩
  by_cases hy : Φ.symm y ∈ E
  · rw [indicator_of_mem (he.mpr hy), indicator_of_mem hy]
  · rw [indicator_of_notMem (mt he.mp hy), indicator_of_notMem hy]

lemma compression_inverse_height_lt {β : EuclideanSpace ℝ (Fin 2) → ℝ}
    {c δ : ℝ} {y : AmbientSpace} (hb : 0 < β (graphProjectionN 2 y))
    (hy : y 2 < c - β (graphProjectionN 2 y) * δ) :
    verticalCompression (fun p => (β p)⁻¹) c y 2 < c - δ := by
  rw [verticalCompression_height]
  have hh : (y 2 - c) / β (graphProjectionN 2 y) < -δ :=
    (div_lt_iff₀ hb).mpr (by nlinarith [hy])
  simpa only [div_eq_mul_inv, mul_comm, sub_eq_add_neg, add_comm] using add_lt_add_left hh c

lemma compression_inverse_height_gt {β : EuclideanSpace ℝ (Fin 2) → ℝ}
    {c δ : ℝ} {y : AmbientSpace} (hb : 0 < β (graphProjectionN 2 y))
    (hy : c + β (graphProjectionN 2 y) * δ < y 2) :
    c + δ < verticalCompression (fun p => (β p)⁻¹) c y 2 := by
  rw [verticalCompression_height]
  have hh : δ < (y 2 - c) / β (graphProjectionN 2 y) :=
    (lt_div_iff₀ hb).mpr (by nlinarith [hy])
  simpa only [div_eq_mul_inv, mul_comm, add_comm] using add_lt_add_left hh c

/-- The transformed indicator is exactly in its prescribed phase away from
the compressed slab, up to ambient volume null sets. -/
theorem IsSlabCapConfiguration.compressed_extension_phases
    {E : Set AmbientSpace} {hE : HasLocallyFinitePerimeter E}
    {hmE : NullMeasurableSet E volume} {r c η : ℝ}
    (h : IsSlabCapConfiguration E hE hmE r c η)
    {σ τ ε : ℝ} (hσ : 0 < σ) (hst : σ < τ) (hε : 0 < ε) (hε1 : ε ≤ 1) :
    ∀ᵐ y : AmbientSpace ∂volume,
      (‖graphProjectionN 2 y‖ < r →
        y 2 < c - compressionBeta σ τ ε (graphProjectionN 2 y) * (η * r) →
        (verticalCompression (compressionBeta σ τ ε) c '' verticalPhaseExtension E r).indicator
          (fun _ => (1 : ℝ)) y = 1) ∧
      (‖graphProjectionN 2 y‖ < r →
        c + compressionBeta σ τ ε (graphProjectionN 2 y) * (η * r) < y 2 →
        (verticalCompression (compressionBeta σ τ ε) c '' verticalPhaseExtension E r).indicator
          (fun _ => (1 : ℝ)) y = 0) := by
  let Φ := verticalCompressionHomeomorph (compressionBeta σ τ ε)
    (contDiff_compressionBeta hσ hst ε) (compressionBeta_ne_zero hε hε1) c
  have hq := quasiMeasurePreserving_symm_of_differentiable Φ
    ((contDiff_verticalCompression (contDiff_compressionBeta hσ hst ε) c).differentiable
      one_ne_zero)
  obtain ⟨hl, hu⟩ := h.extension_phases
  have hl' := hq.ae ((ae_restrict_iff'
    (isOpen_lowerPhaseColumn r (c - η * r)).measurableSet).mp hl)
  have hu' := hq.ae ((ae_restrict_iff'
    (isOpen_upperPhaseColumn r (c + η * r)).measurableSet).mp hu)
  filter_upwards [hl', hu'] with y hyl hyu
  have hb : 0 < compressionBeta σ τ ε (graphProjectionN 2 y) :=
    hε.trans_le (compressionBeta_bounds σ τ hε.le hε1 _).1
  have hi : (verticalCompression (compressionBeta σ τ ε) c ''
      verticalPhaseExtension E r).indicator (fun _ => (1 : ℝ)) y =
      (verticalPhaseExtension E r).indicator (fun _ => (1 : ℝ)) (Φ.symm y) :=
    indicator_image_homeomorph Φ _ y
  constructor
  · intro hp hy
    rw [hi]
    apply hyl
    exact ⟨by simpa only [Φ, verticalCompressionHomeomorph_symm_apply,
      verticalCompression_projection] using hp, compression_inverse_height_lt hb hy⟩
  · intro hp hy
    rw [hi]
    apply hyu
    exact ⟨by simpa only [Φ, verticalCompressionHomeomorph_symm_apply,
      verticalCompression_projection] using hp, compression_inverse_height_gt hb hy⟩

end LiquidDrop

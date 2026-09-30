module

public import NoCompromise.Regularity.DeformationExtension

@[expose] public section

/-! # The extended slices have no interface outside the cleared slab -/

noncomputable section
open Set MeasureTheory Metric Filter
open scoped ENNReal
namespace LiquidDrop

def lowerPhaseColumn (r a : ℝ) : Set AmbientSpace :=
  {x | ‖graphProjectionN 2 x‖ < r ∧ x 2 < a}

def upperPhaseColumn (r a : ℝ) : Set AmbientSpace :=
  {x | ‖graphProjectionN 2 x‖ < r ∧ a < x 2}

lemma isOpen_lowerPhaseColumn (r a : ℝ) : IsOpen (lowerPhaseColumn r a) :=
  (isOpen_lt (graphProjectionN 2).continuous.norm continuous_const).inter
    (isOpen_lt (EuclideanSpace.proj (2 : Fin 3) : AmbientSpace →L[ℝ] ℝ).continuous
      continuous_const)

lemma isOpen_upperPhaseColumn (r a : ℝ) : IsOpen (upperPhaseColumn r a) :=
  (isOpen_lt (graphProjectionN 2).continuous.norm continuous_const).inter
    (isOpen_lt continuous_const
      (EuclideanSpace.proj (2 : Fin 3) : AmbientSpace →L[ℝ] ℝ).continuous)

lemma verticalPhaseExtension_agrees_on_cylinder {E : Set AmbientSpace} {r : ℝ}
    {x : AmbientSpace} (hx : x ∈ standardCylinder r) :
    x ∈ verticalPhaseExtension E r ↔ x ∈ E :=
  verticalPhaseExtension_mem_between ⟨(abs_lt.mp hx.2).1.le, (abs_lt.mp hx.2).2⟩

theorem IsSlabCapConfiguration.extension_phases
    {E : Set AmbientSpace} {hE : HasLocallyFinitePerimeter E}
    {hmE : NullMeasurableSet E volume} {r c η : ℝ}
    (h : IsSlabCapConfiguration E hE hmE r c η) :
    ((verticalPhaseExtension E r).indicator (fun _ => (1 : ℝ))
      =ᵐ[volume.restrict (lowerPhaseColumn r (c - η * r))] fun _ => 1) ∧
    ((verticalPhaseExtension E r).indicator (fun _ => (1 : ℝ))
      =ᵐ[volume.restrict (upperPhaseColumn r (c + η * r))] fun _ => 0) := by
  obtain ⟨hl, hu⟩ := h.phases_off_slab
  have hl' := (ae_restrict_iff' (isOpen_lowerSlabRegion r c η).measurableSet).mp hl
  have hu' := (ae_restrict_iff' (isOpen_upperSlabRegion r c η).measurableSet).mp hu
  have hηr : 0 < η * r := mul_pos h.1.2.1 h.1.1
  have hgapL : -r < c - η * r := by linarith [neg_abs_le c, h.1.2.2.2.1]
  have hgapU : c + η * r < r := by linarith [le_abs_self c, h.1.2.2.2.1]
  have hplane : ∀ᵐ x : AmbientSpace ∂volume, x 2 ≠ -r := by
    have hh := (measure_eq_zero_iff_ae_notMem).mp (volume_flatHyperplane 2 (-r))
    simpa only [mem_ofPred_eq, show (Fin.last 2 : Fin 3) = 2 from rfl] using hh
  constructor
  · apply (ae_restrict_iff' (isOpen_lowerPhaseColumn r (c - η * r)).measurableSet).mpr
    filter_upwards [hl', hplane] with x hx hxp
    intro hxcol
    by_cases hlow : x 2 < -r
    · exact indicator_of_mem (verticalPhaseExtension_mem_lower hlow) _
    · have hheight : -r < x 2 := lt_of_le_of_ne (le_of_not_gt hlow) (Ne.symm hxp)
      have hxr : x 2 < r := by linarith [hxcol.2]
      have hxreg : x ∈ lowerSlabRegion r c η :=
        ⟨by simpa only [mem_preimage, mem_ball, dist_zero_right] using hxcol.1,
          hheight, hxcol.2⟩
      have heq := hx hxreg
      have hxE : x ∈ E := by
        by_contra hh
        simp only [indicator_of_notMem hh] at heq
        norm_num at heq
      exact indicator_of_mem ((verticalPhaseExtension_mem_between ⟨hheight.le, hxr⟩).mpr hxE) _
  · apply (ae_restrict_iff' (isOpen_upperPhaseColumn r (c + η * r)).measurableSet).mpr
    filter_upwards [hu'] with x hx
    intro hxcol
    by_cases hup : r ≤ x 2
    · exact indicator_of_notMem (verticalPhaseExtension_notMem_upper h.1.1.le hup) _
    · have hheight : x 2 < r := lt_of_not_ge hup
      have hxl : -r < x 2 := by linarith [hxcol.2]
      have hxreg : x ∈ upperSlabRegion r c η :=
        ⟨by simpa only [mem_preimage, mem_ball, dist_zero_right] using hxcol.1,
          hxcol.2, hheight⟩
      have heq := hx hxreg
      have hxE : x ∉ E := by
        intro hh
        simp only [indicator_of_mem hh] at heq
        norm_num at heq
      exact indicator_of_notMem
        (fun hh => hxE ((verticalPhaseExtension_mem_between ⟨hxl.le, hheight⟩).mp hh)) _

theorem IsSlabCapConfiguration.extension_perimeter_off_slab
    {E : Set AmbientSpace} {hE : HasLocallyFinitePerimeter E}
    {hmE : NullMeasurableSet E volume} {r c η : ℝ}
    (h : IsSlabCapConfiguration E hE hmE r c η) :
    perimeterIn (verticalPhaseExtension E r) (lowerPhaseColumn r (c - η * r)) = 0 ∧
      perimeterIn (verticalPhaseExtension E r) (upperPhaseColumn r (c + η * r)) = 0 := by
  obtain ⟨hl, hu⟩ := h.extension_phases
  constructor
  · change variation _ _ = 0
    rw [variation_congr_ae _ hl, variation_const_eq_zero]
  · change variation _ _ = 0
    rw [variation_congr_ae _ hu, variation_const_eq_zero]

end LiquidDrop

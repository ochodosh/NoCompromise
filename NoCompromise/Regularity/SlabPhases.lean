module

public import NoCompromise.Regularity.SlabCap
public import NoCompromise.BV.ZeroVariation

@[expose] public section

/-! # Vanishing perimeter and constant phases outside the cleared slab -/

noncomputable section
open Set MeasureTheory Metric Filter
open scoped ENNReal
namespace LiquidDrop

lemma indicator_ae_constant_phase_of_perimeter_zero {n : ℕ}
    {E U : Set (EuclideanSpace ℝ (Fin n))} (hmE : NullMeasurableSet E volume)
    (hU : IsOpen U) (hcU : IsPreconnected U) (hp : perimeterIn E U = 0) :
    (E.indicator (fun _ => (1 : ℝ)) =ᵐ[volume.restrict U] fun _ => 0) ∨
      (E.indicator (fun _ => (1 : ℝ)) =ᵐ[volume.restrict U] fun _ => 1) := by
  obtain ⟨c, hc⟩ := ae_eq_const_of_variation_eq_zero hU hcU
    ((locallyIntegrable_indicator_one hmE).locallyIntegrableOn U) hp
  by_cases hz : volume.restrict U = 0
  · left
    simp [Filter.EventuallyEq, hz]
  · have : (ae (volume.restrict U)).NeBot := ae_neBot.mpr hz
    obtain ⟨x, hx⟩ := hc.exists
    by_cases hxE : x ∈ E
    · have he : c = 1 := by simpa only [indicator_of_mem hxE] using hx.symm
      exact Or.inr (he ▸ hc)
    · have he : c = 0 := by simpa only [indicator_of_notMem hxE] using hx.symm
      exact Or.inl (he ▸ hc)

def lowerSlabRegion (r c η : ℝ) : Set AmbientSpace :=
  (graphProjectionN 2) ⁻¹' ball 0 r ∩
    (EuclideanSpace.proj (2 : Fin 3) : AmbientSpace →L[ℝ] ℝ) ⁻¹' Ioo (-r) (c - η * r)

def upperSlabRegion (r c η : ℝ) : Set AmbientSpace :=
  (graphProjectionN 2) ⁻¹' ball 0 r ∩
    (EuclideanSpace.proj (2 : Fin 3) : AmbientSpace →L[ℝ] ℝ) ⁻¹' Ioo (c + η * r) r

lemma isOpen_lowerSlabRegion (r c η : ℝ) : IsOpen (lowerSlabRegion r c η) :=
  (isOpen_ball.preimage (graphProjectionN 2).continuous).inter
    (isOpen_Ioo.preimage (EuclideanSpace.proj (2 : Fin 3) : AmbientSpace →L[ℝ] ℝ).continuous)

lemma isOpen_upperSlabRegion (r c η : ℝ) : IsOpen (upperSlabRegion r c η) :=
  (isOpen_ball.preimage (graphProjectionN 2).continuous).inter
    (isOpen_Ioo.preimage (EuclideanSpace.proj (2 : Fin 3) : AmbientSpace →L[ℝ] ℝ).continuous)

lemma convex_lowerSlabRegion (r c η : ℝ) : Convex ℝ (lowerSlabRegion r c η) :=
  ((convex_ball (0 : EuclideanSpace ℝ (Fin 2)) r).linear_preimage
    (graphProjectionN 2).toLinearMap).inter
      ((convex_Ioo (-r) (c - η * r)).linear_preimage
        (EuclideanSpace.proj (2 : Fin 3) : AmbientSpace →L[ℝ] ℝ).toLinearMap)

lemma convex_upperSlabRegion (r c η : ℝ) : Convex ℝ (upperSlabRegion r c η) :=
  ((convex_ball (0 : EuclideanSpace ℝ (Fin 2)) r).linear_preimage
    (graphProjectionN 2).toLinearMap).inter
      ((convex_Ioo (c + η * r) r).linear_preimage
        (EuclideanSpace.proj (2 : Fin 3) : AmbientSpace →L[ℝ] ℝ).toLinearMap)

lemma HasCylindricalSlab.perimeter_lower_upper_eq_zero
    {E : Set AmbientSpace} {hE : HasLocallyFinitePerimeter E}
    {hmE : NullMeasurableSet E volume} {r c η : ℝ}
    (h : HasCylindricalSlab E hE hmE r c η) :
    perimeterIn E (lowerSlabRegion r c η) = 0 ∧
      perimeterIn E (upperSlabRegion r c η) = 0 := by
  have hηr : 0 < η * r := mul_pos h.2.1 h.1
  have hc : -r < c - η * r ∧ c + η * r < r := by
    constructor <;> linarith [neg_abs_le c, le_abs_self c, h.2.2.2.1]
  have heL : lowerSlabRegion r c η ∩ reducedBoundary E hE hmE = ∅ := by
    apply eq_empty_iff_forall_notMem.mpr
    intro x hx
    have hxl : ‖graphProjectionN 2 x‖ < r ∧ -r < x 2 ∧ x 2 < c - η * r := by
      refine ⟨?_, hx.1.2.1, hx.1.2.2⟩
      simpa only [mem_preimage, mem_ball, dist_zero_right] using hx.1.1
    have hs := h.2.2.2.2 x ⟨hx.2, hxl.1, abs_lt.mpr ⟨hxl.2.1, by linarith [hxl.2.2]⟩⟩
    have := (abs_lt.mp hs).1
    linarith [hxl.2.2]
  have heU : upperSlabRegion r c η ∩ reducedBoundary E hE hmE = ∅ := by
    apply eq_empty_iff_forall_notMem.mpr
    intro x hx
    have hxu : ‖graphProjectionN 2 x‖ < r ∧ c + η * r < x 2 ∧ x 2 < r := by
      refine ⟨?_, hx.1.2.1, hx.1.2.2⟩
      simpa only [mem_preimage, mem_ball, dist_zero_right] using hx.1.1
    have hs := h.2.2.2.2 x ⟨hx.2, hxu.1, abs_lt.mpr ⟨by linarith [hxu.2.1], hxu.2.2⟩⟩
    have := (abs_lt.mp hs).2
    linarith [hxu.2.1]
  constructor
  · rw [perimeterIn_eq_reducedBoundary_area E hE hmE (isOpen_lowerSlabRegion r c η),
      heL, measure_empty]
  · rw [perimeterIn_eq_reducedBoundary_area E hE hmE (isOpen_upperSlabRegion r c η),
      heU, measure_empty]

end LiquidDrop

module

public import NoCompromise.Regularity.HeightBound
public import NoCompromise.Regularity.SlabGeometry

@[expose] public section

/-!
# Fixed open regions surrounding the graph-approximation caps

The regions lie strictly above and below the cleared slab of height one quarter,
inside the cylinder of radius three quarters. Constant phases on these regions
give actual density membership at every point of the half-radius caps.
-/

noncomputable section
open Set MeasureTheory Metric Filter
open scoped ENNReal Topology
namespace LiquidDrop

def graphLowerCapRegion : Set AmbientSpace := lowerSlabRegion (3 / 4) 0 (1 / 3)
def graphUpperCapRegion : Set AmbientSpace := upperSlabRegion (3 / 4) 0 (1 / 3)

/-- The correctly oriented actual constant phases on the two fixed open regions. -/
def HasGraphCapPhases (E : Set AmbientSpace) : Prop :=
  (E.indicator (fun _ => (1 : ℝ)) =ᵐ[volume.restrict graphLowerCapRegion] fun _ => 1) ∧
    (E.indicator (fun _ => (1 : ℝ)) =ᵐ[volume.restrict graphUpperCapRegion] fun _ => 0)

lemma isOpen_graphLowerCapRegion : IsOpen graphLowerCapRegion :=
  isOpen_lowerSlabRegion _ _ _

lemma isOpen_graphUpperCapRegion : IsOpen graphUpperCapRegion :=
  isOpen_upperSlabRegion _ _ _

lemma graphLowerCapRegion_subset {x : AmbientSpace} (hx : x ∈ graphLowerCapRegion) :
    x ∈ standardCylinder (3 / 4) ∧ x 2 < 0 := by
  have hh : ‖graphProjectionN 2 x‖ < 3 / 4 ∧ -(3 / 4 : ℝ) < x 2 ∧ x 2 < -(1 / 4 : ℝ) := by
    simpa only [graphLowerCapRegion, lowerSlabRegion, mem_inter_iff, mem_preimage,
      mem_ball, dist_zero_right, mem_Ioo,
      show (EuclideanSpace.proj (2 : Fin 3) : AmbientSpace →L[ℝ] ℝ) x = x 2 from rfl,
      show (0 : ℝ) - 1 / 3 * (3 / 4) = -(1 / 4) by norm_num] using hx
  exact ⟨⟨hh.1, abs_lt.mpr ⟨hh.2.1, by linarith [hh.2.2]⟩⟩, by linarith [hh.2.2]⟩

lemma graphUpperCapRegion_subset {x : AmbientSpace} (hx : x ∈ graphUpperCapRegion) :
    x ∈ standardCylinder (3 / 4) ∧ 0 < x 2 := by
  have hh : ‖graphProjectionN 2 x‖ < 3 / 4 ∧ (1 / 4 : ℝ) < x 2 ∧ x 2 < 3 / 4 := by
    simpa only [graphUpperCapRegion, upperSlabRegion, mem_inter_iff, mem_preimage,
      mem_ball, dist_zero_right, mem_Ioo,
      show (EuclideanSpace.proj (2 : Fin 3) : AmbientSpace →L[ℝ] ℝ) x = x 2 from rfl,
      show (0 : ℝ) + 1 / 3 * (3 / 4) = 1 / 4 by norm_num] using hx
  exact ⟨⟨hh.1, abs_lt.mpr ⟨by linarith [hh.2.1], hh.2.2⟩⟩, by linarith [hh.2.1]⟩

lemma graphAppend_mem_graphLowerCapRegion {p : EuclideanSpace ℝ (Fin 2)}
    (hp : p ∈ ball 0 (1 / 2)) : graphAppendN p (-(1 / 2 : ℝ)) ∈ graphLowerCapRegion := by
  have hp' : ‖p‖ < 3 / 4 := (mem_ball_zero_iff.mp hp).trans (by norm_num)
  change graphProjectionN 2 (graphAppendN p (-(1 / 2 : ℝ))) ∈ ball 0 (3 / 4) ∧ _
  constructor
  · simpa only [graphProjectionN_append, mem_ball, dist_zero_right] using hp'
  · change -(3 / 4 : ℝ) < graphAppendN p (-(1 / 2 : ℝ)) 2 ∧
      graphAppendN p (-(1 / 2 : ℝ)) 2 < 0 - 1 / 3 * (3 / 4)
    rw [graphAppendN_height_three]
    norm_num

lemma graphAppend_mem_graphUpperCapRegion {p : EuclideanSpace ℝ (Fin 2)}
    (hp : p ∈ ball 0 (1 / 2)) : graphAppendN p (1 / 2 : ℝ) ∈ graphUpperCapRegion := by
  have hp' : ‖p‖ < 3 / 4 := (mem_ball_zero_iff.mp hp).trans (by norm_num)
  change graphProjectionN 2 (graphAppendN p (1 / 2 : ℝ)) ∈ ball 0 (3 / 4) ∧ _
  constructor
  · simpa only [graphProjectionN_append, mem_ball, dist_zero_right] using hp'
  · change 0 + 1 / 3 * (3 / 4 : ℝ) < graphAppendN p (1 / 2 : ℝ) 2 ∧
      graphAppendN p (1 / 2 : ℝ) 2 < 3 / 4
    rw [graphAppendN_height_three]
    norm_num

lemma graphLowerCapRegion_nonempty : graphLowerCapRegion.Nonempty :=
  ⟨graphAppendN 0 (-(1 / 2 : ℝ)), graphAppend_mem_graphLowerCapRegion (by simp)⟩

lemma graphUpperCapRegion_nonempty : graphUpperCapRegion.Nonempty :=
  ⟨graphAppendN 0 (1 / 2 : ℝ), graphAppend_mem_graphUpperCapRegion (by simp)⟩

/-- A genuine boundary height bound clears the reduced boundary from both cap regions. -/
lemma graphPhaseCaps_has_slab {E : Set AmbientSpace} {ω : ℝ} (hE : IsOmegaMinimal E ω)
    (hh : ∀ x ∈ frontier (densityOne E) ∩ standardCylinder (3 / 4), |x 2| < 1 / 4) :
    HasCylindricalSlab E hE.locallyFinite hE.nullMeasurable (3 / 4) 0 (1 / 3) := by
  refine ⟨by norm_num, by norm_num, by norm_num, by norm_num, fun x hx => ?_⟩
  have hx' : x ∈ frontier (densityOne E) := by
    rw [hE.frontier_densityOne]
    exact reducedBoundary_subset_essentialBoundary hE.locallyFinite hE.nullMeasurable hx.1
  simpa only [sub_zero, show (1 / 3 : ℝ) * (3 / 4) = 1 / 4 by norm_num] using
    hh x ⟨hx', hx.2⟩

/-- Actual BV constancy gives the two possible phases on each connected cap region. -/
theorem graphPhaseCaps_phase_dichotomy {E : Set AmbientSpace} {ω : ℝ}
    (hE : IsOmegaMinimal E ω)
    (hh : ∀ x ∈ frontier (densityOne E) ∩ standardCylinder (3 / 4), |x 2| < 1 / 4) :
    ((E.indicator (fun _ => (1 : ℝ)) =ᵐ[volume.restrict graphLowerCapRegion] fun _ => 0) ∨
      (E.indicator (fun _ => (1 : ℝ)) =ᵐ[volume.restrict graphLowerCapRegion] fun _ => 1)) ∧
    ((E.indicator (fun _ => (1 : ℝ)) =ᵐ[volume.restrict graphUpperCapRegion] fun _ => 0) ∨
      (E.indicator (fun _ => (1 : ℝ)) =ᵐ[volume.restrict graphUpperCapRegion] fun _ => 1)) := by
  obtain ⟨hl, hu⟩ := (graphPhaseCaps_has_slab hE hh).perimeter_lower_upper_eq_zero
  exact ⟨indicator_ae_constant_phase_of_perimeter_zero hE.nullMeasurable
    isOpen_graphLowerCapRegion (convex_lowerSlabRegion _ _ _).isPreconnected hl,
    indicator_ae_constant_phase_of_perimeter_zero hE.nullMeasurable
      isOpen_graphUpperCapRegion (convex_upperSlabRegion _ _ _).isPreconnected hu⟩

/-- An actual zero phase on an open set gives density zero at every point there. -/
lemma graphPhaseCaps_densityZero_of_zero_phase {E U : Set AmbientSpace}
    (hmE : NullMeasurableSet E volume) (hU : IsOpen U)
    (hz : E.indicator (fun _ => (1 : ℝ)) =ᵐ[volume.restrict U] fun _ => 0) :
    U ⊆ densityZero E := by
  intro x hx
  obtain ⟨r, hr, hball⟩ := Metric.isOpen_iff.mp hU x hx
  apply mem_densityZero_of_measure_inter_ball_eq_zero hr
  apply volume_inter_zero_of_ae_empty hmE
  filter_upwards [ae_restrict_of_ae_restrict_of_subset hball hz] with y hy
  by_cases hyE : y ∈ E
  · simp [hyE] at hy
  · change (y ∈ E) = (y ∈ (∅ : Set AmbientSpace))
    simp [hyE]

/-- An actual one phase on an open set gives density one at every point there. -/
lemma graphPhaseCaps_densityOne_of_one_phase {E U : Set AmbientSpace}
    (hmE : NullMeasurableSet E volume) (hU : IsOpen U)
    (ho : E.indicator (fun _ => (1 : ℝ)) =ᵐ[volume.restrict U] fun _ => 1) :
    U ⊆ densityOne E := by
  intro x hx
  obtain ⟨r, hr, hball⟩ := Metric.isOpen_iff.mp hU x hx
  apply mem_densityOne_of_compl_inter_ball_eq_zero hmE hr
  apply volume_compl_inter_zero_of_ae_full hmE
  filter_upwards [ae_restrict_of_ae_restrict_of_subset hball ho] with y hy
  by_cases hyE : y ∈ E
  · change (y ∈ E) = (y ∈ (univ : Set AmbientSpace))
    simp [hyE]
  · simp [hyE] at hy

end LiquidDrop

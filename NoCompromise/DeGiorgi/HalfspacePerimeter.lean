module

public import NoCompromise.DeGiorgi.HalfspacePairing
public import NoCompromise.DeGiorgi.ConstantPolarMeasure

@[expose] public section

/-!
# Halfspace perimeter and its complete boundary measure

The proved compact-test identity identifies the actual BV perimeter measure
with normalized Hausdorff area on the boundary plane. In particular the relative
perimeter in a central radius-`R` ball is exactly `π R²`, and every central sphere
is null for this perimeter measure.
-/

noncomputable section
open MeasureTheory Set Filter Metric
open scoped Topology ENNReal
namespace LiquidDrop
set_option maxSynthPendingDepth 8

/-- The full boundary measure has the exact mass `π R²` on a central ball. -/
lemma halfspacePlaneMeasure_ball {ν : AmbientSpace} (hν : ‖ν‖ = 1)
    {R : ℝ} (hR : 0 ≤ R) :
    halfspacePlaneMeasure ν (ball (0 : AmbientSpace) R) = ENNReal.ofReal (Real.pi * R ^ 2) := by
  rw [halfspacePlaneMeasure, Measure.restrict_apply isOpen_ball.measurableSet]
  have hp : {x : AmbientSpace | inner ℝ ν x = 0} = {x | inner ℝ x ν = 0} := by
    ext x
    change inner ℝ ν x = 0 ↔ inner ℝ x ν = 0
    rw [real_inner_comm]
  rw [hp]
  exact hausdorffMeasure2_central_plane_ball hν hR

/-- The full boundary measure assigns zero mass to every central sphere. -/
lemma halfspacePlaneMeasure_sphere {ν : AmbientSpace} (hν : ‖ν‖ = 1) (R : ℝ) :
    halfspacePlaneMeasure ν (sphere (0 : AmbientSpace) R) = 0 := by
  rw [halfspacePlaneMeasure, Measure.restrict_apply isClosed_sphere.measurableSet]
  have hp : {x : AmbientSpace | inner ℝ ν x = 0} = {x | inner ℝ x ν = 0} := by
    ext x
    change inner ℝ ν x = 0 ↔ inner ℝ x ν = 0
    rw [real_inner_comm]
  rw [hp]
  exact hausdorffMeasure2_central_plane_sphere hν R

/-- Plane area is locally finite as an ambient measure. -/
lemma halfspacePlaneMeasure_isLocallyFinite {ν : AmbientSpace} (hν : ‖ν‖ = 1) :
    IsLocallyFiniteMeasure (halfspacePlaneMeasure ν) := by
  refine ⟨fun x => ⟨ball (0 : AmbientSpace) (‖x‖ + 1), ?_, ?_⟩⟩
  · exact isOpen_ball.mem_nhds (by simp only [mem_ball, dist_zero_right]; linarith)
  · rw [halfspacePlaneMeasure_ball hν (by positivity)]
    exact ENNReal.ofReal_lt_top

/-- Plane area is a regular Radon measure. -/
lemma halfspacePlaneMeasure_regular {ν : AmbientSpace} (hν : ‖ν‖ = 1) :
    (halfspacePlaneMeasure ν).Regular := by
  let := halfspacePlaneMeasure_isLocallyFinite hν
  infer_instance

/-- The actual relative perimeter equals boundary-plane area on every open set. -/
theorem negativeHalfspace_perimeterIn_eq {ν : AmbientSpace} (hν : ‖ν‖ = 1)
    {O : Set AmbientSpace} (hO : IsOpen O) :
    perimeterIn (negativeHalfspace ν) O = halfspacePlaneMeasure ν O := by
  let := halfspacePlaneMeasure_regular hν
  exact (negativeHalfspace_hasConstantIndicatorPolar hν).perimeterIn_eq
    (isOpen_negativeHalfspace ν).measurableSet.nullMeasurableSet hν hO

/-- Unit-normal halfspaces have locally finite perimeter. -/
theorem negativeHalfspace_hasLocallyFinitePerimeter {ν : AmbientSpace} (hν : ‖ν‖ = 1) :
    HasLocallyFinitePerimeter (negativeHalfspace ν) := by
  let := halfspacePlaneMeasure_regular hν
  exact (negativeHalfspace_hasConstantIndicatorPolar hν).hasLocallyFinitePerimeter
    (isOpen_negativeHalfspace ν).measurableSet.nullMeasurableSet hν

/-- The full outward perimeter polar is the constant unit normal `ν`. -/
theorem negativeHalfspace_isAmbientOutwardPerimeterPolar {ν : AmbientSpace} (hν : ‖ν‖ = 1) :
    IsAmbientOutwardPerimeterPolar (negativeHalfspace ν) (halfspacePlaneMeasure ν)
      (fun _ => ν) := by
  let := halfspacePlaneMeasure_regular hν
  exact (negativeHalfspace_hasConstantIndicatorPolar hν).isAmbientOutwardPerimeterPolar
    (isOpen_negativeHalfspace ν).measurableSet.nullMeasurableSet hν

/-- Exact identification of the canonical measure, independent of its construction proofs. -/
theorem canonicalPerimeterMeasure_negativeHalfspace {ν : AmbientSpace} (hν : ‖ν‖ = 1)
    (hH : HasLocallyFinitePerimeter (negativeHalfspace ν))
    (hmH : NullMeasurableSet (negativeHalfspace ν) volume) :
    canonicalPerimeterMeasure (negativeHalfspace ν) hH hmH = halfspacePlaneMeasure ν := by
  let := halfspacePlaneMeasure_regular hν
  exact (negativeHalfspace_hasConstantIndicatorPolar hν).canonicalPerimeterMeasure_eq hH hmH hν

/-- The geometric halfspace perimeter in a central ball, including the zero-radius case. -/
theorem perimeterIn_negativeHalfspace_ball {ν : AmbientSpace} (hν : ‖ν‖ = 1)
    {R : ℝ} (hR : 0 ≤ R) :
    perimeterIn (negativeHalfspace ν) (ball (0 : AmbientSpace) R) =
      ENNReal.ofReal (Real.pi * R ^ 2) := by
  rw [negativeHalfspace_perimeterIn_eq hν isOpen_ball, halfspacePlaneMeasure_ball hν hR]

/-- Canonical halfspace perimeter mass on a central ball. -/
theorem canonicalPerimeterMeasure_negativeHalfspace_ball {ν : AmbientSpace} (hν : ‖ν‖ = 1)
    (hH : HasLocallyFinitePerimeter (negativeHalfspace ν))
    (hmH : NullMeasurableSet (negativeHalfspace ν) volume) {R : ℝ} (hR : 0 ≤ R) :
    canonicalPerimeterMeasure (negativeHalfspace ν) hH hmH (ball (0 : AmbientSpace) R) =
      ENNReal.ofReal (Real.pi * R ^ 2) := by
  rw [canonicalPerimeterMeasure_negativeHalfspace hν, halfspacePlaneMeasure_ball hν hR]

/-- Every central sphere is null for the canonical halfspace perimeter measure. -/
theorem canonicalPerimeterMeasure_negativeHalfspace_sphere {ν : AmbientSpace} (hν : ‖ν‖ = 1)
    (hH : HasLocallyFinitePerimeter (negativeHalfspace ν))
    (hmH : NullMeasurableSet (negativeHalfspace ν) volume) (R : ℝ) :
    canonicalPerimeterMeasure (negativeHalfspace ν) hH hmH (sphere (0 : AmbientSpace) R) = 0 := by
  rw [canonicalPerimeterMeasure_negativeHalfspace hν, halfspacePlaneMeasure_sphere hν R]

/-- Distributional constant-polar identities are unaffected by a volume-null change of set. -/
lemma HasConstantIndicatorPolar.congr_set_ae {E F : Set AmbientSpace}
    {μ : Measure AmbientSpace} {ν : AmbientSpace} (h : HasConstantIndicatorPolar E μ ν)
    (hEF : E =ᵐ[volume] F) : HasConstantIndicatorPolar F μ ν := by
  intro i φ hφ
  rw [← h i φ hφ]
  congr 1
  apply integral_congr_ae
  exact ((indicator_ae_eq_of_ae_eq_set hEF).symm).mul (ae_eq_refl _)

/-- Any regular positive measure giving the same unit halfspace polar is precisely plane area. -/
theorem halfspacePlaneMeasure_eq_of_constantPolar {ν : AmbientSpace} (hν : ‖ν‖ = 1)
    {μ : Measure AmbientSpace} [μ.Regular]
    (h : HasConstantIndicatorPolar (negativeHalfspace ν) μ ν) : μ = halfspacePlaneMeasure ν := by
  let := halfspacePlaneMeasure_regular hν
  apply Measure.OuterRegular.ext_isOpen
  intro O hO
  rw [← h.perimeterIn_eq (isOpen_negativeHalfspace ν).measurableSet.nullMeasurableSet hν hO,
    negativeHalfspace_perimeterIn_eq hν hO]

/-- The measure identification also holds for an almost-everywhere halfspace representative. -/
theorem halfspacePlaneMeasure_eq_of_constantPolar_ae {ν : AmbientSpace} (hν : ‖ν‖ = 1)
    {E : Set AmbientSpace} {μ : Measure AmbientSpace} [μ.Regular]
    (h : HasConstantIndicatorPolar E μ ν) (hEH : E =ᵐ[volume] negativeHalfspace ν) :
    μ = halfspacePlaneMeasure ν :=
  halfspacePlaneMeasure_eq_of_constantPolar hν (h.congr_set_ae hEH)

end LiquidDrop

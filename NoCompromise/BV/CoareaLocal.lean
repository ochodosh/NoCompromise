module

public import NoCompromise.BV.CoareaCharts
public import NoCompromise.Area.C1Graph
public import Mathlib.MeasureTheory.Function.Jacobian

@[expose] public section

/-!
# Weighted scalar coarea in a genuine inverse coordinate chart

Equidimensional change of variables, Tonelli, and the independently proved graph
area formula yield coarea on every Borel patch of a scalar inverse chart.
-/

noncomputable section
open MeasureTheory Set Filter InnerProductSpace
open scoped ENNReal NNReal Topology Gradient
namespace LiquidDrop
set_option maxSynthPendingDepth 8
namespace ScalarCoareaChart
variable {k : ℕ} {u : EuclideanSpace ℝ (Fin (k + 1)) → ℝ} (d : ScalarCoareaChart u)

/-- The graph area density in inverse coordinates, extended measurably off the chart. -/
def levelDensity (y : EuclideanSpace ℝ (Fin (k + 1))) : ℝ :=
  Real.sqrt (1 + ‖coareaGraphSlope (gradient u (d.measurableInverse y))‖ ^ 2)

lemma measurable_levelDensity : Measurable d.levelDensity := by
  have hgrad : Measurable (gradient u) :=
    (toDual ℝ (EuclideanSpace ℝ (Fin (k + 1)))).symm.continuous.measurable.comp
      (measurable_fderiv ℝ u)
  have hcomp := hgrad.comp d.measurable_measurableInverse
  unfold levelDensity coareaGraphSlope
  fun_prop

lemma inverse_jacobian_density {y : EuclideanSpace ℝ (Fin (k + 1))}
    (hy : y ∈ d.chart.target) :
    ENNReal.ofReal |(fderiv ℝ d.chart.symm y).det| *
      ENNReal.ofReal ‖gradient u (d.chart.symm y)‖ = ENNReal.ofReal (d.levelDensity y) := by
  rw [← ENNReal.ofReal_mul (abs_nonneg _), (d.hasFDerivAt_inverse hy).fderiv,
    coarea_inverse_jacobian_factor]
  rw [levelDensity, d.measurableInverse_eq hy]

/-- A globally Borel integrand representing the transformed weight on the chart patch. -/
def transformedWeight (A : Set (EuclideanSpace ℝ (Fin (k + 1))))
    (g : EuclideanSpace ℝ (Fin (k + 1)) → ℝ≥0∞) :
    EuclideanSpace ℝ (Fin (k + 1)) → ℝ≥0∞ :=
  (d.chart '' A).indicator
    (fun y => g (d.measurableInverse y) * ENNReal.ofReal (d.levelDensity y))

lemma measurable_transformedWeight {A : Set (EuclideanSpace ℝ (Fin (k + 1)))}
    (hA : MeasurableSet A) (hAs : A ⊆ d.chart.source)
    {g : EuclideanSpace ℝ (Fin (k + 1)) → ℝ≥0∞} (hg : Measurable g) :
    Measurable (d.transformedWeight A g) :=
  ((hg.comp d.measurable_measurableInverse).mul d.measurable_levelDensity.ennreal_ofReal).indicator
    (d.measurableSet_image hA hAs)

/-- Ordinary change of variables converts gradient mass into the inverse graph density. -/
lemma lintegral_gradient_eq_transformed {A : Set (EuclideanSpace ℝ (Fin (k + 1)))}
    (hA : MeasurableSet A) (hAs : A ⊆ d.chart.source)
    (g : EuclideanSpace ℝ (Fin (k + 1)) → ℝ≥0∞) :
    (∫⁻ x in A, g x * ENNReal.ofReal ‖gradient u x‖) =
      ∫⁻ y, d.transformedWeight A g y := by
  have hT := d.measurableSet_image hA hAs
  have hTt : d.chart '' A ⊆ d.chart.target := by
    rintro _ ⟨x, hx, rfl⟩
    exact d.chart.map_source (hAs hx)
  have hIA : d.chart.symm '' (d.chart '' A) = A := by
    rw [image_image]
    calc
      _ = (fun x => x) '' A := image_congr fun x hx => d.chart.left_inv (hAs hx)
      _ = A := image_id A
  have hcov := lintegral_image_eq_lintegral_abs_det_fderiv_mul volume hT
    (f' := fderiv ℝ d.chart.symm)
    (fun y hy => (d.hasFDerivAt_inverse (hTt hy)).differentiableAt.hasFDerivAt.hasFDerivWithinAt)
    (d.chart.symm.injOn.mono hTt) (fun x => g x * ENNReal.ofReal ‖gradient u x‖)
  rw [hIA] at hcov
  rw [hcov]
  change _ = ∫⁻ y, (d.chart '' A).indicator
    (fun y => g (d.measurableInverse y) * ENNReal.ofReal (d.levelDensity y)) y
  rw [lintegral_indicator hT]
  apply setLIntegral_congr_fun hT
  intro y hy
  dsimp only
  rw [d.measurableInverse_eq (hTt hy), ← d.inverse_jacobian_density (hTt hy)]
  ac_rfl

/-- On each level, graph area is the horizontal integral of the transformed weight. -/
lemma lintegral_level_eq_transformed {A : Set (EuclideanSpace ℝ (Fin (k + 1)))}
    (hA : MeasurableSet A) (hAs : A ⊆ d.chart.source)
    {g : EuclideanSpace ℝ (Fin (k + 1)) → ℝ≥0∞} (hg : Measurable g) (t : ℝ) :
    (∫⁻ y in A ∩ u ⁻¹' {t}, g y ∂Measure.euclideanHausdorffMeasure k) =
      ∫⁻ x : EuclideanSpace ℝ (Fin k), d.transformedWeight A g (graphAppendN x t) := by
  rw [← d.graphMapN_levelPatch hAs t,
    c1_graph_lintegral (d.isOpen_levelDomain t) (d.contDiffOn_levelHeight t)
      (d.measurableSet_levelPatch hA hAs t) (d.levelPatch_subset_levelDomain hAs t) hg]
  have heq : (fun x => d.transformedWeight A g (graphAppendN x t)) =
      (d.levelPatch A t).indicator (fun x => g (d.measurableInverse (graphAppendN x t)) *
        ENNReal.ofReal (d.levelDensity (graphAppendN x t))) := by
    funext x
    rfl
  rw [heq, lintegral_indicator (d.measurableSet_levelPatch hA hAs t)]
  apply setLIntegral_congr_fun (d.measurableSet_levelPatch hA hAs t)
  intro x hx
  dsimp only
  have hxd := d.levelPatch_subset_levelDomain hAs t hx
  rw [d.gradient_levelHeight hxd, levelDensity, d.measurableInverse_eq hxd,
    d.inverse_eq_graphMapN hxd]

/-- The weighted level integral is Borel measurable on every chart patch. -/
lemma measurable_lintegral_level {A : Set (EuclideanSpace ℝ (Fin (k + 1)))}
    (hA : MeasurableSet A) (hAs : A ⊆ d.chart.source)
    {g : EuclideanSpace ℝ (Fin (k + 1)) → ℝ≥0∞} (hg : Measurable g) :
    Measurable (fun t : ℝ =>
      ∫⁻ y in A ∩ u ⁻¹' {t}, g y ∂Measure.euclideanHausdorffMeasure k) := by
  have hm := (d.measurable_transformedWeight hA hAs hg).comp
    (euclideanLastEquiv k).symm.continuous.measurable
  have hi := hm.lintegral_prod_right' (ν := (volume : Measure (EuclideanSpace ℝ (Fin k))))
  have heq : (fun t : ℝ =>
      ∫⁻ y in A ∩ u ⁻¹' {t}, g y ∂Measure.euclideanHausdorffMeasure k) =
      fun t : ℝ => ∫⁻ x : EuclideanSpace ℝ (Fin k),
        d.transformedWeight A g (graphAppendN x t) :=
    funext (d.lintegral_level_eq_transformed hA hAs hg)
  rw [heq]
  exact hi

/-- Weighted coarea on a Borel patch of an actual C¹ inverse-function chart. -/
theorem weighted_coarea {A : Set (EuclideanSpace ℝ (Fin (k + 1)))}
    (hA : MeasurableSet A) (hAs : A ⊆ d.chart.source)
    {g : EuclideanSpace ℝ (Fin (k + 1)) → ℝ≥0∞} (hg : Measurable g) :
    (∫⁻ x in A, g x * ENNReal.ofReal ‖gradient u x‖) =
      ∫⁻ t : ℝ,
        ∫⁻ y in A ∩ u ⁻¹' {t}, g y ∂Measure.euclideanHausdorffMeasure k := by
  rw [d.lintegral_gradient_eq_transformed hA hAs g,
    lintegral_euclidean_last (d.measurable_transformedWeight hA hAs hg)]
  exact lintegral_congr fun t => (d.lintegral_level_eq_transformed hA hAs hg t).symm

end ScalarCoareaChart
end LiquidDrop

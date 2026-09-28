import Mathlib.Analysis.Calculus.Rademacher
import Mathlib.Analysis.Calculus.LocalExtr.Basic
import Mathlib.Analysis.Calculus.Gradient.Basic
import Mathlib.Geometry.Euclidean.Volume.Measure
import Mathlib.Topology.Algebra.MetricSpace.Lipschitz

namespace LiquidDrop

open Filter Topology

/-- A nonnegative function has zero derivative at each zero in the open set where it is
nonnegative. The convention that `fderiv` is zero at nondifferentiability points makes
this pointwise statement possible without regularity assumptions. -/
theorem fderiv_eq_zero_on_zero_set {n : ℕ}
    {U : Set (EuclideanSpace ℝ (Fin n))} (hU : IsOpen U)
    {g : EuclideanSpace ℝ (Fin n) → ℝ} (hg : ∀ x ∈ U, 0 ≤ g x)
    {x : EuclideanSpace ℝ (Fin n)} (hx : x ∈ U) (hxg : g x = 0) :
    fderiv ℝ g x = 0 := by
  apply IsLocalMin.fderiv_eq_zero
  change ∀ᶠ y in 𝓝 x, g x ≤ g y
  filter_upwards [hU.mem_nhds hx] with y hy
  simpa [hxg] using hg y hy

/-- The derivative vanishes almost everywhere on the zero set of a nonnegative
locally Lipschitz function on an open set. In fact the conclusion holds pointwise. -/
theorem fderiv_eq_zero_ae_on_zero_set {n : ℕ}
    {U : Set (EuclideanSpace ℝ (Fin n))} (hU : IsOpen U)
    {g : EuclideanSpace ℝ (Fin n) → ℝ} (hlip : LocallyLipschitzOn U g)
    (hg : ∀ x ∈ U, 0 ≤ g x) :
    ∀ᵐ x ∂(MeasureTheory.volume.restrict {x ∈ U | g x = 0}), fderiv ℝ g x = 0 := by
  have hmeas : MeasurableSet {x ∈ U | g x = 0} := by
    have hopen : IsOpen (U ∩ g ⁻¹' {0}ᶜ) :=
      hlip.continuousOn.isOpen_inter_preimage hU isOpen_compl_singleton
    have heq : {x ∈ U | g x = 0} = U \ (U ∩ g ⁻¹' {0}ᶜ) := by
      ext x
      simp
    rw [heq]
    exact hU.measurableSet.diff hopen.measurableSet
  filter_upwards [MeasureTheory.ae_restrict_mem (μ := MeasureTheory.volume) hmeas]
    with x hx
  exact fderiv_eq_zero_on_zero_set hU hg hx.1 hx.2

/-- The gradient form of the zero-set identity. -/
theorem gradient_eq_zero_ae_on_zero_set {n : ℕ}
    {U : Set (EuclideanSpace ℝ (Fin n))} (hU : IsOpen U)
    {g : EuclideanSpace ℝ (Fin n) → ℝ} (hlip : LocallyLipschitzOn U g)
    (hg : ∀ x ∈ U, 0 ≤ g x) :
    ∀ᵐ x ∂(MeasureTheory.volume.restrict {x ∈ U | g x = 0}), gradient g x = 0 := by
  filter_upwards [fderiv_eq_zero_ae_on_zero_set hU hlip hg] with x hx
  simp [gradient, hx]

end LiquidDrop

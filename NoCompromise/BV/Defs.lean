module

public import NoCompromise.Conventions
public import Mathlib.Analysis.Calculus.ContDiff.Basic
public import Mathlib.MeasureTheory.Function.LocallyIntegrable
public import Mathlib.MeasureTheory.Integral.Bochner.Set
public import Mathlib.MeasureTheory.Measure.Haar.InnerProductSpace

@[expose] public section

/-!
# Variation and perimeter: definitions

Blueprint `def:density`, `def:variation`, and `def:perimeter`.

Functions are actual functions, with almost-everywhere invariance proved separately.
The scalar `variation f U` implements the supremum on an open set `U`; it is not
yet the variation *measure*. Its measure extension is a later theorem.
The formula is defined for all `f` and `U`, but its analytic interpretation uses
`IsOpen U` and `LocallyIntegrableOn f U`. The BV predicates include integrability.

Test fields are globally `C¹`, with compact topological support contained in `U`.
This realizes the usual ambient zero-extension convention for `C¹_c(U)`.
The dimension is an implicit natural-number argument; geometric results may
add `0 < n` as needed. Measurability of sets is a separate hypothesis from
the two perimeter-finiteness predicates below.
-/

noncomputable section

open MeasureTheory Metric Filter
open scoped ENNReal Topology

namespace LiquidDrop

/-- Divergence in arbitrary finite dimension. -/
def divergenceN {n : ℕ} (X : EuclideanSpace ℝ (Fin n) → EuclideanSpace ℝ (Fin n))
    (x : EuclideanSpace ℝ (Fin n)) : ℝ :=
  ∑ i, fderiv ℝ X x (EuclideanSpace.single i 1) i

/-- The divergence of a vector field on `ℝ³`. The showcase definition is unchanged. -/
def divergence (X : AmbientSpace → AmbientSpace) (x : AmbientSpace) : ℝ :=
  ∑ i, fderiv ℝ X x (EuclideanSpace.single i 1) i

/-- The admissible test fields in the variation supremum on `U`. -/
def IsVariationTestField {n : ℕ} (U : Set (EuclideanSpace ℝ (Fin n)))
    (X : EuclideanSpace ℝ (Fin n) → EuclideanSpace ℝ (Fin n)) : Prop :=
  ContDiff ℝ 1 X ∧ HasCompactSupport X ∧ tsupport X ⊆ U ∧ ∀ x, ‖X x‖ ≤ 1

/-- Variation on an open region, as a nonnegative extended-real supremum. -/
def variation {n : ℕ} (f : EuclideanSpace ℝ (Fin n) → ℝ)
    (U : Set (EuclideanSpace ℝ (Fin n))) : ℝ≥0∞ :=
  ⨆ (X : EuclideanSpace ℝ (Fin n) → EuclideanSpace ℝ (Fin n))
    (_ : IsVariationTestField U X), ENNReal.ofReal (∫ x in U, f x * divergenceN X x)

/-- `f ∈ BV(U)`: integrability and finite variation. Used for open `U`. -/
def IsBVOn {n : ℕ} (f : EuclideanSpace ℝ (Fin n) → ℝ)
    (U : Set (EuclideanSpace ℝ (Fin n))) : Prop :=
  IntegrableOn f U ∧ variation f U < ∞

/-- Local BV on an open `U`, tested on open sets whose closure is compact in `U`. -/
def IsLocallyBVOn {n : ℕ} (f : EuclideanSpace ℝ (Fin n) → ℝ)
    (U : Set (EuclideanSpace ℝ (Fin n))) : Prop :=
  LocallyIntegrableOn f U ∧
    ∀ A : Set (EuclideanSpace ℝ (Fin n)),
      IsOpen A → IsCompact (closure A) → closure A ⊆ U → variation f A < ∞

/-- The perimeter of `E` in an open region `U`, in arbitrary finite dimension. -/
def perimeterIn {n : ℕ} (E U : Set (EuclideanSpace ℝ (Fin n))) : ℝ≥0∞ :=
  variation (E.indicator (fun _ => (1 : ℝ))) U

/-- Global perimeter in arbitrary finite dimension. -/
def perimeterN {n : ℕ} (E : Set (EuclideanSpace ℝ (Fin n))) : ℝ≥0∞ :=
  perimeterIn E Set.univ

/-- Finiteness of global perimeter. Measurability is imposed separately. -/
def HasFinitePerimeter {n : ℕ} (E : Set (EuclideanSpace ℝ (Fin n))) : Prop :=
  perimeterN E < ∞

/-- Local finiteness of perimeter. Measurability is imposed separately. -/
def HasLocallyFinitePerimeter {n : ℕ} (E : Set (EuclideanSpace ℝ (Fin n))) : Prop :=
  ∀ A : Set (EuclideanSpace ℝ (Fin n)),
    IsOpen A → IsCompact (closure A) → perimeterIn E A < ∞

/-- The De Giorgi perimeter of a set in `ℝ³`. The showcase definition is unchanged. -/
def perimeter (Ω : Set AmbientSpace) : ℝ≥0∞ :=
  ⨆ (X : AmbientSpace → AmbientSpace)
    (_ : ContDiff ℝ 1 X)
    (_ : HasCompactSupport X)
    (_ : ∀ x, ‖X x‖ ≤ 1),
    ENNReal.ofReal (∫ x in Ω, divergence X x)

/-- The volume fraction of `E` in a ball. Density limits use only `r > 0`. -/
def densityRatio {n : ℕ} (E : Set (EuclideanSpace ℝ (Fin n)))
    (x : EuclideanSpace ℝ (Fin n)) (r : ℝ) : ℝ :=
  (volume (E ∩ ball x r)).toReal / (volume (ball x r)).toReal

/-- Density-one points, with the radius tending to zero through positive values. -/
def densityOne {n : ℕ} (E : Set (EuclideanSpace ℝ (Fin n))) :
    Set (EuclideanSpace ℝ (Fin n)) :=
  {x | Tendsto (densityRatio E x) (𝓝[>] (0 : ℝ)) (𝓝 1)}

/-- Density-zero points. -/
def densityZero {n : ℕ} (E : Set (EuclideanSpace ℝ (Fin n))) :
    Set (EuclideanSpace ℝ (Fin n)) :=
  {x | Tendsto (densityRatio E x) (𝓝[>] (0 : ℝ)) (𝓝 0)}

/-- The essential boundary; its Borel measurability is a separate proof obligation. -/
def essentialBoundary {n : ℕ} (E : Set (EuclideanSpace ℝ (Fin n))) :
    Set (EuclideanSpace ℝ (Fin n)) :=
  (densityZero E ∪ densityOne E)ᶜ

end LiquidDrop

import NoCompromise.Conventions
import Mathlib.MeasureTheory.Measure.Haar.InnerProductSpace
import Mathlib.MeasureTheory.Measure.Prod

/-!
# Coulomb definitions

Blueprint `def:coulomb`, defined in nonnegative extended reals. The kernel
equals infinity on the diagonal, exactly as in the original showcase. Its
agreement with the real-valued kernel under integration is proved using the
diagonal-null and integrability results in `Energy/Coulomb.lean`.
No real-valued conversion is used here, so infinite integrals remain infinite.
-/

noncomputable section

open MeasureTheory
open scoped ENNReal

namespace LiquidDrop

/-- The nonnegative extended-real Coulomb kernel. -/
def coulombKernel (x y : AmbientSpace) : ℝ≥0∞ :=
  (ENNReal.ofReal ‖x - y‖)⁻¹

/-- The Coulomb potential, allowing an infinite value. -/
def coulombPotential (E : Set AmbientSpace) (x : AmbientSpace) : ℝ≥0∞ :=
  ∫⁻ y in E, coulombKernel x y

/-- The interaction of two sets; disjointness is not required to define it. -/
def coulombInteraction (E F : Set AmbientSpace) : ℝ≥0∞ :=
  ∫⁻ p in E ×ˢ F, coulombKernel p.1 p.2

/-- The Coulomb self-interaction energy. The showcase definition is unchanged. -/
def coulombEnergy (Ω : Set AmbientSpace) : ℝ≥0∞ :=
  (2 : ℝ≥0∞)⁻¹ * ∫⁻ p in Ω ×ˢ Ω, (ENNReal.ofReal ‖p.1 - p.2‖)⁻¹

end LiquidDrop

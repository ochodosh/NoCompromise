module

public import NoCompromise.Sobolev.W11TraceFlat

@[expose] public section

/-!
# Compact C¹ functions as genuine W¹,¹ data

The classical gradient is the distributional weak gradient. Compact support
makes both components integrable on the whole space.
-/

noncomputable section
open MeasureTheory Set Filter
open scoped ENNReal Topology Gradient
namespace LiquidDrop

theorem hasW11GradientOn_of_contDiff_compact {n : ℕ}
    {f : EuclideanSpace ℝ (Fin n) → ℝ} (hf : ContDiff ℝ 1 f) (hc : HasCompactSupport f) :
    HasW11GradientOn f (gradient f) univ := by
  refine ⟨hasWeakGradientOn_of_contDiffOn isOpen_univ hf.contDiffOn,
    (hf.continuous.integrable_of_hasCompactSupport hc).integrableOn, ?_⟩
  exact ((continuous_gradient_of_contDiff hf).integrable_of_hasCompactSupport
    (hc.of_isClosed_subset (isClosed_tsupport _) (tsupport_gradient_subset f))).integrableOn

end LiquidDrop

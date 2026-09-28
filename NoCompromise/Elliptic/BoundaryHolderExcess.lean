import NoCompromise.Elliptic.BoundaryHolderVariance
import NoCompromise.Elliptic.CampanatoGrowthComparison

/-! Stability, almost-everywhere invariance, and monotonicity of the actual
normal excess used for flat Dirichlet boundary comparisons. -/

noncomputable section
open MeasureTheory Filter Metric Set InnerProductSpace
open scoped ENNReal NNReal Topology Gradient RealInnerProductSpace
namespace LiquidDrop

lemma boundary_normal_excess_congr_ae {X E : Type*} [MeasurableSpace X]
    [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]
    {μ : Measure X} (n : E) {F G : X → E} (he : F =ᵐ[μ] G) :
    boundaryNormalExcess n F μ = boundaryNormalExcess n G μ := by
  have hm : boundaryNormalMean n F μ = boundaryNormalMean n G μ := by
    rw [boundaryNormalMean, boundaryNormalMean, average_eq, average_eq, integral_congr_ae he]
  rw [boundaryNormalExcess, boundaryNormalExcess, hm]
  apply integral_congr_ae
  filter_upwards [he] with x hx
  rw [hx]

lemma boundary_normal_excess_le_twice {X E : Type*} [MeasurableSpace X]
    [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]
    {μ : Measure X} [IsFiniteMeasure μ] {F G : X → E}
    (hF : MemLp F 2 μ) (hG : MemLp G 2 μ) (n : E) (hn : ‖n‖ = 1) :
    boundaryNormalExcess n F μ ≤
      2 * (∫ x, ‖F x - G x‖ ^ 2 ∂μ) + 2 * boundaryNormalExcess n G μ := by
  let b := boundaryNormalMean n G μ
  have h := campanato_integral_norm_sq_le_twice
    (hF.sub (memLp_const (b • n))) (hG.sub (memLp_const (b • n)))
  simp only [Pi.sub_apply, sub_sub_sub_cancel_right] at h
  exact (boundary_normal_excess_minimizes hF n hn b).trans h

lemma boundary_normal_excess_mono {X E : Type*} [MeasurableSpace X]
    [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]
    {μ : Measure X} {U V : Set X} (hUV : U ⊆ V) (hfin : μ V < ∞) {F : X → E}
    (hF : MemLp F 2 (μ.restrict V)) (n : E) (hn : ‖n‖ = 1) :
    boundaryNormalExcess n F (μ.restrict U) ≤ boundaryNormalExcess n F (μ.restrict V) := by
  let : IsFiniteMeasure (μ.restrict V) := ⟨by simpa using hfin⟩
  let : IsFiniteMeasure (μ.restrict U) := ⟨by
    simpa using (measure_mono hUV).trans_lt hfin⟩
  let b := boundaryNormalMean n F (μ.restrict V)
  have hFU := hF.mono_measure (Measure.restrict_mono hUV le_rfl)
  apply (boundary_normal_excess_minimizes hFU n hn b).trans
  exact setIntegral_mono_set ((hF.sub (memLp_const (b • n))).norm.integrable_sq)
    (Eventually.of_forall fun x => sq_nonneg _) (ae_of_all _ fun _ hx => hUV hx)

end LiquidDrop

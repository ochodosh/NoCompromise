module

public import NoCompromise.Regularity.DeformationTransport
public import NoCompromise.Regularity.DeformationColumn
public import NoCompromise.Regularity.DeformationCompetitor

@[expose] public section

/-!
# A fixed compact source for every compressed local perimeter

The exact column identity puts the extension's perimeter inside the original
cylinder below the active base radius. Outside that column compression is the
identity. Thus no inverse-Lipschitz bound depending on epsilon is needed.
-/

noncomputable section
open MeasureTheory Set Filter Metric
open scoped ENNReal Topology
namespace LiquidDrop
set_option maxSynthPendingDepth 8

lemma IsSlabCapConfiguration.extension_perimeter_ae_mem_cylinder
    {E : Set AmbientSpace} {hE : HasLocallyFinitePerimeter E}
    {hmE : NullMeasurableSet E volume} {r c η : ℝ}
    (h : IsSlabCapConfiguration E hE hmE r c η)
    (hExt : HasLocallyFinitePerimeter (verticalPhaseExtension E r))
    (hmExt : NullMeasurableSet (verticalPhaseExtension E r) volume)
    {τ : ℝ} (hτr : τ ≤ r) :
    ∀ᵐ x ∂canonicalPerimeterMeasure (verticalPhaseExtension E r) hExt hmExt,
      ‖graphProjectionN 2 x‖ < τ → x ∈ standardCylinder r := by
  have hS : MeasurableSet {x : AmbientSpace | ‖graphProjectionN 2 x‖ < τ} :=
    (isOpen_lt (graphProjectionN 2).continuous.norm continuous_const).measurableSet
  apply (ae_restrict_iff' hS).mp
  rw [h.extension_perimeter_column hExt hmExt hτr]
  filter_upwards [ae_restrict_mem (hS.inter (isOpen_standardCylinder r).measurableSet)]
    with x hx
  exact hx.2

/-- The relevant source is contained almost everywhere in a fixed compact
union, even though the inverse compression degenerates as epsilon tends to zero. -/
lemma IsSlabCapConfiguration.compression_preimage_ae_mem_fixed_source
    {E : Set AmbientSpace} {hE : HasLocallyFinitePerimeter E}
    {hmE : NullMeasurableSet E volume} {r c η : ℝ}
    (h : IsSlabCapConfiguration E hE hmE r c η)
    (hExt : HasLocallyFinitePerimeter (verticalPhaseExtension E r))
    (hmExt : NullMeasurableSet (verticalPhaseExtension E r) volume)
    {σ τ : ℝ} (hst : σ < τ) (hτr : τ ≤ r) (ε : ℝ) (U : Set AmbientSpace) :
    ∀ᵐ x ∂canonicalPerimeterMeasure (verticalPhaseExtension E r) hExt hmExt,
      x ∈ verticalCompression (compressionBeta σ τ ε) c ⁻¹' U →
        x ∈ closure U ∪ closure (standardCylinder r) := by
  filter_upwards [h.extension_perimeter_ae_mem_cylinder hExt hmExt hτr] with x hx
  intro hpre
  by_cases hp : ‖graphProjectionN 2 x‖ < τ
  · exact Or.inr (subset_closure (hx hp))
  · have heq := verticalCompression_eq_self (c := c)
      (compressionBeta_eq_one (ε := ε) hst (le_of_not_gt hp))
    exact Or.inl (subset_closure (by simpa only [mem_preimage, heq] using hpre))

/-- The actual compressed extension has uniformly bounded perimeter on every
bounded open set for all positive epsilon at most one. -/
theorem IsSlabCapConfiguration.exists_uniform_compressed_extension_perimeter_bound
    {E : Set AmbientSpace} {hE : HasLocallyFinitePerimeter E}
    {hmE : NullMeasurableSet E volume} {r c η : ℝ}
    (h : IsSlabCapConfiguration E hE hmE r c η)
    {σ τ : ℝ} (hσ : 0 < σ) (hst : σ < τ) (hτr : τ ≤ r)
    {U : Set AmbientSpace} (hU : IsOpen U) (hbU : Bornology.IsBounded U) :
    ∃ C : ℝ≥0∞, C < ∞ ∧ ∀ ε : ℝ, 0 < ε → ε ≤ 1 →
      perimeterIn (verticalCompression (compressionBeta σ τ ε) c ''
        verticalPhaseExtension E r) U ≤ C := by
  have hExt := hasLocallyFinitePerimeter_verticalPhaseExtension hE hmE h.1.1.le
  have hmExt := nullMeasurableSet_verticalPhaseExtension hmE r
  let μ := canonicalPerimeterMeasure (verticalPhaseExtension E r) hExt hmExt
  let : IsFiniteMeasureOnCompacts μ :=
    (canonicalPerimeterPolar (verticalPhaseExtension E r) hExt hmExt).finiteOnCompacts
  let K := closure U ∪ closure (standardCylinder r)
  have hK : IsCompact K := hbU.isCompact_closure.union
    (isBounded_standardCylinder r).isCompact_closure
  have hc : Continuous (fun x : AmbientSpace => (x 2 - c) ^ 2) := by fun_prop
  have hi : IntegrableOn (fun x : AmbientSpace => (x 2 - c) ^ 2) K μ :=
    hc.continuousOn.integrableOn_compact hK
  have hmoment : (∫⁻ x in K, ENNReal.ofReal ((x 2 - c) ^ 2) ∂μ) < ∞ :=
    (hasFiniteIntegral_iff_ofReal
      (Eventually.of_forall fun x : AmbientSpace => sq_nonneg (x 2 - c))).mp hi.2
  refine ⟨μ K + ENNReal.ofReal (Real.pi ^ 2 / (τ - σ) ^ 2) *
    ∫⁻ x in K, ENNReal.ofReal ((x 2 - c) ^ 2) ∂μ, ?_, ?_⟩
  · exact ENNReal.add_lt_top.mpr ⟨hK.measure_lt_top,
      ENNReal.mul_lt_top ENNReal.ofReal_lt_top hmoment⟩
  · intro ε hε hε1
    let Φ := verticalCompressionHomeomorph (compressionBeta σ τ ε)
      (contDiff_compressionBeta hσ hst ε) (compressionBeta_ne_zero hε hε1) c
    have hG := hasLocallyFinitePerimeter_verticalCompression hσ hst hε hε1 c
      (verticalPhaseExtension E r) hExt hmExt
    have hmG := nullMeasurableSet_image_of_differentiable
      ((contDiff_verticalCompression (contDiff_compressionBeta hσ hst ε) c).differentiable
        one_ne_zero) Φ.injective hmExt
    have hA : MeasurableSet (verticalCompression (compressionBeta σ τ ε) c ⁻¹' U) :=
      hU.measurableSet.preimage Φ.continuous.measurable
    have himage : verticalCompression (compressionBeta σ τ ε) c ''
        (verticalCompression (compressionBeta σ τ ε) c ⁻¹' U) = U :=
      Φ.surjective.image_preimage U
    have hb := perimeter_verticalCompression_le_source_measure hσ hst hε hε1 c
      (verticalPhaseExtension E r) hExt hmExt hG hmG hA
    rw [himage, canonicalPerimeterMeasure_open _ hG hmG hU] at hb
    have hsub := h.compression_preimage_ae_mem_fixed_source hExt hmExt hst hτr ε U
    exact hb.trans (add_le_add (measure_mono_ae hsub)
      (mul_le_mul le_rfl (lintegral_mono_set' hsub) bot_le bot_le))

end LiquidDrop

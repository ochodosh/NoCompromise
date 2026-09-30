module

public import NoCompromise.BV.GraphCut
public import NoCompromise.DeGiorgi.SmoothBoundary
public import NoCompromise.BV.ScalarDistributionUniqueness

@[expose] public section

/-!
# BV traces in rigidly placed C¹ boundary charts

These are the essential one-sided graph traces transported by the actual rigid
chart placement. Their integrability is with respect to the chart's Hausdorff
surface measure, and the full graph-domain cut remains locally BV.
-/

noncomputable section
open MeasureTheory Set Filter Metric Topology
open scoped ENNReal Topology Gradient
namespace LiquidDrop
set_option maxSynthPendingDepth 8

/-- The trace from the domain side of a C¹ boundary chart. -/
def C1BoundaryChart.lowerBVTrace (c : C1BoundaryChart) (f : AmbientSpace → ℝ)
    (z : AmbientSpace) : ℝ :=
  graphBVLowerTrace (f ∘ c.placement) c.height (c.placement.symm z)

/-- The trace from the exterior side of a C¹ boundary chart. -/
def C1BoundaryChart.upperBVTrace (c : C1BoundaryChart) (f : AmbientSpace → ℝ)
    (z : AmbientSpace) : ℝ :=
  graphBVUpperTrace (f ∘ c.placement) c.height (c.placement.symm z)

lemma IsLocallyBVOn.comp_rigidPlacement {f : AmbientSpace → ℝ}
    (hf : IsLocallyBVOn f univ) (a : AmbientSpace ≃ᵃⁱ[ℝ] AmbientSpace) :
    IsLocallyBVOn (f ∘ a) univ :=
  hf.comp_C1_diffeomorphism a.toHomeomorph (contDiff_rigidPlacement a)
    (contDiff_rigidPlacement a.symm)

/-- Both actual chart traces are locally integrable for surface area. -/
theorem C1BoundaryChart.locallyIntegrable_BVTraces (c : C1BoundaryChart)
    {f : AmbientSpace → ℝ} (hf : IsLocallyBVOn f univ) :
    LocallyIntegrable (c.lowerBVTrace f) ((hausdorffMeasure2 3).restrict c.graphSurface) ∧
      LocallyIntegrable (c.upperBVTrace f) ((hausdorffMeasure2 3).restrict c.graphSurface) := by
  have hg := (hf.comp_rigidPlacement c.placement).locallyIntegrable_graphBVTraces c.height_contDiff
  rw [C1BoundaryChart.graphSurface, hausdorffMeasure2_restrict_affineIsometry_image]
  change LocallyIntegrable (c.lowerBVTrace f)
      (Measure.map c.placement.toHomeomorph (smoothGraphArea c.height)) ∧
    LocallyIntegrable (c.upperBVTrace f)
      (Measure.map c.placement.toHomeomorph (smoothGraphArea c.height))
  rw [locallyIntegrable_map_homeomorph, locallyIntegrable_map_homeomorph]
  change LocallyIntegrable (fun z => graphBVLowerTrace (f ∘ c.placement) c.height
      (c.placement.symm (c.placement z))) (smoothGraphArea c.height) ∧
    LocallyIntegrable (fun z => graphBVUpperTrace (f ∘ c.placement) c.height
      (c.placement.symm (c.placement z))) (smoothGraphArea c.height)
  simpa only [c.placement.symm_apply_apply] using hg

/-- A compact chart patch has finite L¹ traces on both sides. -/
theorem C1BoundaryChart.integrableOn_BVTraces (c : C1BoundaryChart)
    {f : AmbientSpace → ℝ} (hf : IsLocallyBVOn f univ)
    {K : Set AmbientSpace} (hK : IsCompact K) :
    IntegrableOn (c.lowerBVTrace f) K ((hausdorffMeasure2 3).restrict c.graphSurface) ∧
      IntegrableOn (c.upperBVTrace f) K ((hausdorffMeasure2 3).restrict c.graphSurface) :=
  ⟨(c.locallyIntegrable_BVTraces hf).1.integrableOn_isCompact hK,
    (c.locallyIntegrable_BVTraces hf).2.integrableOn_isCompact hK⟩

/-- Cutting by the full placed graph domain preserves local BV. -/
theorem C1BoundaryChart.indicator_graphDomain_isLocallyBV (c : C1BoundaryChart)
    {f : AmbientSpace → ℝ} (hf : IsLocallyBVOn f univ) :
    IsLocallyBVOn (c.graphDomain.indicator f) univ := by
  classical
  have hh := ((hf.comp_rigidPlacement c.placement).indicator_smoothSubgraph c.height_contDiff
    ).comp_rigidPlacement c.placement.symm
  convert hh using 1
  funext z
  have hz : c.placement.symm z ∈ smoothSubgraph c.height ↔ z ∈ c.graphDomain := by
    change c.placement.symm z ∈ smoothSubgraph c.height ↔
      z ∈ c.placement '' smoothSubgraph c.height
    constructor
    · intro h
      exact ⟨c.placement.symm z, h, c.placement.apply_symm_apply z⟩
    · rintro ⟨x, hx, rfl⟩
      simpa only [c.placement.symm_apply_apply] using hx
  by_cases h : z ∈ c.graphDomain
  · simp only [Function.comp_def, Set.indicator_of_mem h, Set.indicator_of_mem (hz.mpr h),
      c.placement.apply_symm_apply]
  · simp only [Function.comp_def, Set.indicator_of_notMem h,
      Set.indicator_of_notMem (mt hz.mp h)]

/-- A placed graph has a genuine ambient derivative representation and the cut
formula with the chart's actual geometric normal and constructed trace. -/
theorem C1BoundaryChart.exists_cut_representation (c : C1BoundaryChart)
    {f : AmbientSpace → ℝ} (hf : IsLocallyBVOn f univ) :
    ∃ μ : Measure AmbientSpace, ∃ σ : AmbientSpace → AmbientSpace,
      μ.Regular ∧ IsFiniteMeasureOnCompacts μ ∧ Measurable σ ∧
      (∀ᵐ z ∂μ, ‖σ z‖ = 1) ∧ LocallyIntegrable σ μ ∧
      (∀ (v : AmbientSpace) (φ : AmbientSpace → ℝ), ContDiff ℝ 1 φ → HasCompactSupport φ →
        (∫ z, f z * fderiv ℝ φ z v) = -∫ z, φ z * inner ℝ v (σ z) ∂μ) ∧
      (∀ (v : AmbientSpace) (φ : AmbientSpace → ℝ), ContDiff ℝ 1 φ → HasCompactSupport φ →
        (∫ z in c.graphDomain, f z * fderiv ℝ φ z v) =
          -(∫ z in c.graphDomain, φ z * inner ℝ v (σ z) ∂μ) +
          ∫ z, c.lowerBVTrace f z * (φ z * inner ℝ v (c.outwardNormal z))
            ∂(hausdorffMeasure2 3).restrict c.graphSurface) := by
  let a := c.placement
  let L := a.linearIsometryEquiv
  have hu := hf.comp_rigidPlacement a
  obtain ⟨μ, σ, hμ, hμfin, hmσ, hnσ, _, hfull, hcut⟩ :=
    hu.exists_ambient_smoothSubgraph_cut_representation c.height_contDiff
  let : μ.Regular := hμ
  let : IsFiniteMeasureOnCompacts μ := hμfin
  let ν := Measure.map a.toHomeomorph μ
  let τ := fun z => L (σ (a.symm z))
  let : ν.Regular := Measure.Regular.map a.toHomeomorph
  have hmτ : Measurable τ := L.continuous.measurable.comp
    (hmσ.comp a.symm.continuous.measurable)
  have hnτ : ∀ᵐ z ∂ν, ‖τ z‖ = 1 := by
    rw [show ν = Measure.map a.toHomeomorph μ from rfl,
      a.toHomeomorph.measurableEmbedding.ae_map_iff]
    change ∀ᵐ z ∂μ, ‖L (σ (a.symm (a z)))‖ = 1
    simpa only [a.symm_apply_apply, L.norm_map] using hnσ
  have hiτ : LocallyIntegrable τ ν :=
    locallyIntegrable_of_ae_norm_le ν hmτ.aestronglyMeasurable (hnτ.mono fun _ hz => hz.le)
  have hinner (v w : AmbientSpace) : inner ℝ v (L w) = inner ℝ (L.symm v) w := by
    simpa only [L.apply_symm_apply] using L.inner_map_map (L.symm v) w
  have hder (v : AmbientSpace) {φ : AmbientSpace → ℝ} (hφ : ContDiff ℝ 1 φ) (z : AmbientSpace) :
      fderiv ℝ (φ ∘ a) z (L.symm v) = fderiv ℝ φ (a z) v := by
    have hd := (hφ.differentiable one_ne_zero (a z)).hasFDerivAt.comp z
      (hasFDerivAt_rigidPlacement a z)
    have hh := congrArg (fun M => M (L.symm v)) hd.fderiv
    change fderiv ℝ (φ ∘ a) z (L.symm v) = fderiv ℝ φ (a z) (L (L.symm v)) at hh
    simpa only [L.apply_symm_apply] using hh
  have hdiv (v : AmbientSpace) {φ : AmbientSpace → ℝ} (hφ : ContDiff ℝ 1 φ) (z : AmbientSpace) :
      divergenceN (fun y => (φ ∘ a) y • L.symm v) z = fderiv ℝ φ (a z) v := by
    rw [divergenceN_smul (hφ.comp (contDiff_rigidPlacement a)) contDiff_const]
    have hz : divergenceN (fun _ : AmbientSpace => L.symm v) z = 0 := by
      simp [divergenceN]
    rw [hz, mul_zero, zero_add, inner_gradient_left]
    exact hder v hφ z
  refine ⟨ν, τ, inferInstance, inferInstance, hmτ, hnτ, hiτ, ?_, ?_⟩
  · intro v φ hφ hcφ
    let X : AmbientSpace → AmbientSpace := fun z => (φ ∘ a) z • L.symm v
    have hX : ContDiff ℝ 1 X := (hφ.comp (contDiff_rigidPlacement a)).smul contDiff_const
    have hcX : HasCompactSupport X := (hcφ.comp_homeomorph a.toHomeomorph).smul_right
    have ht := hfull X hX hcX
    simp only [X] at ht
    simp_rw [hdiv v hφ] at ht
    simp only [Function.comp_def, real_inner_smul_left] at ht
    rw [← (measurePreserving_affineIsometry a).integral_comp a.toHomeomorph.measurableEmbedding
      (fun z => f z * fderiv ℝ φ z v),
      show ν = Measure.map a.toHomeomorph μ from rfl,
      a.toHomeomorph.measurableEmbedding.integral_map]
    change (∫ z, f (a z) * fderiv ℝ φ (a z) v) =
      -∫ z, φ (a z) * inner ℝ v (L (σ (a.symm (a z)))) ∂μ
    simpa only [a.symm_apply_apply, hinner] using ht
  · intro v φ hφ hcφ
    let X : AmbientSpace → AmbientSpace := fun z => (φ ∘ a) z • L.symm v
    have hX : ContDiff ℝ 1 X := (hφ.comp (contDiff_rigidPlacement a)).smul contDiff_const
    have hcX : HasCompactSupport X := (hcφ.comp_homeomorph a.toHomeomorph).smul_right
    have ht := hcut X hX hcX
    simp only [X] at ht
    simp_rw [hdiv v hφ] at ht
    simp only [Function.comp_def, real_inner_smul_left] at ht
    have hpre : a ⁻¹' c.graphDomain = smoothSubgraph c.height :=
      preimage_image_eq _ a.injective
    have hp := (measurePreserving_affineIsometry a).restrict_preimage
      c.isOpen_graphDomain.measurableSet
    rw [hpre] at hp
    rw [← hp.integral_comp a.toHomeomorph.measurableEmbedding (fun z => f z * fderiv ℝ φ z v),
      show ν = Measure.map a.toHomeomorph μ from rfl,
      a.toHomeomorph.measurableEmbedding.setIntegral_map]
    change (∫ z in smoothSubgraph c.height, f (a z) * fderiv ℝ φ (a z) v) =
      -(∫ z in a ⁻¹' c.graphDomain, φ (a z) * inner ℝ v (L (σ (a.symm (a z)))) ∂μ) + _
    rw [hpre]
    simp only [a.symm_apply_apply, hinner]
    have ha : MeasurableEmbedding (c.placement : AmbientSpace → AmbientSpace) :=
      c.placement.toHomeomorph.measurableEmbedding
    rw [C1BoundaryChart.graphSurface, hausdorffMeasure2_restrict_affineIsometry_image,
      ha.integral_map]
    change (∫ z in smoothSubgraph c.height, f (a z) * fderiv ℝ φ (a z) v) =
      -(∫ z in smoothSubgraph c.height, φ (a z) * inner ℝ (L.symm v) (σ z) ∂μ) +
      ∫ z, c.lowerBVTrace f (a z) * (φ (a z) * inner ℝ v (c.outwardNormal (a z)))
        ∂smoothGraphArea c.height
    have htval (z : AmbientSpace) : c.lowerBVTrace f (a z) =
        graphBVLowerTrace (f ∘ a) c.height z := by
      change graphBVLowerTrace (f ∘ a) c.height (a.symm (a z)) = _
      rw [a.symm_apply_apply]
    have hnval (z : AmbientSpace) :
        c.outwardNormal (a z) = L (smoothSubgraphNormal c.height z) := by
      change L (smoothSubgraphNormal c.height (a.symm (a z))) = _
      rw [a.symm_apply_apply]
    simpa only [htval, hnval, hinner, Function.comp_def] using ht

/-- The cut formula uses any genuine ambient derivative representation, so its
bulk term is compatible with all other boundary charts. -/
theorem C1BoundaryChart.cut_pairing_of_coordinate_polar (c : C1BoundaryChart)
    {f : AmbientSpace → ℝ} (hf : IsLocallyBVOn f univ)
    {μ : Measure AmbientSpace} [SigmaFinite μ] {σ : AmbientSpace → AmbientSpace}
    (hσ : LocallyIntegrable σ μ)
    (hpair : ∀ (i : Fin 3) (φ : CompactlySupportedContinuousMap AmbientSpace ℝ),
      ContDiff ℝ 1 φ → -(∫ z, f z * fderiv ℝ φ z (EuclideanSpace.single i 1)) =
        ∫ z, φ z * σ z i ∂μ)
    (v : AmbientSpace) {φ : AmbientSpace → ℝ} (hφ : ContDiff ℝ 1 φ)
    (hcφ : HasCompactSupport φ) :
    (∫ z in c.graphDomain, f z * fderiv ℝ φ z v) =
      -(∫ z in c.graphDomain, φ z * inner ℝ v (σ z) ∂μ) +
      ∫ z, c.lowerBVTrace f z * (φ z * inner ℝ v (c.outwardNormal z))
        ∂(hausdorffMeasure2 3).restrict c.graphSurface := by
  obtain ⟨ρ, τ, hρ, hρfin, _, _, hτ, hp, hcut⟩ := c.exists_cut_representation hf
  let : ρ.Regular := hρ
  let : IsFiniteMeasureOnCompacts ρ := hρfin
  have he (i : Fin 3) (ψ : CompactlySupportedContinuousMap AmbientSpace ℝ)
      (hψ : ContDiff ℝ 1 ψ) (_ : tsupport ψ ⊆ univ) :
      (∫ z, ψ z * τ z i ∂ρ) = ∫ z, ψ z * σ z i ∂μ := by
    have ht := hp (EuclideanSpace.single i 1) ψ hψ ψ.hasCompactSupport
    have hs := hpair i ψ hψ
    simp only [EuclideanSpace.inner_single_left, map_one, one_mul] at ht
    linarith
  have hb := setIntegral_inner_eq_of_coordinate_pairings isOpen_univ hτ hσ he
    c.isOpen_graphDomain.measurableSet (subset_univ _) (fun z => φ z • v)
  simp only [real_inner_smul_left] at hb
  exact (hcut v φ hφ hcφ).trans (by rw [hb])

/-- The actual traces are L¹ on the bounded chart region of the domain boundary. -/
theorem C1BoundaryChart.IsChartFor.integrableOn_BVTraces {c : C1BoundaryChart}
    {E : Set AmbientSpace} (hc : c.IsChartFor E)
    {f : AmbientSpace → ℝ} (hf : IsLocallyBVOn f univ) :
    IntegrableOn (c.lowerBVTrace f) c.region ((hausdorffMeasure2 3).restrict (frontier E)) ∧
      IntegrableOn (c.upperBVTrace f) c.region ((hausdorffMeasure2 3).restrict (frontier E)) := by
  have h := c.integrableOn_BVTraces hf c.bounded_region.isCompact_closure
  change Integrable _ (((hausdorffMeasure2 3).restrict (frontier E)).restrict c.region) ∧
    Integrable _ (((hausdorffMeasure2 3).restrict (frontier E)).restrict c.region)
  rw [hc.boundaryArea_restrict]
  exact ⟨h.1.mono_set subset_closure, h.2.mono_set subset_closure⟩

lemma C1BoundaryChart.IsChartFor.setIntegral_eq_graphDomain {c : C1BoundaryChart}
    {E : Set AmbientSpace} (hc : c.IsChartFor E) (hE : MeasurableSet E)
    {μ : Measure AmbientSpace} (q : AmbientSpace → ℝ)
    (hq : ∀ z ∉ c.region, q z = 0) : (∫ z in E, q z ∂μ) = ∫ z in c.graphDomain, q z ∂μ := by
  classical
  rw [← integral_indicator hE, ← integral_indicator c.isOpen_graphDomain.measurableSet]
  apply integral_congr_ae
  exact ae_of_all _ fun z => by
    by_cases hz : z ∈ c.region
    · have he : z ∈ E ↔ z ∈ c.graphDomain := by
        exact ⟨fun h => (hc.inter_eq ▸ (show z ∈ E ∩ c.region from ⟨h, hz⟩)).1,
          fun h => (hc.inter_eq.symm ▸ (show z ∈ c.graphDomain ∩ c.region from ⟨h, hz⟩)).1⟩
      simp only [Set.indicator_apply, he]
    · simp [Set.indicator_apply, hq z hz]

lemma C1BoundaryChart.IsChartFor.integral_boundaryArea_eq_graphArea {c : C1BoundaryChart}
    {E : Set AmbientSpace} (hc : c.IsChartFor E) (q : AmbientSpace → ℝ)
    (hq : ∀ z ∉ c.region, q z = 0) :
    (∫ z, q z ∂(hausdorffMeasure2 3).restrict (frontier E)) =
      ∫ z, q z ∂(hausdorffMeasure2 3).restrict c.graphSurface := by
  calc
    _ = ∫ z in c.region, q z ∂(hausdorffMeasure2 3).restrict (frontier E) :=
      (setIntegral_eq_integral_of_forall_compl_eq_zero hq).symm
    _ = ∫ z in c.region, q z ∂(hausdorffMeasure2 3).restrict c.graphSurface := by
      rw [hc.boundaryArea_restrict]
    _ = _ := setIntegral_eq_integral_of_forall_compl_eq_zero hq

/-- The actual supported-test cut identity in a boundary chart. The same fixed
ambient derivative can be used for every chart, and the surface measure is that
of the domain's topological boundary. -/
theorem C1BoundaryChart.IsChartFor.cut_pairing {c : C1BoundaryChart}
    {E : Set AmbientSpace} (hc : c.IsChartFor E) (hE : MeasurableSet E)
    {f : AmbientSpace → ℝ} (hf : IsLocallyBVOn f univ)
    {μ : Measure AmbientSpace} [SigmaFinite μ] {σ : AmbientSpace → AmbientSpace}
    (hσ : LocallyIntegrable σ μ)
    (hpair : ∀ (i : Fin 3) (φ : CompactlySupportedContinuousMap AmbientSpace ℝ),
      ContDiff ℝ 1 φ → -(∫ z, f z * fderiv ℝ φ z (EuclideanSpace.single i 1)) =
        ∫ z, φ z * σ z i ∂μ)
    (v : AmbientSpace) {φ : AmbientSpace → ℝ} (hφ : ContDiff ℝ 1 φ)
    (hcφ : HasCompactSupport φ) (hsφ : tsupport φ ⊆ c.region) :
    (∫ z in E, f z * fderiv ℝ φ z v) =
      -(∫ z in E, φ z * inner ℝ v (σ z) ∂μ) +
      ∫ z, c.lowerBVTrace f z * (φ z * inner ℝ v (c.outwardNormal z))
        ∂(hausdorffMeasure2 3).restrict (frontier E) := by
  have hz (z : AmbientSpace) (hcZ : z ∉ c.region) : z ∉ tsupport φ :=
    fun h => hcZ (hsφ h)
  rw [hc.setIntegral_eq_graphDomain hE (fun z => f z * fderiv ℝ φ z v)
    (fun z h => by rw [fderiv_of_notMem_tsupport ℝ (hz z h)]; simp),
    hc.setIntegral_eq_graphDomain hE (fun z => φ z * inner ℝ v (σ z))
      (fun z h => by rw [image_eq_zero_of_notMem_tsupport (hz z h), zero_mul]),
    hc.integral_boundaryArea_eq_graphArea
      (fun z => c.lowerBVTrace f z * (φ z * inner ℝ v (c.outwardNormal z)))
      (fun z h => by rw [image_eq_zero_of_notMem_tsupport (hz z h), zero_mul, mul_zero])]
  exact c.cut_pairing_of_coordinate_polar hf hσ hpair v hφ hcφ

end LiquidDrop

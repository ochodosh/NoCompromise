import NoCompromise.Cones.MinimalGraphEquation
import NoCompromise.DeGiorgi.AmbientPolar
import NoCompromise.Regularity.ApproxHarmonicTest
import NoCompromise.Regularity.ApproxHarmonicSupport

/-!
# Local first variation on a minimal graph

`minimal_graph_weak_equation` proves the weak minimal-surface equation for the
C¹ graph piece. The measure and normal identifications are local: no regularity
of the boundary outside the open comparison region is assumed. The epigraph
case is reduced to the subgraph case by complementing the minimizing set.
-/

noncomputable section
open MeasureTheory Set Filter Metric
open scoped Topology ENNReal Gradient
namespace LiquidDrop

/-- Agreement with a C¹ subgraph on an open region identifies the restricted
canonical perimeter measure with graph area. -/
theorem canonicalPerimeterMeasure_restrict_eq_smoothGraphArea
    {E U : Set AmbientSpace} (hE : HasLocallyFinitePerimeter E)
    (hmE : NullMeasurableSet E volume) (hU : IsOpen U)
    {g : EuclideanSpace ℝ (Fin 2) → ℝ} (hg : ContDiff ℝ 1 g)
    (he : E =ᵐ[volume.restrict U] smoothSubgraph g) :
    (canonicalPerimeterMeasure E hE hmE).restrict U = (smoothGraphArea g).restrict U := by
  let := (canonicalPerimeterPolar E hE hmE).regular
  let := smoothGraphArea_regular hg
  apply Measure.OuterRegular.ext_isOpen
  intro O hO
  rw [Measure.restrict_apply hO.measurableSet, Measure.restrict_apply hO.measurableSet,
    canonicalPerimeterMeasure_open E hE hmE (hO.inter hU)]
  exact perimeterIn_eq_smoothGraphArea_of_ae_eq hg (hO.inter hU)
    (ae_restrict_of_ae_restrict_of_subset inter_subset_right he)

/-- Compact scalar tests supported in a region of almost-everywhere subgraph
agreement have the classical graph boundary pairing. -/
theorem smoothSubgraph_local_directional_pairing_of_ae_eq
    {E U : Set AmbientSpace} (hmE : NullMeasurableSet E volume) (hU : IsOpen U)
    {g : EuclideanSpace ℝ (Fin 2) → ℝ} (hg : ContDiff ℝ 1 g)
    (he : E =ᵐ[volume.restrict U] smoothSubgraph g)
    {φ : AmbientSpace → ℝ} (hφ : ContDiff ℝ 1 φ) (hcφ : HasCompactSupport φ)
    (hsφ : tsupport φ ⊆ U) (v : AmbientSpace) :
    (∫ z in E, fderiv ℝ φ z v) =
      ∫ z, φ z * inner ℝ v (smoothSubgraphNormal g z) ∂smoothGraphArea g := by
  classical
  simp only [smoothSubgraphNormal]
  rw [← smoothSubgraph_directional_pairing_surface hg hφ hcφ v,
    ← integral_indicator₀ hmE,
    ← integral_indicator (isOpen_smoothSubgraph hg.continuous).measurableSet]
  apply integral_congr_ae
  filter_upwards [(ae_restrict_iff' hU.measurableSet).mp he] with z hz
  by_cases hs : z ∈ tsupport φ
  · have hez : z ∈ E ↔ z ∈ smoothSubgraph g := Iff.of_eq (hz (hsφ hs))
    simp only [Set.indicator_apply, hez]
  · simp [Set.indicator_apply, fderiv_of_notMem_tsupport ℝ hs]

/-- The canonical outward polar is the upward graph normal locally, without
any hypothesis on the rest of the boundary. -/
theorem canonicalOutwardPolarDensity_eq_smoothSubgraphNormal_locally
    {E U : Set AmbientSpace} (hE : HasLocallyFinitePerimeter E)
    (hmE : NullMeasurableSet E volume) (hU : IsOpen U)
    {g : EuclideanSpace ℝ (Fin 2) → ℝ} (hg : ContDiff ℝ 1 g)
    (he : E =ᵐ[volume.restrict U] smoothSubgraph g) :
    ∀ᵐ z ∂canonicalPerimeterMeasure E hE hmE, z ∈ U →
      canonicalOutwardPolarDensity E hE hmE z = smoothSubgraphNormal g z := by
  let μ := canonicalPerimeterMeasure E hE hmE
  let ν := canonicalOutwardPolarDensity E hE hmE
  have hp := canonicalPerimeterPolar E hE hmE
  let := hp.regular
  let := hp.finiteOnCompacts
  have hre := canonicalPerimeterMeasure_restrict_eq_smoothGraphArea hE hmE hU hg he
  have hint (q : AmbientSpace → ℝ) (hq : ∀ z ∉ U, q z = 0) :
      (∫ z, q z ∂μ) = ∫ z, q z ∂smoothGraphArea g := by
    rw [← setIntegral_eq_integral_of_forall_compl_eq_zero hq,
      ← setIntegral_eq_integral_of_forall_compl_eq_zero (μ := smoothGraphArea g) hq]
    rw [show μ.restrict U = (smoothGraphArea g).restrict U from hre]
  have hi (i : Fin 3) : LocallyIntegrable (fun z => ν z i) μ := by
    apply locallyIntegrable_iff.mpr
    intro K hK
    simpa only [Function.comp_def] using!
      (EuclideanSpace.proj i : AmbientSpace →L[ℝ] ℝ).integrable_comp
        (hp.locallyIntegrable.integrableOn_isCompact hK)
  have hj (i : Fin 3) : LocallyIntegrable (fun z => smoothSubgraphNormal g z i) μ :=
    ((EuclideanSpace.proj i).continuous.comp (continuous_smoothSubgraphNormal hg)).locallyIntegrable
  have ha (i : Fin 3) : ∀ᵐ z ∂μ, z ∈ U → ν z i = smoothSubgraphNormal g z i := by
    have hz := hU.ae_eq_zero_of_integral_contDiff_smul_eq_zero
      (((hi i).sub (hj i)).locallyIntegrableOn U) ?_
    · filter_upwards [hz] with z hz
      intro hzU
      exact sub_eq_zero.mp (hz hzU)
    intro q hq hcq hsq
    let φ : CompactlySupportedContinuousMap AmbientSpace ℝ := ⟨⟨q, hq.continuous⟩, hcq⟩
    have hφ : ContDiff ℝ 1 φ := hq.of_le (by simp)
    have hpair := hp.coordinate_eq i φ hφ
    have hid : (fun z => E.indicator (fun _ => (1 : ℝ)) z *
        fderiv ℝ φ z (EuclideanSpace.single i 1)) =
        E.indicator (fun z => fderiv ℝ φ z (EuclideanSpace.single i 1)) := by
      funext z
      by_cases hz : z ∈ E <;> simp [hz]
    rw [hid, integral_indicator₀ hmE] at hpair
    simp only [mul_neg, integral_neg, neg_inj] at hpair
    have hgraph := smoothSubgraph_local_directional_pairing_of_ae_eq hmE hU hg he
      hφ hcq hsq (EuclideanSpace.single i 1)
    simp only [EuclideanSpace.inner_single_left, map_one, one_mul] at hgraph
    have htrans := hint (fun z => q z * smoothSubgraphNormal g z i) (by
      intro z hz
      rw [image_eq_zero_of_notMem_tsupport (fun hs => hz (hsq hs)), zero_mul])
    have heqint : (∫ z, q z * ν z i ∂μ) = ∫ z, q z * smoothSubgraphNormal g z i ∂μ :=
      hpair.symm.trans (hgraph.trans htrans.symm)
    have hqi := (hi i).integrable_smul_left_of_hasCompactSupport hq.continuous hcq
    have hqj := (hj i).integrable_smul_left_of_hasCompactSupport hq.continuous hcq
    simp only [smul_eq_mul] at hqi hqj
    simp only [smul_eq_mul, Pi.sub_apply, mul_sub, integral_sub hqi hqj, heqint, sub_self]
  filter_upwards [ae_all_iff.mpr ha] with z hz
  intro hzU
  exact PiLp.ext (fun i => hz i hzU)

/-- A minimal set has zero graph first variation wherever it agrees almost
everywhere with a C¹ subgraph. -/
theorem minimal_graph_first_variation_of_ae_subgraph
    {E U : Set AmbientSpace} (hE : IsOmegaMinimal E 0) (hU : IsOpen U)
    {g : EuclideanSpace ℝ (Fin 2) → ℝ} (hg : ContDiff ℝ 1 g)
    (he : E =ᵐ[volume.restrict U] smoothSubgraph g)
    {X : AmbientSpace → AmbientSpace} (hX : ContDiff ℝ 1 X)
    (hcX : HasCompactSupport X) (hsX : tsupport X ⊆ U)
    (hbX : tsupport X ⊆ ball (0 : AmbientSpace) 1) :
    (∫ z, tangentialDivergence X (smoothSubgraphNormal g) z ∂smoothGraphArea g) = 0 := by
  have hv := hE.bounded_first_variation hX hcX hbX
  rw [← canonicalPerimeterMeasure_eq_reducedBoundary_area] at hv
  simp only [zero_mul, abs_nonpos_iff] at hv
  have hn := canonicalOutwardPolarDensity_eq_smoothSubgraphNormal_locally
    hE.locallyFinite hE.nullMeasurable hU hg he
  have hr := reducedNormal_ae_eq_polarDensity E hE.locallyFinite hE.nullMeasurable
  have hre := canonicalPerimeterMeasure_restrict_eq_smoothGraphArea
    hE.locallyFinite hE.nullMeasurable hU hg he
  have hz (ν : AmbientSpace → AmbientSpace) (z : AmbientSpace) (hz : z ∉ U) :
      tangentialDivergence X ν z = 0 :=
    tangentialDivergence_eq_zero_of_notMem_tsupport (fun ht => hz (hsX ht))
  calc
    _ = ∫ z in U, tangentialDivergence X (smoothSubgraphNormal g) z
        ∂smoothGraphArea g := (setIntegral_eq_integral_of_forall_compl_eq_zero (hz _)).symm
    _ = ∫ z in U, tangentialDivergence X (smoothSubgraphNormal g) z
        ∂canonicalPerimeterMeasure E hE.locallyFinite hE.nullMeasurable := by rw [hre]
    _ = ∫ z, tangentialDivergence X (smoothSubgraphNormal g) z
        ∂canonicalPerimeterMeasure E hE.locallyFinite hE.nullMeasurable :=
      setIntegral_eq_integral_of_forall_compl_eq_zero (hz _)
    _ = ∫ z, tangentialDivergence X
        (reducedNormal E hE.locallyFinite hE.nullMeasurable) z
        ∂canonicalPerimeterMeasure E hE.locallyFinite hE.nullMeasurable := by
      apply integral_congr_ae
      filter_upwards [hn, hr] with z hn hr
      by_cases hzU : z ∈ U
      · simp only [tangentialDivergence, hr.trans (hn hzU)]
      · rw [hz _ z hzU, hz _ z hzU]
    _ = 0 := hv

/-- The weighted graph first variation of a vertical tensor is precisely the
weak minimal-surface integrand when its height cutoff is flat on the tested graph. -/
theorem minimal_graph_vertical_integral
    {g φ : EuclideanSpace ℝ (Fin 2) → ℝ} (hg : ContDiff ℝ 1 g)
    (hφ : ContDiff ℝ 1 φ) {ψ : ℝ → ℝ} (hψ : ContDiff ℝ 1 ψ)
    (hflat : ∀ y ∈ tsupport φ, ψ (g y) = 1 ∧ deriv ψ (g y) = 0) :
    (∫ z, tangentialDivergence
      (fun x : AmbientSpace => (φ (graphProjectionN 2 x) * ψ (x 2)) •
        EuclideanSpace.single 2 1) (smoothSubgraphNormal g) z ∂smoothGraphArea g) =
      ∫ y, inner ℝ (gradient g y) (gradient φ y) /
        Real.sqrt (1 + ‖gradient g y‖ ^ 2) := by
  rw [integral_smoothGraphArea hg]
  apply integral_congr_ae
  filter_upwards with y
  have hp : graphProjectionN 2 (graphMapN g y) = y := graphProjectionN_append y (g y)
  by_cases hy : y ∈ tsupport φ
  · obtain ⟨hflat₀, hflat₁⟩ := hflat y hy
    have hheight : graphMapN g y 2 = g y := graphMapN_last g y
    rw [tangentialDivergence_vertical_tensor hφ hψ (smoothSubgraphNormal g)
      (graphMapN g y) (hheight ▸ hflat₀) (hheight ▸ hflat₁)]
    simp only [smoothSubgraphNormal, hp, smoothGraphUnitNormal, PiLp.smul_apply,
      graphAppendN_height_three, smul_eq_mul, mul_one, map_smul,
      graphProjectionN_append, map_neg]
    rw [← inner_gradient_left, real_inner_comm (gradient φ y)]
    have hq : Real.sqrt (1 + ‖gradient g y‖ ^ 2) ≠ 0 := ne_of_gt (by positivity)
    field_simp
  · have hs : graphMapN g y ∉ tsupport (fun x : AmbientSpace =>
        (φ (graphProjectionN 2 x) * ψ (x 2)) • EuclideanSpace.single (2 : Fin 3) (1 : ℝ)) := by
      intro hs
      have hb := (tsupport_vertical_tensor_subset φ ψ
        (tsupport_smul_subset_left _ _ hs)).1
      exact hy (hp ▸ hb)
    rw [tangentialDivergence_eq_zero_of_notMem_tsupport hs,
      gradient_eq_zero_of_notMem_tsupport hy, inner_zero_right, zero_div, mul_zero]

/-- The weak equation for a global C¹ height when the minimizing set occupies
its subgraph in a neighborhood containing the entire tested vertical slab. -/
theorem minimal_graph_weak_equation_of_ae_subgraph
    {E U : Set AmbientSpace} (hE : IsOmegaMinimal E 0) (hU : IsOpen U)
    {ρ : ℝ} (hρ : 0 < ρ) (hρ1 : ρ ≤ 1 / 2)
    {g φ : EuclideanSpace ℝ (Fin 2) → ℝ} (hg : ContDiff ℝ 1 g)
    (he : E =ᵐ[volume.restrict U] smoothSubgraph g)
    (hφ : ContDiff ℝ 1 φ) (hcφ : HasCompactSupport φ)
    (hsφ : tsupport φ ⊆ ball (0 : EuclideanSpace ℝ (Fin 2)) ρ)
    (hh : ∀ y ∈ tsupport φ, |g y| < ρ / 2)
    (hslab : ∀ z ∈ standardCylinder ρ, graphProjectionN 2 z ∈ tsupport φ → z ∈ U) :
    ∫ y, inner ℝ (gradient g y) (gradient φ y) /
      Real.sqrt (1 + ‖gradient g y‖ ^ 2) = 0 := by
  let ψ : ContDiffBump (0 : ℝ) := ⟨ρ / 2, 3 * ρ / 4, by positivity, by linarith⟩
  have hsψ : tsupport ψ ⊆ Ioo (-ρ) ρ := by
    intro t ht
    rw [ψ.tsupport_eq] at ht
    have ht' : |t| ≤ 3 * ρ / 4 := by
      simpa only [mem_closedBall, Real.dist_eq, sub_zero] using ht
    exact abs_lt.mp (ht'.trans_lt (by linarith))
  have hflat : ∀ y ∈ tsupport φ, ψ (g y) = 1 ∧ deriv ψ (g y) = 0 := by
    intro y hy
    have hm : g y ∈ ball 0 ψ.rIn := by
      simpa only [mem_ball, Real.dist_eq, sub_zero] using hh y hy
    refine ⟨ψ.one_of_mem_closedBall (ball_subset_closedBall hm), ?_⟩
    simpa only [Pi.one_def, deriv_const] using
      (ψ.eventuallyEq_one_of_mem_ball hm).deriv_eq
  let X : AmbientSpace → AmbientSpace := fun z =>
    (φ (graphProjectionN 2 z) * ψ (z 2)) • EuclideanSpace.single 2 1
  have hX : ContDiff ℝ 1 X :=
    ((hφ.comp (graphProjectionN 2).contDiff).mul
      (ψ.contDiff.comp
        (EuclideanSpace.proj (2 : Fin 3) : AmbientSpace →L[ℝ] ℝ).contDiff)).smul contDiff_const
  have hcX : HasCompactSupport X := vertical_field_compact_support hcφ ψ.hasCompactSupport
  have hsX : tsupport X ⊆ standardCylinder ρ :=
    tsupport_vertical_field_subset_cylinder hsφ hsψ
  have hXU : tsupport X ⊆ U := by
    intro z hz
    exact hslab z (hsX hz)
      (tsupport_vertical_tensor_subset φ ψ (tsupport_smul_subset_left _ _ hz)).1
  have hXB : tsupport X ⊆ ball (0 : AmbientSpace) 1 := by
    apply hsX.trans
    apply Subset.trans (b := standardCylinder (1 / 2))
    · intro z hz
      exact ⟨hz.1.trans_le hρ1, hz.2.trans_le hρ1⟩
    · exact standardCylinder_half_subset_unit_ball
  rw [← minimal_graph_vertical_integral hg hφ ψ.contDiff hflat]
  exact minimal_graph_first_variation_of_ae_subgraph hE hU hg he hX hcX hXU hXB

/-- A C¹ graph piece of the boundary of a perimeter minimizer satisfies the
weak minimal-surface equation, independently of which side is occupied. -/
theorem minimal_graph_weak_equation {E : Set AmbientSpace} (hE : IsOmegaMinimal E 0)
    {ρ : ℝ} (hρ : 0 < ρ) (hρ1 : ρ ≤ 1 / 2) {f : EuclideanSpace ℝ (Fin 2) → ℝ}
    (hgraph : frontier (densityOne E) ∩ standardCylinder ρ =
      (fun x' => graphAppendN x' (f x')) '' ball (0 : EuclideanSpace ℝ (Fin 2)) ρ)
    (hf : ∀ x' ∈ ball (0 : EuclideanSpace ℝ (Fin 2)) ρ, |f x'| < ρ / 2)
    (hC1 : ContDiffOn ℝ 1 f (ball (0 : EuclideanSpace ℝ (Fin 2)) ρ))
    {φ : EuclideanSpace ℝ (Fin 2) → ℝ} (hφ : ContDiff ℝ 1 φ) (hcφ : HasCompactSupport φ)
    (hsφ : tsupport φ ⊆ ball (0 : EuclideanSpace ℝ (Fin 2)) ρ) :
    ∫ y, inner ℝ (gradient f y) (gradient φ y) / Real.sqrt (1 + ‖gradient f y‖ ^ 2) = 0 := by
  obtain ⟨g, hg, hgf, hI⟩ := minimal_graph_weak_integral_localization hC1 hcφ hsφ
  rw [hI]
  let V := ball (0 : EuclideanSpace ℝ (Fin 2)) ρ ∩ interior {y | g y = f y}
  have hV : IsOpen V := isOpen_ball.inter isOpen_interior
  have hsV : tsupport φ ⊆ V := fun y hy =>
    ⟨hsφ hy, mem_interior_iff_mem_nhds.mpr (hgf y hy)⟩
  have hgV : ∀ y ∈ V, g y = f y := by
    intro y hy
    exact (show y ∈ {y | g y = f y} from interior_subset hy.2)
  let U : Set AmbientSpace := standardCylinder ρ ∩ graphProjectionN 2 ⁻¹' V
  have hU : IsOpen U := (isOpen_standardCylinder ρ).inter
    (hV.preimage (graphProjectionN 2).continuous)
  have hUC : U ⊆ standardCylinder ρ := inter_subset_left
  have hslab : ∀ z ∈ standardCylinder ρ, graphProjectionN 2 z ∈ tsupport φ → z ∈ U :=
    fun _ hz hy => ⟨hz, hsV hy⟩
  have hh : ∀ y ∈ tsupport φ, |g y| < ρ / 2 := by
    intro y hy
    rw [hgV y (hsV hy)]
    exact hf y (hsφ hy)
  have hsub : smoothSubgraph f =ᵐ[volume.restrict U] smoothSubgraph g := by
    filter_upwards [ae_restrict_mem hU.measurableSet] with z hz
    change (z 2 < f (graphProjectionN 2 z)) = (z 2 < g (graphProjectionN 2 z))
    rw [hgV _ hz.2]
  have hepi : smoothEpigraph f =ᵐ[volume.restrict U] smoothEpigraph g := by
    filter_upwards [ae_restrict_mem hU.measurableSet] with z hz
    change (f (graphProjectionN 2 z) < z 2) = (g (graphProjectionN 2 z) < z 2)
    rw [hgV _ hz.2]
  rcases minimal_graph_ae_subgraph_or_epigraph hE hρ hgraph hf hC1.continuousOn with he | he
  · have heU : E =ᵐ[volume.restrict U] smoothSubgraph f :=
      ae_restrict_of_ae_restrict_of_subset hUC he
    exact minimal_graph_weak_equation_of_ae_subgraph hE hU hρ hρ1 hg
      (heU.trans hsub) hφ hcφ hsφ hh hslab
  · have he' : E =ᵐ[volume.restrict U] (smoothSubgraph g)ᶜ :=
      (Filter.EventuallyEq.trans (ae_restrict_of_ae_restrict_of_subset hUC he) hepi).trans
        (ae_restrict_of_ae (smoothEpigraph_ae_compl hg.continuous))
    have he'' : Eᶜ =ᵐ[volume.restrict U] smoothSubgraph g := by
      filter_upwards [he'.compl] with z hz
      exact hz.trans (propext not_not)
    exact minimal_graph_weak_equation_of_ae_subgraph hE.compl hU hρ hρ1 hg he''
      hφ hcφ hsφ hh hslab

end LiquidDrop

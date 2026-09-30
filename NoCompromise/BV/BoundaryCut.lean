module

public import NoCompromise.BV.BoundaryTraceAtlas
public import NoCompromise.BV.LocalToGlobal
public import NoCompromise.BV.ScalarDistributionGluing

@[expose] public section

/-!
# Cutting a locally BV function along a C¹ boundary

Local graph cuts first give genuine local BV regularity of the cut function.
The actual distributional derivative is then identified with its bulk and
boundary terms by local test identities.
-/

noncomputable section
open MeasureTheory Set Filter Metric
open scoped ENNReal Topology
namespace LiquidDrop
set_option maxSynthPendingDepth 8

/-- Cutting by an open C¹ domain preserves local BV, without boundedness of the
function or the domain and without a global variation hypothesis. -/
theorem HasC1Boundary.indicator_isLocallyBV {E : Set AmbientSpace}
    (h : HasC1Boundary E) (hE : IsOpen E) {f : AmbientSpace → ℝ}
    (hf : IsLocallyBVOn f univ) : IsLocallyBVOn (E.indicator f) univ := by
  classical
  apply isLocallyBVOn_univ_of_local_variation
    ((locallyIntegrableOn_univ.mp hf.1).indicator hE.measurableSet)
  intro x
  by_cases hx : x ∈ frontier E
  · obtain ⟨c, hc, hxc⟩ := h x hx
    refine ⟨c.region, c.isOpen_region, hxc, ?_⟩
    have he : E.indicator f =ᵐ[volume.restrict c.region] c.graphDomain.indicator f := by
      filter_upwards [ae_restrict_mem c.isOpen_region.measurableSet] with z hz
      have hez : z ∈ E ↔ z ∈ c.graphDomain := by
        exact ⟨fun h => (hc.inter_eq ▸ (show z ∈ E ∩ c.region from ⟨h, hz⟩)).1,
          fun h => (hc.inter_eq.symm ▸
            (show z ∈ c.graphDomain ∩ c.region from ⟨h, hz⟩)).1⟩
      simp only [Set.indicator_apply, hez]
    rw [variation_congr_ae c.region he]
    exact (c.indicator_graphDomain_isLocallyBV hf).2 c.region c.isOpen_region
      c.bounded_region.isCompact_closure (subset_univ _)
  · have hx' : x ∈ interior E ∪ interior Eᶜ := by
      rw [← compl_frontier_eq_union_interior]
      exact hx
    rcases hx' with hx' | hx'
    · let V := interior E ∩ ball x 1
      have hV : IsOpen V := isOpen_interior.inter isOpen_ball
      refine ⟨V, hV, ⟨hx', mem_ball_self zero_lt_one⟩, ?_⟩
      have he : E.indicator f =ᵐ[volume.restrict V] f := by
        filter_upwards [ae_restrict_mem hV.measurableSet] with z hz
        exact Set.indicator_of_mem (interior_subset hz.1) f
      rw [variation_congr_ae V he]
      exact hf.2 V hV (isBounded_ball.subset inter_subset_right).isCompact_closure
        (subset_univ _)
    · let V := interior Eᶜ ∩ ball x 1
      have hV : IsOpen V := isOpen_interior.inter isOpen_ball
      refine ⟨V, hV, ⟨hx', mem_ball_self zero_lt_one⟩, ?_⟩
      have he : E.indicator f =ᵐ[volume.restrict V] (fun _ => 0) := by
        filter_upwards [ae_restrict_mem hV.measurableSet] with z hz
        exact Set.indicator_of_notMem (interior_subset hz.1) f
      rw [variation_congr_ae V he, variation_zero]
      exact ENNReal.zero_lt_top

/-- A positive measure carrying the disjoint bulk and boundary contributions. -/
def boundaryCutMeasure (E : Set AmbientSpace) (μ : Measure AmbientSpace) :
    Measure AmbientSpace := μ.restrict E + (hausdorffMeasure2 3).restrict (frontier E)

/-- The signed vector density of a cut: original derivative in the domain,
minus the interior trace times the outward normal on the boundary. -/
def boundaryCutDensity (E : Set AmbientSpace) (σ : AmbientSpace → AmbientSpace)
    (T : AmbientSpace → ℝ) (ν : AmbientSpace → AmbientSpace) (z : AmbientSpace) :
    AmbientSpace := @ite AmbientSpace (z ∈ E) (Classical.propDecidable _)
      (σ z) (-T z • ν z)

lemma boundaryCutDensity_ae_bulk {E : Set AmbientSpace} (hE : MeasurableSet E)
    (μ : Measure AmbientSpace) (σ : AmbientSpace → AmbientSpace)
    (T : AmbientSpace → ℝ) (ν : AmbientSpace → AmbientSpace) :
    boundaryCutDensity E σ T ν =ᵐ[μ.restrict E] σ := by
  filter_upwards [ae_restrict_mem hE] with z hz
  exact ite_eq_left hz

lemma boundaryCutDensity_ae_surface {E : Set AmbientSpace} (hE : IsOpen E)
    (σ : AmbientSpace → AmbientSpace) (T : AmbientSpace → ℝ)
    (ν : AmbientSpace → AmbientSpace) :
    boundaryCutDensity E σ T ν =ᵐ[(hausdorffMeasure2 3).restrict (frontier E)]
      (fun z => -T z • ν z) := by
  filter_upwards [ae_restrict_mem isClosed_frontier.measurableSet] with z hz
  apply ite_eq_right
  exact fun he => disjoint_interior_frontier.le_bot ⟨hE.interior_eq.symm ▸ he, hz⟩

lemma locallyIntegrable_boundaryCutDensity {E : Set AmbientSpace} (hE : IsOpen E)
    {μ : Measure AmbientSpace} {σ ν : AmbientSpace → AmbientSpace}
    {T : AmbientSpace → ℝ} (hσ : LocallyIntegrable σ μ)
    (hT : Integrable T ((hausdorffMeasure2 3).restrict (frontier E)))
    (hν : AEStronglyMeasurable ν ((hausdorffMeasure2 3).restrict (frontier E)))
    (hn : ∀ᵐ z ∂(hausdorffMeasure2 3).restrict (frontier E), ‖ν z‖ ≤ 1) :
    LocallyIntegrable (boundaryCutDensity E σ T ν) (boundaryCutMeasure E μ) := by
  have hb := (hσ.mono_measure (Measure.restrict_le_self (s := E))).congr
    (boundaryCutDensity_ae_bulk hE.measurableSet μ σ T ν).symm
  have hs := ((hT.neg.smul_bdd 1 hν hn).locallyIntegrable).congr
    (boundaryCutDensity_ae_surface hE σ T ν).symm
  apply locallyIntegrable_iff.mpr
  intro K hK
  exact (hb.integrableOn_isCompact hK).add_measure (hs.integrableOn_isCompact hK)

lemma integral_coordinate_boundaryCutDensity {E : Set AmbientSpace} (hE : IsOpen E)
    {μ : Measure AmbientSpace} {σ ν : AmbientSpace → AmbientSpace}
    {T : AmbientSpace → ℝ} (hσ : LocallyIntegrable σ μ)
    (hT : Integrable T ((hausdorffMeasure2 3).restrict (frontier E)))
    (hν : AEStronglyMeasurable ν ((hausdorffMeasure2 3).restrict (frontier E)))
    (hn : ∀ᵐ z ∂(hausdorffMeasure2 3).restrict (frontier E), ‖ν z‖ ≤ 1)
    (i : Fin 3) (φ : CompactlySupportedContinuousMap AmbientSpace ℝ) :
    (∫ z, φ z * boundaryCutDensity E σ T ν z i ∂boundaryCutMeasure E μ) =
      (∫ z in E, φ z * σ z i ∂μ) -
        ∫ z, T z * (φ z * ν z i) ∂(hausdorffMeasure2 3).restrict (frontier E) := by
  have hi : Integrable (fun z => φ z * boundaryCutDensity E σ T ν z i)
      (boundaryCutMeasure E μ) := by
    simpa only [smul_eq_mul, mul_comm] using!
      (locallyIntegrable_scalar_component
        (locallyIntegrable_boundaryCutDensity hE hσ hT hν hn) i
        ).integrable_smul_right_of_hasCompactSupport φ.continuous φ.hasCompactSupport
  have hib : Integrable (fun z => φ z * boundaryCutDensity E σ T ν z i)
      (μ.restrict E) := hi.mono_measure (Measure.le_add_right le_rfl)
  have his : Integrable (fun z => φ z * boundaryCutDensity E σ T ν z i)
      ((hausdorffMeasure2 3).restrict (frontier E)) :=
    hi.mono_measure (Measure.le_add_left le_rfl)
  rw [boundaryCutMeasure, integral_add_measure hib his]
  have hb : (∫ z in E, φ z * boundaryCutDensity E σ T ν z i ∂μ) =
      ∫ z in E, φ z * σ z i ∂μ := integral_congr_ae
    ((boundaryCutDensity_ae_bulk hE.measurableSet μ σ T ν).mono fun z hz => by dsimp only; rw [hz])
  have hs : (∫ z, φ z * boundaryCutDensity E σ T ν z i
      ∂(hausdorffMeasure2 3).restrict (frontier E)) =
      -(∫ z, T z * (φ z * ν z i) ∂(hausdorffMeasure2 3).restrict (frontier E)) := by
    rw [← integral_neg]
    apply integral_congr_ae
    filter_upwards [boundaryCutDensity_ae_surface hE σ T ν] with z hz
    rw [hz, PiLp.smul_apply, smul_eq_mul]
    ring
  rw [hb, hs, sub_eq_add_neg]

/-- The coordinate cut identity is valid on some neighborhood of each point;
its boundary trace and normal are identified with the actual chart quantities. -/
lemma HasC1Boundary.local_cut_coordinate_pairing {E : Set AmbientSpace}
    (h : HasC1Boundary E) (hE : IsOpen E) {f : AmbientSpace → ℝ}
    (hf : IsLocallyBVOn f univ) {μ : Measure AmbientSpace} [SigmaFinite μ]
    {σ ν : AmbientSpace → AmbientSpace} {T : AmbientSpace → ℝ}
    (hσ : LocallyIntegrable σ μ)
    (hpair : ∀ (i : Fin 3) (φ : CompactlySupportedContinuousMap AmbientSpace ℝ),
      ContDiff ℝ 1 φ → -(∫ z, f z * fderiv ℝ φ z (EuclideanSpace.single i 1)) =
        ∫ z, φ z * σ z i ∂μ)
    (hT : ∀ c : C1BoundaryChart, c.IsChartFor E →
      ∀ᵐ z ∂(hausdorffMeasure2 3).restrict (frontier E), z ∈ c.region →
        T z = c.lowerBVTrace f z)
    (hν : ∀ c : C1BoundaryChart, c.IsChartFor E →
      ∀ᵐ z ∂(hausdorffMeasure2 3).restrict (frontier E), z ∈ c.region →
        ν z = c.outwardNormal z) :
    ∀ x, ∃ U : Set AmbientSpace, IsOpen U ∧ x ∈ U ∧
      ∀ (i : Fin 3) (φ : CompactlySupportedContinuousMap AmbientSpace ℝ),
        ContDiff ℝ 1 φ → tsupport φ ⊆ U →
          (∫ z in E, f z * fderiv ℝ φ z (EuclideanSpace.single i 1)) =
            -(∫ z in E, φ z * σ z i ∂μ) +
              ∫ z, T z * (φ z * ν z i)
                ∂(hausdorffMeasure2 3).restrict (frontier E) := by
  intro x
  by_cases hx : x ∈ frontier E
  · obtain ⟨c, hc, hxc⟩ := h x hx
    refine ⟨c.region, c.isOpen_region, hxc, fun i φ hφ hsφ => ?_⟩
    have ht := hc.cut_pairing hE.measurableSet hf hσ hpair
      (EuclideanSpace.single i 1) hφ φ.hasCompactSupport hsφ
    simp only [EuclideanSpace.inner_single_left, map_one, one_mul] at ht
    rw [ht]
    congr 1
    apply integral_congr_ae
    filter_upwards [hT c hc, hν c hc] with z hTz hνz
    by_cases hz : z ∈ c.region
    · rw [hTz hz, hνz hz]
    · rw [image_eq_zero_of_notMem_tsupport (fun hh => hz (hsφ hh))]
      simp
  · have hx' : x ∈ interior E ∪ interior Eᶜ := by
      rw [← compl_frontier_eq_union_interior]
      exact hx
    rcases hx' with hx' | hx'
    · refine ⟨E, hE, interior_subset hx', fun i φ hφ hsφ => ?_⟩
      have hl : (∫ z in E, f z * fderiv ℝ φ z (EuclideanSpace.single i 1)) =
          ∫ z, f z * fderiv ℝ φ z (EuclideanSpace.single i 1) := by
        apply setIntegral_eq_integral_of_forall_compl_eq_zero
        intro z hz
        rw [fderiv_of_notMem_tsupport ℝ (fun hh => hz (hsφ hh))]
        simp
      have hb : (∫ z in E, φ z * σ z i ∂μ) = ∫ z, φ z * σ z i ∂μ := by
        apply setIntegral_eq_integral_of_forall_compl_eq_zero
        intro z hz
        rw [image_eq_zero_of_notMem_tsupport (fun hh => hz (hsφ hh)), zero_mul]
      have hs : (∫ z, T z * (φ z * ν z i)
          ∂(hausdorffMeasure2 3).restrict (frontier E)) = 0 := by
        apply integral_eq_zero_of_ae
        filter_upwards [ae_restrict_mem isClosed_frontier.measurableSet] with z hz
        have hze : z ∉ E := fun he =>
          disjoint_interior_frontier.le_bot ⟨hE.interior_eq.symm ▸ he, hz⟩
        rw [image_eq_zero_of_notMem_tsupport (fun hh => hze (hsφ hh))]
        simp
      rw [hl, hb, hs, add_zero, ← hpair i φ hφ, neg_neg]
    · refine ⟨interior Eᶜ, isOpen_interior, hx', fun i φ _ hsφ => ?_⟩
      have hl : (∫ z in E, f z * fderiv ℝ φ z (EuclideanSpace.single i 1)) = 0 := by
        apply integral_eq_zero_of_ae
        filter_upwards [ae_restrict_mem hE.measurableSet] with z hz
        have hzs : z ∉ tsupport φ := fun hh => (interior_subset (hsφ hh)) hz
        rw [fderiv_of_notMem_tsupport ℝ hzs]
        simp
      have hb : (∫ z in E, φ z * σ z i ∂μ) = 0 := by
        apply integral_eq_zero_of_ae
        filter_upwards [ae_restrict_mem hE.measurableSet] with z hz
        rw [image_eq_zero_of_notMem_tsupport (fun hh => (interior_subset (hsφ hh)) hz)]
        simp
      have hs : (∫ z, T z * (φ z * ν z i)
          ∂(hausdorffMeasure2 3).restrict (frontier E)) = 0 := by
        apply integral_eq_zero_of_ae
        filter_upwards [ae_restrict_mem isClosed_frontier.measurableSet] with z hz
        have hzi : z ∉ interior Eᶜ := fun hz' =>
          disjoint_interior_frontier.le_bot ⟨hz', (frontier_compl (s := E)).symm ▸ hz⟩
        rw [image_eq_zero_of_notMem_tsupport (fun hh => hzi (hsφ hh))]
        simp
      rw [hl, hb, hs]
      simp

/-- The actual coordinate derivative of the cut, identified globally from the
proved local traces and geometric chart normals. -/
theorem HasC1Boundary.cut_coordinate_pairing {E : Set AmbientSpace}
    (h : HasC1Boundary E) (hE : IsOpen E) {f : AmbientSpace → ℝ}
    (hf : IsLocallyBVOn f univ) {μ : Measure AmbientSpace} [SigmaFinite μ]
    {σ ν : AmbientSpace → AmbientSpace} {T : AmbientSpace → ℝ}
    (hσ : LocallyIntegrable σ μ)
    (hpair : ∀ (i : Fin 3) (φ : CompactlySupportedContinuousMap AmbientSpace ℝ),
      ContDiff ℝ 1 φ → -(∫ z, f z * fderiv ℝ φ z (EuclideanSpace.single i 1)) =
        ∫ z, φ z * σ z i ∂μ)
    (hTi : Integrable T ((hausdorffMeasure2 3).restrict (frontier E)))
    (hνm : AEStronglyMeasurable ν ((hausdorffMeasure2 3).restrict (frontier E)))
    (hn : ∀ᵐ z ∂(hausdorffMeasure2 3).restrict (frontier E), ‖ν z‖ ≤ 1)
    (hT : ∀ c : C1BoundaryChart, c.IsChartFor E →
      ∀ᵐ z ∂(hausdorffMeasure2 3).restrict (frontier E), z ∈ c.region →
        T z = c.lowerBVTrace f z)
    (hν : ∀ c : C1BoundaryChart, c.IsChartFor E →
      ∀ᵐ z ∂(hausdorffMeasure2 3).restrict (frontier E), z ∈ c.region →
        ν z = c.outwardNormal z)
    (i : Fin 3) (φ : CompactlySupportedContinuousMap AmbientSpace ℝ)
    (hφ : ContDiff ℝ 1 φ) :
    -(∫ z, E.indicator f z * fderiv ℝ φ z (EuclideanSpace.single i 1)) =
      ∫ z, φ z * boundaryCutDensity E σ T ν z i ∂boundaryCutMeasure E μ := by
  classical
  let := h.boundaryArea_finiteOnCompacts hE
  have : SigmaFinite (boundaryCutMeasure E μ) := inferInstanceAs
    (SigmaFinite (μ.restrict E + (hausdorffMeasure2 3).restrict (frontier E)))
  obtain ⟨ρ, τ, hρ, hρfin, _, _, hτ, hpτ, _⟩ :=
    (h.indicator_isLocallyBV hE hf).exists_ambient_scalar_polar
  let : ρ.Regular := hρ
  let : IsFiniteMeasureOnCompacts ρ := hρfin
  have hD := locallyIntegrable_boundaryCutDensity hE hσ hTi hνm hn
  have hl := h.local_cut_coordinate_pairing hE hf hσ hpair hT hν
  have hind (ψ : AmbientSpace → ℝ) :
      (∫ z, E.indicator f z * ψ z) = ∫ z in E, f z * ψ z := by
    have hh : (fun z => E.indicator f z * ψ z) = E.indicator (fun z => f z * ψ z) := by
      funext z
      by_cases hz : z ∈ E <;> simp [hz]
    rw [hh, integral_indicator hE.measurableSet]
  have he := integral_inner_eq_of_locally_coordinate_pairings hτ hD (by
    intro x
    obtain ⟨U, hU, hxU, hpU⟩ := hl x
    refine ⟨U, hU, hxU, fun j ψ hψ hsψ => ?_⟩
    rw [← hpτ j ψ hψ, hind,
      integral_coordinate_boundaryCutDensity hE hσ hTi hνm hn,
      hpU j ψ hψ hsψ]
    ring) (fun z => φ z • EuclideanSpace.single i 1)
  simp only [real_inner_smul_left, EuclideanSpace.inner_single_left, map_one, one_mul] at he
  exact (hpτ i φ hφ).trans he

lemma integral_inner_boundaryCutDensity {E : Set AmbientSpace} (hE : IsOpen E)
    {μ : Measure AmbientSpace} {σ ν : AmbientSpace → AmbientSpace}
    {T : AmbientSpace → ℝ} (hσ : LocallyIntegrable σ μ)
    (hT : Integrable T ((hausdorffMeasure2 3).restrict (frontier E)))
    (hν : AEStronglyMeasurable ν ((hausdorffMeasure2 3).restrict (frontier E)))
    (hn : ∀ᵐ z ∂(hausdorffMeasure2 3).restrict (frontier E), ‖ν z‖ ≤ 1)
    {X : AmbientSpace → AmbientSpace} (hX : Continuous X) (hcX : HasCompactSupport X) :
    (∫ z, inner ℝ (X z) (boundaryCutDensity E σ T ν z) ∂boundaryCutMeasure E μ) =
      (∫ z in E, inner ℝ (X z) (σ z) ∂μ) -
        ∫ z, T z * inner ℝ (X z) (ν z)
          ∂(hausdorffMeasure2 3).restrict (frontier E) := by
  have hi := integrable_inner_density_compact
    (locallyIntegrable_boundaryCutDensity hE hσ hT hν hn) hX hcX
  have hib : Integrable (fun z => inner ℝ (X z) (boundaryCutDensity E σ T ν z))
      (μ.restrict E) := hi.mono_measure (Measure.le_add_right le_rfl)
  have his : Integrable (fun z => inner ℝ (X z) (boundaryCutDensity E σ T ν z))
      ((hausdorffMeasure2 3).restrict (frontier E)) :=
    hi.mono_measure (Measure.le_add_left le_rfl)
  rw [boundaryCutMeasure, integral_add_measure hib his]
  have hb : (∫ z in E, inner ℝ (X z) (boundaryCutDensity E σ T ν z) ∂μ) =
      ∫ z in E, inner ℝ (X z) (σ z) ∂μ := integral_congr_ae
    ((boundaryCutDensity_ae_bulk hE.measurableSet μ σ T ν).mono fun z hz => by dsimp only; rw [hz])
  have hs : (∫ z, inner ℝ (X z) (boundaryCutDensity E σ T ν z)
      ∂(hausdorffMeasure2 3).restrict (frontier E)) =
      -(∫ z, T z * inner ℝ (X z) (ν z)
        ∂(hausdorffMeasure2 3).restrict (frontier E)) := by
    rw [← integral_neg]
    apply integral_congr_ae
    filter_upwards [boundaryCutDensity_ae_surface hE σ T ν] with z hz
    rw [hz, inner_smul_right, neg_mul]
  rw [hb, hs, sub_eq_add_neg]

/-- Global Gauss--Green formula for the interior trace, with an arbitrary genuine
ambient distributional representation of the original locally BV function. -/
theorem HasC1Boundary.cut_pairing {E : Set AmbientSpace}
    (h : HasC1Boundary E) (hE : IsOpen E) {f : AmbientSpace → ℝ}
    (hf : IsLocallyBVOn f univ) {μ : Measure AmbientSpace} [SigmaFinite μ]
    {σ ν : AmbientSpace → AmbientSpace} {T : AmbientSpace → ℝ}
    (hσ : LocallyIntegrable σ μ)
    (hpair : ∀ (i : Fin 3) (φ : CompactlySupportedContinuousMap AmbientSpace ℝ),
      ContDiff ℝ 1 φ → -(∫ z, f z * fderiv ℝ φ z (EuclideanSpace.single i 1)) =
        ∫ z, φ z * σ z i ∂μ)
    (hTi : Integrable T ((hausdorffMeasure2 3).restrict (frontier E)))
    (hνm : AEStronglyMeasurable ν ((hausdorffMeasure2 3).restrict (frontier E)))
    (hn : ∀ᵐ z ∂(hausdorffMeasure2 3).restrict (frontier E), ‖ν z‖ ≤ 1)
    (hT : ∀ c : C1BoundaryChart, c.IsChartFor E →
      ∀ᵐ z ∂(hausdorffMeasure2 3).restrict (frontier E), z ∈ c.region →
        T z = c.lowerBVTrace f z)
    (hν : ∀ c : C1BoundaryChart, c.IsChartFor E →
      ∀ᵐ z ∂(hausdorffMeasure2 3).restrict (frontier E), z ∈ c.region →
        ν z = c.outwardNormal z)
    {X : AmbientSpace → AmbientSpace} (hX : ContDiff ℝ 1 X) (hcX : HasCompactSupport X) :
    (∫ z in E, f z * divergenceN X z) =
      -(∫ z in E, inner ℝ (X z) (σ z) ∂μ) +
        ∫ z, T z * inner ℝ (X z) (ν z)
          ∂(hausdorffMeasure2 3).restrict (frontier E) := by
  have ht := integral_divergence_eq_sum_of_coordinate_pairings
    (ι := Unit) (μ := fun _ => boundaryCutMeasure E μ)
    (σ := fun _ => boundaryCutDensity E σ T ν)
    ((locallyIntegrableOn_univ.mp hf.1).indicator hE.measurableSet)
    (fun _ => locallyIntegrable_boundaryCutDensity hE hσ hTi hνm hn)
    (fun i φ hφ => by simpa using
      h.cut_coordinate_pairing hE hf hσ hpair hTi hνm hn hT hν i φ hφ) hX hcX
  simp only [Fintype.sum_unique] at ht
  have hind : (fun z => E.indicator f z * divergenceN X z) =
      E.indicator (fun z => f z * divergenceN X z) := by
    funext z
    by_cases hz : z ∈ E <;> simp [hz]
  rw [hind, integral_indicator hE.measurableSet,
    integral_inner_boundaryCutDensity hE hσ hTi hνm hn hX.continuous hcX] at ht
  linarith

/-- Existence of an actual integrable interior trace and a geometric outward
normal, together with the global cut formula. Only compactness of the frontier
is required; the open domain itself may be unbounded. -/
theorem HasC1Boundary.exists_integrable_trace_cut_pairing {E : Set AmbientSpace}
    (h : HasC1Boundary E) (hE : IsOpen E) (hK : IsCompact (frontier E))
    {f : AmbientSpace → ℝ} (hf : IsLocallyBVOn f univ)
    {μ : Measure AmbientSpace} [SigmaFinite μ] {σ : AmbientSpace → AmbientSpace}
    (hσ : LocallyIntegrable σ μ)
    (hpair : ∀ (i : Fin 3) (φ : CompactlySupportedContinuousMap AmbientSpace ℝ),
      ContDiff ℝ 1 φ → -(∫ z, f z * fderiv ℝ φ z (EuclideanSpace.single i 1)) =
        ∫ z, φ z * σ z i ∂μ) :
    ∃ T : AmbientSpace → ℝ, ∃ ν : AmbientSpace → AmbientSpace,
      Integrable T ((hausdorffMeasure2 3).restrict (frontier E)) ∧
      Measurable ν ∧
      (∀ᵐ z ∂(hausdorffMeasure2 3).restrict (frontier E), ‖ν z‖ = 1) ∧
      (∀ c : C1BoundaryChart, c.IsChartFor E →
        ∀ᵐ z ∂(hausdorffMeasure2 3).restrict (frontier E), z ∈ c.region →
          T z = c.lowerBVTrace f z) ∧
      (∀ c : C1BoundaryChart, c.IsChartFor E →
        ∀ᵐ z ∂(hausdorffMeasure2 3).restrict (frontier E), z ∈ c.region →
          ν z = c.outwardNormal z) ∧
      ∀ (X : AmbientSpace → AmbientSpace), ContDiff ℝ 1 X → HasCompactSupport X →
        (∫ z in E, f z * divergenceN X z) =
          -(∫ z in E, inner ℝ (X z) (σ z) ∂μ) +
            ∫ z, T z * inner ℝ (X z) (ν z)
              ∂(hausdorffMeasure2 3).restrict (frontier E) := by
  obtain ⟨T, hTi, hT⟩ := h.exists_integrable_lowerTrace hE hK hf
  let hP := h.hasLocallyFinitePerimeter hE
  let ν := canonicalOutwardPolarDensity E hP hE.measurableSet.nullMeasurableSet
  have hp := canonicalPerimeterPolar E hP hE.measurableSet.nullMeasurableSet
  have hn : ∀ᵐ z ∂(hausdorffMeasure2 3).restrict (frontier E), ‖ν z‖ = 1 := by
    rw [← h.canonicalPerimeterMeasure_eq hE hP]
    exact hp.norm_ae
  have hν : ∀ c : C1BoundaryChart, c.IsChartFor E →
      ∀ᵐ z ∂(hausdorffMeasure2 3).restrict (frontier E), z ∈ c.region →
        ν z = c.outwardNormal z := by
    intro c hc
    rw [← h.canonicalPerimeterMeasure_eq hE hP]
    exact hc.canonical_normal_eq_ae h hE hP
  refine ⟨T, ν, hTi, hp.measurable, hn, hT, hν, fun X hX hcX => ?_⟩
  exact h.cut_pairing hE hf hσ hpair hTi hp.measurable.aestronglyMeasurable
    (hn.mono fun _ hz => hz.le) hT hν hX hcX

end LiquidDrop

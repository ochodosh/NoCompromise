module

public import NoCompromise.BV.Gluing
public import NoCompromise.BV.GoodRadii
public import NoCompromise.BV.RadialCuts

@[expose] public section

/-!
# Agreement of both traces at a good spherical radius

The derivative has zero mass on a good sphere. Adding the genuine two-sided
cut identities therefore forces the trace jump to vanish. Distributional
uniqueness recovers equality of the scalar traces from their unit normal field.
-/

noncomputable section
open MeasureTheory Set Filter Metric
open scoped ENNReal Topology
namespace LiquidDrop
set_option maxSynthPendingDepth 8

lemma ae_eq_of_unit_normal_pairings {μ : Measure AmbientSpace}
    {T S : AmbientSpace → ℝ} {N : AmbientSpace → AmbientSpace}
    (hT : Integrable T μ) (hS : Integrable S μ) (hNm : Measurable N)
    (hN : ∀ᵐ z ∂μ, ‖N z‖ = 1)
    (hp : ∀ (X : AmbientSpace → AmbientSpace), ContDiff ℝ 1 X → HasCompactSupport X →
      (∫ z, T z * inner ℝ (X z) (N z) ∂μ) =
        ∫ z, S z * inner ℝ (X z) (N z) ∂μ) : T =ᵐ[μ] S := by
  have hTi := hT.smul_bdd 1 hNm.aestronglyMeasurable (hN.mono fun _ hz => hz.le)
  have hSi := hS.smul_bdd 1 hNm.aestronglyMeasurable (hN.mono fun _ hz => hz.le)
  have he := ae_eq_density_on_of_coordinate_pairings isOpen_univ
    hTi.locallyIntegrable hSi.locallyIntegrable (by
      intro i φ hφ _
      have hh := hp (fun z => φ z • EuclideanSpace.single i 1)
        (hφ.smul contDiff_const) φ.hasCompactSupport.smul_right
      simp only [real_inner_smul_left, EuclideanSpace.inner_single_left,
        conj_trivial, one_mul, Pi.smul_apply', PiLp.smul_apply, smul_eq_mul] at hh ⊢
      simpa only [mul_left_comm] using hh)
  rw [Measure.restrict_univ] at he
  filter_upwards [he, hN] with z hz hn
  have hv : (T z - S z) • N z = 0 := by
    change T z • N z = S z • N z at hz
    rw [sub_smul, hz, sub_self]
  have hh := congrArg norm hv
  rw [norm_smul, hn, mul_one, norm_zero] at hh
  exact sub_eq_zero.mp (norm_eq_zero.mp hh)

/-- A good radius gives the same density-one value for the exterior trace as
for the interior trace, in every genuine boundary chart. -/
theorem IsGoodRadius.upperBVTrace_eq {E : Set AmbientSpace}
    {hE : HasLocallyFinitePerimeter E} {hmE : NullMeasurableSet E volume}
    {c : AmbientSpace} {r : ℝ} (hg : IsGoodRadius E hE hmE c r)
    (d : C1BoundaryChart) (hd : d.IsChartFor (ball c r)) :
    ∀ᵐ z ∂(hausdorffMeasure2 3).restrict (sphere c r), z ∈ d.region →
      d.upperBVTrace (E.indicator (fun _ => (1 : ℝ))) z =
        (densityOne E).indicator (fun _ => (1 : ℝ)) z := by
  have hp := canonicalPerimeterPolar E hE hmE
  let := hp.regular
  let := hp.finiteOnCompacts
  have hB := hasC1Boundary_ball c hg.1
  have hK : IsCompact (frontier (ball c r)) := by
    rw [frontier_ball c hg.1.ne']
    exact isCompact_sphere c r
  have hf := hE.isLocallyBVOn_indicator hmE univ
  have hpair : ∀ (i : Fin 3) (φ : CompactlySupportedContinuousMap AmbientSpace ℝ),
      ContDiff ℝ 1 φ → -(∫ z, E.indicator (fun _ => (1 : ℝ)) z *
        fderiv ℝ φ z (EuclideanSpace.single i 1)) =
        ∫ z, φ z * (-canonicalOutwardPolarDensity E hE hmE z) i
          ∂canonicalPerimeterMeasure E hE hmE := fun i φ hφ => hp.coordinate_eq i φ hφ
  obtain ⟨Tin, Tout, N, hTi, hTo, hNm, hn, hC, hin, hout⟩ :=
    hB.exists_integrable_traces_cut_pairings isOpen_ball hK hf hp.locallyIntegrable.neg hpair
  have hTin : Tin =ᵐ[(hausdorffMeasure2 3).restrict (frontier (ball c r))]
      (densityOne E).indicator (fun _ => (1 : ℝ)) := by
    apply hB.ae_of_chartwise hK
    intro a ha
    have hh := hg.2.2 a ha
    rw [← frontier_ball c hg.1.ne'] at hh
    filter_upwards [hC a ha, hh] with z hz hz'
    intro hza
    exact (hz hza).1.trans (hz' hza)
  have heq : Tin =ᵐ[(hausdorffMeasure2 3).restrict (frontier (ball c r))] Tout := by
    apply ae_eq_of_unit_normal_pairings hTi hTo hNm hn
    intro X hX hcX
    have hi := hin X hX hcX
    have ho := hout X hX hcX
    rw [closure_ball c hg.1.ne'] at ho
    have hsource := integral_ball_add_closedBall_compl
      (Measure.addHaar_sphere volume c r)
      (integrable_mul_divergenceN hf.1 hX hcX (subset_univ _))
    have hbulk := integral_ball_add_closedBall_compl hg.2.1
      (integrable_inner_density_compact hp.locallyIntegrable.neg hX.continuous hcX)
    have htotal := hp.divergence_eq X hX hcX
    have hfun : (fun z => E.indicator (fun _ => (1 : ℝ)) z * divergenceN X z) =
        E.indicator (divergenceN X) := by
      funext z
      by_cases hz : z ∈ E <;> simp [hz]
    rw [hfun] at hi ho
    rw [hfun, integral_indicator₀ hmE] at hsource
    simp only [Pi.neg_apply, inner_neg_right, integral_neg] at hbulk hi ho
    linarith
  have hdC := hC d hd
  rw [frontier_ball c hg.1.ne'] at heq hTin hdC
  filter_upwards [heq, hTin, hdC] with z hz ht hc
  intro hzd
  exact (hc hzd).2.1.symm.trans (hz.symm.trans ht)

end LiquidDrop

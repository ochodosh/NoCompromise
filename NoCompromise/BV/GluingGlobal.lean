module

public import NoCompromise.BV.GluingLocalTraces

@[expose] public section

/-!
# The BV gluing estimate for global realizations

The two actual distributional cut identities combine before taking norms, so
the boundary cost is the trace difference. This lemma is also used after compact
localization; it does not impose global BV assumptions on the eventual local
set-gluing theorem.
-/

noncomputable section
open MeasureTheory Set Filter Metric
open scoped ENNReal Topology
namespace LiquidDrop
set_option maxSynthPendingDepth 8

lemma lintegral_enorm_unit_restrict {μ : Measure AmbientSpace}
    {σ : AmbientSpace → AmbientSpace} (hσ : ∀ᵐ z ∂μ, ‖σ z‖ = 1)
    (A : Set AmbientSpace) {U : Set AmbientSpace} (hU : MeasurableSet U) :
    (∫⁻ z in U, ‖σ z‖ₑ ∂μ.restrict A) = μ (U ∩ A) := by
  have hn : ∀ᵐ z ∂(μ.restrict A).restrict U, ‖σ z‖ₑ = 1 := by
    filter_upwards [ae_restrict_of_ae (ae_restrict_of_ae hσ)] with z hz
    simp only [← ofReal_norm, hz, ENNReal.ofReal_one]
  rw [lintegral_congr_ae hn]
  simp only [lintegral_const, one_mul, Measure.restrict_apply_univ,
    Measure.restrict_apply hU]

/-- Taking variation after adding the signed boundary terms retains their
mismatch, rather than charging the two traces separately. -/
lemma variation_le_bulk_and_traceMismatch {w T S : AmbientSpace → ℝ}
    {A B : Set AmbientSpace} {μ ρ τ : Measure AmbientSpace}
    {σ ν N : AmbientSpace → AmbientSpace}
    (hσ : ∀ᵐ z ∂μ, ‖σ z‖ = 1) (hν : ∀ᵐ z ∂ρ, ‖ν z‖ = 1)
    (hN : ∀ᵐ z ∂τ, ‖N z‖ = 1) (hTS : Integrable (fun z => T z - S z) τ)
    (hpair : ∀ (X : AmbientSpace → AmbientSpace), ContDiff ℝ 1 X → HasCompactSupport X →
      -(∫ z, w z * divergenceN X z) =
        (∫ z in A, inner ℝ (X z) (σ z) ∂μ) +
        (∫ z in B, inner ℝ (X z) (ν z) ∂ρ) -
        ∫ z, (T z - S z) * inner ℝ (X z) (N z) ∂τ)
    {U : Set AmbientSpace} (hU : IsOpen U) :
    variation w U ≤ μ (U ∩ A) + ρ (U ∩ B) +
      ENNReal.ofReal (∫ z, |T z - S z| ∂τ) := by
  let μs : Fin 3 → Measure AmbientSpace := ![μ.restrict A, ρ.restrict B, τ]
  let σs : Fin 3 → AmbientSpace → AmbientSpace :=
    ![σ, ν, fun z => -(T z - S z) • N z]
  have hp (X : AmbientSpace → AmbientSpace) (hX : ContDiff ℝ 1 X)
      (hcX : HasCompactSupport X) :
      -(∫ z, w z * divergenceN X z) = ∑ j, ∫ z, inner ℝ (X z) (σs j z) ∂μs j := by
    simp only [μs, σs, Fin.sum_univ_three]
    change -(∫ z, w z * divergenceN X z) =
      (∫ z in A, inner ℝ (X z) (σ z) ∂μ) +
      (∫ z in B, inner ℝ (X z) (ν z) ∂ρ) +
      ∫ z, inner ℝ (X z) (-(T z - S z) • N z) ∂τ
    simp only [inner_smul_right, neg_mul, integral_neg]
    rw [hpair X hX hcX]
    ring
  have hv := variation_le_sum_lintegral_of_divergence_pairing hp U
  have hs : (∫⁻ z in U, ‖-(T z - S z) • N z‖ₑ ∂τ) ≤
      ENNReal.ofReal (∫ z, |T z - S z| ∂τ) := by
    apply (setLIntegral_le_lintegral _ _).trans
    have hn : ∀ᵐ z ∂τ, ‖-(T z - S z) • N z‖ₑ = ‖T z - S z‖ₑ := by
      filter_upwards [hN] with z hz
      simp only [← ofReal_norm, norm_smul, norm_neg, hz, mul_one]
    rw [lintegral_congr_ae hn, ← ofReal_integral_norm_eq_lintegral_enorm hTS]
    simp only [Real.norm_eq_abs, le_refl]
  simp only [Fin.sum_univ_three] at hv
  change variation w U ≤ (∫⁻ z in U, ‖σ z‖ₑ ∂μ.restrict A) +
    (∫⁻ z in U, ‖ν z‖ₑ ∂ρ.restrict B) +
    ∫⁻ z in U, ‖-(T z - S z) • N z‖ₑ ∂τ at hv
  rw [lintegral_enorm_unit_restrict hσ A hU.measurableSet,
    lintegral_enorm_unit_restrict hν B hU.measurableSet] at hv
  exact hv.trans (add_le_add le_rfl hs)

/-- Gluing two global BV realizations has exactly the boundary mismatch cost.
The supplied traces must agree with the already constructed essential chart
traces; their distributional formulas are derived below. -/
theorem HasC1Boundary.variation_gluing_le {A : Set AmbientSpace}
    (h : HasC1Boundary A) (hA : IsOpen A) (hbA : Bornology.IsBounded A)
    {f g : AmbientSpace → ℝ} (hf : IsLocallyBVOn f univ) (hg : IsLocallyBVOn g univ)
    {Tin Tout : AmbientSpace → ℝ}
    (hTi : Integrable Tin ((hausdorffMeasure2 3).restrict (frontier A)))
    (hTo : Integrable Tout ((hausdorffMeasure2 3).restrict (frontier A)))
    (hTic : ∀ c : C1BoundaryChart, c.IsChartFor A →
      ∀ᵐ z ∂(hausdorffMeasure2 3).restrict (frontier A), z ∈ c.region →
        Tin z = c.lowerBVTrace g z)
    (hToc : ∀ c : C1BoundaryChart, c.IsChartFor A →
      ∀ᵐ z ∂(hausdorffMeasure2 3).restrict (frontier A), z ∈ c.region →
        Tout z = c.upperBVTrace f z)
    {U : Set AmbientSpace} (hU : IsOpen U) :
    variation (fun z => A.indicator g z + (closure A)ᶜ.indicator f z) U ≤
      variation g (U ∩ A) + variation f (U ∩ (closure A)ᶜ) +
        ENNReal.ofReal (∫ z in frontier A, |Tin z - Tout z| ∂hausdorffMeasure2 3) := by
  have hK : IsCompact (frontier A) :=
    hbA.isCompact_closure.of_isClosed_subset isClosed_frontier frontier_subset_closure
  obtain ⟨μ, σ, hμ, hμfin, _, hnσ, hσ, hσpair, hμvar⟩ := hg.exists_ambient_scalar_polar
  obtain ⟨ρ, ν, hρ, hρfin, _, hnν, hν, hνpair, hρvar⟩ := hf.exists_ambient_scalar_polar
  let : μ.Regular := hμ
  let : IsFiniteMeasureOnCompacts μ := hμfin
  let : ρ.Regular := hρ
  let : IsFiniteMeasureOnCompacts ρ := hρfin
  obtain ⟨Tg, _, Ng, _, _, hNgm, hNgn, hCg, hgin, _⟩ :=
    h.exists_integrable_traces_cut_pairings hA hK hg hσ hσpair
  obtain ⟨_, Tf, Nf, _, _, _, _, hCf, _, hfout⟩ :=
    h.exists_integrable_traces_cut_pairings hA hK hf hν hνpair
  have hTg : Tg =ᵐ[(hausdorffMeasure2 3).restrict (frontier A)] Tin :=
    h.trace_eq_ae_of_chart_agreement hK
      (fun c hc => (hCg c hc).mono fun z hz hzc => (hz hzc).1) hTic
  have hTf : Tf =ᵐ[(hausdorffMeasure2 3).restrict (frontier A)] Tout :=
    h.trace_eq_ae_of_chart_agreement hK
      (fun c hc => (hCf c hc).mono fun z hz hzc => (hz hzc).2.1) hToc
  have hN : Nf =ᵐ[(hausdorffMeasure2 3).restrict (frontier A)] Ng :=
    h.normal_eq_ae_of_chart_agreement hK
      (fun c hc => (hCf c hc).mono fun z hz hzc => (hz hzc).2.2)
      (fun c hc => (hCg c hc).mono fun z hz hzc => (hz hzc).2.2)
  have hpair (X : AmbientSpace → AmbientSpace) (hX : ContDiff ℝ 1 X)
      (hcX : HasCompactSupport X) :
      -(∫ z, (A.indicator g z + (closure A)ᶜ.indicator f z) * divergenceN X z) =
        (∫ z in A, inner ℝ (X z) (σ z) ∂μ) +
        (∫ z in (closure A)ᶜ, inner ℝ (X z) (ν z) ∂ρ) -
        ∫ z in frontier A, (Tin z - Tout z) * inner ℝ (X z) (Ng z)
          ∂hausdorffMeasure2 3 := by
    have hi (T : AmbientSpace → ℝ)
        (hT : Integrable T ((hausdorffMeasure2 3).restrict (frontier A))) :
        Integrable (fun z => T z * inner ℝ (X z) (Ng z))
          ((hausdorffMeasure2 3).restrict (frontier A)) := by
      have hv := hT.smul_bdd 1 hNgm.aestronglyMeasurable (hNgn.mono fun _ hz => hz.le)
      simpa only [Pi.smul_apply', inner_smul_right, mul_comm] using!
        integrable_inner_density_compact hv.locallyIntegrable hX.continuous hcX
    have hgin' := hgin X hX hcX
    have hfout' := hfout X hX hcX
    have hegin : (∫ z in frontier A, Tg z * inner ℝ (X z) (Ng z) ∂hausdorffMeasure2 3) =
        ∫ z in frontier A, Tin z * inner ℝ (X z) (Ng z) ∂hausdorffMeasure2 3 :=
      integral_congr_ae (hTg.mono fun z hz => congrArg (fun t => t * inner ℝ (X z) (Ng z)) hz)
    have hefout : (∫ z in frontier A, Tf z * inner ℝ (X z) (Nf z) ∂hausdorffMeasure2 3) =
        ∫ z in frontier A, Tout z * inner ℝ (X z) (Ng z) ∂hausdorffMeasure2 3 := by
      apply integral_congr_ae
      filter_upwards [hTf, hN] with z hz hnz
      rw [hz, hnz]
    rw [hegin] at hgin'
    rw [hefout] at hfout'
    have he : (∫ z in frontier A, (Tin z - Tout z) * inner ℝ (X z) (Ng z)
        ∂hausdorffMeasure2 3) =
        (∫ z in frontier A, Tin z * inner ℝ (X z) (Ng z) ∂hausdorffMeasure2 3) -
        ∫ z in frontier A, Tout z * inner ℝ (X z) (Ng z) ∂hausdorffMeasure2 3 := by
      simp_rw [sub_mul]
      exact integral_sub (hi Tin hTi) (hi Tout hTo)
    have hw : (fun z => (A.indicator g z + (closure A)ᶜ.indicator f z) * divergenceN X z) =
        fun z => A.indicator (fun z => g z * divergenceN X z) z +
          (closure A)ᶜ.indicator (fun z => f z * divergenceN X z) z := by
      funext z
      rw [add_mul, Set.indicator_mul_left, Set.indicator_mul_left]
    rw [hw, integral_add
      ((integrable_mul_divergenceN hg.1 hX hcX (subset_univ _)).indicator hA.measurableSet)
      ((integrable_mul_divergenceN hf.1 hX hcX (subset_univ _)).indicator
        isClosed_closure.measurableSet.compl),
      integral_indicator hA.measurableSet,
      integral_indicator isClosed_closure.measurableSet.compl, he]
    linarith
  have hv := variation_le_bulk_and_traceMismatch hnσ hnν hNgn (hTi.sub hTo) hpair hU
  rw [← hμvar _ (hU.inter hA), ← hρvar _ (hU.inter isClosed_closure.isOpen_compl)] at hv
  exact hv

end LiquidDrop

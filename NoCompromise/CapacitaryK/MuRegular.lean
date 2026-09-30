module

public import NoCompromise.CapacitaryK.MuMeasure

@[expose] public section

/-!
# The Laplacian measure on the regular set

Where the gradient is nonzero, its length is C² and Green's identity identifies
its distributional Laplacian with its continuous, nonnegative pointwise Laplacian.
Smooth cutoffs and dominated convergence determine compact-set masses; regularity
of the measures on the open subtype then determines their restrictions.

`K_mu_restrict_regular` is the input of `lem:K-pushforward-density` identifying the
absolutely continuous part of `μ = Δ|∇u|` (`prop:K-mu`) on the regular set `{w > 0}` with
`Δw dx`; combined with `K_pushforward_density_coarea` it gives the density of `u_#μ` there.
-/

noncomputable section
open MeasureTheory Filter Set InnerProductSpace Metric
open scoped Topology Gradient ContDiff RealInnerProductSpace ENNReal

namespace LiquidDrop.CapacitaryK

lemma gradNorm_contDiffAt_of_pos {u : E3 → ℝ} {x : E3}
    (hu : ContDiffAt ℝ 3 u x) (hw : 0 < gradNorm u x) :
    ContDiffAt ℝ 2 (gradNorm u) x := by
  have hcoord (i : Fin 3) : ContDiffAt ℝ 2 (fun y => gradient u y i) x := by
    simpa only [← poissonCoordinateDerivative_eq_gradient, poissonCoordinateDerivative] using
      (hu.fderiv_right (show (2 : ℕ∞ω) + 1 ≤ 3 by norm_num)).clm_apply
        (contDiffAt_const (c := basisVec i))
  have hs : ContDiffAt ℝ 2 (fun y => gradNorm u y ^ 2) x := by
    simp only [gradNorm_sq]
    exact ContDiffAt.sum fun i _ => (hcoord i).pow 2
  have hh : ContDiffAt ℝ 2 (gradNormEps 0 u) x :=
    (hs.add contDiffAt_const).sqrt (by simpa using ne_of_gt (sq_pos_of_pos hw))
  simpa only [gradNormEps_zero] using hh

lemma isOpen_regularSet {U : Set E3} (hU : IsOpen U) {u : E3 → ℝ}
    (hu : ContDiffOn ℝ 3 u U) : IsOpen (U ∩ {x | 0 < gradNorm u x}) := by
  exact (continuousOn_gradNorm hU hu).isOpen_inter_preimage hU isOpen_Ioi

lemma laplacianN_gradNorm_nonneg_of_pos {u : E3 → ℝ} {x : E3}
    (hu : ContDiffAt ℝ 3 u x) (hΔ : ∀ᶠ y in 𝓝 x, laplacianN u y = 0)
    (hw : 0 < gradNorm u x) : 0 ≤ laplacianN (gradNorm u) x := by
  have hp : 0 < gradNorm u x ^ 2 + (0 : ℝ) ^ 2 := by positivity
  have hh := laplacianN_gradNormEps hu hΔ hp
  rw [gradNormEps_zero] at hh
  rw [hh]
  simpa only [gradNormEps_zero] using
    (bochner_rhs_ge u x hp).2.trans (bochner_rhs_ge u x hp).1

lemma continuousOn_laplacianN_gradNorm_regular {U : Set E3} (hU : IsOpen U)
    {u : E3 → ℝ} (hu : ContDiffOn ℝ 3 u U) (hpos : ∀ x ∈ U, 0 < gradNorm u x) :
    ContinuousOn (laplacianN (gradNorm u)) U := by
  intro x hx
  have hv := gradNorm_contDiffAt_of_pos (hu.contDiffAt (hU.mem_nhds hx)) (hpos x hx)
  apply ContinuousAt.continuousWithinAt
  apply tendsto_finsetSum
  intro i _
  have hfirst : ContDiffAt ℝ 1 (poissonCoordinateDerivative i (gradNorm u)) x :=
    (hv.fderiv_right (by norm_num)).clm_apply contDiffAt_const
  exact ((hfirst.fderiv_right (show (0 : ℕ∞ω) + 1 ≤ 1 by norm_num)).clm_apply
    (contDiffAt_const (c := basisVec i))).continuousAt

/-- Green's identity on an open set where the gradient does not vanish. -/
lemma integral_gradNorm_mul_laplacianN_regular {U : Set E3} (hU : IsOpen U)
    {u : E3 → ℝ} (hu : ContDiffOn ℝ 3 u U) (hpos : ∀ x ∈ U, 0 < gradNorm u x)
    {φ : E3 → ℝ} (hφ : ContDiff ℝ (⊤ : ℕ∞) φ)
    (hcφ : HasCompactSupport φ) (hsφ : tsupport φ ⊆ U) :
    (∫ x, gradNorm u x * laplacianN φ x) =
      ∫ x, φ x * laplacianN (gradNorm u) x := by
  obtain ⟨χ, hχ, hcχ, hsχ, hone, _⟩ :=
    exists_smooth_cutoff_one_near_compact hcφ hU hsφ
  let v : E3 → ℝ := fun x => χ x * gradNorm u x
  have hv : ContDiff ℝ 2 v := by
    apply contDiff_iff_contDiffAt.mpr
    intro x
    by_cases hx : x ∈ U
    · exact (hχ.of_le (by simp)).contDiffAt.mul
        (gradNorm_contDiffAt_of_pos (hu.contDiffAt (hU.mem_nhds hx)) (hpos x hx))
    · have hxt : x ∉ tsupport χ := fun ht => hx (hsχ ht)
      apply (contDiffAt_const (c := (0 : ℝ))).congr_of_eventuallyEq
      filter_upwards [(isClosed_tsupport χ).isOpen_compl.mem_nhds hxt] with y hy
      simp only [v, image_eq_zero_of_notMem_tsupport hy, zero_mul]
  have hcv : HasCompactSupport v := hcχ.mul_right
  have hnear (x : E3) (hx : x ∈ tsupport φ) : v =ᶠ[𝓝 x] gradNorm u := by
    filter_upwards [hone.filter_mono (nhds_le_nhdsSet hx)] with y hy
    simp only [v, hy, one_mul]
  calc
    _ = ∫ x, v x * laplacianN φ x := by
      apply integral_congr_ae
      filter_upwards with x
      by_cases hx : x ∈ tsupport φ
      · rw [(hnear x hx).self_of_nhds]
      · have hz : laplacianN φ x = 0 := image_eq_zero_of_notMem_tsupport
          (fun ht => hx (laplacian_support φ ht))
        simp only [hz, mul_zero]
    _ = ∫ x, φ x * laplacianN v x := by
      rw [integral_mul_laplacianN (hφ.of_le (by simp)) (hv.of_le (by norm_num)) hcv,
        integral_mul_laplacianN hv (hφ.of_le (by simp)) hcφ]
      congr 1
      apply integral_congr_ae
      filter_upwards with x
      exact real_inner_comm _ _
    _ = _ := by
      apply integral_congr_ae
      filter_upwards with x
      by_cases hx : x ∈ tsupport φ
      · rw [laplacian_congr_near (hnear x hx)]
      · simp only [image_eq_zero_of_notMem_tsupport hx, zero_mul]

/-- Smooth supported tests determine the mass of compact subsets of an open set. -/
lemma measure_isCompact_eq_of_integral_smooth {V : Set E3} (hV : IsOpen V)
    {μ ν : Measure E3}
    (hμK : ∀ K : Set E3, IsCompact K → K ⊆ V → μ K < ⊤)
    (hνK : ∀ K : Set E3, IsCompact K → K ⊆ V → ν K < ⊤)
    (h : ∀ φ : E3 → ℝ, ContDiff ℝ (⊤ : ℕ∞) φ → HasCompactSupport φ →
      tsupport φ ⊆ V → ∫ x, φ x ∂μ = ∫ x, φ x ∂ν)
    {K : Set E3} (hK : IsCompact K) (hKV : K ⊆ V) : μ K = ν K := by
  obtain ⟨δ, hδ, hδV⟩ := hK.exists_cthickening_subset_open hV hKV
  have hcδ : IsCompact (cthickening δ K) := hK.cthickening
  obtain ⟨r, -, hr, hrlim⟩ : ∃ r, StrictAnti r ∧ (∀ n : ℕ, r n ∈ Ioo 0 δ) ∧
      Tendsto r atTop (𝓝 0) := exists_seq_strictAnti_tendsto' hδ
  have hex (n : ℕ) : ∃ φ : E3 → ℝ, ContDiff ℝ (⊤ : ℕ∞) φ ∧ HasCompactSupport φ ∧
      tsupport φ ⊆ thickening (r n) K ∧ (∀ x ∈ K, φ x = 1) ∧
      (∀ x, φ x ∈ Icc 0 1) := by
    obtain ⟨φ, hφ, hcφ, hsφ, hone, h01⟩ := exists_smooth_cutoff_one_near_compact
      hK isOpen_thickening (self_subset_thickening (hr n).1 K)
    exact ⟨φ, hφ, hcφ, hsφ, fun x hx =>
      (hone.filter_mono (nhds_le_nhdsSet hx)).self_of_nhds, h01⟩
  choose φ hφ hcφ hsφ hone h01 using hex
  have hsδ (n : ℕ) : tsupport (φ n) ⊆ cthickening δ K :=
    (hsφ n).trans (thickening_subset_cthickening_of_le (hr n).2.le K)
  have hlim (ρ : Measure E3) (hρ : ρ (cthickening δ K) < ⊤) :
      Tendsto (fun n => ∫ x, φ n x ∂ρ) atTop (𝓝 ((ρ K).toReal)) := by
    have hbound : Integrable ((cthickening δ K).indicator (fun _ : E3 => (1 : ℝ))) ρ := by
      rw [integrable_indicator_iff hcδ.measurableSet]
      exact integrableOn_const hρ.ne
    have hconv : ∀ᵐ x ∂ρ, Tendsto (fun n => φ n x) atTop
        (𝓝 (K.indicator (fun _ : E3 => (1 : ℝ)) x)) := by
      filter_upwards with x
      by_cases hx : x ∈ K
      · simpa only [hone _ x hx, indicator_of_mem hx] using
          (tendsto_const_nhds : Tendsto (fun _ : ℕ => (1 : ℝ)) atTop (𝓝 1))
      · rw [indicator_of_notMem hx]
        apply tendsto_const_nhds.congr'
        obtain ⟨ε, hε, hxε⟩ : ∃ ε, 0 < ε ∧ x ∉ thickening ε K := by
          rw [← hK.isClosed.closure_eq, closure_eq_iInter_thickening K] at hx
          simpa using hx
        filter_upwards [(tendsto_order.1 hrlim).2 _ hε] with n hn
        symm
        apply image_eq_zero_of_notMem_tsupport
        exact fun ht => hxε (thickening_mono hn.le K (hsφ n ht))
    have hb (n : ℕ) : ∀ᵐ x ∂ρ, ‖φ n x‖ ≤
        (cthickening δ K).indicator (fun _ : E3 => (1 : ℝ)) x := by
      filter_upwards with x
      by_cases hx : x ∈ cthickening δ K
      · rw [indicator_of_mem hx, Real.norm_of_nonneg (h01 n x).1]
        exact (h01 n x).2
      · rw [indicator_of_notMem hx,
          image_eq_zero_of_notMem_tsupport (fun ht => hx (hsδ n ht)), norm_zero]
    have hh := tendsto_integral_of_dominated_convergence _
      (fun n => (hφ n).continuous.aestronglyMeasurable) hbound hb hconv
    simpa only [integral_indicator hK.measurableSet, integral_const, smul_eq_mul,
      mul_one, measureReal_def, Measure.restrict_apply_univ] using hh
  have heq : (μ K).toReal = (ν K).toReal := by
    apply tendsto_nhds_unique (hlim μ (hμK _ hcδ hδV))
    convert hlim ν (hνK _ hcδ hδV) using 1
    ext n
    exact h (φ n) (hφ n) (hcφ n) ((hsδ n).trans hδV)
  exact (ENNReal.toReal_eq_toReal_iff' (hμK K hK hKV).ne (hνK K hK hKV).ne).mp heq

/-- Local finiteness and agreement on smooth supported tests determine a restriction. -/
lemma restrict_eq_of_integral_smooth {V : Set E3} (hV : IsOpen V)
    {μ ν : Measure E3}
    (hμK : ∀ K : Set E3, IsCompact K → K ⊆ V → μ K < ⊤)
    (hνK : ∀ K : Set E3, IsCompact K → K ⊆ V → ν K < ⊤)
    (h : ∀ φ : E3 → ℝ, ContDiff ℝ (⊤ : ℕ∞) φ → HasCompactSupport φ →
      tsupport φ ⊆ V → ∫ x, φ x ∂μ = ∫ x, φ x ∂ν) :
    μ.restrict V = ν.restrict V := by
  let : LocallyCompactSpace V := hV.locallyCompactSpace
  let μV : Measure V := μ.comap Subtype.val
  let νV : Measure V := ν.comap Subtype.val
  have hf (ρ : Measure E3) (hρ : ∀ K : Set E3, IsCompact K → K ⊆ V → ρ K < ⊤) :
      IsFiniteMeasureOnCompacts (ρ.comap (Subtype.val : V → E3)) := by
    constructor
    intro K hK
    rw [comap_subtype_coe_apply hV.measurableSet]
    exact hρ _ (hK.image continuous_subtype_val) (by rintro _ ⟨x, _, rfl⟩; exact x.property)
  let : IsFiniteMeasureOnCompacts μV := hf μ hμK
  let : IsFiniteMeasureOnCompacts νV := hf ν hνK
  have heq : μV = νV := by
    apply Measure.OuterRegular.ext_isOpen
    intro O hO
    rw [hO.measure_eq_iSup_isCompact μV, hO.measure_eq_iSup_isCompact νV]
    apply iSup_congr
    intro K
    apply iSup_congr
    intro _
    apply iSup_congr
    intro hK
    dsimp [μV, νV]
    rw [comap_subtype_coe_apply hV.measurableSet,
      comap_subtype_coe_apply hV.measurableSet]
    exact measure_isCompact_eq_of_integral_smooth hV hμK hνK h
      (hK.image continuous_subtype_val) (by rintro _ ⟨x, _, rfl⟩; exact x.property)
  have hm := congrArg (fun ρ : Measure V => ρ.map (Subtype.val : V → E3)) heq
  simpa only [μV, νV, map_comap_subtype_coe hV.measurableSet] using hm

/-- On the regular set `V = U ∩ {w > 0}`, any measure `μ` representing the distribution `Δw`
(as produced by `K_mu_measure`) is `Δw dx`. -/
theorem K_mu_restrict_regular {U : Set E3} (hU : IsOpen U) {u : E3 → ℝ}
    (hu : ContDiffOn ℝ 3 u U) (hΔ : ∀ x ∈ U, laplacianN u x = 0) {μ : Measure E3}
    (hμK : ∀ K : Set E3, IsCompact K → K ⊆ U → μ K < ⊤)
    (hμ : ∀ φ : E3 → ℝ, ContDiff ℝ (⊤ : ℕ∞) φ → HasCompactSupport φ → tsupport φ ⊆ U →
        ∫ x, gradNorm u x * laplacianN φ x = ∫ x, φ x ∂μ) :
    μ.restrict (U ∩ {x | 0 < gradNorm u x}) =
      (volume.restrict (U ∩ {x | 0 < gradNorm u x})).withDensity
        (fun x => ENNReal.ofReal (laplacianN (gradNorm u) x)) := by
  let V := U ∩ {x | 0 < gradNorm u x}
  have hV : IsOpen V := isOpen_regularSet hU hu
  have hVU : V ⊆ U := inter_subset_left
  have huV : ContDiffOn ℝ 3 u V := hu.mono hVU
  have hwV : ∀ x ∈ V, 0 < gradNorm u x := fun _ hx => hx.2
  have hc : ContinuousOn (laplacianN (gradNorm u)) V :=
    continuousOn_laplacianN_gradNorm_regular hV huV hwV
  have hnonneg : ∀ x ∈ V, 0 ≤ laplacianN (gradNorm u) x := by
    intro x hx
    apply laplacianN_gradNorm_nonneg_of_pos (hu.contDiffAt (hU.mem_nhds hx.1))
      _ hx.2
    filter_upwards [hU.mem_nhds hx.1] with y hy
    exact hΔ y hy
  let ν := (volume.restrict V).withDensity
    (fun x => ENNReal.ofReal (laplacianN (gradNorm u) x))
  have hνK : ∀ K : Set E3, IsCompact K → K ⊆ V → ν K < ⊤ := by
    intro K hK hKV
    rw [withDensity_apply _ hK.measurableSet,
      Measure.restrict_restrict_of_subset hKV]
    apply (hasFiniteIntegral_iff_ofReal _).mp ((hc.mono hKV).integrableOn_compact hK).2
    filter_upwards [ae_restrict_mem hK.measurableSet] with x hx
    exact hnonneg x (hKV hx)
  have heq : μ.restrict V = ν.restrict V := by
    apply restrict_eq_of_integral_smooth hV
      (fun K hK hKV => hμK K hK (hKV.trans hVU)) hνK
    intro φ hφ hcφ hsφ
    rw [← hμ φ hφ hcφ (hsφ.trans hVU),
      integral_gradNorm_mul_laplacianN_regular hV huV hwV hφ hcφ hsφ]
    have hmeas : AEMeasurable (fun x => ENNReal.ofReal (laplacianN (gradNorm u) x))
        (volume.restrict V) :=
      (hc.aestronglyMeasurable hV.measurableSet).aemeasurable.ennreal_ofReal
    rw [integral_withDensity_eq_integral_toReal_smul₀ hmeas
      (ae_of_all _ fun _ => ENNReal.ofReal_lt_top) φ]
    calc
      _ = ∫ x in V, φ x * laplacianN (gradNorm u) x := by
        symm
        apply setIntegral_eq_integral_of_forall_compl_eq_zero
        intro x hx
        rw [image_eq_zero_of_notMem_tsupport (fun ht => hx (hsφ ht)), zero_mul]
      _ = _ := by
        apply integral_congr_ae
        filter_upwards [ae_restrict_mem hV.measurableSet] with x hx
        rw [ENNReal.toReal_ofReal (hnonneg x hx), smul_eq_mul, mul_comm]
  have hν : ν.restrict V = ν := by
    dsimp [ν]
    rw [restrict_withDensity hV.measurableSet,
      Measure.restrict_restrict_of_subset (Subset.rfl : V ⊆ V)]
  exact heq.trans hν

end LiquidDrop.CapacitaryK

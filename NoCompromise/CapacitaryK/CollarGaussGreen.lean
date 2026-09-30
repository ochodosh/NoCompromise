module

public import NoCompromise.Capacity.FluxLevel
public import NoCompromise.Capacity.FluxBoundaryW
public import NoCompromise.CapacitaryK.PGeometric

@[expose] public section

/-!
# Gauss–Green on the collar between a regular level and `∂K`

The collar `Kᶜ ∩ {u ≥ s}` between a regular level `{u = s}` and the conductor
boundary is the difference of the exterior truncation and the truncated
sublevel. Subtracting the two Gauss–Green formulas gives the collar formula;
letting `s ↑ 1` the collar volume term vanishes, which gives the endpoint
values of the level integrals.
-/

noncomputable section
open MeasureTheory Filter Metric Set InnerProductSpace
open scoped Topology Gradient RealInnerProductSpace ENNReal

namespace LiquidDrop.CapacitaryK

/-- Gauss–Green on the collar `Kᶜ ∩ {u ≥ s}` between a regular level and `∂K`. -/
theorem collar_gauss_green {K : Set E3} (hK : IsCompact K)
    (hreg : K = closure (interior K)) (hC1 : HasC1Boundary (interior K))
    {u : E3 → ℝ} (hu : Continuous u) (hb : ∀ x ∈ K, u x = 1)
    (hinf : Tendsto u (cocompact E3) (𝓝 0))
    {U : Set E3} (hU : IsOpen U) (hdu : ContDiffOn ℝ 1 u U)
    {s : ℝ} (hs : 0 < s) (hs1 : s < 1) (hlevel : u ⁻¹' {s} ⊆ U)
    (hregs : ∀ x, u x = s → gradient u x ≠ 0)
    {Z : E3 → E3} (hZ : ContDiff ℝ 1 Z) :
    (∫ x in Kᶜ ∩ u ⁻¹' Ici s, divergenceN Z x) =
      (∫ x in u ⁻¹' {s}, ⟪Z x, unitNormal u x⟫ ∂hausdorffMeasure2 3) -
      ∫ x in frontier K, ⟪Z x, hC1.outwardNormal x⟫ ∂hausdorffMeasure2 3 := by
  have hcs : IsCompact (u ⁻¹' Ici s) := fluxLevel_isCompact_superlevel hu hinf hs
  obtain ⟨r, hr, hsub⟩ := (hcs.union hK).isBounded.subset_ball_lt 0 0
  have hAr : u ⁻¹' Ici s ⊆ ball 0 r := subset_union_left.trans hsub
  have hKr : K ⊆ ball 0 r := subset_union_right.trans hsub
  have hann := capacity_annulus_gauss_green hK hreg hC1 hr hKr hZ
  have hsubl := fluxLevel_truncation_gauss_green hU hu hdu hinf hs hr hAr hlevel hregs hZ
  have hdiv : Continuous (divergenceN Z) := continuous_divergenceN hZ
  have hint : IntegrableOn (divergenceN Z) (ball (0 : E3) r) :=
    (hdiv.continuousOn.integrableOn_compact (isCompact_closedBall (0 : E3) r)).mono_set
      ball_subset_closedBall
  have hsplit : ball (0 : E3) r ∩ Kᶜ =
      (ball (0 : E3) r ∩ u ⁻¹' Iio s) ∪ (Kᶜ ∩ u ⁻¹' Ici s) := by
    ext x
    simp only [mem_inter_iff, mem_compl_iff, mem_preimage, mem_Iio, mem_Ici, mem_union]
    constructor
    · rintro ⟨hxr, hxK⟩
      rcases lt_or_ge (u x) s with h | h
      · exact Or.inl ⟨hxr, h⟩
      · exact Or.inr ⟨hxK, h⟩
    · rintro (⟨hxr, h⟩ | ⟨hxK, h⟩)
      · refine ⟨hxr, fun hxK => ?_⟩
        rw [hb x hxK] at h
        exact hs1.not_gt h
      · exact ⟨hAr h, hxK⟩
  have hdis : Disjoint (ball (0 : E3) r ∩ u ⁻¹' Iio s) (Kᶜ ∩ u ⁻¹' Ici s) := by
    apply disjoint_left.mpr
    rintro x ⟨_, h1⟩ ⟨_, h2⟩
    exact (not_le.mpr (show u x < s from h1)) h2
  have hmeas : MeasurableSet (Kᶜ ∩ u ⁻¹' Ici s) :=
    hK.isClosed.isOpen_compl.measurableSet.inter (measurableSet_Ici.preimage hu.measurable)
  have hunion := setIntegral_union hdis hmeas
    (hint.mono_set inter_subset_left) (hint.mono_set (fun x hx => hAr hx.2))
  rw [← hsplit, hann, hsubl] at hunion
  have hneg : (∫ x in u ⁻¹' {s}, ⟪Z x, unitNormal u x⟫ ∂hausdorffMeasure2 3) =
      -∫ x in u ⁻¹' {s}, ⟪Z x, ‖gradient u x‖⁻¹ • gradient u x⟫ ∂hausdorffMeasure2 3 := by
    rw [← integral_neg]
    congr 1
    funext x
    rw [unitNormal, inner_neg_right]
    rfl
  rw [hneg]
  linarith

/-- The collar volume term vanishes as the level tends to the boundary value. -/
theorem tendsto_collar_setIntegral_zero {K : Set E3} (hK : IsCompact K)
    {u : E3 → ℝ} (hu : Continuous u) (hlt : ∀ x ∈ Kᶜ, u x < 1)
    (hinf : Tendsto u (cocompact E3) (𝓝 0))
    {f : E3 → ℝ} (hf : Continuous f) :
    Tendsto (fun s => ∫ x in Kᶜ ∩ u ⁻¹' Ici s, f x) (𝓝[<] 1) (𝓝 0) := by
  have hC : IsCompact (u ⁻¹' Ici (1 / 2 : ℝ)) :=
    fluxLevel_isCompact_superlevel hu hinf (by norm_num)
  have hCm : MeasurableSet (u ⁻¹' Ici (1 / 2 : ℝ)) :=
    measurableSet_Ici.preimage hu.measurable
  have hmeas (s : ℝ) : MeasurableSet (Kᶜ ∩ u ⁻¹' Ici s) :=
    hK.isClosed.isOpen_compl.measurableSet.inter (measurableSet_Ici.preimage hu.measurable)
  have key : Tendsto (fun s => ∫ x, (Kᶜ ∩ u ⁻¹' Ici s).indicator f x) (𝓝[<] 1)
      (𝓝 (∫ _x : E3, (0 : ℝ))) := by
    refine MeasureTheory.tendsto_integral_filter_of_dominated_convergence
      ((u ⁻¹' Ici (1 / 2 : ℝ)).indicator fun x => ‖f x‖) ?_ ?_ ?_ ?_
    · exact Eventually.of_forall fun s => hf.aestronglyMeasurable.indicator (hmeas s)
    · filter_upwards [Ioo_mem_nhdsLT (show (1 / 2 : ℝ) < 1 by norm_num)] with s hs
      refine Eventually.of_forall fun x => ?_
      rw [norm_indicator_eq_indicator_norm]
      apply indicator_le_indicator_of_subset _ (fun _ => norm_nonneg _)
      intro y hy
      exact le_trans hs.1.le hy.2
    · exact (integrable_indicator_iff hCm).mpr
        (hf.norm.continuousOn.integrableOn_compact hC)
    · refine Eventually.of_forall fun x => tendsto_const_nhds.congr' ?_
      by_cases hxK : x ∈ K
      · refine Eventually.of_forall fun s => ?_
        change (0 : ℝ) = (Kᶜ ∩ u ⁻¹' Ici s).indicator f x
        rw [indicator_of_notMem (fun h : x ∈ Kᶜ ∩ u ⁻¹' Ici s => h.1 hxK)]
      · filter_upwards [Ioo_mem_nhdsLT (hlt x hxK)] with s hs
        rw [indicator_of_notMem (fun h : x ∈ Kᶜ ∩ u ⁻¹' Ici s => not_le.mpr hs.1 h.2)]
  rw [integral_zero] at key
  refine key.congr' (Eventually.of_forall fun s => ?_)
  exact integral_indicator (hmeas s)

/-- As the regular levels tend to the boundary value, their fluxes tend to the
boundary flux. -/
theorem tendsto_collar_flux {K : Set E3} (hK : IsCompact K)
    (hreg : K = closure (interior K)) (hC1 : HasC1Boundary (interior K))
    {u : E3 → ℝ} (hu : Continuous u) (hb : ∀ x ∈ K, u x = 1)
    (hlt : ∀ x ∈ Kᶜ, u x < 1)
    (hinf : Tendsto u (cocompact E3) (𝓝 0))
    {U : Set E3} (hU : IsOpen U) (hdu : ContDiffOn ℝ 1 u U)
    {t₁ : ℝ} (ht₁ : t₁ < 1)
    (hlev : ∀ s ∈ Ioo t₁ 1, u ⁻¹' {s} ⊆ U ∧ ∀ x, u x = s → gradient u x ≠ 0)
    {Z : E3 → E3} (hZ : ContDiff ℝ 1 Z) :
    Tendsto (fun s => ∫ x in u ⁻¹' {s}, ⟪Z x, unitNormal u x⟫ ∂hausdorffMeasure2 3)
      (𝓝[<] 1)
      (𝓝 (∫ x in frontier K, ⟪Z x, hC1.outwardNormal x⟫ ∂hausdorffMeasure2 3)) := by
  set B := ∫ x in frontier K, ⟪Z x, hC1.outwardNormal x⟫ ∂hausdorffMeasure2 3
  have hvol := tendsto_collar_setIntegral_zero hK hu hlt hinf (continuous_divergenceN hZ)
  have hlim := hvol.add (tendsto_const_nhds (x := B))
  rw [zero_add] at hlim
  refine hlim.congr' ?_
  filter_upwards [Ioo_mem_nhdsLT (show max t₁ 0 < 1 from max_lt ht₁ one_pos)] with s hs
  have hs0 : 0 < s := lt_of_le_of_lt (le_max_right _ _) hs.1
  have hst : s ∈ Ioo t₁ 1 := ⟨lt_of_le_of_lt (le_max_left _ _) hs.1, hs.2⟩
  rw [collar_gauss_green hK hreg hC1 hu hb hinf hU hdu hs0 hs.2 (hlev s hst).1
    (hlev s hst).2 hZ]
  ring

/-- Regular levels near the boundary value have finite area. -/
theorem eventually_level_measure_lt_top {u : E3 → ℝ} (hu : Continuous u)
    (hinf : Tendsto u (cocompact E3) (𝓝 0))
    {U : Set E3} (hU : IsOpen U) (hdu : ContDiffOn ℝ 1 u U)
    {t₁ : ℝ} (ht₁ : t₁ < 1)
    (hlev : ∀ s ∈ Ioo t₁ 1, u ⁻¹' {s} ⊆ U ∧ ∀ x, u x = s → gradient u x ≠ 0) :
    ∀ᶠ s in 𝓝[<] 1, hausdorffMeasure2 3 (u ⁻¹' {s}) < ⊤ := by
  filter_upwards [Ioo_mem_nhdsLT (show max t₁ 0 < 1 from max_lt ht₁ one_pos)] with s hs
  have hs0 : 0 < s := lt_of_le_of_lt (le_max_right _ _) hs.1
  have hst : s ∈ Ioo t₁ 1 := ⟨lt_of_le_of_lt (le_max_left _ _) hs.1, hs.2⟩
  obtain ⟨r, hr, hAr⟩ :=
    (fluxLevel_isCompact_superlevel hu hinf hs0).isBounded.subset_ball_lt 0 0
  have hD := fluxLevel_truncation_hasC1Boundary hU hu hdu hinf hs0 hr hAr (hlev s hst).1
    (hlev s hst).2
  have hopen : IsOpen (ball (0 : E3) r ∩ u ⁻¹' Iio s) :=
    isOpen_ball.inter (isOpen_Iio.preimage hu)
  have hbdd : Bornology.IsBounded (ball (0 : E3) r ∩ u ⁻¹' Iio s) :=
    isBounded_ball.subset inter_subset_left
  have hfin := capacity_boundary_measure_lt_top hopen hbdd hD
  rw [fluxLevel_frontier_truncation hu hinf hs0 hr hAr (hlev s hst).2] at hfin
  exact lt_of_le_of_lt (measure_mono subset_union_right) hfin

/-- A cutoff times a field which is `C¹` on an open set containing the
support of the cutoff is globally `C¹`. -/
lemma contDiff_cutoff_smul {ζ : E3 → ℝ} (hζ : ContDiff ℝ 1 ζ) {W : Set E3}
    (hW : IsOpen W) (hsupp : tsupport ζ ⊆ W) {V : E3 → E3} (hV : ContDiffOn ℝ 1 V W) :
    ContDiff ℝ 1 (fun x => ζ x • V x) := by
  refine contDiff_iff_contDiffAt.mpr fun x => ?_
  by_cases hx : x ∈ W
  · exact hζ.contDiffAt.smul (hV.contDiffAt (hW.mem_nhds hx))
  · have hev : (fun x => ζ x • V x) =ᶠ[𝓝 x] fun _ => 0 := by
      filter_upwards [(isClosed_tsupport ζ).isOpen_compl.mem_nhds
        (fun h => hx (hsupp h))] with y hy
      rw [image_eq_zero_of_notMem_tsupport hy, zero_smul]
    exact contDiffAt_const.congr_of_eventuallyEq hev

/-- The common setting of the endpoint statements: regularity of the levels near
the boundary value, the identification of gradients, and a smooth cutoff which is
one on the collar and supported where `∇g ≠ 0`. -/
lemma collar_endpoint_setup {K : Set E3} (hK : IsCompact K)
    {u : E3 → ℝ} (hu : Continuous u) (hb : ∀ x ∈ K, u x = 1)
    (hinf : Tendsto u (cocompact E3) (𝓝 0))
    {g : E3 → ℝ} (hg : ContDiff ℝ 2 g) (hug : EqOn u g (closure Kᶜ))
    {t₁ : ℝ} (ht₁ : t₁ < 1)
    (hcol : ∀ x ∈ closure Kᶜ, t₁ < u x → 0 < ‖gradient g x‖) :
    ContDiffOn ℝ 1 u Kᶜ ∧
    (∀ x ∈ Kᶜ, gradient u x = gradient g x) ∧
    (∀ s ∈ Ioo t₁ 1, u ⁻¹' {s} ⊆ Kᶜ ∧ ∀ x, u x = s → gradient u x ≠ 0) ∧
    ∃ s₁ ∈ Ioo t₁ 1, ∃ ζ : E3 → ℝ, ContDiff ℝ 1 ζ ∧
      tsupport ζ ⊆ {x | 0 < ‖gradient g x‖} ∧
      ∀ x ∈ closure Kᶜ, s₁ ≤ u x → ζ x = 1 := by
  have hgrad : ContDiff ℝ 1 (gradient g) := contDiff_gradient_of_contDiff_succ hg
  have hdu : ContDiffOn ℝ 1 u Kᶜ :=
    (hg.of_le (by norm_num)).contDiffOn.congr fun x hx => hug (subset_closure hx)
  have hgu (x : E3) (hx : x ∈ Kᶜ) : gradient u x = gradient g x := by
    apply Filter.EventuallyEq.gradient_eq
    filter_upwards [hK.isClosed.isOpen_compl.mem_nhds hx] with y hy
    exact hug (subset_closure hy)
  have hlevK (s : ℝ) (hs : s < 1) : u ⁻¹' {s} ⊆ Kᶜ := by
    intro x hx hxK
    have hxs : u x = s := hx
    rw [hb x hxK] at hxs
    exact hs.ne hxs.symm
  refine ⟨hdu, hgu, fun s hs => ⟨hlevK s hs.2, fun x hx => ?_⟩, ?_⟩
  · have hxK : x ∈ Kᶜ := hlevK s hs.2 (show u x = s from hx)
    rw [hgu x hxK]
    exact norm_pos_iff.mp (hcol x (subset_closure hxK) (hx ▸ hs.1))
  · set s₁ := (max t₁ 0 + 1) / 2 with hs₁
    have hm : max t₁ 0 < 1 := max_lt ht₁ one_pos
    have hs₁0 : 0 < s₁ := by have := le_max_right t₁ 0; linarith
    have hts₁ : t₁ < s₁ := by have := le_max_left t₁ 0; linarith
    have hs₁1 : s₁ < 1 := by linarith
    have hC : IsCompact (closure Kᶜ ∩ u ⁻¹' Ici s₁) :=
      (fluxLevel_isCompact_superlevel hu hinf hs₁0).inter_left isClosed_closure
    have hW : IsOpen {x : E3 | 0 < ‖gradient g x‖} :=
      isOpen_lt continuous_const hgrad.continuous.norm
    have hCW : closure Kᶜ ∩ u ⁻¹' Ici s₁ ⊆ {x : E3 | 0 < ‖gradient g x‖} :=
      fun x hx => hcol x hx.1 (lt_of_lt_of_le hts₁ hx.2)
    obtain ⟨ζ, hζ, _, hsupp, hone, _⟩ := exists_smooth_cutoff_one_near_compact hC hW hCW
    refine ⟨s₁, ⟨hts₁, hs₁1⟩, ζ, hζ.of_le (by norm_cast), hsupp, ?_⟩
    intro x hx hsx
    exact (hone.filter_mono (nhds_le_nhdsSet (show x ∈ closure Kᶜ ∩ u ⁻¹' Ici s₁ from
      ⟨hx, hsx⟩))).self_of_nhds

/-- A point of the boundary of `K` lies in the closure of the exterior and has
boundary value `1`. -/
lemma frontier_mem_closure_compl {K : Set E3} (hK : IsCompact K)
    {u : E3 → ℝ} (hb : ∀ x ∈ K, u x = 1) {x : E3} (hx : x ∈ frontier K) :
    x ∈ closure Kᶜ ∧ u x = 1 := by
  refine ⟨?_, hb x (hK.isClosed.frontier_subset hx)⟩
  rw [closure_compl]
  exact hx.2

/-- The endpoint `F(1)`: the level integrals `F(s) = ∫_{u=s} |∇u|²` tend to
`∫_{∂K} |∇g|²` as `s ↑ 1`. -/
theorem levelF_tendsto_boundary {K : Set E3} (hK : IsCompact K)
    (hreg : K = closure (interior K)) (hC1 : HasC1Boundary (interior K))
    {u : E3 → ℝ} (hu : Continuous u) (hb : ∀ x ∈ K, u x = 1)
    (hlt : ∀ x ∈ Kᶜ, u x < 1)
    (hinf : Tendsto u (cocompact E3) (𝓝 0))
    {g : E3 → ℝ} (hg : ContDiff ℝ 2 g) (hug : EqOn u g (closure Kᶜ))
    {t₁ : ℝ} (ht₁ : t₁ < 1)
    (hcol : ∀ x ∈ closure Kᶜ, t₁ < u x → 0 < ‖gradient g x‖)
    (hbd : ∀ x ∈ frontier K, gradient g x = -‖gradient g x‖ • hC1.outwardNormal x) :
    Tendsto (levelF Kᶜ u) (𝓝[<] 1)
      (𝓝 (∫ x in frontier K, ‖gradient g x‖ ^ 2 ∂hausdorffMeasure2 3)) := by
  obtain ⟨hdu, hgu, hlev, s₁, hs₁, ζ, hζ, hsupp, hone⟩ :=
    collar_endpoint_setup hK hu hb hinf hg hug ht₁ hcol
  have hgrad : ContDiff ℝ 1 (gradient g) := contDiff_gradient_of_contDiff_succ hg
  have hW : IsOpen {x : E3 | 0 < ‖gradient g x‖} :=
    isOpen_lt continuous_const hgrad.continuous.norm
  have hV : ContDiffOn ℝ 1 (fun x => -(‖gradient g x‖ • gradient g x))
      {x : E3 | 0 < ‖gradient g x‖} := by
    intro x hx
    exact (((hgrad.contDiffAt.norm ℝ (norm_pos_iff.mp hx)).smul
      hgrad.contDiffAt).neg).contDiffWithinAt
  have hZ := contDiff_cutoff_smul hζ hW hsupp hV
  have h := tendsto_collar_flux hK hreg hC1 hu hb hlt hinf hK.isClosed.isOpen_compl hdu ht₁
    hlev hZ
  have hbdry : (∫ x in frontier K,
      ⟪ζ x • -(‖gradient g x‖ • gradient g x), hC1.outwardNormal x⟫ ∂hausdorffMeasure2 3) =
      ∫ x in frontier K, ‖gradient g x‖ ^ 2 ∂hausdorffMeasure2 3 := by
    apply setIntegral_congr_fun isClosed_frontier.measurableSet
    intro x hx
    obtain ⟨hxc, hx1⟩ := frontier_mem_closure_compl hK hb hx
    have hn : ‖hC1.outwardNormal x‖ = 1 :=
      hC1.norm_outwardNormal (by rwa [capacity_frontier_interior hK hreg])
    have hin : ⟪gradient g x, hC1.outwardNormal x⟫ = -‖gradient g x‖ := by
      conv_lhs => rw [hbd x hx]
      rw [real_inner_smul_left, real_inner_self_eq_norm_sq, hn]
      ring
    dsimp only
    rw [hone x hxc (hx1 ▸ hs₁.2.le), one_smul, inner_neg_left, real_inner_smul_left, hin]
    ring
  rw [hbdry] at h
  refine h.congr' ?_
  filter_upwards [Ioo_mem_nhdsLT hs₁.2] with s hs
  have hst : s ∈ Ioo t₁ 1 := ⟨hs₁.1.trans hs.1, hs.2⟩
  have hsub := (hlev s hst).1
  change (∫ x in u ⁻¹' {s},
      ⟪ζ x • -(‖gradient g x‖ • gradient g x), unitNormal u x⟫ ∂hausdorffMeasure2 3) =
    ∫ x in Kᶜ ∩ u ⁻¹' {s}, gradNorm u x ^ 2 ∂hausdorffMeasure2 3
  rw [inter_eq_right.mpr hsub]
  apply setIntegral_congr_fun (isClosed_singleton.preimage hu).measurableSet
  intro x hx
  have hxs : u x = s := hx
  have hxK : x ∈ Kᶜ := hsub hx
  have hne : gradient g x ≠ 0 := by rw [← hgu x hxK]; exact (hlev s hst).2 x hxs
  have hne' : ‖gradient g x‖ ≠ 0 := norm_ne_zero_iff.mpr hne
  dsimp only
  rw [hone x (subset_closure hxK) (hxs ▸ hs.1.le), one_smul, unitNormal, gradNorm,
    hgu x hxK, inner_neg_left, inner_neg_right, neg_neg, real_inner_smul_left,
    real_inner_smul_right, real_inner_self_eq_norm_sq]
  field_simp

/-- The endpoint of the level areas: `H²({u = s}) → H²(∂K)` as `s ↑ 1`. -/
theorem area_tendsto_boundary {K : Set E3} (hK : IsCompact K)
    (hreg : K = closure (interior K)) (hC1 : HasC1Boundary (interior K))
    {u : E3 → ℝ} (hu : Continuous u) (hb : ∀ x ∈ K, u x = 1)
    (hlt : ∀ x ∈ Kᶜ, u x < 1)
    (hinf : Tendsto u (cocompact E3) (𝓝 0))
    {g : E3 → ℝ} (hg : ContDiff ℝ 2 g) (hug : EqOn u g (closure Kᶜ))
    {t₁ : ℝ} (ht₁ : t₁ < 1)
    (hcol : ∀ x ∈ closure Kᶜ, t₁ < u x → 0 < ‖gradient g x‖)
    (hbd : ∀ x ∈ frontier K, gradient g x = -‖gradient g x‖ • hC1.outwardNormal x) :
    Tendsto (fun s => (hausdorffMeasure2 3 (u ⁻¹' {s})).toReal) (𝓝[<] 1)
      (𝓝 (hausdorffMeasure2 3 (frontier K)).toReal) := by
  obtain ⟨hdu, hgu, hlev, s₁, hs₁, ζ, hζ, hsupp, hone⟩ :=
    collar_endpoint_setup hK hu hb hinf hg hug ht₁ hcol
  have hgrad : ContDiff ℝ 1 (gradient g) := contDiff_gradient_of_contDiff_succ hg
  have hW : IsOpen {x : E3 | 0 < ‖gradient g x‖} :=
    isOpen_lt continuous_const hgrad.continuous.norm
  have hV : ContDiffOn ℝ 1 (fun x => -(‖gradient g x‖⁻¹ • gradient g x))
      {x : E3 | 0 < ‖gradient g x‖} := by
    intro x hx
    exact ((((hgrad.contDiffAt.norm ℝ (norm_pos_iff.mp hx)).inv hx.ne').smul
      hgrad.contDiffAt).neg).contDiffWithinAt
  have hZ := contDiff_cutoff_smul hζ hW hsupp hV
  have h := tendsto_collar_flux hK hreg hC1 hu hb hlt hinf hK.isClosed.isOpen_compl hdu ht₁
    hlev hZ
  have hbdry : (∫ x in frontier K,
      ⟪ζ x • -(‖gradient g x‖⁻¹ • gradient g x), hC1.outwardNormal x⟫
        ∂hausdorffMeasure2 3) = (hausdorffMeasure2 3 (frontier K)).toReal := by
    rw [← mul_one (hausdorffMeasure2 3 (frontier K)).toReal, ← smul_eq_mul,
      ← measureReal_def, ← setIntegral_const]
    apply setIntegral_congr_fun isClosed_frontier.measurableSet
    intro x hx
    obtain ⟨hxc, hx1⟩ := frontier_mem_closure_compl hK hb hx
    have hn : ‖hC1.outwardNormal x‖ = 1 :=
      hC1.norm_outwardNormal (by rwa [capacity_frontier_interior hK hreg])
    have hpos : 0 < ‖gradient g x‖ := hcol x hxc (hx1 ▸ ht₁)
    have hin : ⟪gradient g x, hC1.outwardNormal x⟫ = -‖gradient g x‖ := by
      conv_lhs => rw [hbd x hx]
      rw [real_inner_smul_left, real_inner_self_eq_norm_sq, hn]
      ring
    dsimp only
    rw [hone x hxc (hx1 ▸ hs₁.2.le), one_smul, inner_neg_left, real_inner_smul_left, hin]
    field_simp
  rw [hbdry] at h
  refine h.congr' ?_
  filter_upwards [Ioo_mem_nhdsLT hs₁.2] with s hs
  have hst : s ∈ Ioo t₁ 1 := ⟨hs₁.1.trans hs.1, hs.2⟩
  have hsub := (hlev s hst).1
  rw [← mul_one (hausdorffMeasure2 3 (u ⁻¹' {s})).toReal, ← smul_eq_mul,
    ← measureReal_def, ← setIntegral_const]
  apply setIntegral_congr_fun (isClosed_singleton.preimage hu).measurableSet
  intro x hx
  have hxs : u x = s := hx
  have hxK : x ∈ Kᶜ := hsub hx
  have hne : gradient g x ≠ 0 := by rw [← hgu x hxK]; exact (hlev s hst).2 x hxs
  have hne' : ‖gradient g x‖ ≠ 0 := norm_ne_zero_iff.mpr hne
  dsimp only
  rw [hone x (subset_closure hxK) (hxs ▸ hs.1.le), one_smul, unitNormal, gradNorm,
    hgu x hxK, inner_neg_left, inner_neg_right, neg_neg, real_inner_smul_left,
    real_inner_smul_right, real_inner_self_eq_norm_sq]
  field_simp

/-- The levels near the boundary value have finite area, in the endpoint setting. -/
theorem eventually_level_measure_lt_top_of_collar {K : Set E3} (hK : IsCompact K)
    {u : E3 → ℝ} (hu : Continuous u) (hb : ∀ x ∈ K, u x = 1)
    (hinf : Tendsto u (cocompact E3) (𝓝 0))
    {g : E3 → ℝ} (hg : ContDiff ℝ 2 g) (hug : EqOn u g (closure Kᶜ))
    {t₁ : ℝ} (ht₁ : t₁ < 1)
    (hcol : ∀ x ∈ closure Kᶜ, t₁ < u x → 0 < ‖gradient g x‖) :
    ∀ᶠ s in 𝓝[<] 1, hausdorffMeasure2 3 (u ⁻¹' {s}) < ⊤ := by
  obtain ⟨hdu, -, hlev, -⟩ := collar_endpoint_setup hK hu hb hinf hg hug ht₁ hcol
  exact eventually_level_measure_lt_top hu hinf hK.isClosed.isOpen_compl hdu ht₁ hlev

/-- In the endpoint setting the hypothesis `u < 1` on `Kᶜ` is automatic: a point
of `Kᶜ` with `u ≥ 1` produces an exterior global maximum of `u`, where the
gradient of `u = g` would vanish, contradicting the collar hypothesis. -/
theorem collar_lt_one {K : Set E3} (hK : IsCompact K)
    {u : E3 → ℝ} (hu : Continuous u) (hb : ∀ x ∈ K, u x = 1)
    (hinf : Tendsto u (cocompact E3) (𝓝 0))
    {g : E3 → ℝ} (hug : EqOn u g (closure Kᶜ))
    {t₁ : ℝ} (ht₁ : t₁ < 1)
    (hcol : ∀ x ∈ closure Kᶜ, t₁ < u x → 0 < ‖gradient g x‖) :
    ∀ x ∈ Kᶜ, u x < 1 := by
  intro x hx
  by_contra hlt
  have hge : 1 ≤ u x := not_lt.mp hlt
  have hC : IsCompact (u ⁻¹' Ici (u x)) :=
    fluxLevel_isCompact_superlevel hu hinf (lt_of_lt_of_le one_pos hge)
  obtain ⟨y, hy, hmax⟩ := hC.exists_isMaxOn ⟨x, le_refl (u x)⟩ hu.continuousOn
  have hyx : u x ≤ u y := hy
  have hglob : ∀ z, u z ≤ u y := by
    intro z
    by_cases hz : u x ≤ u z
    · exact hmax hz
    · exact (le_of_lt (not_le.mp hz)).trans hyx
  obtain ⟨z, hzK, hzmax⟩ : ∃ z ∈ Kᶜ, ∀ w, u w ≤ u z := by
    rcases eq_or_lt_of_le (hge.trans hyx) with h1 | h1
    · refine ⟨x, hx, fun w => ?_⟩
      have : u x = 1 := le_antisymm (h1 ▸ hyx) hge
      rw [this, h1]
      exact hglob w
    · refine ⟨y, fun hyK => ?_, hglob⟩
      rw [hb y hyK] at h1
      exact lt_irrefl _ h1
  have hm : IsLocalMax u z := Eventually.of_forall hzmax
  have hgz : gradient u z = gradient g z := by
    apply Filter.EventuallyEq.gradient_eq
    filter_upwards [hK.isClosed.isOpen_compl.mem_nhds hzK] with w hw
    exact hug (subset_closure hw)
  have hz1 : 1 ≤ u z := hge.trans (hzmax x)
  have hpos := hcol z (subset_closure hzK) (lt_of_lt_of_le ht₁ hz1)
  rw [← hgz] at hpos
  simp only [gradient, hm.fderiv_eq_zero, map_zero, norm_zero, lt_irrefl] at hpos

end LiquidDrop.CapacitaryK

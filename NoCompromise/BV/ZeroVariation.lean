module

public import NoCompromise.BV.StrictApprox
public import Mathlib.Analysis.Calculus.MeanValue
public import Mathlib.MeasureTheory.Function.ConvergenceInMeasure
public import Mathlib.Topology.LocallyConstant.Basic
public import Mathlib.Topology.Compactness.Lindelof

@[expose] public section

/-!
# Constancy from vanishing variation

The distributional derivative vanishes when the test-field variation vanishes.
Mollification then gives classical constancy on connected interior regions.
-/

open MeasureTheory Filter Metric Set
open scoped ENNReal Topology CompactlySupported Convolution

namespace LiquidDrop

/-- Zero variation annihilates every compactly supported C¹ vector test field. -/
lemma integral_mul_divergenceN_eq_zero_of_variation_eq_zero {n : ℕ}
    {U : Set (EuclideanSpace ℝ (Fin n))} {f : EuclideanSpace ℝ (Fin n) → ℝ}
    (hV : variation f U = 0)
    {X : EuclideanSpace ℝ (Fin n) → EuclideanSpace ℝ (Fin n)}
    (hX : ContDiff ℝ 1 X) (hcX : HasCompactSupport X) (hsX : tsupport X ⊆ U) :
    (∫ x in U, f x * divergenceN X x) = 0 := by
  obtain ⟨C, hb⟩ := hcX.exists_bound_of_continuous hX.continuous
  have hC : 0 ≤ C := (norm_nonneg (X 0)).trans (hb 0)
  have h := abs_integral_mul_divergenceN_le_mul_variation (f := f)
    (by simp [hV]) hX hcX hsX hC hb
  apply abs_eq_zero.mp
  exact le_antisymm (by simpa [hV] using h) (abs_nonneg _)

/-- Zero variation annihilates every compactly supported coordinate derivative. -/
lemma integral_mul_fderiv_eq_zero_of_variation_eq_zero {n : ℕ}
    {U : Set (EuclideanSpace ℝ (Fin n))} {f φ : EuclideanSpace ℝ (Fin n) → ℝ}
    (hV : variation f U = 0) (hφ : ContDiff ℝ 1 φ)
    (hcφ : HasCompactSupport φ) (hsφ : tsupport φ ⊆ U) (i : Fin n) :
    (∫ x in U, f x * fderiv ℝ φ x (EuclideanSpace.single i 1)) = 0 := by
  let ψ : C_c(EuclideanSpace ℝ (Fin n), ℝ) := ⟨⟨φ, hφ.continuous⟩, hcφ⟩
  let X := coordinateTestField i ψ.toBoundedContinuousFunction
  have hX : ContDiff ℝ 1 X := hφ.smul contDiff_const
  have hcX : HasCompactSupport X := hcφ.smul_right
  have hsX : tsupport X ⊆ U := (tsupport_smul_subset_left _ _).trans hsφ
  have h := integral_mul_divergenceN_eq_zero_of_variation_eq_zero hV hX hcX hsX
  change (∫ x in U, f x * divergenceN
    (coordinateTestField i ψ.toBoundedContinuousFunction) x) = 0 at h
  simp_rw [divergenceN_coordinateTestField i
    (show ContDiff ℝ 1 ψ.toBoundedContinuousFunction from hφ)] at h
  exact h

/-- A mollification has zero gradient wherever the translated kernel support lies in a
region of zero variation. Values outside the region are cut off before convolution. -/
lemma gradient_convolution_indicator_eq_zero_of_variation_eq_zero {n : ℕ}
    {U : Set (EuclideanSpace ℝ (Fin n))} (hU : MeasurableSet U)
    {f k : EuclideanSpace ℝ (Fin n) → ℝ} (hf : IntegrableOn f U)
    (hV : variation f U = 0) (hk : ContDiff ℝ 1 k) (hck : HasCompactSupport k)
    (x : EuclideanSpace ℝ (Fin n)) (hs : tsupport (fun y => k (x - y)) ⊆ U) :
    gradient (k ⋆[ContinuousLinearMap.lsmul ℝ ℝ] (U.indicator f)) x = 0 := by
  have hif : Integrable (U.indicator f) := hf.integrable_indicator hU
  rw [gradient_convolution_left hif.locallyIntegrable hk hck]
  have hcgrad : HasCompactSupport (gradient k) :=
    hck.of_isClosed_subset (isClosed_tsupport _) (tsupport_gradient_subset k)
  have hiG := hcgrad.convolutionExists_right (μ := volume) (ContinuousLinearMap.lsmul ℝ ℝ)
    hif.locallyIntegrable (continuous_gradient_of_contDiff hk) x
  change Integrable (fun y => U.indicator f y • gradient k (x - y)) at hiG
  apply PiLp.ext
  intro i
  rw [eval_integral_piLp hiG.eval_piLp]
  have h := integral_mul_fderiv_eq_zero_of_variation_eq_zero hV
    (hk.comp (contDiff_const.sub contDiff_id))
    (hck.comp_homeomorph (Homeomorph.subLeft x)) hs i
  change (∫ y in U, f y * fderiv ℝ (fun z => k (x - z)) y
    (EuclideanSpace.single i 1)) = 0 at h
  simp_rw [fderiv_comp_const_sub hk, mul_neg, integral_neg] at h
  have hzero : (∫ y in U, f y * gradient k (x - y) i) = 0 := by
    simpa only [← gradient_apply_eq_fderiv_single, neg_eq_zero] using h
  change (∫ y, U.indicator f y * gradient k (x - y) i) = 0
  rw [← integral_indicator hU] at hzero
  convert hzero using 1
  congr 1
  ext y
  by_cases hy : y ∈ U <;> simp [hy]

/-- Every smooth convolution is constant on a connected open region whose translated
kernel supports stay inside the zero-variation domain. -/
theorem convolution_indicator_is_const_of_variation_eq_zero {n : ℕ}
    {U V : Set (EuclideanSpace ℝ (Fin n))} (hU : MeasurableSet U)
    (hV : IsOpen V) (hcV : IsPreconnected V)
    {f k : EuclideanSpace ℝ (Fin n) → ℝ} (hf : IntegrableOn f U)
    (hz : variation f U = 0) (hk : ContDiff ℝ 1 k) (hck : HasCompactSupport k)
    (hs : ∀ x ∈ V, tsupport (fun y => k (x - y)) ⊆ U) :
    ∃ c : ℝ, ∀ x ∈ V,
      (k ⋆[ContinuousLinearMap.lsmul ℝ ℝ] U.indicator f) x = c := by
  have hif : Integrable (U.indicator f) := hf.integrable_indicator hU
  have hg := hck.contDiff_convolution_left (ContinuousLinearMap.lsmul ℝ ℝ) hk
    hif.locallyIntegrable
  apply hV.exists_is_const_of_fderiv_eq_zero hcV (hg.differentiable one_ne_zero).differentiableOn
  intro x hx
  rw [← toDual_gradient,
    gradient_convolution_indicator_eq_zero_of_variation_eq_zero hU hf hz hk hck x (hs x hx),
    map_zero]
  rfl

/-- On every fixed interior ball, sufficiently small bump convolutions are constant. -/
lemma bump_convolution_indicator_is_const_on_ball {n : ℕ}
    {U : Set (EuclideanSpace ℝ (Fin n))} (hU : MeasurableSet U)
    {f : EuclideanSpace ℝ (Fin n) → ℝ} (hf : IntegrableOn f U)
    (hz : variation f U = 0) {a : EuclideanSpace ℝ (Fin n)} {r δ : ℝ}
    (hsub : ball a (r + δ) ⊆ U) (φ : ContDiffBump (0 : EuclideanSpace ℝ (Fin n)))
    (hφ : φ.rOut ≤ δ) :
    ∃ c : ℝ, ∀ x ∈ ball a r,
      (φ.normed volume ⋆[ContinuousLinearMap.lsmul ℝ ℝ] U.indicator f) x = c := by
  apply convolution_indicator_is_const_of_variation_eq_zero hU isOpen_ball
    (convex_ball a r).isPreconnected hf hz φ.contDiff_normed φ.hasCompactSupport_normed
  intro x hx y hy
  apply hsub
  have hy' : x - y ∈ tsupport (φ.normed volume) := by
    have := tsupport_comp_eq_preimage (φ.normed volume) (Homeomorph.subLeft x)
    change y ∈ tsupport ((φ.normed volume) ∘ (Homeomorph.subLeft x)) at hy
    rw [this] at hy
    exact hy
  rw [φ.tsupport_normed_eq] at hy'
  have hdist : dist y x ≤ δ := by
    simpa only [mem_closedBall, dist_zero_right, ← dist_eq_norm, dist_comm x y] using
      (show dist (x - y) 0 ≤ δ from hy'.trans hφ)
  exact (dist_triangle y x a).trans_lt (add_lt_add_of_le_of_lt hdist hx)
    |>.trans_eq (add_comm δ r)

/-- An L¹ limit of almost everywhere constant functions remains almost everywhere constant.
The measure need only be nonzero; its total mass need not be finite. -/
lemma ae_eq_const_of_l1_limit_of_ae_const {α : Type*} [MeasurableSpace α]
    {μ : Measure α} (hμ : μ ≠ 0) {g : ℕ → α → ℝ} {f : α → ℝ}
    (hg : ∀ j, Integrable (g j) μ) (hf : Integrable f μ)
    (ht : Tendsto (fun j => ∫ x, ‖g j x - f x‖ ∂μ) atTop (𝓝 0))
    (hc : ∀ j, ∃ c : ℝ, g j =ᵐ[μ] fun _ => c) :
    ∃ c : ℝ, f =ᵐ[μ] fun _ => c := by
  have he : Tendsto (fun j => eLpNorm (g j - f) 1 μ) atTop (𝓝 0) := by
    have ht' := ENNReal.continuous_ofReal.continuousAt.tendsto.comp ht
    simp only [ENNReal.ofReal_zero] at ht'
    convert ht' using 1
    ext j
    rw [eLpNorm_one_eq_lintegral_enorm ((hg j).sub hf).aestronglyMeasurable,
      ← ofReal_integral_norm_eq_lintegral_enorm ((hg j).sub hf)]
    rfl
  have hm := tendstoInMeasure_of_tendsto_eLpNorm one_ne_zero he
  obtain ⟨σ, _, hσ⟩ := hm.exists_seq_tendsto_ae
  choose c hc using hc
  have hboth := hσ.and (ae_all_iff.mpr hc)
  have : (ae μ).NeBot := ae_neBot.mpr hμ
  obtain ⟨a, ha, hca⟩ := hboth.exists
  refine ⟨f a, ?_⟩
  filter_upwards [hboth] with x hx
  apply tendsto_nhds_unique hx.1
  convert ha using 1
  ext j
  exact (hx.2 (σ j)).trans (hca (σ j)).symm

/-- Vanishing variation implies almost everywhere constancy on every ball with positive
clearance from the boundary. Only integrability on the containing domain is used. -/
theorem ae_eq_const_on_ball_of_variation_eq_zero {n : ℕ}
    {U : Set (EuclideanSpace ℝ (Fin n))} (hU : MeasurableSet U)
    {f : EuclideanSpace ℝ (Fin n) → ℝ} (hf : IntegrableOn f U)
    (hz : variation f U = 0) {a : EuclideanSpace ℝ (Fin n)} {r δ : ℝ}
    (hr : 0 < r) (hδ : 0 < δ) (hsub : ball a (r + δ) ⊆ U) :
    ∃ c : ℝ, f =ᵐ[volume.restrict (ball a r)] fun _ => c := by
  let φ (j : ℕ) : ContDiffBump (0 : EuclideanSpace ℝ (Fin n)) :=
    ⟨(δ / ((j : ℝ) + 1)) / 2, δ / ((j : ℝ) + 1), by positivity,
      half_lt_self (by positivity)⟩
  let F := U.indicator f
  let g (j : ℕ) := (φ j).normed volume ⋆[ContinuousLinearMap.lsmul ℝ ℝ] F
  have hF : Integrable F := hf.integrable_indicator hU
  have hg (j) : Integrable (g j) := (φ j).integrable_normed.integrable_convolution _ hF
  have hφ (j) : (φ j).rOut ≤ δ := div_le_self hδ.le (by norm_num)
  have hφlim : Tendsto (fun j => (φ j).rOut) atTop (𝓝 0) := by
    simpa only [mul_one_div, mul_zero] using
      (tendsto_one_div_add_atTop_nhds_zero_nat (𝕜 := ℝ)).const_mul δ
  have ht : Tendsto (fun j => ∫ x in ball a r, ‖g j x - F x‖) atTop (𝓝 0) := by
    apply squeeze_zero (fun _ => integral_nonneg fun _ => norm_nonneg _)
      (fun j => ?_) (tendsto_integral_norm_bump_convolution_sub hF hφlim)
    exact integral_mono_measure Measure.restrict_le_self
      (Eventually.of_forall fun _ => norm_nonneg _) ((hg j).sub hF).norm
  have hcj (j) : ∃ c : ℝ, g j =ᵐ[volume.restrict (ball a r)] fun _ => c := by
    obtain ⟨c, hc⟩ := bump_convolution_indicator_is_const_on_ball hU hf hz hsub (φ j) (hφ j)
    exact ⟨c, ae_restrict_of_forall_mem measurableSet_ball hc⟩
  obtain ⟨c, hc⟩ := ae_eq_const_of_l1_limit_of_ae_const
    (mt Measure.restrict_eq_zero.mp (measure_ball_pos volume a hr).ne')
    (fun j => (hg j).integrableOn) hF.integrableOn ht hcj
  refine ⟨c, ?_⟩
  filter_upwards [hc, ae_restrict_mem measurableSet_ball] with x hx hxb
  have hxU : x ∈ U := hsub (ball_subset_ball (by linarith) hxb)
  simpa only [F, indicator_of_mem hxU] using hx

/-- The local version needs only local integrability: each point admits an open ball on
which the function is almost everywhere constant. -/
lemma exists_ball_ae_eq_const_of_variation_eq_zero {n : ℕ}
    {U : Set (EuclideanSpace ℝ (Fin n))} (hU : IsOpen U)
    {f : EuclideanSpace ℝ (Fin n) → ℝ} (hf : LocallyIntegrableOn f U)
    (hz : variation f U = 0) {a : EuclideanSpace ℝ (Fin n)} (ha : a ∈ U) :
    ∃ r : ℝ, 0 < r ∧ ball a r ⊆ U ∧
      ∃ c : ℝ, f =ᵐ[volume.restrict (ball a r)] fun _ => c := by
  obtain ⟨ε, hε, hεU⟩ := Metric.isOpen_iff.mp hU a ha
  have hclosed : closedBall a (ε / 2) ⊆ U :=
    (closedBall_subset_ball (by linarith)).trans hεU
  have hif := hf.integrableOn_compact_subset hclosed (isCompact_closedBall a (ε / 2))
  have hv : variation f (closedBall a (ε / 2)) = 0 :=
    le_antisymm ((variation_mono hU.measurableSet hclosed).trans_eq hz) bot_le
  refine ⟨ε / 4, by positivity,
    (ball_subset_ball (by linarith)).trans hεU, ?_⟩
  apply ae_eq_const_on_ball_of_variation_eq_zero measurableSet_closedBall hif hv
    (by positivity) (show 0 < ε / 4 by positivity)
  have hrad : ε / 4 + ε / 4 = ε / 2 := by ring
  rw [hrad]
  exact ball_subset_closedBall

/-- Locally almost everywhere constant functions on a connected open Euclidean set
have a single almost everywhere constant value. Overlaps have positive volume, so their
constants agree; a countable open subcover then gives the global null-set statement. -/
theorem ae_eq_const_of_locally_ae_eq_const {n : ℕ}
    {U : Set (EuclideanSpace ℝ (Fin n))} (hcU : IsPreconnected U)
    {f : EuclideanSpace ℝ (Fin n) → ℝ}
    (hloc : ∀ x ∈ U, ∃ V : Set (EuclideanSpace ℝ (Fin n)),
      IsOpen V ∧ x ∈ V ∧ V ⊆ U ∧ ∃ c : ℝ, f =ᵐ[volume.restrict V] fun _ => c) :
    ∃ c : ℝ, f =ᵐ[volume.restrict U] fun _ => c := by
  classical
  choose V hoV hxV hVU c hc using fun x : U => hloc x x.property
  have heq (x y : U) (hy : (y : EuclideanSpace ℝ (Fin n)) ∈ V x) : c y = c x := by
    have hpos : volume (V y ∩ V x) ≠ 0 :=
      ((hoV y).inter (hoV x) |>.measure_pos volume ⟨y, hxV y, hy⟩).ne'
    have : (ae (volume.restrict (V y ∩ V x))).NeBot :=
      ae_neBot.mpr (mt Measure.restrict_eq_zero.mp hpos)
    have hay := ae_restrict_of_ae_restrict_of_subset (inter_subset_left : V y ∩ V x ⊆ V y)
      (hc y)
    have hax := ae_restrict_of_ae_restrict_of_subset (inter_subset_right : V y ∩ V x ⊆ V x)
      (hc x)
    obtain ⟨z, hz, hz'⟩ := (hay.and hax).exists
    exact hz.symm.trans hz'
  have hlc : IsLocallyConstant c := by
    apply (IsLocallyConstant.iff_eventually_eq c).mpr
    intro x
    have hmem : ∀ᶠ y : U in 𝓝 x, (y : EuclideanSpace ℝ (Fin n)) ∈ V x :=
      continuous_subtype_val.continuousAt (hoV x |>.mem_nhds (hxV x))
    exact hmem.mono fun y hy => heq x y hy
  have : PreconnectedSpace U := isPreconnected_iff_preconnectedSpace.mp hcU
  obtain ⟨a, ha⟩ := hlc.exists_eq_const
  have hcover : U ⊆ ⋃ x : U, V x := by
    intro x hx
    exact mem_iUnion.mpr ⟨⟨x, hx⟩, hxV ⟨x, hx⟩⟩
  obtain ⟨S, hS, hcoverS⟩ := (HereditarilyLindelofSpace.isLindelof U).elim_countable_subcover
    V hoV hcover
  refine ⟨a, ae_restrict_of_ae_restrict_of_subset hcoverS ?_⟩
  apply (ae_restrict_biUnion_iff V hS _).mpr
  intro x hx
  filter_upwards [hc x] with y hy
  exact hy.trans (congrFun ha x)

/-- Vanishing BV variation on a connected open domain forces almost everywhere constancy.
No global integrability, boundedness, boundary regularity, or positive-dimensional hypothesis
is needed. Empty domains are included. -/
theorem ae_eq_const_of_variation_eq_zero {n : ℕ}
    {U : Set (EuclideanSpace ℝ (Fin n))} (hU : IsOpen U) (hcU : IsPreconnected U)
    {f : EuclideanSpace ℝ (Fin n) → ℝ} (hf : LocallyIntegrableOn f U)
    (hz : variation f U = 0) :
    ∃ c : ℝ, f =ᵐ[volume.restrict U] fun _ => c := by
  apply ae_eq_const_of_locally_ae_eq_const hcU
  intro x hx
  obtain ⟨r, hr, hsub, c, hc⟩ := exists_ball_ae_eq_const_of_variation_eq_zero hU hf hz hx
  exact ⟨ball x r, isOpen_ball, mem_ball_self hr, hsub, c, hc⟩

end LiquidDrop

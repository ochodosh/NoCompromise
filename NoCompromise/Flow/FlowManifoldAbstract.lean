import Mathlib.Geometry.Manifold.IntegralCurve.UniformTime
import Mathlib.Geometry.Manifold.IntegralCurve.ExistUnique
import Mathlib.Analysis.ODE.PicardLindelof
import Mathlib.Analysis.ODE.ExistUnique
import NoCompromise.Flow.FlowMaximal

/-!
# Maximal integral curves on abstract manifolds

The manifold is finite dimensional, Hausdorff, and without boundary. The vector
field is `C¹`, with regularity expressed as a map into the tangent bundle.

This file constructs its unique maximal integral curves, proves uniform local
existence, compact escape in both time directions, completeness on compact
manifolds, and the group law with its domain equivalence. On a smooth manifold,
a `C^k` field has a jointly `C^k` maximal flow on a neighbourhood of every
`(0, x₀)`, for `1 ≤ k ≤ ∞`. Openness and regularity on the entire abstract flow
domain are not asserted here.
-/

open Set Filter Function Manifold
open scoped Topology

namespace LiquidDrop

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] {H : Type*} [TopologicalSpace H]
  {I : ModelWithCorners ℝ E H} {M : Type*} [TopologicalSpace M]
  [ChartedSpace H M] [IsManifold I 1 M] [T2Space M] [BoundarylessManifold I M]
  {v : (x : M) → TangentSpace I x}

/-- The maximal existence interval through `x`: the union of all open real
intervals containing zero on which an integral curve through `x` exists. -/
def mMaxFlowInterval (v : (x : M) → TangentSpace I x) (x : M) : Set ℝ :=
  {t | ∃ a b : ℝ, ∃ γ : ℝ → M,
    0 ∈ Ioo a b ∧ γ 0 = x ∧ IsMIntegralCurveOn γ v (Ioo a b) ∧ t ∈ Ioo a b}

open Classical in
/-- The value of the maximal integral curve through `x` at time `t`, chosen
from a local integral curve; outside its maximal interval the value is `x`. -/
noncomputable def mMaxFlow (v : (x : M) → TangentSpace I x) (t : ℝ) (x : M) : M :=
  if h : ∃ p : ℝ × ℝ × (ℝ → M),
      0 ∈ Ioo p.1 p.2.1 ∧ p.2.2 0 = x ∧
        IsMIntegralCurveOn p.2.2 v (Ioo p.1 p.2.1) ∧ t ∈ Ioo p.1 p.2.1
  then (Classical.choose h).2.2 t else x

omit [FiniteDimensional ℝ E] [IsManifold I 1 M] [T2Space M] [BoundarylessManifold I M] in
/-- The maximal existence interval is open. -/
theorem isOpen_mMaxFlowInterval (x : M) : IsOpen (mMaxFlowInterval v x) := by
  refine isOpen_iff_mem_nhds.mpr ?_
  rintro t ⟨a, b, γ, h0, hγ0, hγ, ht⟩
  exact mem_of_superset (isOpen_Ioo.mem_nhds ht)
    (fun s hs => ⟨a, b, γ, h0, hγ0, hγ, hs⟩)

omit [FiniteDimensional ℝ E] [IsManifold I 1 M] [T2Space M] [BoundarylessManifold I M] in
/-- The maximal existence interval is order-connected. -/
theorem ordConnected_mMaxFlowInterval (x : M) : (mMaxFlowInterval v x).OrdConnected := by
  refine ⟨?_⟩
  rintro s ⟨a, b, γ, h0, hγ0, hγ, hs⟩ t ⟨a', b', γ', h0', hγ0', hγ', ht⟩ u hu
  rcases le_total u 0 with hu0 | hu0
  · exact ⟨a, b, γ, h0, hγ0, hγ, lt_of_lt_of_le hs.1 hu.1, lt_of_le_of_lt hu0 h0.2⟩
  · exact ⟨a', b', γ', h0', hγ0', hγ', lt_of_lt_of_le h0'.1 hu0,
      lt_of_le_of_lt hu.2 ht.2⟩

omit [FiniteDimensional ℝ E] [IsManifold I 1 M] [T2Space M] [BoundarylessManifold I M] in
/-- Every interval carrying an integral curve through `x` belongs to the maximal interval. -/
theorem subset_mMaxFlowInterval {x : M} {a b : ℝ} {γ : ℝ → M}
    (h0 : 0 ∈ Ioo a b) (hγ0 : γ 0 = x) (hγ : IsMIntegralCurveOn γ v (Ioo a b)) :
    Ioo a b ⊆ mMaxFlowInterval v x :=
  fun _ ht => ⟨a, b, γ, h0, hγ0, hγ, ht⟩

variable (hv : CMDiff 1 (fun x ↦ (⟨x, v x⟩ : TangentBundle I M)))

include hv

omit [T2Space M] in
/-- Local existence on a symmetric interval at each initial point. -/
theorem exists_isMIntegralCurveOn_Ioo (x : M) :
    ∃ ε > 0, ∃ γ : ℝ → M, γ 0 = x ∧ IsMIntegralCurveOn γ v (Ioo (-ε) ε) := by
  obtain ⟨γ, hγ0, hγ⟩ :=
    exists_isMIntegralCurveAt_of_contMDiffAt_boundaryless 0 (hv.contMDiffAt (x := x))
  obtain ⟨ε, hε, hγ⟩ := isMIntegralCurveAt_iff'.mp hγ
  exact ⟨ε, hε, γ, hγ0, by simpa [Real.ball_eq_Ioo] using hγ⟩

omit [T2Space M] in
/-- Zero belongs to the maximal interval. -/
theorem zero_mem_mMaxFlowInterval (x : M) : 0 ∈ mMaxFlowInterval v x := by
  obtain ⟨ε, hε, γ, hγ0, hγ⟩ := exists_isMIntegralCurveOn_Ioo hv x
  exact ⟨-ε, ε, γ, ⟨by linarith, hε⟩, hγ0, hγ, by linarith, hε⟩

omit [FiniteDimensional ℝ E] in
/-- The chosen maximal flow agrees with any integral curve through its initial point. -/
theorem mMaxFlow_eq_of_isMIntegralCurveOn {x : M} {a b : ℝ} {γ : ℝ → M}
    (h0 : 0 ∈ Ioo a b) (hγ0 : γ 0 = x) (hγ : IsMIntegralCurveOn γ v (Ioo a b))
    {t : ℝ} (ht : t ∈ Ioo a b) : mMaxFlow v t x = γ t := by
  have hex : ∃ p : ℝ × ℝ × (ℝ → M),
      0 ∈ Ioo p.1 p.2.1 ∧ p.2.2 0 = x ∧
        IsMIntegralCurveOn p.2.2 v (Ioo p.1 p.2.1) ∧ t ∈ Ioo p.1 p.2.1 :=
    ⟨(a, b, γ), h0, hγ0, hγ, ht⟩
  rw [mMaxFlow, dite_eq_left hex]
  obtain ⟨h0', hγ0', hγ', ht'⟩ := Classical.choose_spec hex
  exact isMIntegralCurveOn_Ioo_eqOn_of_contMDiff_boundaryless
    (a := max (Classical.choose hex).1 a) (b := min (Classical.choose hex).2.1 b)
    ⟨max_lt h0'.1 h0.1, lt_min h0'.2 h0.2⟩ hv
    (hγ'.mono (Ioo_subset_Ioo (le_max_left ..) (min_le_left ..)))
    (hγ.mono (Ioo_subset_Ioo (le_max_right ..) (min_le_right ..)))
    (hγ0'.trans hγ0.symm) ⟨max_lt ht'.1 ht.1, lt_min ht'.2 ht.2⟩

/-- The maximal integral curve has the prescribed initial point. -/
theorem mMaxFlow_zero (x : M) : mMaxFlow v 0 x = x := by
  obtain ⟨a, b, γ, h0, hγ0, hγ, _⟩ := zero_mem_mMaxFlowInterval hv x
  exact (mMaxFlow_eq_of_isMIntegralCurveOn hv h0 hγ0 hγ h0).trans hγ0

omit [FiniteDimensional ℝ E] in
/-- The maximal flow is an integral curve on its maximal interval. -/
theorem isMIntegralCurveOn_mMaxFlow (x : M) :
    IsMIntegralCurveOn (fun t => mMaxFlow v t x) v (mMaxFlowInterval v x) := by
  rintro t ⟨a, b, γ, h0, hγ0, hγ, ht⟩
  have heq : (fun s => mMaxFlow v s x) =ᶠ[𝓝 t] γ :=
    mem_of_superset (isOpen_Ioo.mem_nhds ht)
      (fun s hs => mMaxFlow_eq_of_isMIntegralCurveOn hv h0 hγ0 hγ hs)
  have hd := ((hγ t ht).hasMFDerivAt (isOpen_Ioo.mem_nhds ht)).congr_of_eventuallyEq_abuse heq
  exact hd.hasMFDerivWithinAt.congr_mfderiv
    (congrArg (fun y : E => (1 : ℝ →L[ℝ] ℝ).smulRight y)
      (congrArg (fun p : M => (v p : E)) heq.eq_of_nhds).symm)

omit [FiniteDimensional ℝ E] in
/-- Uniqueness and maximality on every open interval containing zero. -/
theorem mMaxFlow_maximal {x : M} {a b : ℝ} {γ : ℝ → M}
    (h0 : 0 ∈ Ioo a b) (hγ0 : γ 0 = x) (hγ : IsMIntegralCurveOn γ v (Ioo a b)) :
    Ioo a b ⊆ mMaxFlowInterval v x ∧ EqOn γ (fun t => mMaxFlow v t x) (Ioo a b) :=
  ⟨subset_mMaxFlowInterval h0 hγ0 hγ,
    fun _ ht => (mMaxFlow_eq_of_isMIntegralCurveOn hv h0 hγ0 hγ ht).symm⟩

omit [T2Space M] in
set_option backward.isDefEq.respectTransparency false in
/-- Uniform local existence near an initial point: every point of one
neighbourhood has an integral curve on the same symmetric time interval. -/
theorem exists_uniform_isMIntegralCurveOn_nhds (x₀ : M) :
    ∃ N ∈ 𝓝 x₀, ∃ ε > 0, ∀ x ∈ N, ∃ γ : ℝ → M,
      γ 0 = x ∧ IsMIntegralCurveOn γ v (Ioo (-ε) ε) := by
  have hx₀ : I.IsInteriorPoint x₀ := BoundarylessManifold.isInteriorPoint
  have hv₀ := hv.contMDiffAt (x := x₀)
  rw [contMDiffAt_iff] at hv₀
  obtain ⟨_, hv₀⟩ := hv₀
  let w : E → E := fun y =>
    tangentCoordChange I ((extChartAt I x₀).symm y) x₀ ((extChartAt I x₀).symm y)
      (v ((extChartAt I x₀).symm y))
  have hw : ContDiffAt ℝ 1 w (extChartAt I x₀ x₀) :=
    (hv₀.contDiffAt (range_mem_nhds_isInteriorPoint hx₀)).snd
  obtain ⟨ε, hε, a, r, L, K, hr, hpl⟩ := IsPicardLindelof.of_contDiffAt_one hw
  obtain ⟨α, hα, hαcont⟩ :=
    (hpl 0).exists_forall_mem_closedBall_eq_hasDerivWithinAt_continuousOn
  simp only [zero_sub, zero_add] at hα hαcont
  have hdom : Metric.closedBall (extChartAt I x₀ x₀) (r : ℝ) ×ˢ Icc (-ε) ε ∈
      𝓝 (extChartAt I x₀ x₀, (0 : ℝ)) :=
    prod_mem_nhds (Metric.closedBall_mem_nhds _ hr) (Icc_mem_nhds (by linarith) hε)
  have hα0 : α (extChartAt I x₀ x₀, 0) = extChartAt I x₀ x₀ :=
    (hα _ (Metric.mem_closedBall_self r.coe_nonneg)).1
  have htarget : α ⁻¹' interior (extChartAt I x₀).target ∈
      𝓝 (extChartAt I x₀ x₀, (0 : ℝ)) := by
    apply (hαcont.continuousAt hdom).preimage_mem_nhds
    rw [hα0]
    exact isOpen_interior.mem_nhds ((I.isInteriorPoint_iff).mp hx₀)
  have hsmall : (Metric.closedBall (extChartAt I x₀ x₀) (r : ℝ) ×ˢ Ioo (-ε) ε) ∩
      α ⁻¹' interior (extChartAt I x₀).target ∈ 𝓝 (extChartAt I x₀ x₀, (0 : ℝ)) :=
    inter_mem (prod_mem_nhds (Metric.closedBall_mem_nhds _ hr)
      (Ioo_mem_nhds (by linarith) hε)) htarget
  obtain ⟨U, hU, V, hV, hUV⟩ := mem_nhds_prod_iff.mp hsmall
  obtain ⟨δ, hδ, hδV⟩ := Metric.mem_nhds_iff.mp hV
  have hδV' : Ioo (-δ) δ ⊆ V := by simpa [Real.ball_eq_Ioo] using hδV
  refine ⟨(extChartAt I x₀).source ∩ (extChartAt I x₀) ⁻¹' U,
    inter_mem (extChartAt_source_mem_nhds x₀)
      ((continuousAt_extChartAt x₀).preimage_mem_nhds hU), δ, hδ, ?_⟩
  rintro x ⟨hxsrc, hxU⟩
  let f : ℝ → E := fun t => α (extChartAt I x₀ x, t)
  have hxball := (hUV (a := (extChartAt I x₀ x, 0)) ⟨hxU, mem_of_mem_nhds hV⟩).1.1
  have hf0 : f 0 = extChartAt I x₀ x := (hα _ hxball).1
  refine ⟨(extChartAt I x₀).symm ∘ f, ?_, ?_⟩
  · rw [Function.comp_apply, hf0, (extChartAt I x₀).left_inv hxsrc]
  · intro t ht
    have htε := (hUV (a := (extChartAt I x₀ x, t)) ⟨hxU, hδV' ht⟩).1.2
    have hf3 : f t ∈ interior (extChartAt I x₀).target :=
      (hUV (a := (extChartAt I x₀ x, t)) ⟨hxU, hδV' ht⟩).2
    have hf3' := interior_subset hf3
    let xₜ : M := (extChartAt I x₀).symm (f t)
    have h : HasDerivAt f (tangentCoordChange I xₜ x₀ xₜ (v xₜ)) t :=
      ((hα _ hxball).2 t (Ioo_subset_Icc_self htε)).hasDerivAt
        (Icc_mem_nhds htε.1 htε.2)
    have hft1 := (extChartAt I x₀).target_subset_preimage_source hf3'
    have hft2 := mem_extChartAt_source (I := I) xₜ
    apply HasMFDerivAt.hasMFDerivWithinAt
    refine ⟨(continuousAt_extChartAt_symm'' hf3').comp h.continuousAt,
      HasDerivWithinAt.hasFDerivWithinAt ?_⟩
    simp only [mfld_simps, hasDerivWithinAt_univ]
    change HasDerivAt ((extChartAt I xₜ ∘ (extChartAt I x₀).symm) ∘ f) (v xₜ) t
    rw [← tangentCoordChange_self (I := I) (x := xₜ) (z := xₜ) (v := v xₜ) hft2,
      ← tangentCoordChange_comp (x := x₀) ⟨⟨hft2, hft1⟩, hft2⟩]
    apply HasFDerivAt.comp_hasDerivAt _ _ h
    apply HasFDerivWithinAt.hasFDerivAt (s := range I) _ <|
      mem_nhds_iff.mpr ⟨interior (extChartAt I x₀).target,
        subset_trans interior_subset (extChartAt_target_subset_range ..), isOpen_interior, hf3⟩
    rw [← (extChartAt I x₀).right_inv hf3']
    exact hasFDerivWithinAt_tangentCoordChange ⟨hft1, hft2⟩

omit hv in
private lemma mFlow_exists_Ioo_subset {S : Set ℝ} (hS : IsOpen S) (hc : S.OrdConnected)
    (h0 : 0 ∈ S) {t : ℝ} (ht : t ∈ S) :
    ∃ a b, 0 ∈ Ioo a b ∧ t ∈ Ioo a b ∧ Ioo a b ⊆ S := by
  have hlo : min 0 t ∈ S := by
    by_cases h : 0 ≤ t
    · simpa [min_eq_left h] using h0
    · simpa [min_eq_right (le_of_not_ge h)] using ht
  have hhi : max 0 t ∈ S := by
    by_cases h : 0 ≤ t
    · simpa [max_eq_right h] using ht
    · simpa [max_eq_left (le_of_not_ge h)] using h0
  obtain ⟨a, b, hab, habS⟩ := mem_nhds_iff_exists_Ioo_subset.mp (hS.mem_nhds hlo)
  obtain ⟨c, d, hcd, hcdS⟩ := mem_nhds_iff_exists_Ioo_subset.mp (hS.mem_nhds hhi)
  have ha : (a + min 0 t) / 2 ∈ S := habS ⟨by linarith [hab.1], by linarith [hab.1, hab.2]⟩
  have hd : (max 0 t + d) / 2 ∈ S := hcdS ⟨by linarith [hcd.1, hcd.2], by linarith [hcd.2]⟩
  refine ⟨(a + min 0 t) / 2, (max 0 t + d) / 2, ?_, ?_, ?_⟩
  · constructor <;> linarith [min_le_left (0 : ℝ) t, le_max_left (0 : ℝ) t, hab.1, hcd.2]
  · constructor <;> linarith [min_le_right (0 : ℝ) t, le_max_right (0 : ℝ) t, hab.1, hcd.2]
  · exact fun _ hs => hc.out ha hd ⟨hs.1.le, hs.2.le⟩

omit [FiniteDimensional ℝ E] in
/-- Maximality also holds on any open order-connected time set containing zero. -/
theorem mMaxFlow_maximal_on_open {x : M} {S : Set ℝ} {γ : ℝ → M}
    (hS : IsOpen S) (hc : S.OrdConnected) (h0 : 0 ∈ S)
    (hγ0 : γ 0 = x) (hγ : IsMIntegralCurveOn γ v S) :
    S ⊆ mMaxFlowInterval v x ∧ EqOn γ (fun t => mMaxFlow v t x) S := by
  have h (t : ℝ) (ht : t ∈ S) : t ∈ mMaxFlowInterval v x ∧ γ t = mMaxFlow v t x := by
    obtain ⟨a, b, h0', ht', hsub⟩ := mFlow_exists_Ioo_subset hS hc h0 ht
    have hm := mMaxFlow_maximal hv h0' hγ0 (hγ.mono hsub)
    exact ⟨hm.1 ht', hm.2 ht'⟩
  exact ⟨fun t ht => (h t ht).1, fun t ht => (h t ht).2⟩

/-- The group law, including the equivalence of its two time-domain conditions. -/
theorem mMaxFlow_add {x : M} {t : ℝ} (ht : t ∈ mMaxFlowInterval v x) (s : ℝ) :
    (s ∈ mMaxFlowInterval v (mMaxFlow v t x) ↔ s + t ∈ mMaxFlowInterval v x) ∧
      (s + t ∈ mMaxFlowInterval v x →
        mMaxFlow v s (mMaxFlow v t x) = mMaxFlow v (s + t) x) := by
  have hγ := isMIntegralCurveOn_mMaxFlow hv x
  have hshift := hγ.comp_add t
  have hopen : IsOpen {r : ℝ | r + t ∈ mMaxFlowInterval v x} :=
    (isOpen_mMaxFlowInterval x).preimage (continuous_id.add continuous_const)
  have hc : OrdConnected {r : ℝ | r + t ∈ mMaxFlowInterval v x} :=
    ⟨fun a ha b hb r hr => (ordConnected_mMaxFlowInterval x).out ha hb
      ⟨by linarith [hr.1], by linarith [hr.2]⟩⟩
  have hm1 := mMaxFlow_maximal_on_open hv hopen hc (by simpa using ht)
    (show (fun r => mMaxFlow v (r + t) x) 0 = mMaxFlow v t x by simp) hshift
  have hmt : -t + t ∈ mMaxFlowInterval v x := by simpa using zero_mem_mMaxFlowInterval hv x
  have hback := (isMIntegralCurveOn_mMaxFlow hv (mMaxFlow v t x)).comp_add (-t)
  have hopen' : IsOpen {r : ℝ | r + -t ∈ mMaxFlowInterval v (mMaxFlow v t x)} :=
    (isOpen_mMaxFlowInterval _).preimage (continuous_id.add continuous_const)
  have hc' : OrdConnected {r : ℝ | r + -t ∈ mMaxFlowInterval v (mMaxFlow v t x)} :=
    ⟨fun a ha b hb r hr => (ordConnected_mMaxFlowInterval _).out ha hb
      ⟨by linarith [hr.1], by linarith [hr.2]⟩⟩
  have hback0 : (fun r => mMaxFlow v (r + -t) (mMaxFlow v t x)) 0 = x := by
    have heq := hm1.2 hmt
    simpa [mMaxFlow_zero hv] using heq.symm
  have hm2 := mMaxFlow_maximal_on_open hv hopen' hc'
    (show 0 + -t ∈ mMaxFlowInterval v (mMaxFlow v t x) by simpa using hm1.1 hmt)
    hback0 hback
  exact ⟨⟨fun hs => hm2.1 (by simpa using hs), fun hs => hm1.1 hs⟩,
    fun hs => (hm1.2 hs).symm⟩

omit [T2Space M] in
/-- A compact set of initial points admits one common positive existence time. -/
theorem exists_uniform_isMIntegralCurveOn_compact {K : Set M} (hK : IsCompact K) :
    ∃ ε > 0, ∀ x ∈ K, ∃ γ : ℝ → M,
      γ 0 = x ∧ IsMIntegralCurveOn γ v (Ioo (-ε) ε) := by
  classical
  choose N hN δ hδ hcurves using exists_uniform_isMIntegralCurveOn_nhds hv
  obtain ⟨F, _, hF⟩ := hK.elim_nhds_subcover N (fun x _ => hN x)
  have hmin : ∀ G : Finset M, ∃ ε > 0, ∀ x ∈ G, ε ≤ δ x := by
    intro G
    induction G using Finset.induction_on with
    | empty => exact ⟨1, zero_lt_one, by simp⟩
    | @insert y G hy ih =>
      obtain ⟨ε, hε, hεG⟩ := ih
      refine ⟨min ε (δ y), lt_min hε (hδ y), ?_⟩
      intro x hx
      rcases Finset.mem_insert.mp hx with rfl | hx
      · exact min_le_right _ _
      · exact (min_le_left _ _).trans (hεG x hx)
  obtain ⟨ε, hε, hεF⟩ := hmin F
  refine ⟨ε, hε, ?_⟩
  intro x hx
  obtain ⟨y, hy, hxy⟩ := mem_iUnion₂.mp (hF hx)
  obtain ⟨γ, hγ0, hγ⟩ := hcurves y x hxy
  exact ⟨γ, hγ0, hγ.mono (Ioo_subset_Ioo (neg_le_neg (hεF y hy)) (hεF y hy))⟩

/-- A maximal curve cannot stop at a finite positive time while staying in a compact set. -/
theorem mem_mMaxFlowInterval_of_mem_compact {K : Set M} (hK : IsCompact K)
    {x : M} {b : ℝ} (hb : 0 < b) (hJ : Ico 0 b ⊆ mMaxFlowInterval v x)
    (hγK : ∀ t ∈ Ico 0 b, mMaxFlow v t x ∈ K) : b ∈ mMaxFlowInterval v x := by
  obtain ⟨ε, hε, hlocal⟩ := exists_uniform_isMIntegralCurveOn_compact hv hK
  let t := b - min (b / 2) (ε / 2)
  have hd : 0 < min (b / 2) (ε / 2) := lt_min (by linarith) (by linarith)
  have ht : t ∈ Ico 0 b := by
    constructor <;> dsimp [t] <;> linarith [min_le_left (b / 2) (ε / 2)]
  obtain ⟨γ, hγ0, hγ⟩ := hlocal _ (hγK t ht)
  have hs : b - t ∈ mMaxFlowInterval v (mMaxFlow v t x) :=
    subset_mMaxFlowInterval ⟨by linarith, hε⟩ hγ0 hγ
      ⟨by dsimp [t]; linarith, by dsimp [t]; linarith [min_le_right (b / 2) (ε / 2)]⟩
  simpa using (mMaxFlow_add hv (hJ ht) (b - t)).1.mp hs

/-- A maximal curve cannot stop at a finite negative time while staying in a compact set. -/
theorem mem_mMaxFlowInterval_of_mem_compact_backward {K : Set M} (hK : IsCompact K)
    {x : M} {b : ℝ} (hb : b < 0) (hJ : Ioc b 0 ⊆ mMaxFlowInterval v x)
    (hγK : ∀ t ∈ Ioc b 0, mMaxFlow v t x ∈ K) : b ∈ mMaxFlowInterval v x := by
  obtain ⟨ε, hε, hlocal⟩ := exists_uniform_isMIntegralCurveOn_compact hv hK
  let t := b + min (-b / 2) (ε / 2)
  have hd : 0 < min (-b / 2) (ε / 2) := lt_min (by linarith) (by linarith)
  have ht : t ∈ Ioc b 0 := by
    constructor <;> dsimp [t] <;> linarith [min_le_left (-b / 2) (ε / 2)]
  obtain ⟨γ, hγ0, hγ⟩ := hlocal _ (hγK t ht)
  have hs : b - t ∈ mMaxFlowInterval v (mMaxFlow v t x) :=
    subset_mMaxFlowInterval ⟨by linarith, hε⟩ hγ0 hγ
      ⟨by dsimp [t]; linarith [min_le_right (-b / 2) (ε / 2)], by dsimp [t]; linarith⟩
  simpa using (mMaxFlow_add hv (hJ ht) (b - t)).1.mp hs

/-- Every `C¹` vector field on a compact boundaryless manifold is complete. -/
theorem exists_isMIntegralCurve_of_compactSpace [CompactSpace M] (x : M) :
    ∃ γ : ℝ → M, γ 0 = x ∧ IsMIntegralCurve γ v := by
  obtain ⟨ε, hε, h⟩ := exists_uniform_isMIntegralCurveOn_compact hv (K := univ) isCompact_univ
  exact exists_isMIntegralCurve_of_isMIntegralCurveOn hv hε (fun x => h x (mem_univ x)) x

/-- On a compact manifold every maximal existence interval is the whole real line. -/
theorem mMaxFlowInterval_eq_univ [CompactSpace M] (x : M) : mMaxFlowInterval v x = univ := by
  obtain ⟨γ, hγ0, hγ⟩ := exists_isMIntegralCurve_of_compactSpace hv x
  apply eq_univ_of_univ_subset
  exact (mMaxFlow_maximal_on_open hv isOpen_univ ordConnected_univ (mem_univ 0)
    hγ0 (hγ.isMIntegralCurveOn univ)).1

/-- On a compact manifold the chosen maximal flow itself is a global integral curve. -/
theorem isMIntegralCurve_mMaxFlow [CompactSpace M] (x : M) :
    IsMIntegralCurve (fun t => mMaxFlow v t x) v := by
  rw [isMIntegralCurve_iff_isMIntegralCurveOn]
  simpa [mMaxFlowInterval_eq_univ hv x] using isMIntegralCurveOn_mMaxFlow hv x

omit hv [FiniteDimensional ℝ E] [T2Space M] [BoundarylessManifold I M] in
set_option backward.isDefEq.respectTransparency false in
private lemma mFlow_chart_transfer (x₀ : M) {f : ℝ → E} {S : Set ℝ}
    (hf : ∀ t ∈ S, HasDerivAt f
      (tangentCoordChange I ((extChartAt I x₀).symm (f t)) x₀
        ((extChartAt I x₀).symm (f t)) (v ((extChartAt I x₀).symm (f t)))) t)
    (hft : ∀ t ∈ S, f t ∈ interior (extChartAt I x₀).target) :
    IsMIntegralCurveOn ((extChartAt I x₀).symm ∘ f) v S := by
  intro t ht
  let xₜ : M := (extChartAt I x₀).symm (f t)
  have h := hf t ht
  have hf3 := hft t ht
  have hf3' := interior_subset hf3
  have hft1 := (extChartAt I x₀).target_subset_preimage_source hf3'
  have hft2 := mem_extChartAt_source (I := I) xₜ
  apply HasMFDerivAt.hasMFDerivWithinAt
  refine ⟨(continuousAt_extChartAt_symm'' hf3').comp h.continuousAt,
    HasDerivWithinAt.hasFDerivWithinAt ?_⟩
  simp only [mfld_simps, hasDerivWithinAt_univ]
  change HasDerivAt ((extChartAt I xₜ ∘ (extChartAt I x₀).symm) ∘ f) (v xₜ) t
  rw [← tangentCoordChange_self (I := I) (x := xₜ) (z := xₜ) (v := v xₜ) hft2,
    ← tangentCoordChange_comp (x := x₀) ⟨⟨hft2, hft1⟩, hft2⟩]
  apply HasFDerivAt.comp_hasDerivAt _ _ h
  apply HasFDerivWithinAt.hasFDerivAt (s := range I) _ <|
    mem_nhds_iff.mpr ⟨interior (extChartAt I x₀).target,
      subset_trans interior_subset (extChartAt_target_subset_range ..), isOpen_interior, hf3⟩
  rw [← (extChartAt I x₀).right_inv hf3']
  exact hasFDerivWithinAt_tangentCoordChange ⟨hft1, hft2⟩

omit hv in
set_option backward.isDefEq.respectTransparency false in
/-- Near each `(0, x₀)`, the abstract maximal flow is jointly `C^k`, including
`k = ∞`. The neighbourhood is contained in the maximal flow domain. -/
theorem exists_contMDiffOn_mMaxFlow_nhds [IsManifold I (⊤ : ℕ∞) M] {k : ℕ∞}
    (hk : 1 ≤ k) (hvk : CMDiff k (fun x ↦ (⟨x, v x⟩ : TangentBundle I M))) (x₀ : M) :
    ∃ N ∈ 𝓝 ((0 : ℝ), x₀),
      N ⊆ {q : ℝ × M | q.1 ∈ mMaxFlowInterval v q.2} ∧
      ContMDiffOn (𝓘(ℝ, ℝ).prod I) I k (fun q : ℝ × M => mMaxFlow v q.1 q.2) N := by
  have hk' : (1 : WithTop ℕ∞) ≤ (k : WithTop ℕ∞) := by exact_mod_cast hk
  have hv : CMDiff 1 (fun x ↦ (⟨x, v x⟩ : TangentBundle I M)) := hvk.of_le hk'
  let w : E → E := fun y =>
    tangentCoordChange I ((extChartAt I x₀).symm y) x₀ ((extChartAt I x₀).symm y)
      (v ((extChartAt I x₀).symm y))
  let U := interior (extChartAt I x₀).target
  have hz : extChartAt I x₀ x₀ ∈ U :=
    (I.isInteriorPoint_iff).mp (BoundarylessManifold.isInteriorPoint (I := I) (x := x₀))
  have hcoord := (contMDiff_iff.mp hvk).2 x₀ (⟨x₀, v x₀⟩ : TangentBundle I M)
  have hwk : ContDiffOn ℝ k w U := by
    apply hcoord.snd.mono
    intro y hy
    refine ⟨interior_subset hy, ?_⟩
    simpa only [mfld_simps] using
      (extChartAt I x₀).target_subset_preimage_source (interior_subset hy)
  have hw : ContDiffOn ℝ 1 w U := hwk.of_le hk'
  obtain ⟨hD, hF⟩ := isOpen_maxFlowDomain_and_contDiffOn isOpen_interior hk hwk
  have hzero : ((0 : ℝ), extChartAt I x₀ x₀) ∈ maxFlowDomain w U :=
    ⟨hz, (isFlowCurveOn_maxFlow isOpen_interior hw hz).2.2.1⟩
  obtain ⟨T, hT, V, hV, hTV⟩ := mem_nhds_prod_iff.mp (hD.mem_nhds hzero)
  obtain ⟨ε, hε, hεT⟩ := Metric.mem_nhds_iff.mp hT
  have hεT' : Ioo (-ε) ε ⊆ T := by simpa [Real.ball_eq_Ioo] using hεT
  let N := (extChartAt I x₀).source ∩ (extChartAt I x₀) ⁻¹' V
  have hN : N ∈ 𝓝 x₀ := inter_mem (extChartAt_source_mem_nhds x₀)
    ((continuousAt_extChartAt x₀).preimage_mem_nhds hV)
  have hcurves : ∀ x ∈ N,
      ((extChartAt I x₀).symm ∘ (fun t => maxFlow w U t (extChartAt I x₀ x))) 0 = x ∧
      IsMIntegralCurveOn
        ((extChartAt I x₀).symm ∘ (fun t => maxFlow w U t (extChartAt I x₀ x)))
        v (Ioo (-ε) ε) := by
    intro x hx
    have hxU := (hTV (a := (0, extChartAt I x₀ x)) ⟨mem_of_mem_nhds hT, hx.2⟩).1
    have hγ := isFlowCurveOn_maxFlow isOpen_interior hw hxU
    refine ⟨?_, mFlow_chart_transfer x₀ (fun t ht => ?_) (fun t ht => ?_)⟩
    · have hγ0 : maxFlow w U 0 (extChartAt I x₀ x) = extChartAt I x₀ x := hγ.2.2.2.1
      rw [comp_apply, hγ0, (extChartAt I x₀).left_inv hx.1]
    · exact (hγ.2.2.2.2 t (hTV (a := (t, extChartAt I x₀ x)) ⟨hεT' ht, hx.2⟩).2).2
    · exact (hγ.2.2.2.2 t (hTV (a := (t, extChartAt I x₀ x)) ⟨hεT' ht, hx.2⟩).2).1
  have hparam : ContMDiffOn (𝓘(ℝ, ℝ).prod I) 𝓘(ℝ, ℝ × E) k
      (fun q : ℝ × M => (q.1, extChartAt I x₀ q.2)) (Ioo (-ε) ε ×ˢ N) := by
    apply contMDiffOn_fst.prodMk_space
    apply contMDiffOn_extChartAt.comp contMDiffOn_snd
    intro q hq
    change q.2 ∈ (chartAt H x₀).source
    simpa only [extChartAt_source] using hq.2.1
  have hparamD : MapsTo (fun q : ℝ × M => (q.1, extChartAt I x₀ q.2))
      (Ioo (-ε) ε ×ˢ N) (maxFlowDomain w U) :=
    fun q hq => hTV ⟨hεT' hq.1, hq.2.2⟩
  have hF' := hF.contMDiffOn.comp hparam hparamD
  have hmaps : MapsTo (fun q : ℝ × M => maxFlow w U q.1 (extChartAt I x₀ q.2))
      (Ioo (-ε) ε ×ˢ N) (extChartAt I x₀).target := by
    intro q hq
    have hqD := hparamD hq
    exact interior_subset
      ((isFlowCurveOn_maxFlow isOpen_interior hw hqD.1).2.2.2.2 q.1 hqD.2).1
  have hΨ := (contMDiffOn_extChartAt_symm (n := (k : WithTop ℕ∞)) x₀).comp hF' hmaps
  have heq : EqOn (fun q : ℝ × M => mMaxFlow v q.1 q.2)
      (fun q : ℝ × M => (extChartAt I x₀).symm (maxFlow w U q.1 (extChartAt I x₀ q.2)))
      (Ioo (-ε) ε ×ˢ N) := by
    intro q hq
    exact mMaxFlow_eq_of_isMIntegralCurveOn hv ⟨by linarith, hε⟩
      (hcurves q.2 hq.2).1 (hcurves q.2 hq.2).2 hq.1
  refine ⟨Ioo (-ε) ε ×ˢ N, prod_mem_nhds (Ioo_mem_nhds (by linarith) hε) hN, ?_, ?_⟩
  · intro q hq
    exact subset_mMaxFlowInterval ⟨by linarith, hε⟩
      (hcurves q.2 hq.2).1 (hcurves q.2 hq.2).2 hq.1
  · exact hΨ.congr heq

end LiquidDrop

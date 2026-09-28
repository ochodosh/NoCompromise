import NoCompromise.Surface.Shape
import Mathlib.Analysis.Normed.Module.Connected

/-!
# Adjacency at regular surface levels

`lem:level-adjacency`: local connected sides of a regular level and constancy
of their adjacent connected components along preconnected regular level sets.
-/

noncomputable section
open Set Filter Function InnerProductSpace
open scoped Topology Gradient
namespace LiquidDrop

private lemma level_derivative_surjective {S U : Set E₃} {q : E₃}
    {φ h : E₃ → ℝ} (hU : IsOpen U) (hqU : q ∈ U)
    (hφ : ContDiffAt ℝ 1 φ q) (hz : S ∩ U = {x ∈ U | φ x = 0})
    (hq : q ∈ S) (hr : gradient φ q ≠ 0)
    (hn : ¬ IsSurfaceCriticalPoint S h q) :
    ((fderiv ℝ φ q).prod (fderiv ℝ h q)).range = ⊤ := by
  have ht := tangentPlane_eq hU hqU hφ hz hq hr
  obtain ⟨v, hv, hvh⟩ : ∃ v ∈ tangentPlane S q, fderiv ℝ h q v ≠ 0 := by
    by_contra! hv
    exact hn ⟨hq, hv⟩
  have hvφ : fderiv ℝ φ q v = 0 := by
    rw [ht, Submodule.mem_orthogonal_singleton_iff_inner_right, inner_gradient_left] at hv
    exact hv
  have hφrange : (fderiv ℝ φ q).range = ⊤ := by
    apply Module.Dual.range_eq_top_of_ne_zero
    intro he
    apply hr
    apply (toDual ℝ E₃).injective
    rw [toDual_gradient, map_zero]
    exact ContinuousLinearMap.ext fun x => congrArg (fun L : E₃ →ₗ[ℝ] ℝ => L x) he
  obtain ⟨u, hu⟩ := (LinearMap.range_eq_top.mp hφrange) 1
  change fderiv ℝ φ q u = 1 at hu
  apply LinearMap.range_eq_top.mpr
  rintro ⟨a, b⟩
  refine ⟨a • u + ((b - a * fderiv ℝ h q u) / fderiv ℝ h q v) • v, ?_⟩
  ext <;> simp [hu, hvφ, hvh]

private lemma chart_slice_connected {K : Type*} [NormedAddCommGroup K] [NormedSpace ℝ K]
    (e : OpenPartialHomeomorph E₃ ((ℝ × ℝ) × K)) {r : ℝ} (hr : 0 < r)
    {J : Set ℝ} (hJ : IsConnected J)
    (hsub : ({0} ×ˢ J) ×ˢ Metric.ball (0 : K) r ⊆ e.target) :
    IsConnected (e.symm '' (({0} ×ˢ J) ×ˢ Metric.ball (0 : K) r)) := by
  exact ((isConnected_singleton.prod hJ).prod
    ((convex_ball (0 : K) r).isConnected ⟨0, Metric.mem_ball_self hr⟩)).image _
      (e.symm.continuousOn.mono hsub)

private lemma chart_slice_closure {K : Type*} [NormedAddCommGroup K]
    (e : OpenPartialHomeomorph E₃ ((ℝ × ℝ) × K)) {r : ℝ} {J : Set ℝ}
    (hJ : (0 : ℝ) ∈ closure J) {z : E₃} (hz : z ∈ e.source)
    (hz₁ : (e z).1.1 = 0) (hz₂ : (e z).1.2 = 0)
    (hzk : (e z).2 ∈ Metric.ball (0 : K) r) :
    z ∈ closure (e.symm '' (({0} ×ˢ J) ×ˢ Metric.ball (0 : K) r)) := by
  have hc : e z ∈ closure (({0} ×ˢ J) ×ˢ Metric.ball (0 : K) r) := by
    rw [closure_prod_eq, closure_prod_eq]
    exact ⟨⟨by simp [hz₁],
      hz₂ ▸ hJ⟩, subset_closure hzk⟩
  have hc' := mem_closure_image
    (e.symm.continuousOn.continuousAt (e.open_target.mem_nhds (e.map_source hz))) hc
  simpa only [e.left_inv hz] using hc'

/-- `lem:level-adjacency`: a regular surface level has two connected, nonempty
local sides, and every level point in the neighborhood adjoins both sides. -/
theorem exists_levelAdjacency_nhds {S : Set E₃} (hS : IsSmoothEmbeddedSurface S)
    {h : E₃ → ℝ} (hh : ContDiff ℝ 1 h) {c : ℝ} {q : E₃}
    (hq : q ∈ S) (hc : h q = c) (hn : ¬ IsSurfaceCriticalPoint S h q) :
    ∃ U : Set E₃, IsOpen U ∧ q ∈ U ∧
      IsConnected (S ∩ U ∩ {x | h x < c}) ∧
      IsConnected (S ∩ U ∩ {x | c < h x}) ∧
      ∀ q' ∈ S ∩ U, h q' = c →
        q' ∈ closure (S ∩ U ∩ {x | h x < c}) ∧
        q' ∈ closure (S ∩ U ∩ {x | c < h x}) := by
  obtain ⟨W, φ, hW, hqW, hφ, hz, hrφ⟩ := hS q hq
  have hφ₁ : ContDiff ℝ 1 φ := hφ.of_le (by simp)
  let F : E₃ → ℝ × ℝ := fun x => (φ x, h x - c)
  let D := (fderiv ℝ φ q).prod (fderiv ℝ h q)
  have hD : HasStrictFDerivAt F D q :=
    (hφ₁.contDiffAt.hasStrictFDerivAt one_ne_zero).prodMk
      ((hh.contDiffAt.hasStrictFDerivAt one_ne_zero).sub_const c)
  have hsur : D.range = ⊤ :=
    level_derivative_surjective hW hqW hφ₁.contDiffAt hz hq (hrφ q ⟨hq, hqW⟩) hn
  let e := hD.implicitToOpenPartialHomeomorph F D hsur
  have hqe : q ∈ e.source := hD.mem_implicitToOpenPartialHomeomorph_source hsur
  have hqφ : φ q = 0 := (hz ▸ (show q ∈ S ∩ W from ⟨hq, hqW⟩)).2
  have heq : e q = 0 := by
    simp [e, F, hqφ, hc]
  have hef (x : E₃) : (e x).1 = (φ x, h x - c) :=
    hD.implicitToOpenPartialHomeomorph_fst hsur x
  have hV : IsOpen (e.target ∩ e.symm ⁻¹' W) := e.isOpen_inter_preimage_symm hW
  have h0V : (0 : (ℝ × ℝ) × D.ker) ∈ e.target ∩ e.symm ⁻¹' W := by
    rw [← heq]
    exact ⟨e.map_source hqe, by simpa only [mem_preimage, e.left_inv hqe] using hqW⟩
  obtain ⟨r, hr, hball⟩ := Metric.isOpen_iff.mp hV 0 h0V
  let U : Set E₃ := e.source ∩ e ⁻¹' Metric.ball 0 r
  have hU : IsOpen U := e.isOpen_inter_preimage Metric.isOpen_ball
  have hqU : q ∈ U := ⟨hqe, by
    change e q ∈ Metric.ball 0 r
    rw [heq]
    exact Metric.mem_ball_self hr⟩
  have hUW : U ⊆ W := by
    intro x hx
    have := (hball hx.2).2
    simpa only [mem_preimage, e.left_inv hx.1] using this
  have hcoords (x : E₃) : (e x).1.1 = φ x ∧ (e x).1.2 = h x - c := by
    rw [hef]
    exact ⟨rfl, rfl⟩
  have hmem (z : (ℝ × ℝ) × D.ker) :
      z ∈ Metric.ball 0 r ↔ |z.1.1| < r ∧ |z.1.2| < r ∧ ‖z.2‖ < r := by
    simp [Metric.mem_ball, dist_zero_right, Prod.norm_def, max_lt_iff, and_assoc]
  have hminusSub : ({0} ×ˢ Ioo (-r) 0) ×ˢ Metric.ball (0 : D.ker) r ⊆ e.target := by
    rintro ⟨⟨a, b⟩, k⟩ ⟨⟨ha, hb⟩, hk⟩
    have ha' : a = 0 := ha
    apply (hball _).1
    rw [hmem, ha']
    exact ⟨by simpa using hr, abs_lt.mpr ⟨hb.1, hb.2.trans hr⟩,
      by simpa using hk⟩
  have hplusSub : ({0} ×ˢ Ioo 0 r) ×ˢ Metric.ball (0 : D.ker) r ⊆ e.target := by
    rintro ⟨⟨a, b⟩, k⟩ ⟨⟨ha, hb⟩, hk⟩
    have ha' : a = 0 := ha
    apply (hball _).1
    rw [hmem, ha']
    exact ⟨by simpa using hr, abs_lt.mpr ⟨(neg_neg_of_pos hr).trans hb.1, hb.2⟩,
      by simpa using hk⟩
  have hminus : S ∩ U ∩ {x | h x < c} =
      e.symm '' (({0} ×ˢ Ioo (-r) 0) ×ˢ Metric.ball (0 : D.ker) r) := by
    rw [e.symm_image_eq_source_inter_preimage hminusSub]
    ext x
    have hxφ (hx : x ∈ U) : x ∈ S ↔ φ x = 0 := by
      constructor
      · intro hxS; exact (hz ▸ (show x ∈ S ∩ W from ⟨hxS, hUW hx⟩)).2
      · intro hx0; exact ((congrArg (fun T : Set E₃ => x ∈ T) hz).mpr ⟨hUW hx, hx0⟩).1
    simp only [mem_inter_iff, mem_ofPred_eq, mem_preimage, mem_prod, mem_singleton_iff,
      mem_Ioo, hcoords x |>.1, hcoords x |>.2]
    constructor
    · rintro ⟨⟨hxS, hxU⟩, hxc⟩
      have hb := (hmem (e x)).mp hxU.2
      exact ⟨hxU.1, ⟨⟨(hxφ hxU).mp hxS, (abs_lt.mp hb.2.1).1, sub_neg.mpr hxc⟩,
        by simpa using hb.2.2⟩⟩
    · rintro ⟨hxe, ⟨⟨hx0, hb⟩, hk⟩⟩
      have hxU : x ∈ U := ⟨hxe, (hmem _).mpr ⟨by simpa [hcoords, hx0] using hr,
        by rw [(hcoords x).2]; exact abs_lt.mpr ⟨hb.1, hb.2.trans hr⟩,
        by simpa using hk⟩⟩
      exact ⟨⟨(hxφ hxU).mpr hx0, hxU⟩, sub_neg.mp hb.2⟩
  have hplus : S ∩ U ∩ {x | c < h x} =
      e.symm '' (({0} ×ˢ Ioo 0 r) ×ˢ Metric.ball (0 : D.ker) r) := by
    rw [e.symm_image_eq_source_inter_preimage hplusSub]
    ext x
    have hxφ (hx : x ∈ U) : x ∈ S ↔ φ x = 0 := by
      constructor
      · intro hxS; exact (hz ▸ (show x ∈ S ∩ W from ⟨hxS, hUW hx⟩)).2
      · intro hx0; exact ((congrArg (fun T : Set E₃ => x ∈ T) hz).mpr ⟨hUW hx, hx0⟩).1
    simp only [mem_inter_iff, mem_ofPred_eq, mem_preimage, mem_prod, mem_singleton_iff,
      mem_Ioo, hcoords x |>.1, hcoords x |>.2]
    constructor
    · rintro ⟨⟨hxS, hxU⟩, hxc⟩
      have hb := (hmem (e x)).mp hxU.2
      exact ⟨hxU.1, ⟨⟨(hxφ hxU).mp hxS, sub_pos.mpr hxc, (abs_lt.mp hb.2.1).2⟩,
        by simpa using hb.2.2⟩⟩
    · rintro ⟨hxe, ⟨⟨hx0, hb⟩, hk⟩⟩
      have hxU : x ∈ U := ⟨hxe, (hmem _).mpr ⟨by simpa [hcoords, hx0] using hr,
        by rw [(hcoords x).2]; exact abs_lt.mpr ⟨(neg_neg_of_pos hr).trans hb.1, hb.2⟩,
        by simpa using hk⟩⟩
      exact ⟨⟨(hxφ hxU).mpr hx0, hxU⟩, sub_pos.mp hb.1⟩
  refine ⟨U, hU, hqU, ?_, ?_, ?_⟩
  · rw [hminus]
    exact chart_slice_connected e hr (isConnected_Ioo (neg_neg_of_pos hr)) hminusSub
  · rw [hplus]
    exact chart_slice_connected e hr (isConnected_Ioo hr) hplusSub
  · intro x hx hxc
    have hx0 : (e x).1.1 = 0 := by
      rw [(hcoords x).1]
      exact (hz ▸ (show x ∈ S ∩ W from ⟨hx.1, hUW hx.2⟩)).2
    have hx1 : (e x).1.2 = 0 := by rw [(hcoords x).2, hxc, sub_self]
    have hxk : (e x).2 ∈ Metric.ball (0 : D.ker) r := by
      simpa using ((hmem (e x)).mp hx.2.2).2.2
    rw [hminus, hplus]
    constructor
    · apply chart_slice_closure e _ hx.2.1 hx0 hx1 hxk
      rw [closure_Ioo (ne_of_lt (neg_neg_of_pos hr))]
      exact ⟨(neg_neg_of_pos hr).le, le_rfl⟩
    · apply chart_slice_closure e _ hx.2.1 hx0 hx1 hxk
      rw [closure_Ioo (ne_of_lt hr)]
      exact ⟨le_rfl, hr.le⟩

private lemma connected_inter_subset_component {A U : Set E₃} {q x : E₃}
    (hU : IsOpen U) (hqU : q ∈ U) (hconn : IsPreconnected (A ∩ U))
    (hq : q ∈ closure (connectedComponentIn A x)) :
    A ∩ U ⊆ connectedComponentIn A x := by
  obtain ⟨y, hyU, hy⟩ := mem_closure_iff.mp hq U hU hqU
  rw [connectedComponentIn_eq hy]
  exact hconn.subset_connectedComponentIn
    ⟨connectedComponentIn_subset A x hy, hyU⟩ inter_subset_left

private lemma component_eq_of_local_connected {A U : Set E₃} {q x x' : E₃}
    (hU : IsOpen U) (hqU : q ∈ U) (hconn : IsConnected (A ∩ U))
    (hq : q ∈ closure (connectedComponentIn A x))
    (hq' : q ∈ closure (connectedComponentIn A x')) :
    connectedComponentIn A x = connectedComponentIn A x' := by
  obtain ⟨y, hy⟩ := hconn.nonempty
  exact (connectedComponentIn_eq
    (connected_inter_subset_component hU hqU hconn.isPreconnected hq hy)).trans
      (connectedComponentIn_eq
        (connected_inter_subset_component hU hqU hconn.isPreconnected hq' hy)).symm

private lemma closure_component_constant {A C : Set E₃} (hC : IsPreconnected C)
    (hloc : ∀ q ∈ C, ∃ U : Set E₃, IsOpen U ∧ q ∈ U ∧
      IsPreconnected (A ∩ U) ∧ ∀ q' ∈ C ∩ U, q' ∈ closure (A ∩ U))
    {q₁ q₂ x : E₃} (hq₁ : q₁ ∈ C) (hq₂ : q₂ ∈ C)
    (hx : q₁ ∈ closure (connectedComponentIn A x)) :
    q₂ ∈ closure (connectedComponentIn A x) := by
  let T : Set C := (Subtype.val : C → E₃) ⁻¹' closure (connectedComponentIn A x)
  have hTclosed : IsClosed T := isClosed_closure.preimage continuous_subtype_val
  have hTopen : IsOpen T := by
    apply isOpen_iff_forall_mem_open.mpr
    intro q hq
    obtain ⟨U, hU, hqU, hconn, hcl⟩ := hloc q q.property
    refine ⟨Subtype.val ⁻¹' U, ?_, hU.preimage continuous_subtype_val, hqU⟩
    intro q' hq'
    exact closure_mono (connected_inter_subset_component hU hqU hconn hq)
      (hcl q' ⟨q'.property, hq'⟩)
  have : PreconnectedSpace C := isPreconnected_iff_preconnectedSpace.mp hC
  have hsub : (univ : Set C) ⊆ T :=
    isPreconnected_univ.subset_left_of_subset_union hTopen hTclosed.isOpen_compl
      disjoint_compl_right (by rw [union_compl_self]) ⟨⟨q₁, hq₁⟩, trivial, hx⟩
  exact hsub (mem_univ (⟨q₂, hq₂⟩ : C))

/-- `lem:level-adjacency`: adjacency to a fixed lower component is constant
on every preconnected subset of the regular level. -/
theorem closure_connectedComponentIn_levelBelow_constant {S : Set E₃}
    (hS : IsSmoothEmbeddedSurface S) {h : E₃ → ℝ} (hh : ContDiff ℝ 1 h)
    {c : ℝ} {C : Set E₃} (hC : IsPreconnected C)
    (hreg : ∀ q ∈ C, q ∈ S ∧ h q = c ∧ ¬ IsSurfaceCriticalPoint S h q)
    {q₁ q₂ x : E₃} (hq₁ : q₁ ∈ C) (hq₂ : q₂ ∈ C)
    (hx : q₁ ∈ closure (connectedComponentIn (S ∩ {y | h y < c}) x)) :
    q₂ ∈ closure (connectedComponentIn (S ∩ {y | h y < c}) x) := by
  apply closure_component_constant hC _ hq₁ hq₂ hx
  intro q hq
  obtain ⟨U, hU, hqU, hbelow, _, hcl⟩ :=
    exists_levelAdjacency_nhds hS hh (hreg q hq).1 (hreg q hq).2.1 (hreg q hq).2.2
  refine ⟨U, hU, hqU, ?_, ?_⟩
  · simpa only [inter_right_comm S] using hbelow.isPreconnected
  · intro q' hq'
    simpa only [inter_right_comm S] using
      (hcl q' ⟨(hreg q' hq'.1).1, hq'.2⟩ (hreg q' hq'.1).2.1).1

/-- `lem:level-adjacency`: adjacency to a fixed upper component is constant
on every preconnected subset of the regular level. -/
theorem closure_connectedComponentIn_levelAbove_constant {S : Set E₃}
    (hS : IsSmoothEmbeddedSurface S) {h : E₃ → ℝ} (hh : ContDiff ℝ 1 h)
    {c : ℝ} {C : Set E₃} (hC : IsPreconnected C)
    (hreg : ∀ q ∈ C, q ∈ S ∧ h q = c ∧ ¬ IsSurfaceCriticalPoint S h q)
    {q₁ q₂ x : E₃} (hq₁ : q₁ ∈ C) (hq₂ : q₂ ∈ C)
    (hx : q₁ ∈ closure (connectedComponentIn (S ∩ {y | c < h y}) x)) :
    q₂ ∈ closure (connectedComponentIn (S ∩ {y | c < h y}) x) := by
  apply closure_component_constant hC _ hq₁ hq₂ hx
  intro q hq
  obtain ⟨U, hU, hqU, _, habove, hcl⟩ :=
    exists_levelAdjacency_nhds hS hh (hreg q hq).1 (hreg q hq).2.1 (hreg q hq).2.2
  refine ⟨U, hU, hqU, ?_, ?_⟩
  · simpa only [inter_right_comm S] using habove.isPreconnected
  · intro q' hq'
    simpa only [inter_right_comm S] using
      (hcl q' ⟨(hreg q' hq'.1).1, hq'.2⟩ (hreg q' hq'.1).2.1).2

/-- `lem:level-adjacency`: a regular level point adjoins at most one lower component. -/
theorem connectedComponentIn_levelBelow_eq_of_mem_closure {S : Set E₃}
    (hS : IsSmoothEmbeddedSurface S) {h : E₃ → ℝ} (hh : ContDiff ℝ 1 h)
    {c : ℝ} {q x x' : E₃} (hq : q ∈ S) (hc : h q = c)
    (hn : ¬ IsSurfaceCriticalPoint S h q)
    (hx : q ∈ closure (connectedComponentIn (S ∩ {y | h y < c}) x))
    (hx' : q ∈ closure (connectedComponentIn (S ∩ {y | h y < c}) x')) :
    connectedComponentIn (S ∩ {y | h y < c}) x =
      connectedComponentIn (S ∩ {y | h y < c}) x' := by
  obtain ⟨U, hU, hqU, hbelow, _, _⟩ := exists_levelAdjacency_nhds hS hh hq hc hn
  exact component_eq_of_local_connected hU hqU
    (by simpa only [inter_right_comm S] using hbelow) hx hx'

/-- `lem:level-adjacency`: a regular level point adjoins at most one upper component. -/
theorem connectedComponentIn_levelAbove_eq_of_mem_closure {S : Set E₃}
    (hS : IsSmoothEmbeddedSurface S) {h : E₃ → ℝ} (hh : ContDiff ℝ 1 h)
    {c : ℝ} {q x x' : E₃} (hq : q ∈ S) (hc : h q = c)
    (hn : ¬ IsSurfaceCriticalPoint S h q)
    (hx : q ∈ closure (connectedComponentIn (S ∩ {y | c < h y}) x))
    (hx' : q ∈ closure (connectedComponentIn (S ∩ {y | c < h y}) x')) :
    connectedComponentIn (S ∩ {y | c < h y}) x =
      connectedComponentIn (S ∩ {y | c < h y}) x' := by
  obtain ⟨U, hU, hqU, _, habove, _⟩ := exists_levelAdjacency_nhds hS hh hq hc hn
  exact component_eq_of_local_connected hU hqU
    (by simpa only [inter_right_comm S] using habove) hx hx'

/-- `lem:level-adjacency`: every regular level point adjoins a lower component. -/
theorem exists_mem_closure_connectedComponentIn_levelBelow {S : Set E₃}
    (hS : IsSmoothEmbeddedSurface S) {h : E₃ → ℝ} (hh : ContDiff ℝ 1 h)
    {c : ℝ} {q : E₃} (hq : q ∈ S) (hc : h q = c)
    (hn : ¬ IsSurfaceCriticalPoint S h q) :
    ∃ x ∈ S ∩ {y | h y < c},
      q ∈ closure (connectedComponentIn (S ∩ {y | h y < c}) x) := by
  obtain ⟨U, _, hqU, hbelow, _, hcl⟩ := exists_levelAdjacency_nhds hS hh hq hc hn
  obtain ⟨x, hx⟩ := hbelow.nonempty
  have hsub : S ∩ U ∩ {y | h y < c} ⊆ S ∩ {y | h y < c} :=
    fun _ hy => ⟨hy.1.1, hy.2⟩
  exact ⟨x, hsub hx, closure_mono
    (hbelow.isPreconnected.subset_connectedComponentIn hx hsub) (hcl q ⟨hq, hqU⟩ hc).1⟩

/-- `lem:level-adjacency`: every regular level point adjoins an upper component. -/
theorem exists_mem_closure_connectedComponentIn_levelAbove {S : Set E₃}
    (hS : IsSmoothEmbeddedSurface S) {h : E₃ → ℝ} (hh : ContDiff ℝ 1 h)
    {c : ℝ} {q : E₃} (hq : q ∈ S) (hc : h q = c)
    (hn : ¬ IsSurfaceCriticalPoint S h q) :
    ∃ x ∈ S ∩ {y | c < h y},
      q ∈ closure (connectedComponentIn (S ∩ {y | c < h y}) x) := by
  obtain ⟨U, _, hqU, _, habove, hcl⟩ := exists_levelAdjacency_nhds hS hh hq hc hn
  obtain ⟨x, hx⟩ := habove.nonempty
  have hsub : S ∩ U ∩ {y | c < h y} ⊆ S ∩ {y | c < h y} :=
    fun _ hy => ⟨hy.1.1, hy.2⟩
  exact ⟨x, hsub hx, closure_mono
    (habove.isPreconnected.subset_connectedComponentIn hx hsub) (hcl q ⟨hq, hqU⟩ hc).2⟩

end LiquidDrop

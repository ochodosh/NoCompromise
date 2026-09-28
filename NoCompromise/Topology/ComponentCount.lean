import NoCompromise.Topology.ParitySides

/-!
# Component count for a disjoint union of surfaces (`thm:component-count`, abstract form)

A crossing parity for every compact connected smooth surface gives: a compact connected
surface inside an open connected set splits it into exactly two open connected pieces, and
by induction on the number of components the complement of a compact smooth surface with
`k` components has `k + 1` components.
-/

namespace LiquidDrop
noncomputable section
open Set Filter
open scoped Topology Gradient

private lemma relative_line_deriv {φ : E₃ → ℝ} (hφ : ContDiff ℝ (⊤ : ℕ∞) φ)
    (y v : E₃) (t : ℝ) :
    HasDerivAt (fun s : ℝ => φ (y + s • v)) (fderiv ℝ φ (y + t • v) v) t := by
  exact (hφ.differentiable (by simp) _).hasFDerivAt.comp_hasDerivAt t
    (by simpa using (((hasDerivAt_id t).smul_const v).const_add y))

private lemma relative_signs_near {φ : E₃ → ℝ} (_hφ : ContDiff ℝ (⊤ : ℕ∞) φ)
    {p : E₃} (hz : φ p = 0) (hr : gradient φ p ≠ 0)
    {V : Set E₃} (hV : IsOpen V) (hpV : p ∈ V) :
    (∃ x ∈ V, 0 < φ x) ∧ (∃ x ∈ V, φ x < 0) := by
  have hv : 0 < fderiv ℝ φ p (gradient φ p) := by
    rw [← inner_gradient_left, real_inner_self_eq_norm_sq]
    exact sq_pos_of_pos (norm_pos_iff.mpr hr)
  constructor
  · by_contra h
    push Not at h
    have hm : IsLocalMax φ p := by
      filter_upwards [hV.mem_nhds hpV] with x hx
      simpa [hz] using h x hx
    rw [hm.fderiv_eq_zero] at hv
    simp at hv
  · by_contra h
    push Not at h
    have hm : IsLocalMin φ p := by
      filter_upwards [hV.mem_nhds hpV] with x hx
      simpa [hz] using h x hx
    rw [hm.fderiv_eq_zero] at hv
    simp at hv

private lemma relative_absorb {F K : Set E₃} {a x : E₃}
    (hK : IsPreconnected K) (hKS : K ⊆ F) (hxK : x ∈ K)
    (hx : x ∈ connectedComponentIn F a) : K ⊆ connectedComponentIn F a := by
  rw [connectedComponentIn_eq hx]
  exact hK.subset_connectedComponentIn hxK hKS

private lemma relative_closure_component {F : Set E₃} (hO : IsOpen F) {a p : E₃}
    (hp : p ∈ closure (connectedComponentIn F a)) (hpS : p ∈ F) :
    p ∈ connectedComponentIn F a := by
  obtain ⟨y, hyp, hya⟩ := mem_closure_iff.mp hp _ hO.connectedComponentIn
    (mem_connectedComponentIn hpS)
  rw [connectedComponentIn_eq hya, ← connectedComponentIn_eq hyp]
  exact mem_connectedComponentIn hpS

private lemma relative_local_sides {S V U : Set E₃} {φ : E₃ → ℝ}
    (hV : IsOpen V) (hU : IsOpen U) (hφ : ContDiff ℝ (⊤ : ℕ∞) φ)
    (hzero : S ∩ U = {x ∈ U | φ x = 0})
    {p : E₃} (hpV : p ∈ V) (hpU : p ∈ U) (hz : φ p = 0)
    (hr : gradient φ p ≠ 0) :
    ∃ r > 0, Metric.ball p r ⊆ U ∩ V ∧ ∃ Kpos Kneg : Set E₃,
      IsPreconnected Kpos ∧ IsPreconnected Kneg ∧
      Kpos ⊆ V \ S ∧ Kneg ⊆ V \ S ∧
      Metric.ball p r ∩ {x | 0 < φ x} ⊆ Kpos ∧
      Metric.ball p r ∩ {x | φ x < 0} ⊆ Kneg := by
  have he : (S ∪ Vᶜ) ∩ (U ∩ V) = {x ∈ U ∩ V | φ x = 0} := by
    ext x
    have hx := congrArg (fun A : Set E₃ => x ∈ A) hzero
    simp only [mem_inter_iff, mem_ofPred_eq] at hx
    simp only [mem_inter_iff, mem_union, mem_compl_iff, mem_ofPred_eq]
    tauto
  have hcomp : (S ∪ Vᶜ)ᶜ = V \ S := by ext x; simp; tauto
  simpa only [hcomp] using exists_local_sides (hU.inter hV) hφ he ⟨hpU, hpV⟩ hz hr

private lemma relative_component_touches {S V : Set E₃}
    (hO : IsOpen (V \ S)) (hV : IsConnected V) (hne : S.Nonempty) (hSV : S ⊆ V)
    {a : E₃} (ha : a ∈ V \ S) :
    (closure (connectedComponentIn (V \ S) a) ∩ S).Nonempty := by
  by_contra h
  have hsub : V ⊆ connectedComponentIn (V \ S) a := by
    apply hV.isPreconnected.subset_of_closure_inter_subset hO.connectedComponentIn
      ⟨a, ha.1, mem_connectedComponentIn ha⟩
    rintro p ⟨hp, hpV⟩
    exact relative_closure_component hO hp ⟨hpV, fun hpS => h ⟨p, hp, hpS⟩⟩
  obtain ⟨p, hp⟩ := hne
  exact (connectedComponentIn_subset (V \ S) a (hsub (hSV hp))).2 hp

private lemma relative_cover_all {S V : Set E₃} (hS : IsSmoothEmbeddedSurface S)
    (hV : IsOpen V) (hVc : IsConnected V) (hSV : S ⊆ V)
    (hO : IsOpen (V \ S)) (hconn : IsConnected S) :
    ∃ a ∈ (V \ S), ∃ b ∈ (V \ S),
      (V \ S) ⊆ connectedComponentIn (V \ S) a ∪ connectedComponentIn (V \ S) b := by
  obtain ⟨p₀, hp₀⟩ := hconn.nonempty
  obtain ⟨U₀, φ₀, hU₀, hp₀U, hφ₀, hz₀, hr₀⟩ := hS p₀ hp₀
  have hzp₀ : φ₀ p₀ = 0 := (hz₀ ▸ (show p₀ ∈ S ∩ U₀ from ⟨hp₀, hp₀U⟩)).2
  obtain ⟨r₀, hr₀pos, hb₀, Kpos, Kneg, hcpos, hcneg, hspos, hsneg, hkpos, hkneg⟩ :=
    relative_local_sides hV hU₀ hφ₀ hz₀ (hSV hp₀) hp₀U hzp₀ (hr₀ p₀ ⟨hp₀, hp₀U⟩)
  obtain ⟨⟨a, ha, hapos⟩, ⟨b, hb, hbneg⟩⟩ := relative_signs_near hφ₀ hzp₀
    (hr₀ p₀ ⟨hp₀, hp₀U⟩) Metric.isOpen_ball (Metric.mem_ball_self hr₀pos)
  have haK := hkpos ⟨ha, hapos⟩
  have hbK := hkneg ⟨hb, hbneg⟩
  have haS := hspos haK
  have hbS := hsneg hbK
  let A := connectedComponentIn (V \ S) a
  let B := connectedComponentIn (V \ S) b
  let G : Set E₃ := {p | ∃ r > 0, Metric.ball p r \ S ⊆ A ∪ B}
  have hg₀ : p₀ ∈ G := by
    refine ⟨r₀, hr₀pos, ?_⟩
    rintro x ⟨hx, hxS⟩
    have hxne : φ₀ x ≠ 0 := by
      intro h
      exact hxS (show x ∈ S ∩ U₀ from hz₀.symm ▸ ⟨(hb₀ hx).1, h⟩).1
    rcases lt_or_gt_of_ne hxne with hn | hp
    · exact Or.inr (hcneg.subset_connectedComponentIn hbK hsneg (hkneg ⟨hx, hn⟩))
    · exact Or.inl (hcpos.subset_connectedComponentIn haK hspos (hkpos ⟨hx, hp⟩))
  have hG : IsOpen G := by
    apply Metric.isOpen_iff.mpr
    rintro p ⟨r, hr, hcov⟩
    refine ⟨r / 2, half_pos hr, ?_⟩
    intro q hq
    refine ⟨r / 2, half_pos hr, ?_⟩
    rintro x ⟨hx, hxS⟩
    apply hcov ⟨?_, hxS⟩
    calc
      dist x p ≤ dist x q + dist q p := dist_triangle _ _ _
      _ < r := by have := Metric.mem_ball.mp hx; have := Metric.mem_ball.mp hq; linarith
  let W : Set S := Subtype.val ⁻¹' G
  have hWclosed : IsClosed W := by
    apply isClosed_of_closure_subset
    intro p hp
    obtain ⟨U, φ, hU, hpU, hφ, hz, hr⟩ := hS p p.property
    have hzp : φ p = 0 := (hz ▸ (show (p : E₃) ∈ S ∩ U from ⟨p.property, hpU⟩)).2
    obtain ⟨r, hrpos, hball, Kp, Kn, hKp, hKn, hKpS, hKnS, hkp, hkn⟩ :=
      relative_local_sides hV hU hφ hz (hSV p.property) hpU hzp (hr p ⟨p.property, hpU⟩)
    obtain ⟨q, hqr, hqG⟩ := mem_closure_iff.mp hp
      (Subtype.val ⁻¹' Metric.ball (p : E₃) r)
      (Metric.isOpen_ball.preimage continuous_subtype_val) (Metric.mem_ball_self hrpos)
    obtain ⟨ρ, hρ, hρcov⟩ := hqG
    have hqU := (hball hqr).1
    have hzq : φ q = 0 := (hz ▸ (show (q : E₃) ∈ S ∩ U from ⟨q.property, hqU⟩)).2
    obtain ⟨⟨x, hx, hxpos⟩, ⟨y, hy, hyneg⟩⟩ := relative_signs_near hφ hzq
      (hr q ⟨q.property, hqU⟩) (Metric.isOpen_ball.inter Metric.isOpen_ball)
      ⟨Metric.mem_ball_self hρ, hqr⟩
    have hxK := hkp ⟨hx.2, hxpos⟩
    have hyK := hkn ⟨hy.2, hyneg⟩
    have hKpcov : Kp ⊆ A ∪ B := by
      rcases hρcov ⟨hx.1, (hKpS hxK).2⟩ with hxa | hxb
      · exact (relative_absorb hKp hKpS hxK hxa).trans subset_union_left
      · exact (relative_absorb hKp hKpS hxK hxb).trans subset_union_right
    have hKncov : Kn ⊆ A ∪ B := by
      rcases hρcov ⟨hy.1, (hKnS hyK).2⟩ with hya | hyb
      · exact (relative_absorb hKn hKnS hyK hya).trans subset_union_left
      · exact (relative_absorb hKn hKnS hyK hyb).trans subset_union_right
    refine ⟨r, hrpos, ?_⟩
    rintro z ⟨hzball, hzS⟩
    have hzne : φ z ≠ 0 := by
      intro h
      exact hzS (show z ∈ S ∩ U from hz.symm ▸ ⟨(hball hzball).1, h⟩).1
    rcases lt_or_gt_of_ne hzne with hn | hp
    · exact hKncov (hkn ⟨hzball, hn⟩)
    · exact hKpcov (hkp ⟨hzball, hp⟩)
  let : ConnectedSpace S := isConnected_iff_connectedSpace.mp hconn
  have hWall : W = univ :=
    (show IsClopen W from ⟨hWclosed, hG.preimage continuous_subtype_val⟩).eq_univ
      ⟨⟨p₀, hp₀⟩, hg₀⟩
  have hSG : S ⊆ G := fun p hp => show (⟨p, hp⟩ : S) ∈ W from hWall.symm ▸ mem_univ _
  refine ⟨a, haS, b, hbS, ?_⟩
  intro z hz
  obtain ⟨p, hpcl, hpS⟩ := relative_component_touches hO hVc hconn.nonempty hSV hz
  obtain ⟨r, hr, hcov⟩ := hSG hpS
  obtain ⟨w, hwr, hwC⟩ := mem_closure_iff.mp hpcl _ Metric.isOpen_ball (Metric.mem_ball_self hr)
  have hwO := connectedComponentIn_subset (V \ S) z hwC
  rcases hcov ⟨hwr, hwO.2⟩ with hwa | hwb
  · exact Or.inl (relative_absorb isPreconnected_connectedComponentIn
      (connectedComponentIn_subset _ _) hwC hwa (mem_connectedComponentIn hz))
  · exact Or.inr (relative_absorb isPreconnected_connectedComponentIn
      (connectedComponentIn_subset _ _) hwC hwb (mem_connectedComponentIn hz))

private lemma relative_crossing_pair {S V : Set E₃}
    (hS : IsSmoothEmbeddedSurface S) (hne : S.Nonempty)
    (hV : IsOpen V) (hSV : S ⊆ V) (I : E₃ → Prop)
    (hcross : ∀ p ∈ S, ∀ ν ∉ tangentPlane S p, ∃ t₀ > 0, ∀ t ∈ Ioo (0 : ℝ) t₀,
      ¬ (I (p - t • ν) ↔ I (p + t • ν))) :
    ∃ x ∈ V \ S, ∃ y ∈ V \ S, ¬ (I x ↔ I y) := by
  obtain ⟨p, hp⟩ := hne
  obtain ⟨U, φ, hU, hpU, hφ, hz, hr⟩ := hS p hp
  have hreg := hr p ⟨hp, hpU⟩
  have hv : 0 < fderiv ℝ φ p (gradient φ p) := by
    rw [← inner_gradient_left, real_inner_self_eq_norm_sq]
    exact sq_pos_of_pos (norm_pos_iff.mpr hreg)
  have hν : gradient φ p ∉ tangentPlane S p := by
    rw [tangentPlane_eq hU hpU (hφ.contDiffAt.of_le (by simp)) hz hp hreg,
      Submodule.mem_orthogonal_singleton_iff_inner_right, inner_gradient_left]
    exact ne_of_gt hv
  obtain ⟨t₀, ht₀, hcross₀⟩ := hcross p hp (gradient φ p) hν
  have hd : HasDerivAt (fun t : ℝ => φ (p + t • gradient φ p))
      (fderiv ℝ φ p (gradient φ p)) 0 := by
    simpa using relative_line_deriv hφ p (gradient φ p) 0
  have hneq : ∀ᶠ t in 𝓝[≠] (0 : ℝ), φ (p + t • gradient φ p) ≠ 0 :=
    hd.eventually_ne hv.ne'
  have hin : ∀ᶠ t in 𝓝 (0 : ℝ), p + t • gradient φ p ∈ U ∩ V :=
    (continuous_const.add (continuous_id.smul continuous_const)).continuousAt.preimage_mem_nhds
      (by simpa using (hU.inter hV).mem_nhds ⟨hpU, hSV hp⟩)
  have hboth : ∀ᶠ t in 𝓝[≠] (0 : ℝ), p + t • gradient φ p ∈ V \ S := by
    filter_upwards [hneq, nhdsWithin_le_nhds hin] with t ht htU
    refine ⟨htU.2, ?_⟩
    intro htS
    exact ht (hz ▸ (show p + t • gradient φ p ∈ S ∩ U from ⟨htS, htU.1⟩)).2
  rw [eventually_nhdsWithin_iff, Metric.eventually_nhds_iff] at hboth
  obtain ⟨δ, hδ, hsmall⟩ := hboth
  let t := min δ t₀ / 2
  have ht : 0 < t := half_pos (lt_min hδ ht₀)
  have htδ : t < δ := (half_lt_self (lt_min hδ ht₀)).trans_le (min_le_left _ _)
  have htt₀ : t < t₀ := (half_lt_self (lt_min hδ ht₀)).trans_le (min_le_right _ _)
  have hplus : p + t • gradient φ p ∈ V \ S :=
    hsmall (by simpa [Real.dist_eq, abs_of_pos ht] using htδ) ht.ne'
  have hminus : p - t • gradient φ p ∈ V \ S := by
    have := hsmall (y := -t)
      (by simpa [Real.dist_eq, abs_of_pos ht] using htδ) (neg_ne_zero.mpr ht.ne')
    simpa only [neg_smul, ← sub_eq_add_neg] using this
  exact ⟨_, hminus, _, hplus, hcross₀ t ⟨ht, htt₀⟩⟩


/-- `thm:component-count`: a compact connected smooth surface contained in an
open connected set splits that set into two open connected sides, assuming a
locally constant parity with a change across every transverse crossing. -/
theorem exists_two_components_diff {V T : Set E₃} (hV : IsOpen V) (hVc : IsConnected V)
    (hT : IsSmoothEmbeddedSurface T) (hTc : IsCompact T) (hTconn : IsConnected T) (hTV : T ⊆ V)
    (I : E₃ → Prop)
    (hloc : ∀ x ∉ T, ∀ᶠ y in 𝓝 x, (I y ↔ I x))
    (hcross : ∀ p ∈ T, ∀ ν ∉ tangentPlane T p, ∃ t₀ > 0, ∀ t ∈ Ioo (0 : ℝ) t₀,
      ¬ (I (p - t • ν) ↔ I (p + t • ν))) :
    ∃ A B : Set E₃, IsOpen A ∧ IsOpen B ∧ IsConnected A ∧ IsConnected B ∧ Disjoint A B ∧
      A ∪ B = V \ T := by
  have hO : IsOpen (V \ T) := hV.sdiff hTc.isClosed
  obtain ⟨a, ha, b, hb, hcover⟩ := relative_cover_all hT hV hVc hTV hO hTconn
  have hmem {x y : ((V \ T) : Set E₃)}
      (h : (x : E₃) ∈ connectedComponentIn (V \ T) (y : E₃)) :
      x ∈ connectedComponent y := by
    rw [connectedComponentIn_eq_image y.property] at h
    obtain ⟨z, hz, hzx⟩ := h
    have heq : z = x := Subtype.ext hzx
    simpa [heq] using hz
  let a' : ((V \ T) : Set E₃) := ⟨a, ha⟩
  let b' : ((V \ T) : Set E₃) := ⟨b, hb⟩
  have hcover' (z : ((V \ T) : Set E₃)) :
      ConnectedComponents.mk z = ConnectedComponents.mk a' ∨
      ConnectedComponents.mk z = ConnectedComponents.mk b' := by
    rcases hcover z.property with hza | hzb
    · exact Or.inl (ConnectedComponents.coe_eq_coe'.mpr (hmem hza))
    · exact Or.inr (ConnectedComponents.coe_eq_coe'.mpr (hmem hzb))
  have hI : IsLocallyConstant (fun x : ((V \ T) : Set E₃) => I x) := by
    apply (IsLocallyConstant.iff_eventually_eq _).mpr
    intro x
    filter_upwards [continuous_subtype_val.continuousAt (hloc x x.property.2)] with y hy
    exact propext hy
  have hIeq {x y : ((V \ T) : Set E₃)}
      (h : ConnectedComponents.mk x = ConnectedComponents.mk y) : I x ↔ I y :=
    iff_of_eq (hI.apply_eq_of_isPreconnected isPreconnected_connectedComponent
      (ConnectedComponents.coe_eq_coe'.mp h) mem_connectedComponent)
  have hne : ConnectedComponents.mk a' ≠ ConnectedComponents.mk b' := by
    intro hab
    have hall (z : ((V \ T) : Set E₃)) : ConnectedComponents.mk z = ConnectedComponents.mk a' :=
      (hcover' z).elim id (fun h => h.trans hab.symm)
    obtain ⟨x, hx, y, hy, hxy⟩ := relative_crossing_pair hT hTconn.nonempty hV hTV I hcross
    exact hxy (hIeq ((hall ⟨x, hx⟩).trans (hall ⟨y, hy⟩).symm))
  refine ⟨connectedComponentIn (V \ T) a, connectedComponentIn (V \ T) b,
    hO.connectedComponentIn, hO.connectedComponentIn,
    isConnected_connectedComponentIn_iff.mpr ha,
    isConnected_connectedComponentIn_iff.mpr hb, ?_, ?_⟩
  · apply Set.disjoint_left.mpr
    intro x hxa hxb
    have hx : x ∈ V \ T := connectedComponentIn_subset _ _ hxa
    exact hne ((ConnectedComponents.coe_eq_coe'.mpr (hmem (x := ⟨x, hx⟩) hxa)).symm.trans
      (ConnectedComponents.coe_eq_coe'.mpr (hmem (x := ⟨x, hx⟩) hxb)))
  · exact Subset.antisymm (union_subset (connectedComponentIn_subset _ _)
      (connectedComponentIn_subset _ _)) hcover

private def components_homeomorph {X Y : Type*} [TopologicalSpace X] [TopologicalSpace Y]
    (h : X ≃ₜ Y) : ConnectedComponents X ≃ ConnectedComponents Y :=
  Quotient.congr h.toEquiv fun x y => by
    change connectedComponent x = connectedComponent y ↔
      connectedComponent (h x) = connectedComponent (h y)
    rw [connectedComponent_eq_iff_mem, connectedComponent_eq_iff_mem]
    constructor
    · intro hxy
      exact h.continuous.mapsTo_connectedComponent y hxy
    · intro hxy
      simpa using h.symm.continuous.mapsTo_connectedComponent (h y) hxy

private def nested_subtype_homeomorph {X : Type*} [TopologicalSpace X]
    {S A : Set X} (hAS : A ⊆ S) : (Subtype.val ⁻¹' A : Set S) ≃ₜ A where
  toFun x := ⟨x.1.1, x.2⟩
  invFun x := ⟨⟨x.1, hAS x.2⟩, x.2⟩
  left_inv _ := rfl
  right_inv _ := rfl
  continuous_toFun := (continuous_subtype_val.comp continuous_subtype_val).subtype_mk _
  continuous_invFun := (continuous_subtype_val.subtype_mk _).subtype_mk _

private def components_partition {X : Type*} [TopologicalSpace X]
    {S A B : Set X} (hAS : A ⊆ S) (hBS : B ⊆ S)
    (hA : IsClopen (Subtype.val ⁻¹' A : Set S))
    (hB : IsClopen (Subtype.val ⁻¹' B : Set S))
    (hd : Disjoint A B) (hu : A ∪ B = S) :
    ConnectedComponents S ≃ ConnectedComponents A ⊕ ConnectedComponents B := by
  let U : Bool → Set S := fun b => bif b then Subtype.val ⁻¹' B else Subtype.val ⁻¹' A
  have hop (b) : IsClopen (U b) := by cases b <;> assumption
  have hdis : Pairwise (Function.onFun Disjoint U) := by
    intro i j hij
    cases i <;> cases j <;> try contradiction
    · exact hd.preimage Subtype.val
    · exact hd.symm.preimage Subtype.val
  have hcov : ⋃ b, U b = univ := by
    ext x
    simp only [mem_iUnion, mem_univ, iff_true]
    have hx : (x : X) ∈ A ∪ B := hu.symm ▸ x.property
    rcases hx with hx | hx
    · exact ⟨false, hx⟩
    · exact ⟨true, hx⟩
  let ea := components_homeomorph (nested_subtype_homeomorph hAS)
  let eb := components_homeomorph (nested_subtype_homeomorph hBS)
  let e : (Σ b, ConnectedComponents (U b)) ≃
      ConnectedComponents A ⊕ ConnectedComponents B :=
    { toFun := fun ⟨b, c⟩ => match b, c with
        | false, c => Sum.inl (ea c)
        | true, c => Sum.inr (eb c)
      invFun := fun c => match c with
        | Sum.inl c => ⟨false, ea.symm c⟩
        | Sum.inr c => ⟨true, eb.symm c⟩
      left_inv := by rintro ⟨b, c⟩; cases b <;> simp
      right_inv := by intro c; cases c <;> simp }
  exact (ConnectedComponents.equivOfIsClopen hop hdis hcov).trans e

private lemma finite_components_clopen {X : Type*} [TopologicalSpace X]
    [Finite (ConnectedComponents X)] (x : X) : IsClopen (connectedComponent x) := by
  have hc (c : ConnectedComponents X) : IsClosed (ConnectedComponents.mk ⁻¹' {c}) := by
    obtain ⟨y, rfl⟩ := ConnectedComponents.surjective_coe c
    rw [connectedComponents_preimage_singleton]
    exact isClosed_connectedComponent
  have he : (connectedComponent x)ᶜ =
      ⋃ c : {c : ConnectedComponents X // c ≠ ConnectedComponents.mk x},
        ConnectedComponents.mk ⁻¹' {c.val} := by
    ext y
    simp only [mem_compl_iff, mem_iUnion, mem_preimage, mem_singleton_iff]
    constructor
    · intro hy
      exact ⟨⟨ConnectedComponents.mk y, mt ConnectedComponents.coe_eq_coe'.mp hy⟩, rfl⟩
    · rintro ⟨c, hc⟩ hy
      exact c.property (hc.symm.trans (ConnectedComponents.coe_eq_coe'.mpr hy))
  exact ⟨isClosed_connectedComponent, isClosed_compl_iff.mp
    (he ▸ isClosed_iUnion_of_finite fun c => hc c.val)⟩

private lemma partition_preimage_compl {X : Type*} [TopologicalSpace X]
    {S A B : Set X} (hd : Disjoint A B) (hu : A ∪ B = S) :
    (Subtype.val ⁻¹' A : Set S)ᶜ = Subtype.val ⁻¹' B := by
  ext x
  have hx : (x : X) ∈ A ∪ B := hu.symm ▸ x.property
  have hn := Set.disjoint_left.mp hd
  simp only [mem_compl_iff, mem_preimage]
  constructor
  · intro h; exact hx.resolve_left h
  · intro hB hA; exact hn hA hB

private def components_partition_open {X : Type*} [TopologicalSpace X]
    {S A B : Set X} (hA : IsOpen A) (hB : IsOpen B)
    (hd : Disjoint A B) (hu : A ∪ B = S) :
    ConnectedComponents S ≃ ConnectedComponents A ⊕ ConnectedComponents B := by
  have he := partition_preimage_compl hd hu
  have he' := partition_preimage_compl hd.symm ((union_comm B A).trans hu)
  apply components_partition (hu ▸ subset_union_left) (hu ▸ subset_union_right)
  · exact ⟨isOpen_compl_iff.mp (he ▸ hB.preimage continuous_subtype_val),
      hA.preimage continuous_subtype_val⟩
  · exact ⟨isOpen_compl_iff.mp (he' ▸ hA.preimage continuous_subtype_val),
      hB.preimage continuous_subtype_val⟩
  · exact hd
  · exact hu

private lemma smooth_subset_rel_open {S T : Set E₃} (hS : IsSmoothEmbeddedSurface S)
    (hTS : T ⊆ S) (hT : IsOpen (Subtype.val ⁻¹' T : Set S)) :
    IsSmoothEmbeddedSurface T := by
  obtain ⟨W, hW, he⟩ := Topology.IsInducing.subtypeVal.isOpen_iff.mp hT
  have hmem (x : E₃) (hx : x ∈ S) : x ∈ W ↔ x ∈ T := by
    exact Iff.of_eq (congrArg (fun A : Set S => (⟨x, hx⟩ : S) ∈ A) he)
  intro p hp
  obtain ⟨U, φ, hU, hpU, hφ, hz, hr⟩ := hS p (hTS hp)
  refine ⟨U ∩ W, φ, hU.inter hW, ⟨hpU, (hmem p (hTS hp)).mpr hp⟩,
    hφ, ?_, ?_⟩
  · ext x
    constructor
    · rintro ⟨hxT, hxU, hxW⟩
      exact ⟨⟨hxU, hxW⟩, (hz ▸ (show x ∈ S ∩ U from ⟨hTS hxT, hxU⟩)).2⟩
    · rintro ⟨⟨hxU, hxW⟩, hxz⟩
      have hxS : x ∈ S := (show x ∈ S ∩ U from hz.symm ▸ ⟨hxU, hxz⟩).1
      exact ⟨(hmem x hxS).mp hxW, hxU, hxW⟩
  · rintro x ⟨hxT, hxU, _⟩
    exact hr x ⟨hTS hxT, hxU⟩

private lemma card_components_connected {X : Type*} [TopologicalSpace X]
    {S : Set X} (hS : IsConnected S) : Nat.card (ConnectedComponents S) = 1 := by
  let : ConnectedSpace S := isConnected_iff_connectedSpace.mp hS
  exact Nat.card_eq_one_iff_unique.mpr ⟨inferInstance, inferInstance⟩

private lemma complement_split_count {T O : Set E₃} (hO : IsOpen O)
    (hT : IsSmoothEmbeddedSurface T) (hTc : IsCompact T) (hTconn : IsConnected T)
    (hTO : T ⊆ O) [Finite (ConnectedComponents O)]
    (I : E₃ → Prop)
    (hloc : ∀ x ∉ T, ∀ᶠ y in 𝓝 x, (I y ↔ I x))
    (hcross : ∀ p ∈ T, ∀ ν ∉ tangentPlane T p, ∃ t₀ > 0, ∀ t ∈ Ioo (0 : ℝ) t₀,
      ¬ (I (p - t • ν) ↔ I (p + t • ν))) :
    Nat.card (ConnectedComponents (O \ T : Set E₃)) = Nat.card (ConnectedComponents O) + 1 := by
  obtain ⟨t, ht⟩ := hTconn.nonempty
  let V := connectedComponentIn O t
  have htO := hTO ht
  have hV : IsOpen V := hO.connectedComponentIn
  have hVc : IsConnected V := isConnected_connectedComponentIn_iff.mpr htO
  have hTV : T ⊆ V := hTconn.isPreconnected.subset_connectedComponentIn ht hTO
  let W := O \ V
  have hW : IsOpen W := by
    have he : W = O ∩ (closure V)ᶜ := by
      ext x
      constructor
      · rintro ⟨hxO, hxV⟩
        exact ⟨hxO, fun hxc => hxV (relative_closure_component hO hxc hxO)⟩
      · rintro ⟨hxO, hxc⟩
        exact ⟨hxO, fun hxV => hxc (subset_closure hxV)⟩
    rw [he]
    exact hO.inter isClosed_closure.isOpen_compl
  have hVW : Disjoint V W := Set.disjoint_left.mpr fun _ hx hy => hy.2 hx
  have hVO : V ⊆ O := connectedComponentIn_subset _ _
  have hcovO : V ∪ W = O := by
    ext x
    change (x ∈ V ∨ x ∈ O ∧ x ∉ V) ↔ x ∈ O
    have := @hVO x
    tauto
  let eO := components_partition_open hV hW hVW hcovO
  let : Finite (ConnectedComponents V ⊕ ConnectedComponents W) :=
    Finite.of_equiv _ eO
  let : Finite (ConnectedComponents V) := Finite.of_injective
    (Sum.inl : ConnectedComponents V → ConnectedComponents V ⊕ ConnectedComponents W)
    Sum.inl_injective
  let : Finite (ConnectedComponents W) := Finite.of_injective
    (Sum.inr : ConnectedComponents W → ConnectedComponents V ⊕ ConnectedComponents W)
    Sum.inr_injective
  have hcardO : Nat.card (ConnectedComponents O) = 1 + Nat.card (ConnectedComponents W) := by
    rw [Nat.card_congr eO, Nat.card_sum, card_components_connected hVc]
  obtain ⟨A, B, hA, hB, hAc, hBc, hd, hcov⟩ :=
    exists_two_components_diff hV hVc hT hTc hTconn hTV I hloc hcross
  have hAB : Nat.card (ConnectedComponents (V \ T : Set E₃)) = 2 := by
    let : Finite (ConnectedComponents A) := Nat.finite_of_card_ne_zero
      (by rw [card_components_connected hAc]; decide)
    let : Finite (ConnectedComponents B) := Nat.finite_of_card_ne_zero
      (by rw [card_components_connected hBc]; decide)
    rw [Nat.card_congr (components_partition_open hA hB hd hcov), Nat.card_sum,
      card_components_connected hAc, card_components_connected hBc]
  let : Finite (ConnectedComponents (V \ T : Set E₃)) := Nat.finite_of_card_ne_zero (by omega)
  have hd' : Disjoint (V \ T) W := hVW.mono_left sdiff_subset
  have hu' : (V \ T) ∪ W = O \ T := by
    ext x
    have hx := @hTV x
    have hv := @hVO x
    simp only [mem_union, Set.mem_sdiff, W]
    tauto
  rw [Nat.card_congr (components_partition_open (hV.sdiff hTc.isClosed) hW hd' hu'),
    Nat.card_sum, hAB, hcardO]
  omega

/-- `thm:component-count`: the complement of a compact smooth embedded surface
has one more connected component than the surface, assuming crossing parity for
every compact connected smooth embedded surface. -/
theorem card_connectedComponents_compl_eq_card_add_one_of_parity
    (hpar : ∀ T : Set E₃, IsSmoothEmbeddedSurface T → IsCompact T → IsConnected T →
      ∃ I : E₃ → Prop, (∀ x ∉ T, ∀ᶠ y in 𝓝 x, (I y ↔ I x)) ∧
        ∀ p ∈ T, ∀ ν ∉ tangentPlane T p, ∃ t₀ > 0, ∀ t ∈ Ioo (0 : ℝ) t₀,
          ¬ (I (p - t • ν) ↔ I (p + t • ν)))
    {S : Set E₃} (hc : IsCompact S) (hS : IsSmoothEmbeddedSurface S)
    (hfin : Finite (ConnectedComponents S)) :
    Nat.card (ConnectedComponents (Sᶜ : Set E₃)) = Nat.card (ConnectedComponents S) + 1 := by
  classical
  suffices h : ∀ n : ℕ, ∀ S : Set E₃, Nat.card (ConnectedComponents S) = n →
      IsCompact S → IsSmoothEmbeddedSurface S → Finite (ConnectedComponents S) →
      Nat.card (ConnectedComponents (Sᶜ : Set E₃)) = Nat.card (ConnectedComponents S) + 1 by
    exact h _ S rfl hc hS hfin
  intro n
  induction n using Nat.strong_induction_on with
  | h n ih =>
    intro S hn hc hS hfin
    let : Finite (ConnectedComponents S) := hfin
    by_cases hne : S.Nonempty
    · obtain ⟨t, ht⟩ := hne
      let t' : S := ⟨t, ht⟩
      let C : Set S := connectedComponent t'
      let T : Set E₃ := Subtype.val '' C
      let R : Set E₃ := S \ T
      have hC : IsClopen C := finite_components_clopen t'
      have hTS : T ⊆ S := by rintro _ ⟨x, _, rfl⟩; exact x.property
      have hTpre : (Subtype.val ⁻¹' T : Set S) = C :=
        Set.preimage_image_eq _ Subtype.val_injective
      have hTc : IsClosed T := hc.isClosed.isClosedMap_subtype_val _ hC.isClosed
      have hTcompact : IsCompact T := hc.of_isClosed_subset hTc hTS
      have hTconn : IsConnected T := isConnected_connectedComponent.image _
        continuous_subtype_val.continuousOn
      have hTsm : IsSmoothEmbeddedSurface T := smooth_subset_rel_open hS hTS
        (hTpre.symm ▸ hC.isOpen)
      have hRS : R ⊆ S := sdiff_subset
      have hd : Disjoint T R := Set.disjoint_left.mpr fun _ hx hy => hy.2 hx
      have hu : T ∪ R = S := by
        ext x
        have := @hTS x
        change (x ∈ T ∨ x ∈ S ∧ x ∉ T) ↔ x ∈ S
        tauto
      have hRpre : (Subtype.val ⁻¹' R : Set S) = Cᶜ := by
        rw [← hTpre, partition_preimage_compl hd hu]
      have hRimage : R = Subtype.val '' Cᶜ := by
        rw [← hRpre, Set.image_preimage_eq_inter_range]
        simp only [Subtype.range_coe]
        exact (inter_eq_left.mpr hRS).symm
      have hRc : IsClosed R := hRimage ▸
        hc.isClosed.isClosedMap_subtype_val _ hC.compl.isClosed
      have hRcompact : IsCompact R := hc.of_isClosed_subset hRc hRS
      have hRsm : IsSmoothEmbeddedSurface R := smooth_subset_rel_open hS hRS
        (hRpre.symm ▸ hC.compl.isOpen)
      let e := components_partition hTS hRS (hTpre.symm ▸ hC)
        (hRpre.symm ▸ hC.compl) hd hu
      let : Finite (ConnectedComponents T ⊕ ConnectedComponents R) := Finite.of_equiv _ e
      let : Finite (ConnectedComponents T) := Finite.of_injective
        (Sum.inl : ConnectedComponents T → ConnectedComponents T ⊕ ConnectedComponents R)
        Sum.inl_injective
      let : Finite (ConnectedComponents R) := Finite.of_injective
        (Sum.inr : ConnectedComponents R → ConnectedComponents T ⊕ ConnectedComponents R)
        Sum.inr_injective
      have hcard : Nat.card (ConnectedComponents S) = Nat.card (ConnectedComponents R) + 1 := by
        rw [Nat.card_congr e, Nat.card_sum, card_components_connected hTconn]
        omega
      have hlt : Nat.card (ConnectedComponents R) < n := by omega
      have hRcount := ih _ hlt R rfl hRcompact hRsm inferInstance
      let : Finite (ConnectedComponents (Rᶜ : Set E₃)) :=
        Nat.finite_of_card_ne_zero (by omega)
      obtain ⟨I, hloc, hcross⟩ := hpar T hTsm hTcompact hTconn
      have hTR : T ⊆ Rᶜ := fun _ hx hy => Set.disjoint_left.mp hd hx hy
      have he : Rᶜ \ T = Sᶜ := by
        ext x
        have := congrArg (fun A : Set E₃ => x ∈ A) hu
        simp only [mem_union] at this
        simp only [Set.mem_sdiff, mem_compl_iff]
        tauto
      have hc' := complement_split_count hRc.isOpen_compl hTsm hTcompact hTconn hTR
        I hloc hcross
      rw [he] at hc'
      omega
    · have he : S = ∅ := Set.not_nonempty_iff_eq_empty.mp hne
      subst S
      have hzero : Nat.card (ConnectedComponents (∅ : Set E₃)) = 0 := by
        let : IsEmpty (ConnectedComponents (∅ : Set E₃)) :=
          ConnectedComponents.isEmpty_iff_isEmpty.mpr inferInstance
        simp
      rw [compl_empty, hzero, zero_add]
      exact card_components_connected isConnected_univ

end
end LiquidDrop

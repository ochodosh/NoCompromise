import NoCompromise.Capacity.Potential
import NoCompromise.Surface.Geometry
import Mathlib.Topology.Connected.LocallyConnected
import Mathlib.Analysis.Normed.Module.Connected

/-!
# Levels of an exterior capacitary potential

The potential and all of its analytic properties are explicit hypotheses.
-/

noncomputable section
open Set Filter Metric MeasureTheory Function InnerProductSpace
open scoped Topology Gradient
namespace LiquidDrop

/-- A bounded-domain maximum principle, requiring continuity also at the boundary. -/
private theorem bounded_maximum {D : Set E₃} (hD : IsOpen D)
    (hbounded : Bornology.IsBounded D) {v : E₃ → ℝ} (hv : Continuous v)
    (hh : HasDistributionalLaplacianOn v (fun _ => 0) D)
    {s : ℝ} (hb : ∀ x ∈ frontier D, v x ≤ s) : ∀ x ∈ D, v x ≤ s := by
  intro x hx
  by_contra hn
  have hpos : s < v x := lt_of_not_ge hn
  obtain ⟨z, hz, hmax⟩ := hbounded.isCompact_closure.exists_isMaxOn
    ⟨x, subset_closure hx⟩ hv.continuousOn
  have hzpos : s < v z := hpos.trans_le (hmax (subset_closure hx))
  let M := closure D ∩ {y | v y = v z}
  have hclosed : IsClosed M := isClosed_closure.inter (isClosed_eq hv continuous_const)
  have hopen : IsOpen M := by
    apply isOpen_iff_mem_nhds.mpr
    intro y hy
    have hyD : y ∈ D := by
      by_contra hnD
      have hyfront : y ∈ frontier D := ⟨hy.1, by simpa [hD.interior_eq] using hnD⟩
      exact (not_le_of_gt hzpos) ((hy.2 ▸ hb y hyfront))
    obtain ⟨r, hr, hrD⟩ := Metric.isOpen_iff.mp hD y hyD
    have heq := strong_maximum (by decide : 3 < 4) isOpen_ball
      (convex_ball y r).isPreconnected hv.continuousOn (hh.mono hrD)
      (mem_ball_self hr) (fun w hw => (hmax (subset_closure (hrD hw))).trans_eq hy.2.symm)
    exact mem_of_superset (ball_mem_nhds y hr) fun w hw =>
      ⟨subset_closure (hrD hw), (heq w hw).trans hy.2⟩
  have heq := (show IsClopen M from ⟨hclosed, hopen⟩).eq_univ ⟨z, hz, rfl⟩
  have : Bornology.IsBounded (univ : Set E₃) := heq ▸ hbounded.closure.subset inter_subset_left
  exact NormedSpace.unbounded_univ ℝ E₃ this

private theorem closure_component_inter {F : Set E₃} {x : E₃} (hx : x ∈ F) :
    closure (connectedComponentIn F x) ∩ F ⊆ connectedComponentIn F x := by
  intro y hy
  rw [connectedComponentIn_eq_image hx] at hy ⊢
  have h := (Topology.IsInducing.subtypeVal.isClosed_iff').mp
    (isClosed_connectedComponent (x := (⟨x, hx⟩ : F))) ⟨y, hy.2⟩ hy.1
  exact ⟨⟨y, hy.2⟩, h, rfl⟩

private theorem frontier_component_subset {F : Set E₃} (hF : IsOpen F)
    {x : E₃} (hx : x ∈ F) : frontier (connectedComponentIn F x) ⊆ frontier F := by
  intro y hy
  refine ⟨closure_mono (connectedComponentIn_subset F x) hy.1, ?_⟩
  rw [hF.interior_eq]
  intro hyF
  apply hy.2
  rw [hF.connectedComponentIn.interior_eq]
  exact closure_component_inter hx ⟨hy.1, hyF⟩

/-- The compact conductor belongs to every superlevel below one. -/
lemma subset_superlevel {K : Set E₃} {u : E₃ → ℝ}
    (hKval : ∀ x ∈ K, u x = 1) {s : ℝ} (hs1 : s < 1) : K ⊆ {x | s < u x} := by
  intro x hx
  change s < u x
  rw [hKval x hx]
  exact hs1

lemma isOpen_superlevel {u : E₃ → ℝ} (hu : Continuous u) (s : ℝ) :
    IsOpen {x | s < u x} := isOpen_lt continuous_const hu

lemma isOpen_sublevel {u : E₃ → ℝ} (hu : Continuous u) (s : ℝ) :
    IsOpen {x | u x < s} := isOpen_lt hu continuous_const

/-- The extended potential's positive superlevel is connected. -/
theorem isConnected_superlevel {K : Set E₃} (_hK : IsCompact K)
    (hconn : IsConnected K) {u : E₃ → ℝ} (hu : Continuous u)
    (hKval : ∀ x ∈ K, u x = 1)
    (hh : HasDistributionalLaplacianOn u (fun _ => 0) Kᶜ)
    (hinf : Tendsto u (cocompact E₃) (𝓝 0))
    {s : ℝ} (hs : 0 < s) (hs1 : s < 1) : IsConnected {x | s < u x} := by
  let F := {x | s < u x}
  have hF : IsOpen F := isOpen_lt continuous_const hu
  have hKF : K ⊆ F := subset_superlevel hKval hs1
  obtain ⟨R, hR⟩ := Metric.closedBall_compl_subset_of_mem_cocompact
    (hinf.eventually (gt_mem_nhds hs)) (0 : E₃)
  have hbounded : Bornology.IsBounded F := isBounded_closedBall.subset (by
    intro x hx
    by_contra hn
    exact (show u x < s from hR hn).not_gt hx)
  have hmeet : ∀ x ∈ F, (connectedComponentIn F x ∩ K).Nonempty := by
    intro x hx
    by_contra hn
    have hCK : connectedComponentIn F x ⊆ Kᶜ := by
      intro y hy hyK
      exact hn ⟨y, hy, hyK⟩
    have hb : ∀ y ∈ frontier (connectedComponentIn F x), u y ≤ s := by
      intro y hy
      have := (frontier_component_subset hF hx hy).2
      rw [hF.interior_eq] at this
      exact le_of_not_gt this
    have hle := bounded_maximum hF.connectedComponentIn
      (hbounded.subset (connectedComponentIn_subset F x)) hu (hh.mono hCK) hb x
      (mem_connectedComponentIn hx)
    exact hle.not_gt hx
  obtain ⟨a, ha⟩ := hconn.nonempty
  have heq : F = connectedComponentIn F a := by
    apply subset_antisymm _ (connectedComponentIn_subset F a)
    intro x hx
    obtain ⟨y, hyC, hyK⟩ := hmeet x hx
    have hyA := hconn.isPreconnected.subset_connectedComponentIn ha hKF hyK
    rw [connectedComponentIn_eq hyA, ← connectedComponentIn_eq hyC]
    exact mem_connectedComponentIn hx
  change IsConnected F
  rw [heq]
  exact isConnected_connectedComponentIn_iff.mpr (hKF ha)

private theorem isConnected_exterior_closedBall {R : ℝ} (hR : 0 ≤ R) :
    IsConnected (closedBall (0 : E₃) R)ᶜ := by
  have hdim : 1 < Module.rank ℝ E₃ := by rw [← Module.finrank_eq_rank]; simp [E₃]
  have hprod := (isConnected_sphere hdim (0 : E₃) (by norm_num : (0 : ℝ) ≤ 1)).prod
    (isConnected_Ioi : IsConnected (Ioi R))
  have himage : (fun p : E₃ × ℝ => p.2 • p.1) '' (sphere (0 : E₃) 1 ×ˢ Ioi R) =
      (closedBall (0 : E₃) R)ᶜ := by
    ext x
    constructor
    · rintro ⟨⟨v, r⟩, ⟨hv, hr⟩, rfl⟩
      have hvnorm : ‖v‖ = 1 := by simpa using hv
      have hrpos : 0 ≤ r := hR.trans hr.le
      simpa [mem_closedBall, norm_smul, Real.norm_eq_abs, abs_of_nonneg hrpos, hvnorm] using hr
    · intro hx
      have hxR : R < ‖x‖ := by simpa using hx
      have hxpos : 0 < ‖x‖ := hR.trans_lt hxR
      refine ⟨⟨‖x‖⁻¹ • x, ‖x‖⟩, ⟨?_, hxR⟩, ?_⟩
      · simp [norm_smul, hxpos.ne']
      · simp [smul_smul, hxpos.ne']
  rw [← himage]
  exact hprod.image _ (by fun_prop)

/-- The sublevel is connected: every component meets the connected exterior of a ball. -/
theorem isConnected_sublevel {K : Set E₃} {u : E₃ → ℝ} (hu : Continuous u)
    (hKval : ∀ x ∈ K, u x = 1)
    (hh : HasDistributionalLaplacianOn u (fun _ => 0) Kᶜ)
    (hinf : Tendsto u (cocompact E₃) (𝓝 0))
    {s : ℝ} (hs : 0 < s) (hs1 : s < 1) : IsConnected {x | u x < s} := by
  let F := {x | u x < s}
  have hF : IsOpen F := isOpen_lt hu continuous_const
  have hFK : F ⊆ Kᶜ := by
    intro x hx hxK
    have := hKval x hxK
    change u x < s at hx
    linarith
  obtain ⟨r, hr⟩ := Metric.closedBall_compl_subset_of_mem_cocompact
    (hinf.eventually (gt_mem_nhds hs)) (0 : E₃)
  let R := max r 0
  let A := (closedBall (0 : E₃) R)ᶜ
  have hAF : A ⊆ F := fun x hx =>
    hr (fun h => hx (closedBall_subset_closedBall (le_max_left r 0) h))
  have hA : IsConnected A := isConnected_exterior_closedBall (le_max_right r 0)
  have hmeet : ∀ x ∈ F, (connectedComponentIn F x ∩ A).Nonempty := by
    intro x hx
    by_contra hn
    have hbounded : Bornology.IsBounded (connectedComponentIn F x) :=
      isBounded_closedBall.subset (by
        intro y hy
        by_contra hyA
        exact hn ⟨y, hy, hyA⟩)
    have hb : ∀ y ∈ frontier (connectedComponentIn F x), -u y ≤ -s := by
      intro y hy
      have := (frontier_component_subset hF hx hy).2
      rw [hF.interior_eq] at this
      exact neg_le_neg (le_of_not_gt this)
    have hneg : HasDistributionalLaplacianOn (fun x => -u x) (fun _ => 0)
        (connectedComponentIn F x) := by
      simpa using (hh.mono ((connectedComponentIn_subset F x).trans hFK)).const_mul (-1)
    have hle := bounded_maximum hF.connectedComponentIn hbounded hu.neg hneg hb x
      (mem_connectedComponentIn hx)
    exact (not_le_of_gt hx) (neg_le_neg_iff.mp hle)
  obtain ⟨a, ha⟩ := hA.nonempty
  have heq : F = connectedComponentIn F a := by
    apply subset_antisymm _ (connectedComponentIn_subset F a)
    intro x hx
    obtain ⟨y, hyC, hyA⟩ := hmeet x hx
    have hy := hA.isPreconnected.subset_connectedComponentIn ha hAF hyA
    rw [connectedComponentIn_eq hy, ← connectedComponentIn_eq hyC]
    exact mem_connectedComponentIn hx
  change IsConnected F
  rw [heq]
  exact isConnected_connectedComponentIn_iff.mpr (hAF ha)

/-- The level of the globally extended potential. -/
def levelSet (u : E₃ → ℝ) (s : ℝ) : Set E₃ := {x | u x = s}

lemma levelSet_subset_compl {K : Set E₃} {u : E₃ → ℝ}
    (hKval : ∀ x ∈ K, u x = 1) {s : ℝ} (hs1 : s < 1) : levelSet u s ⊆ Kᶜ := by
  intro x hx hxK
  have := hKval x hxK
  change u x = s at hx
  linarith

lemma isCompact_levelSet {u : E₃ → ℝ} (hu : Continuous u)
    (hinf : Tendsto u (cocompact E₃) (𝓝 0)) {s : ℝ} (hs : 0 < s) :
    IsCompact (levelSet u s) := by
  obtain ⟨T, hT, hsub⟩ := Filter.mem_cocompact.mp (hinf.eventually (gt_mem_nhds hs))
  apply hT.of_isClosed_subset (isClosed_eq hu continuous_const)
  intro x hx
  by_contra hn
  exact (hsub hn).ne hx

lemma levelSet_nonempty {K : Set E₃} (hK : K.Nonempty) {u : E₃ → ℝ}
    (hu : Continuous u) (hKval : ∀ x ∈ K, u x = 1)
    (hinf : Tendsto u (cocompact E₃) (𝓝 0)) {s : ℝ} (hs : 0 < s) (hs1 : s < 1) :
    (levelSet u s).Nonempty := by
  obtain ⟨a, ha⟩ := hK
  obtain ⟨b, hb⟩ := (hinf.eventually (gt_mem_nhds hs)).exists
  obtain ⟨x, hx⟩ := intermediate_value_univ b a hu ⟨hb.le, by rw [hKval a ha]; exact hs1.le⟩
  exact ⟨x, hx⟩

lemma levelSet_compl (u : E₃ → ℝ) (s : ℝ) :
    (levelSet u s)ᶜ = {x | s < u x} ∪ {x | u x < s} := by
  ext x
  simp only [levelSet, mem_compl_iff, mem_ofPred_eq, mem_union]
  exact ne_iff_lt_or_gt.trans or_comm

lemma disjoint_superlevel_sublevel (u : E₃ → ℝ) (s : ℝ) :
    Disjoint {x | s < u x} {x | u x < s} :=
  Set.disjoint_left.mpr fun x h₁ h₂ => (show s < u x from h₁).not_gt h₂

/-- Regular levels are smooth embedded surfaces, using a smooth ambient extension near the level. -/
theorem isSmoothEmbeddedSurface_levelSet {K : Set E₃} (hK : IsCompact K)
    {u : E₃ → ℝ} (hu : Continuous u) (hKval : ∀ x ∈ K, u x = 1)
    (hinf : Tendsto u (cocompact E₃) (𝓝 0))
    (hsmooth : ContDiffOn ℝ (⊤ : ℕ∞) u Kᶜ)
    {s : ℝ} (hs : 0 < s) (hs1 : s < 1)
    (hreg : ∀ x ∈ levelSet u s, gradient u x ≠ 0) :
    IsSmoothEmbeddedSurface (levelSet u s) := by
  obtain ⟨g, hg, hgu⟩ := exists_smooth_height_eq_near_compact hK.isClosed.isOpen_compl
    (isCompact_levelSet hu hinf hs) (levelSet_subset_compl hKval hs1) hsmooth
  intro p hp
  obtain ⟨U, hUsub, hUopen, hpU⟩ := _root_.mem_nhds_iff.mp (hgu p hp)
  refine ⟨U, fun x => g x - s, hUopen, hpU, hg.sub contDiff_const, ?_, ?_⟩
  · ext x
    simp only [levelSet, mem_inter_iff, mem_ofPred_eq, sub_eq_zero]
    constructor
    · rintro ⟨hx, hxU⟩
      exact ⟨hxU, (hUsub hxU).trans hx⟩
    · rintro ⟨hxU, hx⟩
      exact ⟨(hUsub hxU).symm.trans hx, hxU⟩
  · intro x hx
    have heq : (fun y => g y - s) =ᶠ[𝓝 x] (fun y => u y - s) :=
      (hgu x hx.1).fun_comp (fun t => t - s)
    rw [heq.gradient_eq]
    simpa only [gradient, fderiv_sub_const] using hreg x hx.1

private theorem isConnected_subtype_preimage {A B : Set E₃} (hA : IsConnected A)
    (hAB : A ⊆ B) : IsConnected ((Subtype.val : B → E₃) ⁻¹' A) := by
  refine ⟨?_, Topology.IsInducing.subtypeVal.isPreconnected_image.mp ?_⟩
  · obtain ⟨x, hx⟩ := hA.nonempty
    exact ⟨⟨x, hAB hx⟩, hx⟩
  · simpa only [Subtype.image_preimage_coe, inter_eq_right.mpr hAB] using hA.isPreconnected

/-- The complement has precisely two connected components. -/
theorem card_connectedComponents_levelSet_compl {K : Set E₃} (hK : IsCompact K)
    (hconn : IsConnected K) {u : E₃ → ℝ} (hu : Continuous u)
    (hKval : ∀ x ∈ K, u x = 1)
    (hh : HasDistributionalLaplacianOn u (fun _ => 0) Kᶜ)
    (hinf : Tendsto u (cocompact E₃) (𝓝 0))
    {s : ℝ} (hs : 0 < s) (hs1 : s < 1) :
    Nat.card (ConnectedComponents ((levelSet u s)ᶜ : Set E₃)) = 2 := by
  let B := (levelSet u s)ᶜ
  let U : Bool → Set B := fun b => if b then {x | s < u x} else {x | u x < s}
  have hUopen : ∀ b, IsOpen (U b) := by
    intro b
    cases b <;> dsimp [U] <;> apply isOpen_lt <;> fun_prop
  have hUcompl : ∀ b, (U b)ᶜ = U (!b) := by
    intro b
    ext x
    have hx : u x ≠ s := x.property
    cases b
    · change (¬ u x < s) ↔ s < u x
      constructor <;> intro h <;> order
    · change (¬ s < u x) ↔ u x < s
      constructor <;> intro h <;> order
  have hUclopen : ∀ b, IsClopen (U b) := fun b =>
    ⟨isOpen_compl_iff.mp (hUcompl b ▸ hUopen (!b)), hUopen b⟩
  have hdisj : Pairwise (Disjoint on U) := by
    intro i j hij
    cases i <;> cases j <;> try exact (hij rfl).elim
    all_goals
      apply Set.disjoint_left.mpr
      intro x h₁ h₂
      dsimp [U] at h₁ h₂
      linarith
  have hcover : ⋃ b, U b = univ := by
    ext x
    have hx : u x ≠ s := x.property
    simp only [mem_iUnion, mem_univ, iff_true]
    rcases lt_or_gt_of_ne hx with h | h
    · exact ⟨false, h⟩
    · exact ⟨true, h⟩
  have hUconn : ∀ b, IsConnected (U b) := by
    intro b
    cases b
    · exact isConnected_subtype_preimage (isConnected_sublevel hu hKval hh hinf hs hs1)
        (fun _ hx => ne_of_lt hx)
    · exact isConnected_subtype_preimage (isConnected_superlevel hK hconn hu hKval hh hinf hs hs1)
        (fun _ hx => ne_of_gt hx)
  have he := ConnectedComponents.equivOfIsClopenOfIsConnected hUclopen hdisj hcover hUconn
  exact (Nat.card_congr he).trans (by simp)

/-- The component-count theorem from chapter 14, kept as an explicit dependency.
It concerns every compact smooth embedded surface with finitely many components. -/
def ComponentCountStatement : Prop :=
  ∀ S : Set E₃, IsCompact S → IsSmoothEmbeddedSurface S →
    Finite (ConnectedComponents S) →
    Nat.card (ConnectedComponents (Sᶜ : Set E₃)) = Nat.card (ConnectedComponents S) + 1

/-- Local regular defining functions give a basis of connected neighborhoods on a surface. -/
theorem IsSmoothEmbeddedSurface.locallyConnectedSpace {S : Set E₃}
    (hS : IsSmoothEmbeddedSurface S) : LocallyConnectedSpace S := by
  apply locallyConnectedSpace_iff_connected_subsets.mpr
  intro p V hV
  obtain ⟨W, hW, hWV⟩ := (mem_nhds_subtype S p V).mp hV
  obtain ⟨U, φ, hU, hpU, hφ, hzero, hreg⟩ := hS p p.property
  have hpzero : φ p = 0 := (hzero ▸ (show (p : E₃) ∈ S ∩ U from ⟨p.property, hpU⟩)).2
  have hφp : ContDiffAt ℝ 1 φ (p : E₃) := (hφ.of_le (by simp)).contDiffAt
  have hd := hφp.hasStrictFDerivAt one_ne_zero
  have hrange : (fderiv ℝ φ p).range = ⊤ := by
    apply Module.Dual.range_eq_top_of_ne_zero
    intro hz
    apply hreg p ⟨p.property, hpU⟩
    apply (InnerProductSpace.toDual ℝ E₃).injective
    rw [toDual_gradient, map_zero]
    exact ContinuousLinearMap.ext fun x => congrArg (fun L : E₃ →ₗ[ℝ] ℝ => L x) hz
  let e := hd.implicitToOpenPartialHomeomorph φ (fderiv ℝ φ p) hrange
  let γ : (fderiv ℝ φ p).ker → E₃ := fun z => e.symm (φ p, z)
  have hpSource : (p : E₃) ∈ e.source := hd.mem_implicitToOpenPartialHomeomorph_source hrange
  have hpTarget : (φ p, (0 : (fderiv ℝ φ p).ker)) ∈ e.target :=
    hd.mem_implicitToOpenPartialHomeomorph_target hrange
  have hep : e p = (φ p, 0) := hd.implicitToOpenPartialHomeomorph_self hrange
  have hγp : γ 0 = p := by dsimp [γ]; rw [← hep]; exact e.left_inv hpSource
  have hγcont : ContinuousAt γ 0 :=
    (e.continuousAt_symm hpTarget).comp (continuous_const.prodMk continuous_id).continuousAt
  have hslice : Continuous (fun z : (fderiv ℝ φ p).ker => (φ p, z)) :=
    continuous_const.prodMk continuous_id
  have hnear : {z | (φ p, z) ∈ e.target ∧ γ z ∈ U ∩ W} ∈ 𝓝 (0 : (fderiv ℝ φ p).ker) := by
    apply inter_mem (hslice.continuousAt.preimage_mem_nhds (e.open_target.mem_nhds hpTarget))
    exact hγcont.preimage_mem_nhds (by
      simpa only [hγp, Set.inter_def] using inter_mem (hU.mem_nhds hpU) hW)
  obtain ⟨r, hr, hrsub⟩ := Metric.mem_nhds_iff.mp hnear
  let C := γ '' ball 0 r
  have hCS : C ⊆ S := by
    rintro _ ⟨z, hz, rfl⟩
    have ht := hrsub hz
    have hφγ : φ (γ z) = 0 := by
      have he := congrArg Prod.fst (e.right_inv ht.1)
      have hfst := hd.implicitToOpenPartialHomeomorph_fst hrange (γ z)
      exact hfst.symm.trans (he.trans hpzero)
    exact ((congrArg (fun A : Set E₃ => γ z ∈ A) hzero).mpr ⟨ht.2.1, hφγ⟩).1
  have hCW : C ⊆ W := by
    rintro _ ⟨z, hz, rfl⟩
    exact (hrsub hz).2.2
  have hCconn : IsConnected C := (isConnected_ball hr).image γ
    (e.symm.continuousOn.comp hslice.continuousOn (fun z hz => (hrsub hz).1))
  refine ⟨Subtype.val ⁻¹' C, ?_, (isConnected_subtype_preimage hCconn hCS).isPreconnected, ?_⟩
  · apply (mem_nhds_subtype S p _).mpr
    have hcoord : {x : E₃ | (e x).2 ∈ ball 0 r} ∈ 𝓝 (p : E₃) := by
      apply (e.continuousAt hpSource).snd.preimage_mem_nhds
      simpa only [hep] using ball_mem_nhds (0 : (fderiv ℝ φ p).ker) hr
    refine ⟨e.source ∩ U ∩ {x | (e x).2 ∈ ball 0 r},
      inter_mem (inter_mem (e.open_source.mem_nhds hpSource) (hU.mem_nhds hpU)) hcoord, ?_⟩
    intro x hx
    refine ⟨(e x).2, hx.2, ?_⟩
    have hxzero : φ x = 0 :=
      (hzero ▸ (show (x : E₃) ∈ S ∩ U from ⟨x.property, hx.1.2⟩)).2
    have hfst : (e x).1 = φ p :=
      (hd.implicitToOpenPartialHomeomorph_fst hrange x).trans (hxzero.trans hpzero.symm)
    change e.symm (φ p, (e x).2) = x
    rw [← hfst, Prod.mk.eta]
    exact e.left_inv hx.1.1
  · intro x hx
    exact hWV (hCW hx)

/-- A compact smooth embedded surface has finitely many connected components. -/
theorem IsSmoothEmbeddedSurface.finite_connectedComponents {S : Set E₃}
    (hS : IsSmoothEmbeddedSurface S) (hcompact : IsCompact S) :
    Finite (ConnectedComponents S) := by
  let := hS.locallyConnectedSpace
  let := isCompact_iff_compactSpace.mp hcompact
  infer_instance

/-- Blueprint `lem:level-connected`, conditional only on the chapter 14 component count. -/
theorem level_connected_of_component_count (hcc : ComponentCountStatement)
    {K : Set E₃} (hK : IsCompact K) (hconn : IsConnected K)
    {u : E₃ → ℝ} (hu : Continuous u) (hKval : ∀ x ∈ K, u x = 1)
    (hh : HasDistributionalLaplacianOn u (fun _ => 0) Kᶜ)
    (hsmooth : ContDiffOn ℝ (⊤ : ℕ∞) u Kᶜ)
    (hinf : Tendsto u (cocompact E₃) (𝓝 0))
    (_hstrict : ∀ x ∉ K, 0 < u x ∧ u x < 1)
    {s : ℝ} (hs : 0 < s) (hs1 : s < 1)
    (hreg : ∀ x ∈ levelSet u s, gradient u x ≠ 0) : IsConnected (levelSet u s) := by
  have hcompact := isCompact_levelSet hu hinf hs
  have hsurface := isSmoothEmbeddedSurface_levelSet hK hu hKval hinf hsmooth hs hs1 hreg
  have hfinite := hsurface.finite_connectedComponents hcompact
  have hcount := hcc (levelSet u s) hcompact hsurface hfinite
  rw [card_connectedComponents_levelSet_compl hK hconn hu hKval hh hinf hs hs1] at hcount
  have hone : Nat.card (ConnectedComponents (levelSet u s)) = 1 := by omega
  have : Subsingleton (ConnectedComponents (levelSet u s)) :=
    (Nat.card_eq_one_iff_unique.mp hone).1
  have hp : PreconnectedSpace (levelSet u s) := by
    apply preconnectedSpace_iff_connectedComponent.mpr
    intro x
    apply Set.eq_univ_of_forall
    intro y
    exact ConnectedComponents.coe_eq_coe'.mp (Subsingleton.elim
      (ConnectedComponents.mk y) (ConnectedComponents.mk x))
  exact ⟨levelSet_nonempty hconn.nonempty hu hKval hinf hs hs1,
    isPreconnected_iff_preconnectedSpace.mpr hp⟩

end LiquidDrop

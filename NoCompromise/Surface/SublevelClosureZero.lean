module

public import NoCompromise.Surface.SublevelAttach
public import NoCompromise.Surface.SublevelClosureLocal
public import NoCompromise.Surface.MorseCoordsPlanar

@[expose] public section

/-!
# `lem:sublevel-closure`, case `λ = 0`

At an index-zero critical point `p` of a Morse function `h` on an embedded surface, with `p` the
only critical point at its level, passing from `S ∩ {h < h p}` to `S ∩ {h ≤ h p}` adds exactly
one component: the regular level points attach to existing components without joining any two,
and `p` itself is an isolated point of the closed sublevel.
-/

noncomputable section

open Set Function

namespace LiquidDrop

lemma sublevelClosureZero_mk_eq_mk_iff {T : Set E₃} (x y : T) :
    (ConnectedComponents.mk x = ConnectedComponents.mk y) ↔
      (y : E₃) ∈ connectedComponentIn T x := by
  rw [ConnectedComponents.coe_eq_coe, eq_comm, connectedComponent_eq_iff_mem,
    connectedComponentIn_eq_image x.2]
  exact (Subtype.val_injective.mem_set_image).symm

/-- A preconnected subset of `T` through a point `p` isolated in `T` is contained in `{p}`. -/
lemma preconnected_subset_singleton_of_isolated {T U C : Set E₃} {p : E₃} (hU : IsOpen U)
    (hpU : p ∈ U) (hUT : U ∩ T ⊆ {p}) (hC : IsPreconnected C) (hCT : C ⊆ T) (hpC : p ∈ C) :
    C ⊆ {p} := by
  intro y hy
  by_contra hyp
  have hcov : C ⊆ U ∪ {p}ᶜ := by
    intro z _
    by_cases hz : z = p
    · exact Or.inl (hz ▸ hpU)
    · exact Or.inr hz
  obtain ⟨z, hzC, hzU, hzp⟩ :=
    hC U {p}ᶜ hU isOpen_compl_singleton hcov ⟨p, hpC, hpU⟩ ⟨y, hy, hyp⟩
  exact hzp (hUT ⟨hzU, hCT hzC⟩)

/-- Adjoining an isolated point to a set adds exactly one component. -/
theorem componentCount_insert_isolated {A T U : Set E₃} {p : E₃} (hT : T = insert p A)
    (hpA : p ∉ A) (hU : IsOpen U) (hpU : p ∈ U) (hUT : U ∩ T ⊆ {p}) :
    componentCount T = componentCount A + 1 := by
  have hAT : A ⊆ T := fun x hx => hT ▸ Or.inr hx
  have hpT : p ∈ T := hT ▸ Or.inl rfl
  -- components of `T` through points of `A` are those of `A`
  have hcomp : ∀ x ∈ A, connectedComponentIn T x = connectedComponentIn A x := by
    intro x hx
    apply le_antisymm
    · have hpn : p ∉ connectedComponentIn T x := by
        intro hp
        have := preconnected_subset_singleton_of_isolated hU hpU hUT
          isPreconnected_connectedComponentIn (connectedComponentIn_subset T x) hp
          (mem_connectedComponentIn (hAT hx))
        rw [mem_singleton_iff] at this
        exact hpA (this ▸ hx)
      have hsub : connectedComponentIn T x ⊆ A := by
        intro y hy
        have hyT := connectedComponentIn_subset T x hy
        rw [hT] at hyT
        rcases hyT with rfl | hyA
        · exact (hpn hy).elim
        · exact hyA
      exact isPreconnected_connectedComponentIn.subset_connectedComponentIn
        (mem_connectedComponentIn (hAT hx)) hsub
    · exact connectedComponentIn_mono x hAT
  have hc : Continuous (Set.inclusion hAT) := continuous_inclusion hAT
  have hF : ∀ a : A, hc.connectedComponentsMap (ConnectedComponents.mk a) =
      ConnectedComponents.mk (Set.inclusion hAT a) := fun a => hc.connectedComponentsMap_mk a
  let f : ConnectedComponents A ⊕ Unit → ConnectedComponents T :=
    Sum.elim hc.connectedComponentsMap (fun _ => ConnectedComponents.mk ⟨p, hpT⟩)
  have hf : Bijective f := by
    refine ⟨Injective.sumElim ?_ ?_ ?_, ?_⟩
    · intro u v huv
      obtain ⟨a, rfl⟩ := ConnectedComponents.surjective_coe u
      obtain ⟨b, rfl⟩ := ConnectedComponents.surjective_coe v
      rw [hF, hF, sublevelClosureZero_mk_eq_mk_iff] at huv
      rw [sublevelClosureZero_mk_eq_mk_iff, ← hcomp a a.2]
      exact huv
    · intro u v _
      rfl
    · intro u v huv
      obtain ⟨a, rfl⟩ := ConnectedComponents.surjective_coe u
      rw [hF, sublevelClosureZero_mk_eq_mk_iff, hcomp a a.2] at huv
      exact hpA (connectedComponentIn_subset A a huv)
    · intro u
      obtain ⟨x, rfl⟩ := ConnectedComponents.surjective_coe u
      by_cases hxp : (x : E₃) = p
      · refine ⟨Sum.inr (), ?_⟩
        change ConnectedComponents.mk (⟨p, hpT⟩ : T) = ConnectedComponents.mk x
        rw [sublevelClosureZero_mk_eq_mk_iff, hxp]
        exact mem_connectedComponentIn hpT
      · have hxA : (x : E₃) ∈ A := by
          have hx2 : (x : E₃) ∈ insert p A := hT ▸ x.2
          exact hx2.resolve_left hxp
        refine ⟨Sum.inl (ConnectedComponents.mk ⟨x, hxA⟩), ?_⟩
        change hc.connectedComponentsMap _ = _
        rw [hF, sublevelClosureZero_mk_eq_mk_iff]
        exact mem_connectedComponentIn x.2
  rw [componentCount, componentCount, ← ENat.card_congr (Equiv.ofBijective f hf),
    ENat.card_sum]
  simp

/-- The regular level points of `{h = c}` attach to components of `S ∩ {h < c}` without joining
any two: removing a set `Z` containing all critical points at level `c` from the closed sublevel
leaves the component count of the open sublevel. -/
theorem componentCount_sublevel_diff_eq {S : Set E₃} (hS : IsSmoothEmbeddedSurface S)
    {h : E₃ → ℝ} (hh : ContDiff ℝ 1 h) {c : ℝ} {Z : Set E₃}
    (hreg : ∀ q ∈ S, h q = c → q ∉ Z → ¬ IsSurfaceCriticalPoint S h q)
    (hZ : ∀ z ∈ Z, c ≤ h z) :
    componentCount ((S ∩ {y | h y ≤ c}) \ Z) = componentCount (S ∩ {y | h y < c}) := by
  set N := S ∩ {y | h y < c} with hNdef
  set K' := (S ∩ {y | h y ≤ c}) \ Z with hK'def
  have hNK : N ⊆ K' := fun x hx =>
    ⟨⟨hx.1, show h x ≤ c from le_of_lt hx.2⟩, fun hxZ => absurd (hZ x hxZ) (not_le.mpr hx.2)⟩
  refine (componentCount_eq_of_connectedComponentIn hNK ?_ ?_).symm
  · intro x hx
    rcases lt_or_eq_of_le (show h x ≤ c from hx.1.2) with hxc | hxc
    · exact ⟨x, ⟨hx.1.1, hxc⟩, mem_connectedComponentIn hx⟩
    · obtain ⟨w, hwN, hxw⟩ := exists_mem_closure_connectedComponentIn_levelBelow hS hh hx.1.1
        hxc (hreg x hx.1.1 hxc hx.2)
      have hpre : IsPreconnected (insert x (connectedComponentIn N w)) :=
        isPreconnected_connectedComponentIn.subset_closure (subset_insert _ _)
          (insert_subset_iff.mpr ⟨hxw, subset_closure⟩)
      have hsub : insert x (connectedComponentIn N w) ⊆ K' :=
        insert_subset_iff.mpr ⟨hx, (connectedComponentIn_subset N w).trans hNK⟩
      exact ⟨w, hwN, hpre.subset_connectedComponentIn (mem_insert x _) hsub
        (mem_insert_of_mem x (mem_connectedComponentIn hwN))⟩
  · intro x hx y hy
    constructor
    · intro hyx
      exact preconnected_inter_levelBelow_subset hS hh hreg isPreconnected_connectedComponentIn
        (connectedComponentIn_subset K' x) (mem_connectedComponentIn (hNK hx)) hx.2
        ⟨hyx, hy.2⟩
    · intro hyx
      exact connectedComponentIn_mono x hNK hyx

/-- `lem:sublevel-closure`, case `λ = 0`: passing an index-zero critical point `p` (the only
critical point at its level) adds exactly one component to the sublevel. -/
theorem componentCount_sublevel_closure_index_zero {S : Set E₃} {n : E₃ → E₃}
    (hS : IsSmoothEmbeddedSurface S) (hn : IsUnitNormalField S n) {h : E₃ → ℝ}
    (hh : ContDiff ℝ (⊤ : ℕ∞) h) (hM : IsSurfaceMorse S n h)
    (hinj : Set.InjOn h {p | IsSurfaceCriticalPoint S h p}) {p : E₃}
    (hp : IsSurfaceCriticalPoint S h p) (hk : surfaceIndex S n h p = 0) :
    componentCount (S ∩ {x | h x ≤ h p}) = componentCount (S ∩ {x | h x < h p}) + 1 := by
  have hh1 : ContDiff ℝ 1 h := hh.of_le (by exact_mod_cast le_top)
  obtain ⟨U, hU, hpU, hUK⟩ :=
    exists_isolated_sublevel_of_index_zero hS hn hh hp (hM p hp) morseCoordsStatement hk
  have hreg : ∀ q ∈ S, h q = h p → q ∉ ({p} : Set E₃) → ¬ IsSurfaceCriticalPoint S h q :=
    fun q _ hq hqp hcq => hqp (hinj hcq hp hq)
  rw [← componentCount_sublevel_diff_eq hS hh1 hreg
    (fun z hz => (mem_singleton_iff.mp hz) ▸ le_rfl)]
  refine componentCount_insert_isolated ?_ (fun h' => h'.2 rfl) hU hpU hUK.le
  rw [insert_sdiff_singleton]
  have hpK : p ∈ S ∩ {y | h y ≤ h p} := ⟨hp.1, show h p ≤ h p from le_rfl⟩
  exact (insert_eq_of_mem hpK).symm

end LiquidDrop

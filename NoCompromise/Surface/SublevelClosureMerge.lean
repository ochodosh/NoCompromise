import NoCompromise.Surface.SublevelClosureZero
import NoCompromise.Surface.SublevelClosureCount

/-!
# `lem:sublevel-closure`, case `λ = 1`, `p` sub-merging

At a sub-merging saddle `p` (the only critical point at its level), passing from
`S ∩ {h < h p}` to `S ∩ {h ≤ h p}` joins exactly the two components `A₁`, `A₂` of the open
sublevel that adjoin `p`, and joins nothing else: the component count drops by one.
-/

noncomputable section

open Set Filter Function
open scoped Topology

namespace LiquidDrop

/-- A point of `K ⊇ N` in the closure of a component of `N` lies in the corresponding component
of `K`. -/
theorem mem_connectedComponentIn_of_mem_closure_componentIn {N K : Set E₃} (hNK : N ⊆ K)
    {w x : E₃} (hw : w ∈ N) (hxK : x ∈ K) (hx : x ∈ closure (connectedComponentIn N w)) :
    x ∈ connectedComponentIn K w := by
  have hpre : IsPreconnected (insert x (connectedComponentIn N w)) :=
    isPreconnected_connectedComponentIn.subset_closure (subset_insert _ _)
      (insert_subset hx subset_closure)
  have hsub : insert x (connectedComponentIn N w) ⊆ K :=
    insert_subset hxK ((connectedComponentIn_subset N w).trans hNK)
  exact hpre.subset_connectedComponentIn (mem_insert_of_mem _ (mem_connectedComponentIn hw))
    hsub (mem_insert x _)

/-- `lem:sublevel-closure`, attaching step for a union of components: let `A` be a union of
components of `N := S ∩ {h < c}` such that every level-`c` point of `closure A` has an open
neighbourhood whose trace on `K := S ∩ {h ≤ c}` lies in `closure A`. Then a preconnected subset
`C` of `K` meeting `A` has `C ∩ {h < c} ⊆ A`. -/
theorem preconnected_inter_levelBelow_subset_of_saturated {S : Set E₃} {h : E₃ → ℝ}
    (hhc : Continuous h) {c : ℝ} {A : Set E₃} (hAN : A ⊆ S ∩ {y | h y < c})
    (hAcomp : ∀ z ∈ A, connectedComponentIn (S ∩ {y | h y < c}) z ⊆ A)
    (hlev : ∀ z ∈ closure A, z ∈ S → h z = c → ∃ W : Set E₃, IsOpen W ∧ z ∈ W ∧
      W ∩ (S ∩ {y | h y ≤ c}) ⊆ closure A)
    (hlc : ∀ z ∈ S, ∀ O : Set E₃, IsOpen O → z ∈ O →
      ∃ N ⊆ S ∩ O, IsPreconnected N ∧ N ∈ 𝓝[S] z)
    {C : Set E₃} (hC : IsPreconnected C) (hCK : C ⊆ S ∩ {y | h y ≤ c})
    {x : E₃} (hxC : x ∈ C) (hxA : x ∈ A) :
    C ∩ {y | h y < c} ⊆ A := by
  let K := S ∩ {y | h y ≤ c}
  have hNo : IsOpen {y : E₃ | h y < c} := isOpen_lt hhc continuous_const
  have hbelow : ∀ z ∈ closure A, z ∈ S → h z < c → ∃ W : Set E₃, IsOpen W ∧ z ∈ W ∧
      W ∩ S ⊆ A ∧ z ∈ A := by
    intro z hzcl hzS hzc
    obtain ⟨N', hN'sub, hN'pre, hN'nhds⟩ := hlc z hzS _ hNo hzc
    obtain ⟨W, hWo, hzW, hWsub⟩ := mem_nhdsWithin.mp hN'nhds
    obtain ⟨a, haW, haA⟩ := mem_closure_iff.mp hzcl W hWo hzW
    have haN' : a ∈ N' := hWsub ⟨haW, (hAN haA).1⟩
    have hN'A : N' ⊆ A :=
      (hN'pre.subset_connectedComponentIn haN' hN'sub).trans (hAcomp a haA)
    exact ⟨W, hWo, hzW, fun q hq => hN'A (hWsub hq), hN'A (hWsub ⟨hzW, hzS⟩)⟩
  have hloc : ∀ z ∈ closure A ∩ K, ∃ W : Set E₃, IsOpen W ∧ z ∈ W ∧ W ∩ K ⊆ closure A := by
    rintro z ⟨hzcl, hzS, hzle⟩
    rcases lt_or_eq_of_le (show h z ≤ c from hzle) with hzc | hzc
    · obtain ⟨W, hWo, hzW, hWA, -⟩ := hbelow z hzcl hzS hzc
      exact ⟨W, hWo, hzW, fun q hq => subset_closure (hWA ⟨hq.1, hq.2.1⟩)⟩
    · exact hlev z hzcl hzS hzc
  let u : Set E₃ := ⋃₀ {W | IsOpen W ∧ W ∩ K ⊆ closure A}
  let v : Set E₃ := (closure A)ᶜ
  have hu : IsOpen u := isOpen_sUnion fun W hW => hW.1
  have hv : IsOpen v := isClosed_closure.isOpen_compl
  have huK : u ∩ K ⊆ closure A := by
    rintro z ⟨⟨W, hW, hzW⟩, hzK⟩
    exact hW.2 ⟨hzW, hzK⟩
  have hCuv : C ⊆ u ∪ v := by
    intro z hz
    by_cases hzcl : z ∈ closure A
    · obtain ⟨W, hWo, hzW, hWsub⟩ := hloc z ⟨hzcl, hCK hz⟩
      exact Or.inl ⟨W, ⟨hWo, hWsub⟩, hzW⟩
    · exact Or.inr hzcl
  have hxu : x ∈ u := by
    obtain ⟨W, hWo, hxW, hWsub⟩ := hloc x ⟨subset_closure hxA, hCK hxC⟩
    exact ⟨W, ⟨hWo, hWsub⟩, hxW⟩
  rintro y ⟨hyC, hyc⟩
  by_contra hyA
  have hyv : y ∈ v := by
    intro hycl
    obtain ⟨-, -, -, -, hyA'⟩ := hbelow y hycl (hCK hyC).1 hyc
    exact hyA hyA'
  obtain ⟨z, hzC, hzu, hzv⟩ := hC u v hu hv hCuv ⟨x, hxC, hxu⟩ ⟨y, hyC, hyv⟩
  exact hzv (huK ⟨hzu, hCK hzC⟩)

/-- `lem:sublevel-closure`, case `λ = 1`, `p` sub-merging: closing up the sublevel at the level
of a sub-merging saddle (the only critical point at its level) lowers the number of components
by one. -/
theorem componentCount_sublevel_closure_subMerging {S : Set E₃} {n : E₃ → E₃}
    (hS : IsSmoothEmbeddedSurface S) (hn : IsUnitNormalField S n) {h : E₃ → ℝ}
    (hh : ContDiff ℝ (⊤ : ℕ∞) h) (hM : IsSurfaceMorse S n h)
    (hinj : Set.InjOn h {p | IsSurfaceCriticalPoint S h p}) {p : E₃}
    (hsm : IsSubMergingSaddle S n h p) :
    componentCount (S ∩ {x | h x ≤ h p}) + 1 = componentCount (S ∩ {x | h x < h p}) := by
  obtain ⟨hp, hk, x₀, hx₀, y₀, hy₀, hne₀, hpx₀, hpy₀⟩ := hsm
  have hh1 : ContDiff ℝ 1 h := hh.of_le (by exact_mod_cast le_top)
  have hlc : ∀ z ∈ S, ∀ O : Set E₃, IsOpen O → z ∈ O →
      ∃ N ⊆ S ∩ O, IsPreconnected N ∧ N ∈ 𝓝[S] z :=
    fun _ hz _ hO hzO => hS.exists_preconnected_nhdsWithin hz hO hzO
  obtain ⟨U, hU, hpU, T₁, T₂, hT, hT₁, hT₂, hp₁, hp₂, hcl⟩ :=
    exists_saddle_sublevel_nhds hS hn hh hp (hM p hp) hk
  set c := h p with hc
  set N := S ∩ {x | h x < c} with hNdef
  set K := S ∩ {x | h x ≤ c} with hKdef
  have hNK : N ⊆ K := fun y hy => ⟨hy.1, show h y ≤ c from le_of_lt hy.2⟩
  have hpK : p ∈ K := ⟨hp.1, show h p ≤ c from le_rfl⟩
  obtain ⟨t₁, ht₁⟩ := hT₁.nonempty
  obtain ⟨t₂, ht₂⟩ := hT₂.nonempty
  have hTN : T₁ ∪ T₂ ⊆ N := by
    rw [← hT]; exact fun y hy => ⟨hy.1.1, hy.2⟩
  have ht₁N : t₁ ∈ N := hTN (Or.inl ht₁)
  have ht₂N : t₂ ∈ N := hTN (Or.inr ht₂)
  set A₁ := connectedComponentIn N t₁ with hA₁
  set A₂ := connectedComponentIn N t₂ with hA₂
  have hsub₁ : T₁ ⊆ A₁ :=
    hT₁.isPreconnected.subset_connectedComponentIn ht₁ (subset_union_left.trans hTN)
  have hsub₂ : T₂ ⊆ A₂ :=
    hT₂.isPreconnected.subset_connectedComponentIn ht₂ (subset_union_right.trans hTN)
  have hUA : S ∩ U ∩ {x | h x < c} ⊆ A₁ ∪ A₂ := by
    rw [hT]; exact union_subset_union hsub₁ hsub₂
  -- step 1: the components of `N` adjoining `p` are `A₁` and `A₂`, and these are distinct
  have hcomp12 : ∀ w ∈ N, p ∈ closure (connectedComponentIn N w) →
      connectedComponentIn N w = A₁ ∨ connectedComponentIn N w = A₂ := by
    intro w _ hpw
    obtain ⟨a, haU, haw⟩ := mem_closure_iff.mp hpw U hU hpU
    have haN : a ∈ N := connectedComponentIn_subset N w haw
    rw [connectedComponentIn_eq haw]
    rcases hUA ⟨⟨haN.1, haU⟩, haN.2⟩ with ha | ha
    · left; rw [hA₁, connectedComponentIn_eq ha]
    · right; rw [hA₂, connectedComponentIn_eq ha]
  have hA12 : A₁ ≠ A₂ := by
    intro heq
    apply hne₀
    rcases hcomp12 x₀ hx₀ hpx₀ with h1 | h1 <;> rcases hcomp12 y₀ hy₀ hpy₀ with h2 | h2 <;>
      rw [h1, h2] <;> first | rfl | exact heq | exact heq.symm
  -- regular level points adjoining a union of components
  have hreg_lev : ∀ A : Set E₃, A ⊆ N → (∀ z ∈ A, connectedComponentIn N z ⊆ A) →
      ∀ z ∈ closure A, z ∈ S → h z = c → z ≠ p → ∃ W : Set E₃, IsOpen W ∧ z ∈ W ∧
        W ∩ K ⊆ closure A := by
    intro A hAN hAcomp z hzcl hzS hzc hzp
    have hreg : ¬ IsSurfaceCriticalPoint S h z := fun hcz => hzp (hinj hcz hp hzc)
    obtain ⟨W, hWo, hzW, hB, hWcl⟩ := levelBelow_adj_of_regular hS hh1 hzS hzc hreg
    obtain ⟨a, haW, haA⟩ := mem_closure_iff.mp hzcl W hWo hzW
    have haN := hAN haA
    have hBA : S ∩ W ∩ {y | h y < c} ⊆ A := fun b hb =>
      hAcomp a haA (hB a ⟨⟨haN.1, haW⟩, haN.2⟩ b hb)
    refine ⟨W, hWo, hzW, ?_⟩
    rintro q ⟨hqW, hqS, hqle⟩
    rcases lt_or_eq_of_le (show h q ≤ c from hqle) with hqc | hqc
    · exact subset_closure (hBA ⟨⟨hqS, hqW⟩, hqc⟩)
    · exact closure_mono hBA (hWcl q ⟨hqS, hqW⟩ hqc)
  have hN12 : A₁ ∪ A₂ ⊆ N :=
    union_subset (connectedComponentIn_subset _ _) (connectedComponentIn_subset _ _)
  have hsat12 : ∀ z ∈ A₁ ∪ A₂, connectedComponentIn N z ⊆ A₁ ∪ A₂ := by
    rintro z (hz | hz)
    · rw [← connectedComponentIn_eq hz]; exact subset_union_left
    · rw [← connectedComponentIn_eq hz]; exact subset_union_right
  -- step 2: preconnected subsets of `K` through `A₁ ∪ A₂` stay in `A₁ ∪ A₂` below `c`
  have hunion : ∀ C : Set E₃, IsPreconnected C → C ⊆ K → ∀ x ∈ C, x ∈ A₁ ∪ A₂ →
      C ∩ {y | h y < c} ⊆ A₁ ∪ A₂ := by
    intro C hC hCK x hxC hxA
    refine preconnected_inter_levelBelow_subset_of_saturated hh.continuous hN12 hsat12 ?_ hlc
      hC hCK hxC hxA
    intro z hzcl hzS hzc
    by_cases hzp : z = p
    · refine ⟨U, hU, hzp ▸ hpU, ?_⟩
      rintro q ⟨hqU, hqS, hqle⟩
      rcases lt_or_eq_of_le (show h q ≤ c from hqle) with hqc | hqc
      · exact subset_closure (hUA ⟨⟨hqS, hqU⟩, hqc⟩)
      · rcases hcl q ⟨hqS, hqU⟩ hqc with h1 | h1
        · exact closure_mono (hsub₁.trans subset_union_left) h1
        · exact closure_mono (hsub₂.trans subset_union_right) h1
    · exact hreg_lev _ hN12 hsat12 z hzcl hzS hzc hzp
  -- step 2': preconnected subsets of `K` through any other component stay in it below `c`
  have hother : ∀ x ∈ N, x ∉ A₁ ∪ A₂ → ∀ C : Set E₃, IsPreconnected C → C ⊆ K → x ∈ C →
      C ∩ {y | h y < c} ⊆ connectedComponentIn N x := by
    intro x hx hxA C hC hCK hxC
    have hsat : ∀ z ∈ connectedComponentIn N x,
        connectedComponentIn N z ⊆ connectedComponentIn N x := by
      intro z hz
      rw [← connectedComponentIn_eq hz]
    refine preconnected_inter_levelBelow_subset_of_saturated hh.continuous
      (connectedComponentIn_subset _ _) hsat ?_ hlc hC hCK hxC (mem_connectedComponentIn hx)
    intro z hzcl hzS hzc
    by_cases hzp : z = p
    · exfalso
      rw [hzp] at hzcl
      rcases hcomp12 x hx hzcl with h1 | h1
      · exact hxA (Or.inl (h1 ▸ mem_connectedComponentIn hx))
      · exact hxA (Or.inr (h1 ▸ mem_connectedComponentIn hx))
    · exact hreg_lev _ (connectedComponentIn_subset _ _) hsat z hzcl hzS hzc hzp
  -- `p` joins `A₁` and `A₂` in `K`
  have hp1K : p ∈ connectedComponentIn K t₁ :=
    mem_connectedComponentIn_of_mem_closure_componentIn hNK ht₁N hpK (closure_mono hsub₁ hp₁)
  have hp2K : p ∈ connectedComponentIn K t₂ :=
    mem_connectedComponentIn_of_mem_closure_componentIn hNK ht₂N hpK (closure_mono hsub₂ hp₂)
  have hK12 : connectedComponentIn K t₁ = connectedComponentIn K t₂ :=
    (connectedComponentIn_eq hp1K).trans (connectedComponentIn_eq hp2K).symm
  have ht₁A₂ : t₁ ∉ A₂ := by
    intro h'
    apply hA12
    rw [hA₁, hA₂, connectedComponentIn_eq h']
  -- counting
  have hcont : Continuous (Set.inclusion hNK) := continuous_inclusion hNK
  set g := hcont.connectedComponentsMap with hg
  have hF : ∀ a : N, g (ConnectedComponents.mk a) =
      ConnectedComponents.mk (Set.inclusion hNK a) := fun a => hcont.connectedComponentsMap_mk a
  set s : Set (ConnectedComponents N) :=
    univ \ {ConnectedComponents.mk (⟨t₂, ht₂N⟩ : N)} with hs
  have hnotA₂ : ∀ a : N, ConnectedComponents.mk a ∈ s → (a : E₃) ∉ A₂ := by
    intro a ha h'
    apply ha.2
    change ConnectedComponents.mk a = ConnectedComponents.mk (⟨t₂, ht₂N⟩ : N)
    rw [sublevelClosureZero_mk_eq_mk_iff]
    change t₂ ∈ connectedComponentIn N a
    rw [← connectedComponentIn_eq h']
    exact mem_connectedComponentIn ht₂N
  have hinjOn : InjOn g s := by
    intro u hu v hv huv
    obtain ⟨a, rfl⟩ := ConnectedComponents.surjective_coe u
    obtain ⟨b, rfl⟩ := ConnectedComponents.surjective_coe v
    have ha2 := hnotA₂ a hu
    have hb2 := hnotA₂ b hv
    rw [hF, hF, sublevelClosureZero_mk_eq_mk_iff] at huv
    change (b : E₃) ∈ connectedComponentIn K a at huv
    rw [sublevelClosureZero_mk_eq_mk_iff]
    have hbC : (b : E₃) ∈ connectedComponentIn K a ∩ {y | h y < c} := ⟨huv, b.2.2⟩
    by_cases haA : (a : E₃) ∈ A₁ ∪ A₂
    · have ha1 : (a : E₃) ∈ A₁ := haA.resolve_right ha2
      have hb1 : (b : E₃) ∈ A₁ :=
        (hunion _ isPreconnected_connectedComponentIn (connectedComponentIn_subset K a) a
          (mem_connectedComponentIn (hNK a.2)) haA hbC).resolve_right hb2
      rw [← connectedComponentIn_eq ha1]
      exact hb1
    · exact hother a a.2 haA _ isPreconnected_connectedComponentIn
        (connectedComponentIn_subset K a) (mem_connectedComponentIn (hNK a.2)) hbC
  have himage : g '' s = univ := by
    refine eq_univ_of_forall fun u => ?_
    obtain ⟨x, rfl⟩ := ConnectedComponents.surjective_coe u
    have hxK : (x : E₃) ∈ K := x.2
    obtain ⟨w, hwN, hxw⟩ : ∃ w ∈ N, (x : E₃) ∈ connectedComponentIn K w := by
      rcases lt_or_eq_of_le (show h x ≤ c from hxK.2) with hxc | hxc
      · exact ⟨x, ⟨hxK.1, hxc⟩, mem_connectedComponentIn hxK⟩
      · by_cases hxp : (x : E₃) = p
        · exact ⟨t₁, ht₁N, hxp ▸ hp1K⟩
        · have hreg : ¬ IsSurfaceCriticalPoint S h x := fun hcx => hxp (hinj hcx hp hxc)
          obtain ⟨w, hwN, hxw⟩ :=
            exists_mem_closure_connectedComponentIn_levelBelow hS hh1 hxK.1 hxc hreg
          exact ⟨w, hwN, mem_connectedComponentIn_of_mem_closure_componentIn hNK hwN hxK hxw⟩
    obtain ⟨a, haN, ha2, hxa⟩ : ∃ a ∈ N, a ∉ A₂ ∧ (x : E₃) ∈ connectedComponentIn K a := by
      by_cases hw2 : w ∈ A₂
      · refine ⟨t₁, ht₁N, ht₁A₂, ?_⟩
        have hwK : w ∈ connectedComponentIn K t₂ := connectedComponentIn_mono t₂ hNK hw2
        rw [hK12, connectedComponentIn_eq hwK]
        exact hxw
      · exact ⟨w, hwN, hw2, hxw⟩
    refine ⟨ConnectedComponents.mk ⟨a, haN⟩, ⟨mem_univ _, ?_⟩, ?_⟩
    · intro h'
      change ConnectedComponents.mk (⟨a, haN⟩ : N) = ConnectedComponents.mk (⟨t₂, ht₂N⟩ : N)
        at h'
      rw [sublevelClosureZero_mk_eq_mk_iff] at h'
      apply ha2
      rw [hA₂, ← connectedComponentIn_eq h']
      exact mem_connectedComponentIn haN
    · rw [hF, sublevelClosureZero_mk_eq_mk_iff]
      exact hxa
  have hcardK : componentCount K = s.encard := by
    rw [componentCount, ← Set.encard_univ, ← himage, hinjOn.encard_image]
  rw [hcardK, componentCount, ← Set.encard_univ]
  exact Set.encard_sdiff_singleton_add_one (mem_univ _)

end LiquidDrop

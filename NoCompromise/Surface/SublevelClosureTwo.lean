module

public import NoCompromise.Surface.SublevelAttach
public import NoCompromise.Surface.SublevelClosureLocal
public import NoCompromise.Surface.MorseCoordsPlanar

@[expose] public section

/-!
# `lem:sublevel-closure`, case `λ = 2`

At an index-two critical point `p` of a Morse function `h` on an embedded surface `S` whose
critical values are distinct, adjoining the level set `{h = h p}` to the open sublevel
`S ∩ {h < h p}` does not change the number of components.
-/

noncomputable section

open Set Filter
open scoped Topology

namespace LiquidDrop

local notation "E2" => EuclideanSpace ℝ (Fin 2)

/-- An embedded surface has no isolated points: every `p ∈ S` lies in the closure of the
punctured trace `(U ∩ S) \ {p}` of any open `U ∋ p`. -/
theorem IsSmoothEmbeddedSurface.mem_closure_inter_diff_singleton {S : Set E₃}
    (hS : IsSmoothEmbeddedSurface S) {p : E₃} (hp : p ∈ S) {U : Set E₃} (hU : IsOpen U)
    (hpU : p ∈ U) : p ∈ closure ((U ∩ S) \ {p}) := by
  obtain ⟨e, -, -, -, -, -, hps, he0, -, -⟩ := hS.exists_projection_chart hp 0
  have h0t : (0 : E2) ∈ e.target := he0 ▸ e.map_source hps
  have hsymm0 : e.symm 0 = ⟨p, hp⟩ := by
    rw [← he0]
    exact e.left_inv hps
  set f : E2 → E₃ := fun y => (e.symm y : E₃) with hf
  have hfc : Tendsto f (𝓝 0) (𝓝 p) := by
    have := (continuous_subtype_val.continuousAt (x := e.symm 0)).comp
      (e.continuousAt_symm h0t)
    have hp' : f 0 = p := by simp [hf, hsymm0]
    rw [← hp']
    exact this
  have hfc' : Tendsto f (𝓝[≠] 0) (𝓝 p) := hfc.mono_left nhdsWithin_le_nhds
  refine mem_closure_of_tendsto hfc' ?_
  have ht : ∀ᶠ y in 𝓝[≠] (0 : E2), y ∈ e.target :=
    nhdsWithin_le_nhds (e.open_target.mem_nhds h0t)
  have hUev : ∀ᶠ y in 𝓝[≠] (0 : E2), f y ∈ U := hfc' (hU.mem_nhds hpU)
  have hne : ∀ᶠ y in 𝓝[≠] (0 : E2), y ≠ 0 := self_mem_nhdsWithin
  filter_upwards [ht, hUev, hne] with y hyt hyU hy0
  refine ⟨⟨hyU, (e.symm y).2⟩, ?_⟩
  intro hyp
  apply hy0
  have : e.symm y = ⟨p, hp⟩ := Subtype.ext hyp
  rw [← e.right_inv hyt, this, he0]

/-- `lem:sublevel-closure`, case `λ = 2`, level adjacency: with `c := h p` for an index-two
critical point `p` and `h` injective on critical points, every level-`c` point `q` of `S` has an
open neighbourhood whose lower trace lies in one component of `S ∩ {h < c}` and has every
level-`c` point of `S ∩ U` in its closure. -/
theorem levelBelow_adj_of_index_two {S : Set E₃} {n : E₃ → E₃}
    (hS : IsSmoothEmbeddedSurface S) (hn : IsUnitNormalField S n) {h : E₃ → ℝ}
    (hh : ContDiff ℝ (⊤ : ℕ∞) h) (hM : IsSurfaceMorse S n h)
    (hinj : Set.InjOn h {p | IsSurfaceCriticalPoint S h p}) {p : E₃}
    (hp : IsSurfaceCriticalPoint S h p) (hk : surfaceIndex S n h p = 2) :
    ∀ q ∈ S, h q = h p → ∃ U : Set E₃, IsOpen U ∧ q ∈ U ∧
      (∀ a ∈ S ∩ U ∩ {y | h y < h p}, ∀ b ∈ S ∩ U ∩ {y | h y < h p},
        b ∈ connectedComponentIn (S ∩ {y | h y < h p}) a) ∧
      ∀ q' ∈ S ∩ U, h q' = h p → q' ∈ closure (S ∩ U ∩ {y | h y < h p}) := by
  intro q hq hqc
  by_cases hqp : q = p
  · subst hqp
    obtain ⟨U, hUo, hpU, -, hlt, hconn⟩ :=
      exists_punctured_sublevel_of_index_two hS hn hh hp (hM q hp) morseCoordsStatement hk
    have hsubN : (U ∩ S) \ {q} ⊆ S ∩ {y | h y < h q} := fun y hy => ⟨hy.1.2, hlt hy⟩
    have hsub : (U ∩ S) \ {q} ⊆ S ∩ U ∩ {y | h y < h q} :=
      fun y hy => ⟨⟨hy.1.2, hy.1.1⟩, hlt hy⟩
    have hmem : ∀ y ∈ S ∩ U ∩ {y | h y < h q}, y ∈ (U ∩ S) \ {q} := by
      rintro y ⟨⟨hyS, hyU⟩, hy⟩
      refine ⟨⟨hyU, hyS⟩, ?_⟩
      rintro rfl
      exact lt_irrefl (h y) hy
    refine ⟨U, hUo, hpU, fun a ha b hb => ?_, fun q' hq' hq'c => ?_⟩
    · exact hconn.isPreconnected.subset_connectedComponentIn (hmem a ha) hsubN (hmem b hb)
    · by_cases hq'p : q' = q
      · subst hq'p
        exact closure_mono hsub (hS.mem_closure_inter_diff_singleton hq hUo hpU)
      · exfalso
        have : h q' < h q := hlt ⟨⟨hq'.2, hq'.1⟩, hq'p⟩
        rw [hq'c] at this
        exact lt_irrefl _ this
  · have hreg : ¬ IsSurfaceCriticalPoint S h q := fun hc => hqp (hinj hc hp hqc)
    exact levelBelow_adj_of_regular hS (hh.of_le (by exact_mod_cast le_top)) hq hqc hreg

/-- `lem:sublevel-closure`, case `λ = 2`: at an index-two critical point `p` of a Morse function
with distinct critical values, `S ∩ {h ≤ h p}` and `S ∩ {h < h p}` have the same number of
components. -/
theorem componentCount_sublevel_closure_index_two {S : Set E₃} {n : E₃ → E₃}
    (hS : IsSmoothEmbeddedSurface S) (hn : IsUnitNormalField S n) {h : E₃ → ℝ}
    (hh : ContDiff ℝ (⊤ : ℕ∞) h) (hM : IsSurfaceMorse S n h)
    (hinj : Set.InjOn h {p | IsSurfaceCriticalPoint S h p}) {p : E₃}
    (hp : IsSurfaceCriticalPoint S h p) (hk : surfaceIndex S n h p = 2) :
    componentCount (S ∩ {x | h x ≤ h p}) = componentCount (S ∩ {x | h x < h p}) := by
  have hh1 : ContDiff ℝ 1 h := hh.of_le (by exact_mod_cast le_top)
  have hadj := levelBelow_adj_of_index_two hS hn hh hM hinj hp hk
  set N := S ∩ {y | h y < h p} with hNdef
  set K := S ∩ {y | h y ≤ h p} with hKdef
  have hNK : N ⊆ K := fun y hy => ⟨hy.1, show h y ≤ h p from le_of_lt hy.2⟩
  -- a preconnected piece of `N` adjoining `x ∈ K` lies in the component of `K` through `x`
  have hjoin : ∀ x ∈ K, ∀ D : Set E₃, IsPreconnected D → D ⊆ N → x ∈ closure D →
      ∀ w ∈ D, w ∈ connectedComponentIn K x := by
    intro x hxK D hD hDN hxD w hw
    have hpre : IsPreconnected (insert x D) :=
      hD.subset_closure (subset_insert x D)
        (insert_subset hxD subset_closure)
    have hsub : insert x D ⊆ K := insert_subset hxK (hDN.trans hNK)
    exact hpre.subset_connectedComponentIn (mem_insert x D) hsub (mem_insert_of_mem x hw)
  refine (componentCount_eq_of_connectedComponentIn hNK ?_ ?_).symm
  · intro x hxK
    rcases lt_or_eq_of_le (show h x ≤ h p from hxK.2) with hxc | hxc
    · exact ⟨x, ⟨hxK.1, hxc⟩, mem_connectedComponentIn hxK⟩
    · by_cases hxp : x = p
      · subst hxp
        obtain ⟨U, hUo, hpU, -, hlt, hconn⟩ :=
          exists_punctured_sublevel_of_index_two hS hn hh hp (hM x hp) morseCoordsStatement hk
        obtain ⟨w, hw⟩ := hconn.nonempty
        have hDN : (U ∩ S) \ {x} ⊆ N := fun y hy => ⟨hy.1.2, hlt hy⟩
        exact ⟨w, hDN hw, hjoin x hxK _ hconn.isPreconnected hDN
          (hS.mem_closure_inter_diff_singleton hp.1 hUo hpU) w hw⟩
      · have hreg : ¬ IsSurfaceCriticalPoint S h x := fun hc => hxp (hinj hc hp hxc)
        obtain ⟨w, hwN, hxw⟩ :=
          exists_mem_closure_connectedComponentIn_levelBelow hS hh1 hxK.1 hxc hreg
        exact ⟨w, hwN, hjoin x hxK _ isPreconnected_connectedComponentIn
          (connectedComponentIn_subset _ _) hxw w (mem_connectedComponentIn hwN)⟩
  · intro x hxN y hyN
    constructor
    · intro hy
      have hCK : connectedComponentIn K x ⊆ K \ (∅ : Set E₃) := by
        rw [sdiff_empty]
        exact connectedComponentIn_subset _ _
      exact preconnected_inter_levelBelow_subset_of_adj hh.continuous
        (fun q hq hqc _ => hadj q hq hqc)
        (fun _ hz _ hO hzO => hS.exists_preconnected_nhdsWithin hz hO hzO)
        isPreconnected_connectedComponentIn hCK (mem_connectedComponentIn (hNK hxN)) hxN.2
        ⟨hy, hyN.2⟩
    · intro hy
      exact connectedComponentIn_mono x hNK hy

end LiquidDrop

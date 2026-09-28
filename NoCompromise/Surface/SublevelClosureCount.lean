import NoCompromise.Surface.SublevelClosureSaddle
import NoCompromise.Surface.SublevelAttach

/-!
# Component counts in `lem:sublevel-closure`: the non-merging saddle

If every point of the level `{h = c}` has a neighbourhood whose lower trace lies in a single
component of `{h < c}` and adjoins all level points there, closing up the sublevel creates and
joins no components. This applies at an index-one critical point that is not sub-merging.
-/

noncomputable section

open Set Filter
open scoped Topology

namespace LiquidDrop

/-- `lem:sublevel-closure`, count step: if every level-`c` point has a neighbourhood whose lower
trace lies in one component of `S ∩ {h < c}` and adjoins every level point of the neighbourhood,
then `S ∩ {h ≤ c}` and `S ∩ {h < c}` have the same number of components. -/
theorem componentCount_sublevel_eq_of_adj {S : Set E₃} (hS : IsSmoothEmbeddedSurface S)
    {h : E₃ → ℝ} (hhc : Continuous h) {c : ℝ}
    (hadj : ∀ q ∈ S, h q = c → ∃ U : Set E₃, IsOpen U ∧ q ∈ U ∧
      (∀ a ∈ S ∩ U ∩ {y | h y < c}, ∀ b ∈ S ∩ U ∩ {y | h y < c},
        b ∈ connectedComponentIn (S ∩ {y | h y < c}) a) ∧
      ∀ q' ∈ S ∩ U, h q' = c → q' ∈ closure (S ∩ U ∩ {y | h y < c})) :
    componentCount (S ∩ {y | h y ≤ c}) = componentCount (S ∩ {y | h y < c}) := by
  have hNK : S ∩ {y | h y < c} ⊆ S ∩ {y | h y ≤ c} := fun y hy => ⟨hy.1, show h y ≤ c from le_of_lt hy.2⟩
  symm
  refine componentCount_eq_of_connectedComponentIn hNK ?_ ?_
  · rintro x ⟨hxS, hxc⟩
    rcases lt_or_eq_of_le (show h x ≤ c from hxc) with hlt | heq
    · exact ⟨x, ⟨hxS, hlt⟩, mem_connectedComponentIn ⟨hxS, hxc⟩⟩
    · obtain ⟨U, -, hxU, hB, hcl⟩ := hadj x hxS heq
      have hxcl := hcl x ⟨hxS, hxU⟩ heq
      obtain ⟨w, hw⟩ : (S ∩ U ∩ {y | h y < c}).Nonempty := by
        by_contra hne
        rw [not_nonempty_iff_eq_empty] at hne
        rw [hne, closure_empty] at hxcl
        exact hxcl
      have hwN : w ∈ S ∩ {y | h y < c} := ⟨hw.1.1, hw.2⟩
      have hBw : S ∩ U ∩ {y | h y < c} ⊆ connectedComponentIn (S ∩ {y | h y < c}) w :=
        fun b hb => hB w hw b hb
      have hxw : x ∈ closure (connectedComponentIn (S ∩ {y | h y < c}) w) :=
        closure_mono hBw hxcl
      have hpre : IsPreconnected (insert x (connectedComponentIn (S ∩ {y | h y < c}) w)) :=
        isPreconnected_connectedComponentIn.subset_closure (subset_insert _ _)
          (insert_subset hxw subset_closure)
      have hsub : insert x (connectedComponentIn (S ∩ {y | h y < c}) w) ⊆
          S ∩ {y | h y ≤ c} :=
        insert_subset ⟨hxS, hxc⟩ ((connectedComponentIn_subset _ _).trans hNK)
      exact ⟨w, hwN, hpre.subset_connectedComponentIn (mem_insert x _) hsub
        (mem_insert_of_mem _ (mem_connectedComponentIn hwN))⟩
  · intro x hx y hy
    constructor
    · intro hyx
      have hC : connectedComponentIn (S ∩ {y | h y ≤ c}) x ⊆ (S ∩ {y | h y ≤ c}) \ ∅ := by
        rw [sdiff_empty]; exact connectedComponentIn_subset _ _
      exact preconnected_inter_levelBelow_subset_of_adj (Z := ∅) hhc
        (fun q hq hqc _ => hadj q hq hqc)
        (fun _ hz _ hO hzO => hS.exists_preconnected_nhdsWithin hz hO hzO)
        isPreconnected_connectedComponentIn hC
        (mem_connectedComponentIn (hNK hx)) hx.2 ⟨hyx, hy.2⟩
    · intro hyx
      exact connectedComponentIn_mono x hNK hyx

variable {S : Set E₃}

/-- `lem:sublevel-closure`, case `λ = 1`, `p` not sub-merging: closing up the sublevel at the
level of a non-merging saddle does not change the number of components. -/
theorem componentCount_sublevel_closure_saddle_of_not_subMerging {n : E₃ → E₃}
    (hS : IsSmoothEmbeddedSurface S) (hn : IsUnitNormalField S n) {h : E₃ → ℝ}
    (hh : ContDiff ℝ (⊤ : ℕ∞) h) (hM : IsSurfaceMorse S n h)
    (hinj : InjOn h {p | IsSurfaceCriticalPoint S h p}) {p : E₃}
    (hp : IsSurfaceCriticalPoint S h p) (hk : surfaceIndex S n h p = 1)
    (hns : ¬ IsSubMergingSaddle S n h p) :
    componentCount (S ∩ {x | h x ≤ h p}) = componentCount (S ∩ {x | h x < h p}) := by
  have hh1 : ContDiff ℝ 1 h := hh.of_le (by norm_cast)
  apply componentCount_sublevel_eq_of_adj hS hh.continuous
  intro q hq hqc
  by_cases hqp : q = p
  · subst hqp
    obtain ⟨U, hU, hqU, T₁, T₂, hT, hT₁, hT₂, hp₁, hp₂, hcl⟩ :=
      exists_saddle_sublevel_nhds hS hn hh hp (hM q hp) hk
    obtain ⟨t₁, ht₁⟩ := hT₁.nonempty
    obtain ⟨t₂, ht₂⟩ := hT₂.nonempty
    have hTN : T₁ ∪ T₂ ⊆ S ∩ {x | h x < h q} := by
      rw [← hT]; exact fun y hy => ⟨hy.1.1, hy.2⟩
    have hsub₁ : T₁ ⊆ connectedComponentIn (S ∩ {x | h x < h q}) t₁ :=
      hT₁.isPreconnected.subset_connectedComponentIn ht₁ (subset_union_left.trans hTN)
    have hsub₂ : T₂ ⊆ connectedComponentIn (S ∩ {x | h x < h q}) t₂ :=
      hT₂.isPreconnected.subset_connectedComponentIn ht₂ (subset_union_right.trans hTN)
    have heq12 : connectedComponentIn (S ∩ {x | h x < h q}) t₁ =
        connectedComponentIn (S ∩ {x | h x < h q}) t₂ := by
      by_contra hne
      exact hns ⟨hp, hk, t₁, hTN (Or.inl ht₁), t₂, hTN (Or.inr ht₂), hne,
        closure_mono hsub₁ hp₁, closure_mono hsub₂ hp₂⟩
    have hall : S ∩ U ∩ {x | h x < h q} ⊆ connectedComponentIn (S ∩ {x | h x < h q}) t₁ := by
      rw [hT]
      rintro y (hy | hy)
      · exact hsub₁ hy
      · rw [heq12]; exact hsub₂ hy
    refine ⟨U, hU, hqU, fun a ha b hb => ?_, fun q' hq' hq'c => ?_⟩
    · rw [← connectedComponentIn_eq (hall ha)]
      exact hall hb
    · rw [hT]
      rcases hcl q' hq' hq'c with h1 | h2
      · exact closure_mono subset_union_left h1
      · exact closure_mono subset_union_right h2
  · have hreg : ¬ IsSurfaceCriticalPoint S h q := fun hcq =>
      hqp (hinj hcq hp hqc)
    exact levelBelow_adj_of_regular hS hh1 hq hqc hreg

end LiquidDrop
